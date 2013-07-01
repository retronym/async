
/*
 * Copyright (C) 2012 Typesafe Inc. <http://www.typesafe.com>
 */

package scala.async

import scala.tools.nsc.Global
import scala.tools.nsc.transform.TypingTransformers

private[async] trait AsyncMacro extends TypingTransformers with AnfTransform with TransformUtils2 with Lifter with ExprBuilder with AsyncTransform {
  val global: Global
  val callSiteTyper: global.analyzer.Typer

  import global._

  abstract class MacroTypingTransformer extends TypingTransformer(callSiteTyper.context.unit) {
    currentOwner = callSiteTyper.context.owner
    def currOwner: Symbol = currentOwner
    localTyper = global.analyzer.newTyper(callSiteTyper.context.make(unit = callSiteTyper.context.unit))
  }

  def transformAt(tree: Tree)(f: PartialFunction[Tree, (analyzer.Context => Tree)]) = {
    object trans extends MacroTypingTransformer {
      override def transform(tree: Tree): Tree = {
        if (f.isDefinedAt(tree)) {
          f(tree)(localTyper.context)
        } else super.transform(tree)
      }
    }
    trans.transform(tree)
  }

  def changeOwner(tree: Tree, oldOwner: Symbol, newOwner: Symbol): tree.type = {
    new ChangeOwnerAndModuleClassTraverser(oldOwner, newOwner).traverse(tree)
    tree
  }


  def spliceMethodBodies(liftables: List[Tree], tree: Tree, applyBody: Tree,
                         resumeBody: Tree): Tree = {

    val liftedSyms = liftables.map(_.symbol).toSet
    val stateMachineClass = tree.symbol
    liftedSyms.foreach {
      sym =>
        if (sym != null) {
          sym.owner = stateMachineClass
          if (sym.isModule)
            sym.moduleClass.owner = stateMachineClass
        }
    }
    // Replace the ValDefs in the splicee with Assigns to the corresponding lifted
    // fields. Similarly, replace references to them with references to the field.
    //
    // This transform will be only be run on the RHS of `def foo`.
    class UseFields extends MacroTypingTransformer {
      override def transform(tree: Tree): Tree = tree match {
        case _ if currentOwner == stateMachineClass =>
          super.transform(tree)
        case ValDef(_, _, _, rhs) if liftedSyms(tree.symbol) =>
          atOwner(currentOwner) {
            val fieldSym = tree.symbol
            val set = Assign(gen.mkAttributedStableRef(fieldSym.owner.thisType, fieldSym), transform(rhs))
            changeOwner(set, tree.symbol, currentOwner)
            localTyper.typedPos(tree.pos)(set)
          }
        case _: DefTree if liftedSyms(tree.symbol) =>
          EmptyTree
        case Ident(name) if liftedSyms(tree.symbol) =>
          val fieldSym = tree.symbol
          gen.mkAttributedStableRef(fieldSym.owner.thisType, fieldSym).setType(tree.tpe)
        case _ =>
          super.transform(tree)
      }
    }

    val liftablesUseFields = liftables.map {
      case vd: ValDef => vd
      case x =>
        val useField = new UseFields()
        //.substituteSymbols(fromSyms, toSyms)
        useField.atOwner(stateMachineClass)(useField.transform(x))
    }

    tree.children.foreach { t =>
      new ChangeOwnerAndModuleClassTraverser(callSiteTyper.context.owner, tree.symbol).traverse(t)
    }
    val treeSubst = tree

    def fixup(dd: DefDef, body: Tree, ctx: analyzer.Context): Tree = {
      // substitute old symbols for the new. We have to use the `UseFields` transform
      // afterwards to complete things.
      val spliceeAnfFixedOwnerSyms = body
      val useField = new UseFields()
      //.substituteSymbols(fromSyms, toSyms)
      val newRhs = useField.atOwner(dd.symbol)(useField.transform(spliceeAnfFixedOwnerSyms))
      val typer = global.analyzer.newTyper(ctx.make(dd, dd.symbol))
      treeCopy.DefDef(dd, dd.mods, dd.name, dd.tparams, dd.vparamss, dd.tpt, typer.typed(newRhs))
    }

    liftablesUseFields.foreach(t => if (t.symbol != null) stateMachineClass.info.decls.enter(t.symbol))

    val result0 = transformAt(treeSubst) {
      case t @ Template(parents, self, stats) =>
        (ctx: analyzer.Context) => {
          treeCopy.Template(t, parents, self, liftablesUseFields ++ stats)
        }
    }
    val result = transformAt(result0) {
      case dd@DefDef(_, name.apply, _, List(List(_)), _, _) =>
        (ctx: analyzer.Context) =>
          val typedTree = fixup(dd, changeOwner(applyBody, callSiteTyper.context.owner, dd.symbol), ctx)
          typedTree
      case dd@DefDef(_, name.resume, _, _, _, _)            =>
        (ctx: analyzer.Context) =>
          val changed = changeOwner(resumeBody, callSiteTyper.context.owner, dd.symbol)
          val res = fixup(dd, changed, ctx)
          res
    }
    result
  }

  class ChangeOwnerAndModuleClassTraverser(oldowner: Symbol, newowner: Symbol)
    extends ChangeOwnerTraverser(oldowner, newowner) {

    override def traverse(tree: Tree) {
      tree match {
        case _: DefTree => change(tree.symbol.moduleClass)
        case _ =>
      }
      super.traverse(tree)
    }
  }
}

private[async] trait AnfTransform extends TypingTransformers {
  self: AsyncMacro =>

  import global._
  import reflect.internal.Flags._

  def anfTransform(tree: Tree): List[Tree] = {
    // Must prepend the () for issue #31.
    val block = callSiteTyper.typed(Block(List(Literal(Constant(()))), tree))

    new SelectiveAnfTransform().transformToList(block)
  }

  sealed abstract class AnfMode

  case object Anf extends AnfMode

  case object Linearizing extends AnfMode

  class SelectiveAnfTransform extends MacroTypingTransformer {
    var mode: AnfMode = Anf
    def blockToList(tree: Tree): List[Tree] = tree match {
      case Block(stats, expr) => stats :+ expr
      case t                  => t :: Nil
    }
    def listToBlock(trees: List[Tree]): Tree = trees match {
      case init :+ last => atPos(trees.head.pos)(Block(init, last).setType(last.tpe))
    }

    def transformToList(tree: Tree): List[Tree] = blockToList(transform(tree))

    override def transform(tree: Tree): Tree = {
      def anfLinearize = {
        val trees: List[Tree] = mode match {
          case Anf         => anf.transformToList0(tree)
          case Linearizing => linearize.transformToList0(tree)
        }
        listToBlock(trees)
      }
      tree match {
        case _: ValDef | _: DefDef | _: Function | _: ClassDef | _: TypeDef =>
          atOwner(tree.symbol)(anfLinearize)
        case _: ModuleDef =>
          atOwner(tree.symbol.moduleClass orElse tree.symbol)(anfLinearize)
        case _ => anfLinearize
      }
    }

    private object trace {
      private var indent = -1

      def indentString = "  " * indent

      def apply[T](args: Any)(t: => T): T = {
        val prefix = mode.toString.toLowerCase
        indent += 1
        def oneLine(s: Any) = s.toString.replaceAll( """\n""", "\\\\n").take(127)
        try {
          AsyncUtils.trace(s"${indentString}$prefix(${oneLine(args)})")
          val result = t
          AsyncUtils.trace(s"${indentString}= ${oneLine(result)}")
          result
        } finally {
          indent -= 1
        }
      }
    }

    private object linearize {
      def transformToList(tree: Tree): List[Tree] = { mode = Linearizing; blockToList(transform(tree)) }

      def transformToList0(tree: Tree): List[Tree] = trace(tree) {
        val stats :+ expr = anf.transformToList(tree)
        expr match {
          case Apply(fun, args) if isAwait(fun) =>
            val valDef = defineVal(name.await, expr, tree.pos)
            stats :+ valDef :+ gen.mkAttributedStableRef(valDef.symbol)

          case If(cond, thenp, elsep) =>
            // if type of if-else is Unit don't introduce assignment,
            // but add Unit value to bring it into form expected by async transform
            if (expr.tpe =:= definitions.UnitTpe) {
              stats :+ expr :+ Literal(Constant(()))
            } else {
              val varDef = defineVar(name.ifRes, expr.tpe, tree.pos)
              def branchWithAssign(orig: Tree) = localTyper.typedPos(orig.pos)(
                orig match {
                  case Block(thenStats, thenExpr) => Block(thenStats, Assign(Ident(varDef.symbol), thenExpr))
                  case _                          => Assign(Ident(varDef.symbol), orig)
                }
              )
              val ifWithAssign = treeCopy.If(tree, cond, branchWithAssign(thenp), branchWithAssign(elsep))
              stats :+ varDef :+ ifWithAssign :+ gen.mkAttributedStableRef(varDef.symbol)
            }

          case Match(scrut, cases) =>
            // if type of match is Unit don't introduce assignment,
            // but add Unit value to bring it into form expected by async transform
            if (expr.tpe =:= definitions.UnitTpe) {
              stats :+ expr :+ Literal(Constant(()))
            }
            else {
              val varDef = defineVar(name.matchRes, expr.tpe, tree.pos)
              def typedAssign(lhs: Tree) =
                localTyper.typedPos(lhs.pos)(Assign(Ident(varDef.symbol), lhs))
              val casesWithAssign = cases map {
                case cd@CaseDef(pat, guard, body) =>
                  val newBody = body match {
                    case b @ Block(caseStats, caseExpr) => treeCopy.Block(b, caseStats, typedAssign(caseExpr))
                    case _                              => typedAssign(body)
                  }
                  treeCopy.CaseDef(cd, pat, guard, newBody)
              }
              val matchWithAssign = treeCopy.Match(tree, scrut, casesWithAssign)
              require(matchWithAssign.tpe != null, matchWithAssign)
              stats :+ varDef :+ matchWithAssign :+ gen.mkAttributedStableRef(varDef.symbol)
            }
          case _                   =>
            stats :+ expr
        }
      }

      def transformToList(trees: List[Tree]): List[Tree] = trees flatMap transformToList

      def transformToBlock(tree: Tree): Block = transformToList(tree) match {
        case stats :+ expr => Block(stats, expr)
      }

      private def defineVar(prefix: String, tp: Type, pos: Position): ValDef = {
        val sym = currOwner.newTermSymbol(name.fresh(prefix), pos, MUTABLE | STABLE /*TODO needed? */ | SYNTHETIC).setTypeSignature(tp)
        localTyper.typedPos(pos)(ValDef(sym, gen.mkZero(tp))).asInstanceOf[ValDef]
      }
    }

    private def defineVal(prefix: String, lhs: Tree, pos: Position): ValDef = {
      val sym = currOwner.newTermSymbol(name.fresh(prefix), pos, SYNTHETIC).setTypeSignature(lhs.tpe)
      changeOwner(lhs, currentOwner, sym)
      ValDef(sym, changeOwner(lhs, currentOwner, sym)).setType(NoType).setPos(pos)
    }

    private object anf {
      def transformToList(tree: Tree): List[Tree] = {mode = Anf; blockToList(transform(tree))}

      def transformToList0(tree: Tree): List[Tree] = trace(tree) {
        val containsAwait = tree exists isAwait
        if (!containsAwait) {
          List(tree)
        } else tree match {
          case Select(qual, sel) =>
            val stats :+ expr = linearize.transformToList(qual)
            stats :+ treeCopy.Select(tree, expr, sel)

          case treeInfo.Applied(fun, targs, argss) if argss.nonEmpty =>
            // we an assume that no await call appears in a by-name argument position,
            // this has already been checked.
            val funStats :+ simpleFun = linearize.transformToList(fun)
            def isAwaitRef(name: Name) = name.toString.startsWith(AnfTransform.this.name.await + "$")
            val (argStatss, argExprss): (List[List[List[Tree]]], List[List[Tree]]) =
              mapArgumentss[List[Tree]](fun, argss) {
                case Arg(expr, byName, _) if byName /*|| isPure(expr) TODO */    => (Nil, expr)
                case Arg(expr@Ident(name), _, _) if isAwaitRef(name)        => (Nil, expr) // TODO needed? // not typed, so it eludes the check in `isSafeToInline`
                case Arg(expr, _, argName)                                  =>
                  linearize.transformToList(expr) match {
                    case stats :+ expr1 =>
                      val valDef = defineVal(argName, expr1, expr1.pos)
                      require(valDef.tpe != null, valDef)
                      val stats1 = stats :+ valDef
                      //stats1.foreach(changeOwner(_, currentOwner, currentOwner.owner))
                      (stats1, gen.stabilize(gen.mkAttributedIdent(valDef.symbol)))
                  }
              }
            val applied = treeInfo.dissectApplied(tree)
            val core = if (targs.isEmpty) simpleFun else treeCopy.TypeApply(applied.callee, simpleFun, targs)
            val newApply = argExprss.foldLeft(core)(Apply(_, _)).setSymbol(tree.symbol)
            val typedNewApply = localTyper.typedPos(tree.pos)(newApply)
            funStats ++ argStatss.flatten.flatten :+ typedNewApply
          case Block(stats, expr)                           =>
            linearize.transformToList(stats :+ expr)

          case ValDef(mods, name, tpt, rhs) =>
            if (rhs exists isAwait) {
              val stats :+ expr = atOwner(currOwner.owner)(linearize.transformToList(rhs))
              stats.foreach(changeOwner(_, currOwner, currOwner.owner))
              stats :+ treeCopy.ValDef(tree, mods, name, tpt, expr)
            } else List(tree)

          case Assign(lhs, rhs) =>
            val stats :+ expr = linearize.transformToList(rhs)
            stats :+ treeCopy.Assign(tree, lhs, expr)

          case If(cond, thenp, elsep) =>
            val condStats :+ condExpr = linearize.transformToList(cond)
            val thenBlock = linearize.transformToBlock(thenp)
            val elseBlock = linearize.transformToBlock(elsep)
            // Typechecking with `condExpr` as the condition fails if the condition
            // contains an await. `ifTree.setType(tree.tpe)` also fails; it seems
            // we rely on this call to `typeCheck` descending into the branches.
            // But, we can get away with typechecking a throwaway `If` tree with the
            // original scrutinee and the new branches, and setting that type on
            // the real `If` tree.
            val iff = treeCopy.If(tree, condExpr, thenBlock, elseBlock)
            condStats :+ iff

          case Match(scrut, cases) =>
            val scrutStats :+ scrutExpr = linearize.transformToList(scrut)
            val caseDefs = cases map {
              case CaseDef(pat, guard, body) =>
                // extract local variables for all names bound in `pat`, and rewrite `body`
                // to refer to these.
                // TODO we can move this into ExprBuilder once we get rid of `AsyncDefinitionUseAnalyzer`.
                val block = linearize.transformToBlock(body)
                val (valDefs, mappings) = (pat collect {
                  case b@Bind(name, _) =>
                    val vd = defineVal(name.toTermName + AnfTransform.this.name.bindSuffix, gen.mkAttributedStableRef(b.symbol), b.pos)
                    (vd, (b.symbol, vd.symbol))
                }).unzip
                val (from, to) = mappings.unzip
                val b @ Block(stats1, expr1) = block.substituteSymbols(from, to).asInstanceOf[Block]
                val newBlock = treeCopy.Block(b, valDefs ++ stats1, expr1)
                treeCopy.CaseDef(tree, pat, guard, newBlock)
            }
            // Refer to comments the translation of `If` above.
            val typedMatch = treeCopy.Match(tree, scrutExpr, caseDefs)
            scrutStats :+ typedMatch

          case LabelDef(name, params, rhs) =>
            List(LabelDef(name, params, Block(linearize.transformToList(rhs), Literal(Constant(())))).setSymbol(tree.symbol))

          case TypeApply(fun, targs) =>
            val funStats :+ simpleFun = linearize.transformToList(fun)
            funStats :+ treeCopy.TypeApply(tree, simpleFun, targs)

          case _ =>
            List(tree)
        }
      }
    }

  }

}
