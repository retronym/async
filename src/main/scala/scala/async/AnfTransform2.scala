
/*
 * Copyright (C) 2012 Typesafe Inc. <http://www.typesafe.com>
 */

package scala.async

import scala.tools.nsc.Global
import scala.tools.nsc.transform.TypingTransformers

private[async] trait AsyncMacro extends TypingTransformers with AnfTransform2 with TransformUtils2 {
  val global: Global
  val callSiteTyper: global.analyzer.Typer

  import global._

  abstract class MacroTypingTransformer extends TypingTransformer(callSiteTyper.context.unit) {
    currentOwner = callSiteTyper.context.owner
    def currOwner: Symbol = currentOwner
    localTyper = global.analyzer.newTyper(callSiteTyper.context.make(callSiteTyper.context.unit))
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

  def spliceMethodBodies(tree: Tree, applyBody: Tree, resumeBody: Tree, lifted: Map[Symbol, Symbol]): Tree = {
    lifted.values.foreach(tree.symbol.info.decls.enter)

    val (fromSyms, toSyms) = lifted.toList.unzip
    // Replace the ValDefs in the splicee with Assigns to the corresponding lifted
    // fields. Similarly, replace references to them with references to the field.
    //
    // This transform will be only be run on the RHS of `def foo`.
    class UseFields extends MacroTypingTransformer {
      override def transform(tree: Tree): Tree = tree match {
        case ValDef(_, _, _, rhs) if toSyms.contains(tree.symbol) =>
          val fieldSym = tree.symbol
          val set = Assign(gen.mkAttributedStableRef(fieldSym.owner.thisType, fieldSym), transform(rhs))
          localTyper.typedPos(tree.pos)(set)
        case Ident(name) if toSyms.contains(tree.symbol) =>
          val fieldSym = tree.symbol
          gen.mkAttributedStableRef(fieldSym.owner.thisType, fieldSym).setType(tree.tpe)
        case _ =>
          super.transform(tree)
      }
    }

    tree.children.foreach { t =>
      new ChangeOwnerAndModuleClassTraverser(callSiteTyper.context.owner, tree.symbol).traverse(t)
    }
    val treeSubst = new UseFields().transform(tree.substituteSymbols(fromSyms, toSyms))

    def fixup(dd: DefDef, body: Tree, ctx: analyzer.Context): Tree = {
      new ChangeOwnerAndModuleClassTraverser(callSiteTyper.context.owner, dd.symbol).traverse(body)
      // substitute old symbols for the new. We have to use the `UseFields` transform
      // afterwards to complete things.
      val spliceeAnfFixedOwnerSyms = body.substituteSymbols(fromSyms, toSyms)
      val newRhs = new UseFields().transform(spliceeAnfFixedOwnerSyms)
      val typer = global.analyzer.newTyper(ctx.make(dd, dd.symbol))
      treeCopy.DefDef(dd, dd.mods, dd.name, dd.tparams, dd.vparamss, dd.tpt, typer.typed(newRhs))
    }
    val result = transformAt(treeSubst) {
      case dd @ DefDef(_, name.apply, _, List(List(_)), _, _) =>
        (ctx: analyzer.Context) =>
          val typedTree = fixup(dd, applyBody, ctx)
          typedTree
      case dd @ DefDef(_, name.resume, _, _, _, _) =>
        (ctx: analyzer.Context) =>
          val res = fixup(dd, resumeBody, ctx)
          res
    }
    //new ChangeOwnerAndModuleClassTraverser(callSiteTyper.context.owner, dd.symbol).traverse(result)
    result
  }

  class PostMacroTyper extends MacroTypingTransformer {
    override def transform(tree: Tree): Tree = {
      tree match {
        case Ident(name) if tree.tpe == null =>
          def lookup(name: Name) = {
            var res: Symbol = NoSymbol
            var ctx = localTyper.context
            while (res == NoSymbol && ctx.outer != ctx) {
              val s = ctx.scope lookup name
              if (s != NoSymbol)
                res = s
              else
                ctx = ctx.outer
            }
            res
          }
          val found = lookup(name)
          super.transform(tree)
        case _ =>
          super.transform(tree)
      }
    }
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

  def repairOwners(t: Tree, macroCallSiteOwner: Symbol): Tree = {
        // TODO: do this during tree construction, but that will require tracking the current owner in treemakers
    // TODO: assign more fine-grained positions
    // fixes symbol nesting, assigns positions
    def fixerUpper(origOwner: Symbol, pos: Position) = new Traverser {
      currentOwner = origOwner

      override def traverse(t: Tree) {
        if (t != EmptyTree && t.pos == NoPosition) {
          t.setPos(pos)
        }
        val correctOwner = if (currentOwner.isLocalDummy) currentOwner.owner else currentOwner

        t match {
//          case Function(_, _) if t.symbol == NoSymbol =>
//            t.symbol = currentOwner.newAnonymousFunctionValue(t.pos)
//            debug.patmat("new symbol for "+ (t, t.symbol.ownerChain))
          case Function(_, _) if (t.symbol.owner == NoSymbol) || (t.symbol.owner != correctOwner) =>
//            debug.patmat("fundef: "+ (t, t.symbol.ownerChain, currentOwner.ownerChain))
            t.symbol.owner = correctOwner
          case d : DefTree if (d.symbol != NoSymbol) && ((d.symbol.owner == NoSymbol) || (d.symbol.owner != correctOwner)) => // don't indiscriminately change existing owners! (see e.g., pos/t3440, pos/t3534, pos/unapplyContexts2)
            //println("def: "+ (d, d.symbol.ownerChain, currentOwner.ownerChain))
            if(d.symbol.moduleClass ne NoSymbol)
              d.symbol.moduleClass.owner = correctOwner

            d.symbol.owner = correctOwner
          case _ =>
        }
        super.traverse(t)
      }

      // override def apply
      // debug.patmat("before fixerupper: "+ xTree)
      // currentRun.trackerFactory.snapshot()
      // debug.patmat("after fixerupper")
      // currentRun.trackerFactory.snapshot()
    }
    fixerUpper(macroCallSiteOwner, t.pos)(t)
  }
}

private[async] trait AnfTransform2 extends TypingTransformers {
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
      val trees: List[Tree] = mode match {
        case Anf         => anf.transformToList0(tree)
        case Linearizing => linearize.transformToList0(tree)
      }
      listToBlock(trees)
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
      localTyper.typedPos(pos)(ValDef(sym, lhs)).asInstanceOf[ValDef]
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
            def isAwaitRef(name: Name) = name.toString.startsWith(AnfTransform2.this.name.await + "$")
            val (argStatss, argExprss): (List[List[List[Tree]]], List[List[Tree]]) =
              mapArgumentss[List[Tree]](fun, argss) {
                case Arg(expr, byName, _) if byName /*|| isPure(expr) TODO */    => (Nil, expr)
                case Arg(expr@Ident(name), _, _) if isAwaitRef(name)        => (Nil, expr) // not typed, so it eludes the check in `isSafeToInline`
                case Arg(expr, _, argName)                                  =>
                  linearize.transformToList(expr) match {
                    case stats :+ expr1 =>
                      val valDef = defineVal(argName, expr1, expr1.pos)
                      require(valDef.tpe != null, valDef)
                      (stats :+ valDef, gen.mkAttributedStableRef(valDef.symbol))
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
              val stats :+ expr = linearize.transformToList(rhs)
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
                    val newName = newTermName(AnfTransform2.this.name.fresh(name.toTermName + AnfTransform2.this.name.bindSuffix))
                    val vd = defineVal(name.toTermName + AnfTransform2.this.name.bindSuffix, gen.mkAttributedStableRef(b.symbol), b.pos)
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
