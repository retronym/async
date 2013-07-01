/*
 * Copyright (C) 2012 Typesafe Inc. <http://www.typesafe.com>
 */
package scala.async

import scala.reflect.macros.Context
import reflect.ClassTag

/**
 * Utilities used in both `ExprBuilder` and `AnfTransform`.
 */
private[async] final case class TransformUtils[C <: Context](c: C) {

  import c.universe._

  object name {
    def suffix(string: String) = string + "$async"

    def suffixedName(prefix: String) = newTermName(suffix(prefix))

    val state         = suffixedName("state")
    val result        = suffixedName("result")
    val resume        = suffixedName("resume")
    val execContext   = suffixedName("execContext")
    val stateMachine  = newTermName(fresh("stateMachine"))
    val stateMachineT = stateMachine.toTypeName
    val apply         = newTermName("apply")
    val tr            = newTermName("tr")
    val t             = newTermName("throwable")
    val bindSuffix    = "$bind"

    def fresh(name: TermName): TermName = newTermName(fresh(name.toString))

    def fresh(name: String): String = if (name.toString.contains("$")) name else c.fresh("" + name + "$")
  }

  def defaultValue(tpe: Type): Tree = {
    val symtab = c.universe.asInstanceOf[reflect.internal.SymbolTable]
    symtab.gen.mkZero(tpe.asInstanceOf[symtab.Type]).asInstanceOf[Tree]
  }

  def isAwait(fun: Tree) =
    fun.symbol == defn.Async_await

  /** Descends into the regions of the tree that are subject to the
    * translation to a state machine by `async`. When a nested template,
    * function, or by-name argument is encountered, the descent stops,
    * and `nestedClass` etc are invoked.
    */
  trait AsyncTraverser extends Traverser {
    def nestedClass(classDef: ClassDef) {
    }

    def nestedModule(module: ModuleDef) {
    }

    def nestedMethod(module: DefDef) {
    }

    def byNameArgument(arg: Tree) {
    }

    def function(function: Function) {
    }

    def patMatFunction(tree: Match) {
    }

    override def traverse(tree: Tree) {
      tree match {
        case cd: ClassDef          => nestedClass(cd)
        case md: ModuleDef         => nestedModule(md)
        case dd: DefDef            => nestedMethod(dd)
        case fun: Function         => function(fun)
        case m@Match(EmptyTree, _) => patMatFunction(m) // Pattern matching anonymous function under -Xoldpatmat of after `restorePatternMatchingFunctions`
        case Applied(fun, targs, argss) if argss.nonEmpty =>
          val isInByName = isByName(fun)
          for ((args, i) <- argss.zipWithIndex) {
            for ((arg, j) <- args.zipWithIndex) {
              if (!isInByName(i, j)) traverse(arg)
              else byNameArgument(arg)
            }
          }
          traverse(fun)
        case _                     => super.traverse(tree)
      }
    }
  }

  private lazy val Boolean_ShortCircuits: Set[Symbol] = {
    import definitions.BooleanClass
    def BooleanTermMember(name: String) = BooleanClass.typeSignature.member(newTermName(name).encodedName)
    val Boolean_&& = BooleanTermMember("&&")
    val Boolean_|| = BooleanTermMember("||")
    Set(Boolean_&&, Boolean_||)
  }

  def isByName(fun: Tree): ((Int, Int) => Boolean) = {
    if (Boolean_ShortCircuits contains fun.symbol) (i, j) => true
    else {
      val symtab = c.universe.asInstanceOf[reflect.internal.SymbolTable]
      val paramss = fun.tpe.asInstanceOf[symtab.Type].paramss
      val byNamess = paramss.map(_.map(_.isByNameParam))
      (i, j) => util.Try(byNamess(i)(j)).getOrElse(false)
    }
  }
  def argName(fun: Tree): ((Int, Int) => String) = {
    val symtab = c.universe.asInstanceOf[reflect.internal.SymbolTable]
    val paramss = fun.tpe.asInstanceOf[symtab.Type].paramss
    val namess = paramss.map(_.map(_.name.toString))
    (i, j) => util.Try(namess(i)(j)).getOrElse(s"arg_${i}_${j}")
  }

  object Applied {
    val symtab = c.universe.asInstanceOf[scala.reflect.internal.SymbolTable]
    object treeInfo extends {
      val global: symtab.type = symtab
    } with reflect.internal.TreeInfo

    def unapply(tree: Tree): Some[(Tree, List[Tree], List[List[Tree]])] = {
      val treeInfo.Applied(core, targs, argss) = tree.asInstanceOf[symtab.Tree]
      Some((core.asInstanceOf[Tree], targs.asInstanceOf[List[Tree]], argss.asInstanceOf[List[List[Tree]]]))
    }
  }

  def statsAndExpr(tree: Tree): (List[Tree], Tree) = tree match {
    case Block(stats, expr) => (stats, expr)
    case _                  => (List(tree), Literal(Constant(())))
  }

  def emptyConstructor: DefDef = {
    val emptySuperCall = Apply(Select(Super(This(tpnme.EMPTY), tpnme.EMPTY), nme.CONSTRUCTOR), Nil)
    DefDef(NoMods, nme.CONSTRUCTOR, List(), List(List()), TypeTree(), Block(List(emptySuperCall), c.literalUnit.tree))
  }

  def applied(className: String, types: List[Type]): AppliedTypeTree =
    AppliedTypeTree(Ident(c.mirror.staticClass(className)), types.map(TypeTree(_)))

  object defn {
    def mkList_apply[A](args: List[Expr[A]]): Expr[List[A]] = {
      c.Expr(Apply(Ident(definitions.List_apply), args.map(_.tree)))
    }

    def mkList_contains[A](self: Expr[List[A]])(elem: Expr[Any]) = reify(self.splice.contains(elem.splice))

    def mkFunction_apply[A, B](self: Expr[Function1[A, B]])(arg: Expr[A]) = reify {
      self.splice.apply(arg.splice)
    }

    def mkAny_==(self: Expr[Any])(other: Expr[Any]) = reify {
      self.splice == other.splice
    }

    def mkTry_get[A](self: Expr[util.Try[A]]) = reify {
      self.splice.get
    }

    val TryClass      = c.mirror.staticClass("scala.util.Try")
    val Try_get       = TryClass.typeSignature.member(newTermName("get")).ensuring(_ != NoSymbol)
    val Try_isFailure = TryClass.typeSignature.member(newTermName("isFailure")).ensuring(_ != NoSymbol)
    val TryAnyType    = appliedType(TryClass.toType, List(definitions.AnyTpe))
    val NonFatalClass = c.mirror.staticModule("scala.util.control.NonFatal")
    val AsyncClass    = c.mirror.staticClass("scala.async.AsyncBase")
    val Async_await   = AsyncClass.typeSignature.member(newTermName("await")).ensuring(_ != NoSymbol)
  }

  /**
   * Using [[scala.reflect.api.Trees.TreeCopier]] copies more than we would like:
   * we don't want to copy types and symbols to the new trees in some cases.
   *
   * Instead, we just copy positions and attachments.
   */
  def attachCopy[T <: Tree](orig: Tree)(tree: T): tree.type = {
    tree.setPos(orig.pos)
    for (att <- orig.attachments.all)
      tree.updateAttachment[Any](att)(ClassTag.apply[Any](att.getClass))
    tree
  }

  def isSafeToInline(tree: Tree) = {
    val symtab = c.universe.asInstanceOf[scala.reflect.internal.SymbolTable]
    object treeInfo extends {
      val global: symtab.type = symtab
    } with reflect.internal.TreeInfo
    val castTree = tree.asInstanceOf[symtab.Tree]
    treeInfo.isExprSafeToInline(castTree)
  }

  /** Map a list of arguments to:
    * - A list of argument Trees
    * - A list of auxillary results.
    *
    * The function unwraps and rewraps the `arg :_*` construct.
    *
    * @param args The original argument trees
    * @param f  A function from argument (with '_*' unwrapped) and argument index to argument.
    * @tparam A The type of the auxillary result
    */
  private def mapArguments[A](args: List[Tree])(f: (Tree, Int) => (A, Tree)): (List[A], List[Tree]) = {
    args match {
      case args :+ Typed(tree, Ident(tpnme.WILDCARD_STAR)) =>
        val (a, argExprs :+ lastArgExpr) = (args :+ tree).zipWithIndex.map(f.tupled).unzip
        val exprs = argExprs :+ Typed(lastArgExpr, Ident(tpnme.WILDCARD_STAR)).setPos(lastArgExpr.pos)
        (a, exprs)
      case args                                            =>
        args.zipWithIndex.map(f.tupled).unzip
    }
  }

  case class Arg(expr: Tree, isByName: Boolean, argName: String)

  /**
   * Transform a list of argument lists, producing the transformed lists, and lists of auxillary
   * results.
   *
   * The function `f` need not concern itself with varargs arguments e.g (`xs : _*`). It will
   * receive `xs`, and it's result will be re-wrapped as `f(xs) : _*`.
   *
   * @param fun   The function being applied
   * @param argss The argument lists
   * @return      (auxillary results, mapped argument trees)
   */
  def mapArgumentss[A](fun: Tree, argss: List[List[Tree]])(f: Arg => (A, Tree)): (List[List[A]], List[List[Tree]]) = {
    val isByNamess: (Int, Int) => Boolean = isByName(fun)
    val argNamess: (Int, Int) => String = argName(fun)
    argss.zipWithIndex.map { case (args, i) =>
      mapArguments[A](args) {
        (tree, j) => f(Arg(tree, isByNamess(i, j), argNamess(i, j)))
      }
    }.unzip
  }
}
