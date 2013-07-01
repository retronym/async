/*
 * Copyright (C) 2012 Typesafe Inc. <http://www.typesafe.com>
 */
package scala.async

import scala.reflect.macros.Context
import reflect.ClassTag

/**
 * Utilities used in both `ExprBuilder` and `AnfTransform`.
 */
private[async] trait TransformUtils2 {
  self: AsyncMacro =>

  import global._

  object name {
    def suffix(string: String) = string + "$async"

    def suffixedName(prefix: String) = newTermName(suffix(prefix))

    val resume        = suffixedName("resume")
    val apply         = newTermName("apply")
    val matchRes      = "matchres"
    val ifRes         = "ifres"
    val await         = "await"
    val bindSuffix    = "$bind"

    val state         = suffixedName("state")
    val result        = suffixedName("result")
    val execContext   = suffixedName("execContext")
    val stateMachine  = newTermName(fresh("stateMachine"))
    val stateMachineT = stateMachine.toTypeName
    val tr            = newTermName("tr")
    val t             = newTermName("throwable")

    def fresh(name: TermName): TermName = newTermName(fresh(name.toString))

    def fresh(name: String): String = if (name.toString.contains("$")) name else currentUnit.freshTermName("" + name + "$").toString
  }

  def isAwait(fun: Tree) =
    fun.symbol == defn.Async_await

  private lazy val Boolean_ShortCircuits: Set[Symbol] = {
    import definitions.BooleanClass
    def BooleanTermMember(name: String) = BooleanClass.typeSignature.member(newTermName(name).encodedName)
    val Boolean_&& = BooleanTermMember("&&")
    val Boolean_|| = BooleanTermMember("||")
    Set(Boolean_&&, Boolean_||)
  }

  private def isByName(fun: Tree): ((Int, Int) => Boolean) = {
    if (Boolean_ShortCircuits contains fun.symbol) (i, j) => true
    else {
      val paramss = fun.tpe.paramss
      val byNamess = paramss.map(_.map(_.isByNameParam))
      (i, j) => util.Try(byNamess(i)(j)).getOrElse(false)
    }
  }
  private def argName(fun: Tree): ((Int, Int) => String) = {
    val paramss = fun.tpe.paramss
    val namess = paramss.map(_.map(_.name.toString))
    (i, j) => util.Try(namess(i)(j)).getOrElse(s"arg_${i}_${j}")
  }

  def Expr[A: WeakTypeTag](t: Tree) = global.Expr[A](rootMirror, new reflect.api.TreeCreator {
    def apply[U <: reflect.api.Universe with Singleton](m: reflect.api.Mirror[U]): U#Tree = t.asInstanceOf[U#Tree]
  })


  object defn {
    def mkList_apply[A](args: List[Expr[A]]): Expr[List[A]] = {
      Expr(Apply(Ident(definitions.List_apply), args.map(_.tree)))
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

    val TryClass      = rootMirror.staticClass("scala.util.Try")
    val Try_get       = TryClass.typeSignature.member(newTermName("get")).ensuring(_ != NoSymbol)
    val Try_isFailure = TryClass.typeSignature.member(newTermName("isFailure")).ensuring(_ != NoSymbol)
    val TryAnyType    = appliedType(TryClass.toType, List(definitions.AnyTpe))
    val NonFatalClass = rootMirror.staticModule("scala.util.control.NonFatal")
    val AsyncClass    = rootMirror.staticClass("scala.async.AsyncBase")
    val Async_await   = AsyncClass.typeSignature.member(newTermName("await")).ensuring(_ != NoSymbol)
  }

  def isSafeToInline(tree: Tree) = {
    treeInfo.isExprSafeToInline(tree)
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


  def statsAndExpr(tree: Tree): (List[Tree], Tree) = tree match {
    case Block(stats, expr) => (stats, expr)
    case _                  => (List(tree), Literal(Constant(())))
  }

  def emptyConstructor: DefDef = {
    val emptySuperCall = Apply(Select(Super(This(tpnme.EMPTY), tpnme.EMPTY), nme.CONSTRUCTOR), Nil)
    DefDef(NoMods, nme.CONSTRUCTOR, List(), List(List()), TypeTree(), Block(List(emptySuperCall), Literal(Constant(()))))
  }

  def applied(className: String, types: List[Type]): AppliedTypeTree =
    AppliedTypeTree(Ident(rootMirror.staticClass(className)), types.map(TypeTree(_)))

}
