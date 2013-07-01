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

  object defn {
    private def asyncMember(name: String) = {
      val asyncMod = rootMirror.staticClass("scala.async.AsyncBase")
      val tpe = asyncMod.asType.toType
      tpe.member(newTermName(name)).ensuring(_ != NoSymbol)
    }

    val Async_await = asyncMember("await")
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
}
