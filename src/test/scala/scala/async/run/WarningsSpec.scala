/*
 * Copyright (C) 2012-2014 Typesafe Inc. <http://www.typesafe.com>
 */

package scala.async
package run

import org.junit.Test

import scala.language.{postfixOps, reflectiveCalls}
import scala.tools.nsc.reporters.StoreReporter


class WarningsSpec {

  @Test
  // https://github.com/scala/async/issues/74
  def noPureExpressionInStatementPositionWarning_t74() {
    val tb = mkToolbox(s"-cp ${toolboxClasspath} -Xfatal-warnings")
    // was: "a pure expression does nothing in statement position; you may be omitting necessary parentheses"
    tb.eval(tb.parse {
      """
        |  import scala.async.internal.AsyncId._
        |   async {
        |     if ("".isEmpty) {
        |       await(println("hello"))
        |       ()
        |     } else 42
        |   }
      """.stripMargin
    })
  }

  @Test
  // https://github.com/scala/async/issues/74
  def noDeadCodeWarningForAsyncThrow() {
    val global = mkGlobal("-cp ${toolboxClasspath} -Yrangepos -Ywarn-dead-code -Xfatal-warnings -Ystop-after:refchecks")
    // was: "a pure expression does nothing in statement position; you may be omitting necessary parentheses"
    val source =
      """
        | class Test {
        |   import scala.async.Async._
        |   import scala.concurrent.ExecutionContext.Implicits.global
        |   async { throw new Error() }
        | }
      """.stripMargin
    val run = new global.Run
    val sourceFile = global.newSourceFile(source)
    run.compileSources(sourceFile :: Nil)
    assert(!global.reporter.hasErrors, global.reporter.asInstanceOf[StoreReporter].infos)
  }

  private def checkNoDeadCodeWarnings(source: String): Unit = {
    val global = mkGlobal("-cp ${toolboxClasspath} -Yrangepos -Ywarn-dead-code -Xfatal-warnings -Ystop-after:refchecks")
    val run = new global.Run
    val sourceFile = global.newSourceFile(source)
    run.compileSources(sourceFile :: Nil)
    assert(!global.reporter.hasErrors, global.reporter.asInstanceOf[StoreReporter].infos)
  }

  @Test
  def noDeadCodeWarningInMacroExpansion() {
    val source = """
        | class Test {
        |  def test = {
        |    import scala.async.Async._, scala.concurrent._, ExecutionContext.Implicits.global
        |    async {
        |      val opt = await(async(Option.empty[String => Future[Unit]]))
        |      opt match {
        |        case None =>
        |          throw new RuntimeException("case a")
        |        case Some(f) =>
        |          await(f("case b"))
        |      }
        |    }
        |  }
        |}
      """.stripMargin
    checkNoDeadCodeWarnings(source)
  }

  @Test
  def noDeadCodeWarningInFutureAnyThatOnlyThrows() {
    val source = """
        | class Test {
        |  def test = {
        |    import scala.async.Async._, scala.concurrent._, ExecutionContext.Implicits.global
        |    val base = Future { "five!".length }
        |    val fut = async[Any] {
        |      val len = await(base)
        |      throw new Exception(s"illegal length: $len")
        |    }
        |  }
        |}
      """.stripMargin
    checkNoDeadCodeWarnings(source)
  }

  @Test
  def noDeadCodeWarningInFutureNothing() {
    val source = """
        | class Test {
        |  def test = {
        |    import scala.async.Async._, scala.concurrent._, ExecutionContext.Implicits.global
        |    val base = Future { "five!".length }
        |    val fut = async[Nothing] {
        |      val len = await(base)
        |      throw new Exception(s"illegal length: $len")
        |    }
        |  }
        |}
      """.stripMargin
    checkNoDeadCodeWarnings(source)
  }
  @Test
  def noDeadCodeWarningInFutureNothingUnderAsyncId() {
    val source = """
        | class Test {
        |  def test = {
        |    import scala.async.internal.AsyncId._
        |    async[Nothing] {
        |      val len = await(42)
        |      throw new Exception(s"illegal length: $len")
        |    }
        |  }
        |}
      """.stripMargin
    checkNoDeadCodeWarnings(source)
  }

  @Test
  def noDeadCodeWarningInMatch() {
    val source = """
        | class Test {
        |  def test = {
        |    import scala.async.internal.AsyncId._
        |    async {
        |      val x = 1
        |      Option(x) match {
        |        case op @ Some(x) =>
        |          assert(op == Some(1))
        |          x + await(x)
        |        case None => await(0)
        |      }
        |    }
        |  }
        |}
      """.stripMargin
    checkNoDeadCodeWarnings(source)
  }

  @Test
  def noDeadCodeWarningInNothingTypedIf() {
    val source = """
        | class Test {
        |  def test = {
        |    import scala.async.internal.AsyncId._
        |    async {
        |      if (true) {
        |        val n = await(1)
        |        if (n < 2) {
        |          throw new RuntimeException("case a")
        |        }
        |        else {
        |          throw new RuntimeException("case b")
        |        }
        |      }
        |      else {
        |        "case c"
        |      }
        |    }
        |  }
        |}
      """.stripMargin
    checkNoDeadCodeWarnings(source)
  }
}
