/*
 * Copyright (C) 2012 Typesafe Inc. <http://www.typesafe.com>
 */

package scala.async

import org.junit.runner.RunWith
import org.junit.runners.JUnit4
import org.junit.Test
import AsyncId._
import tools.reflect.ToolBox

@RunWith(classOf[JUnit4])
class TreeInterrogation {
  @Test
  def `a minimal set of vals are lifted to vars`() {
    val cm = reflect.runtime.currentMirror
    val tb = mkToolbox("-cp target/scala-2.10/classes")
    val tree = tb.parse(
      """| import _root_.scala.async.AsyncId._
        | async {
        |   val x = await(1)
        |   val y = x * 2
        |   def foo(a: Int) = { def nested = 0; a } // don't lift `nested`.
        |   val z = await(x * 3)
        |   foo(z)
        |   z
        | }""".stripMargin)
    val tree1 = tb.typeCheck(tree)

    //println(cm.universe.show(tree1))

    import tb.u._
    val functions = tree1.collect {
      case f: Function => f
      case t: Template => t
    }
    functions.size mustBe 1

    val varDefs = tree1.collect {
      case ValDef(mods, name, _, _) if mods.hasFlag(Flag.MUTABLE) => name
    }
    varDefs.map(_.decoded.trim).toSet mustBe (Set("state$async", "await$1", "await$2"))
    varDefs.map(_.decoded.trim).toSet mustBe (Set("state$async", "await$1", "await$2"))

    val defDefs = tree1.collect {
      case t: Template =>
        val stats: List[Tree] = t.body
        stats.collect {
          case dd : DefDef
            if !dd.symbol.isImplementationArtifact
              && !dd.symbol.asTerm.isAccessor && !dd.symbol.asTerm.isSetter => dd.name
        }
    }.flatten
    defDefs.map(_.decoded.trim).toSet mustBe (Set("foo$1", "apply", "resume$async", "<init>"))
  }
}

object TreeInterrogation extends App {
  def withDebug[T](t: => T) {
    def set(level: String, value: Boolean) = System.setProperty(s"scala.async.$level", value.toString)
    val levels = Seq("trace", "debug")
    def setAll(value: Boolean) = levels.foreach(set(_, value))

    setAll(value = true)
    try t finally setAll(value = false)
  }

  //new stateMachine$3

  withDebug {
    val cm = reflect.runtime.currentMirror
    val tb = mkToolbox("-cp target/scala-2.10/classes -Xprint:typer -uniqid")
    import scala.async.{Async, AsyncId}

    val tree = tb.parse(
      """
        | import scala.async.AsyncId._
        | async {
        |   await(1)
        |   val neg1 = -1
        |   val a = await(1)
        |   val f = { case x => ({case x => neg1 * x}: PartialFunction[Int, Int])(x + a) }: PartialFunction[Int, Int]
        |   await(f(2))
        | }
        |
        | """.stripMargin)
    println(tree)
    val tree1 = tb.typeCheck(tree.duplicate)
    println(cm.universe.show(tree1))
    println(tb.eval(tree))
  }
}

//
//class stateMachine$3 extends scala.async.StateMachine[scala.async.IdentityFutureSystem.Prom[Int], Unit] {
//  import scala.util._, scala.util.control._
//
//  private[this] var state$async: Int = 0;
//  private[this] val result$async: scala.async.IdentityFutureSystem.Prom[Int] = new scala.async.IdentityFutureSystem.Prom[Int](null.asInstanceOf[Int]);
//  private[this] val execContext$async: Unit = ();
//  private[this] var await$1: Int = 0;
//  private[this] var await$2: Int = 0;
//  private[this] var await$3: Int = 0;
//
//  def resume$async(): Unit = try {
//    stateMachine$3.this.state$async match {
//      case 0 => {
//        ();
//        val awaitable$1: Int = 1;
//        {
//          this.apply(Success.apply[Int](awaitable$1));
//          ()
//        };
//        ()
//      }
//      case 1 => {
//        stateMachine$3.this.await$1;
//        val neg1: Int = -1;
//        val awaitable$2: Int = 1;
//        {
//          this.apply(Success.apply[Int](awaitable$2));
//          ()
//        };
//        ()
//      }
//      case 2 => {
//        val a: Int = stateMachine$3.this.await$2;
//        val f: PartialFunction[Int, Int] = (({
//          @SerialVersionUID(0) final class $anonfun extends scala.runtime.AbstractPartialFunction[Int, Int] with Serializable {
//            final override def applyOrElse[A1 >: Nothing <: Int, B1 >: Int <: Any](x1: A1, default: A1 => B1): B1 = ((x1.asInstanceOf[Int]: Int): Int@unchecked) match {
//              case (x@_)            => (({
//                @SerialVersionUID(0) final class $anonfun extends scala.runtime.AbstractPartialFunction[Int, Int] with Serializable {
//                  final override def applyOrElse[A1 >: Nothing <: Int, B1 >: Int <: Any](x2: A1, default: A1 => B1): B1 = ((x2.asInstanceOf[Int]: Int): Int@unchecked) match {
//                    case (x@_)            => neg1.*(x)
//                    case (defaultCase$@_) => default.apply(x2)
//                  };
//
//                  final def isDefinedAt(x2: Int): Boolean = ((x2.asInstanceOf[Int]: Int): Int@unchecked) match {
//                    case (x@_)            => true
//                    case (defaultCase$@_) => false
//                  }
//                };
//                new $anonfun()
//              }: PartialFunction[Int, Int]): PartialFunction[Int, Int]).apply(x.+(a))
//              case (defaultCase$@_) => default.apply(x1)
//            };
//
//            final def isDefinedAt(x1: Int): Boolean = ((x1.asInstanceOf[Int]: Int): (Int @unchecked)) match {
//              case (x@_)            => true
//              case (defaultCase$@_) => false
//            }
//          };
//          new $anonfun()
//        }: PartialFunction[Int, Int]): PartialFunction[Int, Int]);
//        val awaitable$3: Int = f.apply(2);
//        {
//          this.apply(Success.apply[Int](awaitable$3));
//          ()
//        };
//        ()
//      }
//      case 3 => {
//        stateMachine$3.this.result$async.a_=(Success.apply[Int](stateMachine$3.this.await$3).get);
//        ()
//      }
//    }
//  } catch {
//    case (throwable@_) if NonFatal.apply(throwable) => {
//      {
//        stateMachine$3.this.result$async.a_=(Failure.apply[Nothing](throwable).get);
//        ()
//      };
//      ()
//    }
//  };
//
//  def apply(tr: scala.util.Try[Any]): Unit = stateMachine$3.this.state$async match {
//    case 0 => {
//      if (tr.isFailure) {
//        stateMachine$3.this.result$async.a_=(tr.asInstanceOf[scala.util.Try[Int]].get);
//        ()
//      }
//      else {
//        stateMachine$3.this.await$1 = tr.get.asInstanceOf[Int];
//        stateMachine$3.this.state$async = 1;
//        stateMachine$3.this.resume$async()
//      };
//      ()
//    }
//    case 1 => {
//      if (tr.isFailure) {
//        stateMachine$3.this.result$async.a_=(tr.asInstanceOf[scala.util.Try[Int]].get);
//        ()
//      }
//      else {
//        stateMachine$3.this.await$2 = tr.get.asInstanceOf[Int];
//        stateMachine$3.this.state$async = 2;
//        stateMachine$3.this.resume$async()
//      };
//      ()
//    }
//    case 2 => {
//      if (tr.isFailure) {
//        stateMachine$3.this.result$async.a_=(tr.asInstanceOf[scala.util.Try[Int]].get);
//        ()
//      }
//      else {
//        stateMachine$3.this.await$3 = tr.get.asInstanceOf[Int];
//        stateMachine$3.this.state$async = 3;
//        stateMachine$3.this.resume$async()
//      };
//      ()
//    }
//  };
//
//  def apply: Unit = stateMachine$3.this.resume$async()
//};
