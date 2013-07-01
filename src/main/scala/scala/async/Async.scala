/*
 * Copyright (C) 2012 Typesafe Inc. <http://www.typesafe.com>
 */

package scala.async

import scala.language.experimental.macros
import scala.reflect.macros.Context
import scala.reflect.internal.annotations.compileTimeOnly
import scala.tools.nsc.Global
import language.reflectiveCalls

object Async extends AsyncBase {

  import scala.concurrent.Future

  lazy val futureSystem = ScalaConcurrentFutureSystem
  type FS = ScalaConcurrentFutureSystem.type

  def async[T](body: T) = macro asyncImpl[T]

  override def asyncImpl[T: c.WeakTypeTag](c: Context)(body: c.Expr[T]): c.Expr[Future[T]] = super.asyncImpl[T](c)(body)
}

object AsyncId extends AsyncBase {
  lazy val futureSystem = IdentityFutureSystem
  type FS = IdentityFutureSystem.type

  def async[T](body: T) = macro asyncImpl[T]

  override def asyncImpl[T: c.WeakTypeTag](c: Context)(body: c.Expr[T]): c.Expr[T] = super.asyncImpl[T](c)(body)
}

/**
 * A base class for the `async` macro. Subclasses must provide:
 *
 * - Concrete types for a given future system
 * - Tree manipulations to create and complete the equivalent of Future and Promise
 * in that system.
 * - The `async` macro declaration itself, and a forwarder for the macro implementation.
 * (The latter is temporarily needed to workaround bug SI-6650 in the macro system)
 *
 * The default implementation, [[scala.async.Async]], binds the macro to `scala.concurrent._`.
 */
abstract class AsyncBase {
  self =>

  type FS <: FutureSystem
  val futureSystem: FS

  /**
   * A call to `await` must be nested in an enclosing `async` block.
   *
   * A call to `await` does not block the current thread, rather it is a delimiter
   * used by the enclosing `async` macro. Code following the `await`
   * call is executed asynchronously, when the argument of `await` has been completed.
   *
   * @param awaitable the future from which a value is awaited.
   * @tparam T        the type of that value.
   * @return          the value.
   */
  @compileTimeOnly("`await` must be enclosed in an `async` block")
  def await[T](awaitable: futureSystem.Fut[T]): T = ???

  protected[async] def fallbackEnabled = false

  def asyncImpl[T: c.WeakTypeTag](c: Context)(body: c.Expr[T]): c.Expr[futureSystem.Fut[T]] = {
    import c.universe._

    val analyzer = AsyncAnalysis[c.type](c, this)
    val utils = TransformUtils[c.type](c)
    import utils.{name, defn}

    analyzer.reportUnsupportedAwaits(body.tree)

    def powerMode(c: Context) = {
      c.asInstanceOf[c.type {val universe: Global; val callsiteTyper: universe.analyzer.Typer}]
    }
    val powerContext = powerMode(c)
    val asyncMacro = new AsyncMacro {
      val global       : powerContext.universe.type = powerContext.universe
      val callSiteTyper: global.analyzer.Typer      = powerContext.callsiteTyper
    }

    // Transform to A-normal form:
    //  - no await calls in qualifiers or arguments,
    //  - if/match only used in statement position.
    val anfTree: Block = {
      val stats :+ expr = asyncMacro.anfTransform(body.tree.asInstanceOf[powerContext.Tree])
      val block = Block(stats.asInstanceOf[List[Tree]], expr.asInstanceOf[Tree])
      c.typeCheck(block).asInstanceOf[Block]
    }

    val builder = ExprBuilder[c.type, futureSystem.type](c, self.futureSystem, anfTree)
    import builder.futureSystemOps

    lazy val resumeFunTreeDummyBody = DefDef(Modifiers(), name.resume, Nil, List(Nil), Ident(definitions.UnitClass), Literal(Constant(())))

    lazy val applyDefDefDummyBody: DefDef = {
      val applyVParamss = List(List(ValDef(Modifiers(Flag.PARAM), name.tr, TypeTree(defn.TryAnyType), EmptyTree)))
      DefDef(NoMods, name.apply, Nil, applyVParamss, TypeTree(definitions.UnitTpe), Literal(Constant(())))
    }

    lazy val stateMachineType = utils.applied("scala.async.StateMachine", List(futureSystemOps.promType[T], futureSystemOps.execContextType))

    lazy val stateMachine: ClassDef = {
      val body: List[Tree] = {
        val stateVar = ValDef(Modifiers(Flag.MUTABLE | Flag.PRIVATE | Flag.LOCAL), name.state, TypeTree(definitions.IntTpe), Literal(Constant(0)))
        val result = ValDef(NoMods, name.result, TypeTree(futureSystemOps.promType[T]), futureSystemOps.createProm[T].tree)
        val execContext = ValDef(NoMods, name.execContext, TypeTree(), futureSystemOps.execContext.tree)

        val apply0DefDef: DefDef = {
          // We extend () => Unit so we can pass this class as the by-name argument to `Future.apply`.
          // See SI-1247 for the the optimization that avoids creatio
          val applyVParamss = List(List(ValDef(Modifiers(Flag.PARAM), name.tr, TypeTree(defn.TryAnyType), EmptyTree)))
          DefDef(NoMods, name.apply, Nil, Nil, TypeTree(definitions.UnitTpe), Apply(Ident(name.resume), Nil))
        }
        List(utils.emptyConstructor, stateVar, result, execContext) ++ List(resumeFunTreeDummyBody, applyDefDefDummyBody, apply0DefDef)
      }
      val template = {
        Template(List(stateMachineType), emptyValDef, body)
      }
      val t = ClassDef(NoMods, name.stateMachineT, Nil, template)
      c.typeCheck(Block(t :: Nil, Literal(Constant(()))))
      t
    }

    val asyncBlock: builder.AsyncBlock = builder.build(anfTree, new builder.SymLookup(stateMachine.symbol, applyDefDefDummyBody.vparamss.head.head.symbol))

    logDiagnostics(c)(anfTree, asyncBlock.asyncStates.map(_.toString))

    val companions = collection.mutable.Map[Symbol, Symbol]()
    val defs0: Map[Tree, Int] = asyncBlock.asyncStates.flatMap {
      asyncState =>
        val awaits = asyncState match {
          case stateWithAwait: builder.AsyncStateWithAwait =>
            stateWithAwait.awaitable.resultValDef :: Nil
          case _ => Seq()
        }
        def collectDirectDefs(t: Tree): List[DefTree] = t match {
          case dt: DefTree => dt :: Nil
          case _: Function => Nil
          case t           =>
            val childDefs = t.children.flatMap(collectDirectDefs(_))
            val comps = for {
              cd @ ClassDef(_, _, _, _) <- childDefs
              md @ ModuleDef(_, _, _) <- childDefs
              if (cd.name.toTermName == md.name)
            } yield (cd.symbol, md.symbol)
            comps foreach (companions += _)
            childDefs
        }
        val defs = collectDirectDefs(Block(asyncState.stats: _*))
        (awaits ++ defs).map((_, asyncState.state))
    }.toMap

    // In which block are these symbols defined?
    val defMap: Map[Symbol, Int] = defs0.map { case (k, v) => (k.symbol, v) }

    // The definitions trees
    val defTrees: Map[Symbol, Tree] = defs0.map { case (k, v) => (k.symbol, k) }

    // The direct references of each definition tree
    val defRefs: List[(Symbol, List[Symbol])] = defs0.keys.map {
      case tree => (tree.symbol, tree.collect { case rt: RefTree if defMap.contains(rt.symbol) => rt.symbol })
    }.toList
    val defRefsMap = defRefs.toMap

    // The direct references of each block
    val statementRefs: Map[Int, List[Symbol]] = asyncBlock.asyncStates.flatMap (
      asyncState => asyncState.stats.filterNot(_.isDef).flatMap (_.collect {
        case rt: RefTree if defMap.contains(rt.symbol) => (rt.symbol, asyncState.state)
      })
    ).groupBy(_._2).mapValues(_.map(_._1))

    val liftables = collection.mutable.Set[Symbol]()
    def markForLift(sym: Symbol) {
      if (!liftables(sym)) {
        liftables += sym
        val isValOrVar = sym.isTerm && (sym.asTerm.isVal || sym.asTerm.isVar)
        if (!isValOrVar)
          defRefsMap(sym).foreach(sym2 => markForLift(sym2))
      }
    }
    val liftableStatementRefs: List[Symbol] = statementRefs.toList.flatMap {
      case (i, syms) => syms.filter(sym => defMap(sym) != i)
    }
    val liftableRefsOfDefTrees = defRefs.toList.flatMap {
      case (referee, referents) => referents.filter(sym => defMap(sym) != defMap(referee))
    }
    (liftableStatementRefs ++ liftableRefsOfDefTrees).foreach(markForLift)

    val lifted = liftables.map(defTrees).toList.map {
      case vd@ValDef(_, _, tpt, rhs) =>
        import reflect.internal.Flags._
        val sym = vd.symbol.asInstanceOf[asyncMacro.global.Symbol]
        sym.setFlag(MUTABLE | STABLE | PRIVATE | LOCAL)
        sym.name = asyncMacro.name.fresh(sym.name.toTermName)
        sym.modifyInfo(_.deconst)
        ValDef(vd.symbol, asyncMacro.global.gen.mkZero(vd.symbol.typeSignature.asInstanceOf[asyncMacro.global.Type]).asInstanceOf[Tree]).setPos(vd.pos)
      case dd@DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
        import reflect.internal.Flags._
        val sym = dd.symbol.asInstanceOf[asyncMacro.global.Symbol]
        sym.name = asyncMacro.name.fresh(sym.name.toTermName)
        sym.setFlag(PRIVATE | LOCAL)
        DefDef(dd.symbol, rhs).setPos(dd.pos)
      case cd @ ClassDef(_, _, _, impl) =>
        import reflect.internal.Flags._
        val sym = cd.symbol.asInstanceOf[asyncMacro.global.Symbol]
        sym.name = asyncMacro.global.newTypeName(asyncMacro.name.fresh(sym.name.toString).toString)
        companions.toMap.get(cd.symbol) match {
          case Some(moduleSymbol0) =>
            val moduleSymbol = moduleSymbol0.asInstanceOf[asyncMacro.global.Symbol]
            moduleSymbol.name = sym.name.toTermName
            moduleSymbol.moduleClass.name = moduleSymbol.name.toTypeName
          case _ =>
        }
        //sym.resetFlag(PRIVATE | LOCAL)
        ClassDef(cd.symbol, impl).setPos(cd.pos)
      case md @ ModuleDef(_, _, impl) =>
        import reflect.internal.Flags._
        val sym = md.symbol.asInstanceOf[asyncMacro.global.Symbol]
        companions.map(_.swap).toMap.get(md.symbol) match {
          case Some(classSymbol) => // let the case above rename consistently
          case _ =>
            sym.name = asyncMacro.name.fresh(sym.name.toTermName)
            sym.moduleClass.name = sym.name.toTypeName
        }
        //sym.resetFlag(PRIVATE | LOCAL)
        ModuleDef(md.symbol, impl).setPos(md.pos)
      case td @ TypeDef(_, _, _, rhs) =>
        import reflect.internal.Flags._
        val sym = td.symbol.asInstanceOf[asyncMacro.global.Symbol]
        sym.name = asyncMacro.global.newTypeName(asyncMacro.name.fresh(sym.name.toString).toString)
        TypeDef(td.symbol, rhs).setPos(td.pos)
    }

    val applyBody = asyncBlock.onCompleteHandler
    val resumeFunTree = asyncBlock.resumeFunTree[T]
    def castTree(t: Tree) = t.asInstanceOf[asyncMacro.global.Tree]
    def uncastTree(t: asyncMacro.global.Tree): Tree = t.asInstanceOf[Tree]

    lazy val stateMachineFixedUp = uncastTree(asyncMacro.spliceMethodBodies(lifted.asInstanceOf[List[asyncMacro.global.Tree]], castTree(stateMachine), castTree(applyBody), castTree(resumeFunTree.rhs)))

    def selectStateMachine(selection: TermName) = Select(Ident(name.stateMachine), selection)

    val code: c.Expr[futureSystem.Fut[T]] = {
      val isSimple = asyncBlock.asyncStates.size == 1
      val tree =
        if (isSimple)
          Block(Nil, futureSystemOps.spawn(body.tree)) // generate lean code for the simple case of `async { 1 + 1 }`
        else {
          Block(List[Tree](
            stateMachineFixedUp,
            ValDef(NoMods, name.stateMachine, stateMachineType, Apply(Select(New(Ident(stateMachine.symbol)), nme.CONSTRUCTOR), Nil)),
            futureSystemOps.spawn(Apply(selectStateMachine(name.apply), Nil))
          ),
          futureSystemOps.promiseToFuture(c.Expr[futureSystem.Prom[T]](selectStateMachine(name.result))).tree)
        }
      c.Expr[futureSystem.Fut[T]](tree)
    }

    AsyncUtils.vprintln(s"async state machine transform expands to:\n ${code.tree}")
    c.Expr[futureSystem.Fut[T]](code.tree)
  }

  def logDiagnostics(c: Context)(anfTree: c.Tree, states: Seq[String]) {
    def location = try {
      c.macroApplication.pos.source.path
    } catch {
      case _: UnsupportedOperationException =>
        c.macroApplication.pos.toString
    }

    AsyncUtils.vprintln(s"In file '$location':")
    AsyncUtils.vprintln(s"${c.macroApplication}")
    AsyncUtils.vprintln(s"ANF transform expands to:\n $anfTree")
    states foreach (s => AsyncUtils.vprintln(s))
  }
}

/** Internal class used by the `async` macro; should not be manually extended by client code */
abstract class StateMachine[Result, EC] extends (scala.util.Try[Any] => Unit) with (() => Unit) {
  def result$async: Result

  def execContext$async: EC
}
