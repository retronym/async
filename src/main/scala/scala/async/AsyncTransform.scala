package scala.async

trait AsyncTransform {
  self: AsyncMacro =>

  import global._

  def asyncTransform[T](body: Tree, execContext: Tree)(implicit resultType: WeakTypeTag[T]): Tree = {
     // Transform to A-normal form:
    //  - no await calls in qualifiers or arguments,
    //  - if/match only used in statement position.
    val anfTree: Block = {
      val stats :+ expr = anfTransform(body)
      val block = Block(stats.asInstanceOf[List[Tree]], expr)
      callSiteTyper.typed(block).asInstanceOf[Block]
    }

    lazy val resumeFunTreeDummyBody = DefDef(Modifiers(), name.resume, Nil, List(Nil), Ident(definitions.UnitClass), Literal(Constant(())))

    lazy val applyDefDefDummyBody: DefDef = {
      val applyVParamss = List(List(ValDef(Modifiers(Flag.PARAM), name.tr, TypeTree(defn.TryAnyType), EmptyTree)))
      DefDef(NoMods, name.apply, Nil, applyVParamss, TypeTree(definitions.UnitTpe), Literal(Constant(())))
    }

    lazy val stateMachineType = applied("scala.async.StateMachine", List(futureSystemOps.promType[T].asInstanceOf[Type], futureSystemOps.execContextType.asInstanceOf[Type]))

    lazy val stateMachine: ClassDef = {
      val body: List[Tree] = {
        val stateVar = ValDef(Modifiers(Flag.MUTABLE | Flag.PRIVATE | Flag.LOCAL), name.state, TypeTree(definitions.IntTpe), Literal(Constant(0)))
        val result = ValDef(NoMods, name.result, TypeTree(futureSystemOps.promType[T]), futureSystemOps.createProm[T].tree)
        val execContextValDef = ValDef(NoMods, name.execContext, TypeTree(), execContext)

        val apply0DefDef: DefDef = {
          // We extend () => Unit so we can pass this class as the by-name argument to `Future.apply`.
          // See SI-1247 for the the optimization that avoids creatio
          val applyVParamss = List(List(ValDef(Modifiers(Flag.PARAM), name.tr, TypeTree(defn.TryAnyType), EmptyTree)))
          DefDef(NoMods, name.apply, Nil, Nil, TypeTree(definitions.UnitTpe), Apply(Ident(name.resume), Nil))
        }
        List(emptyConstructor, stateVar, result, execContextValDef) ++ List(resumeFunTreeDummyBody, applyDefDefDummyBody, apply0DefDef)
      }
      val template = {
        Template(List(stateMachineType), emptyValDef, body)
      }
      val t = ClassDef(NoMods, name.stateMachineT, Nil, template)
      callSiteTyper.typed(Block(t :: Nil, Literal(Constant(()))))
      t
    }

    val asyncBlock: AsyncBlock =
      buildAsyncBlock(anfTree, new SymLookup(stateMachine.symbol, applyDefDefDummyBody.vparamss.head.head.symbol))

    logDiagnostics(anfTree, asyncBlock.asyncStates.map(_.toString))

    lazy val stateMachineFixedUp =
      lift(
        asyncBlock.asyncStates,
        stateMachine,
        asyncBlock.onCompleteHandler[T](implicitly[WeakTypeTag[T]]),
        asyncBlock.resumeFunTree[T].rhs)

    def selectStateMachine(selection: TermName) = Select(Ident(name.stateMachine), selection)

    val isSimple = asyncBlock.asyncStates.size == 1
    val tree =
      if (isSimple)
        Block(Nil, futureSystemOps.spawn(body, execContext)) // generate lean code for the simple case of `async { 1 + 1 }`
      else {
        Block(List[Tree](
          stateMachineFixedUp,
          ValDef(NoMods, name.stateMachine, stateMachineType, Apply(Select(New(Ident(stateMachine.symbol)), nme.CONSTRUCTOR), Nil)),
          futureSystemOps.spawn(Apply(selectStateMachine(name.apply), Nil), selectStateMachine(name.execContext))
        ),
        futureSystemOps.promiseToFuture(Expr[futureSystem.Prom[T]](selectStateMachine(name.result))).tree)
      }
     tree
  }

  def logDiagnostics(anfTree: c.Tree, states: Seq[String]) {
    val pos = callSiteTyper.context.tree.pos
    def location = try {
      pos.source.path
    } catch {
      case _: UnsupportedOperationException =>
        pos.toString
    }

    AsyncUtils.vprintln(s"In file '$location':")
    //AsyncUtils.vprintln(s"${c.macroApplication}")
    AsyncUtils.vprintln(s"ANF transform expands to:\n $anfTree")
    states foreach (s => AsyncUtils.vprintln(s))
  }

}
