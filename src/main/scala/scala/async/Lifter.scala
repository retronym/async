package scala.async

trait Lifter {
  self: AsyncMacro =>
  import global._

  def lift[E <: ExprBuilder[_, _]](asyncStates: List[E#AsyncState], stateMachine: Tree, applyBody: Tree, resumeBody: Tree): Tree = {
    val lifted = liftables(asyncStates)
    spliceMethodBodies(lifted, stateMachine, applyBody, resumeBody)
  }

  def liftables[E <: ExprBuilder[_, _]](asyncStates: Seq[E#AsyncState]): List[Tree] = {
    val companions = collection.mutable.Map[Symbol, Symbol]()
    val defs0: Map[Tree, Int] = asyncStates.flatMap {
      asyncState =>
        val awaits = asyncState match {
          case stateWithAwait: E#AsyncStateWithAwait =>
            stateWithAwait.awaitable.resultValDef.asInstanceOf[Tree] :: Nil
          case _                                           => Seq()
        }
        def collectDirectDefs(t: Tree): List[DefTree] = t match {
          case dt: DefTree => dt :: Nil
          case _: Function => Nil
          case t           =>
            val childDefs = t.children.flatMap(collectDirectDefs(_))
            val comps = for {
              cd@ClassDef(_, _, _, _) <- childDefs
              md@ModuleDef(_, _, _) <- childDefs
              if (cd.name.toTermName == md.name)
            } yield (cd.symbol, md.symbol)
            comps foreach (companions += _)
            childDefs
        }
        val defs = collectDirectDefs(Block(asyncState.stats.asInstanceOf[List[Tree]]: _*))
        (awaits ++ defs).map((_, asyncState.state))
    }.toMap

    // In which block are these symbols defined?
    val defMap: Map[Symbol, Int] = defs0.map {
      case (k, v) => (k.symbol, v)
    }

    // The definitions trees
    val defTrees: Map[Symbol, Tree] = defs0.map {
      case (k, v) => (k.symbol, k)
    }

    // The direct references of each definition tree
    val defRefs: List[(Symbol, List[Symbol])] = defs0.keys.map {
      case tree => (tree.symbol, tree.collect {
        case rt: RefTree if defMap.contains(rt.symbol) => rt.symbol
      })
    }.toList
    val defRefsMap = defRefs.toMap

    // The direct references of each block
    val statementRefs: Map[Int, List[Symbol]] = asyncStates.flatMap(
      asyncState => asyncState.stats.asInstanceOf[List[Tree]].filterNot(_.isDef).flatMap(_.collect {
        case rt: RefTree if defMap.contains(rt.symbol) => (rt.symbol, asyncState.state)
      })
    ).groupBy(_._2).mapValues(_.map(_._1).toList)

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
      case vd@ValDef(_, _, tpt, rhs)                          =>
        import reflect.internal.Flags._
        val sym = vd.symbol
        sym.setFlag(MUTABLE | STABLE | PRIVATE | LOCAL)
        sym.name = name.fresh(sym.name.toTermName)
        sym.modifyInfo(_.deconst)
        ValDef(vd.symbol, gen.mkZero(vd.symbol.info)).setPos(vd.pos)
      case dd@DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
        import reflect.internal.Flags._
        val sym = dd.symbol
        sym.name = this.name.fresh(sym.name.toTermName)
        sym.setFlag(PRIVATE | LOCAL)
        DefDef(dd.symbol, rhs).setPos(dd.pos)
      case cd@ClassDef(_, _, _, impl)                         =>
        import reflect.internal.Flags._
        val sym = cd.symbol
        sym.name = newTypeName(name.fresh(sym.name.toString).toString)
        companions.toMap.get(cd.symbol) match {
          case Some(moduleSymbol0) =>
            val moduleSymbol = moduleSymbol0
            moduleSymbol.name = sym.name.toTermName
            moduleSymbol.moduleClass.name = moduleSymbol.name.toTypeName
          case _                   =>
        }
        ClassDef(cd.symbol, impl).setPos(cd.pos)
      case md@ModuleDef(_, _, impl)                           =>
        import reflect.internal.Flags._
        val sym = md.symbol
        companions.map(_.swap).toMap.get(md.symbol) match {
          case Some(classSymbol) => // let the case above rename consistently
          case _                 =>
            sym.name = name.fresh(sym.name.toTermName)
            sym.moduleClass.name = sym.name.toTypeName
        }
        //sym.resetFlag(PRIVATE | LOCAL)
        ModuleDef(md.symbol, impl).setPos(md.pos)
      case td@TypeDef(_, _, _, rhs)                           =>
        import reflect.internal.Flags._
        val sym = td.symbol
        sym.name = newTypeName(name.fresh(sym.name.toString).toString)
        TypeDef(td.symbol, rhs).setPos(td.pos)
    }
    lifted
  }
}
