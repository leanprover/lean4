import Lean
import Lean.Elab.Tactic.Do.LetElim

open Lean Parser Meta Elab

declare_syntax_cat dooElem

meta def dooElemParser (rbp : Nat := 0) : Parser :=
  categoryParser `dooElem rbp

meta def dooSeqItem      := leading_parser
  ppLine >> dooElemParser >> optional "; "
meta def dooSeqIndent    := leading_parser
  many1Indent dooSeqItem
meta def dooSeqBracketed := leading_parser
  "{" >> withoutPosition (many1 dooSeqItem) >> ppLine >> "}"
meta def dooSeq :=
  withAntiquot (mkAntiquot "dooSeq" decl_name% (isPseudoKind := true)) <|
    dooSeqBracketed <|> dooSeqIndent
meta def dooIdDecl := leading_parser
  atomic (ident >> Term.optType >> ppSpace >> Term.leftArrow) >>
  dooElemParser
syntax:arg (name := dooBlock) "doo" dooSeq : term

syntax (name := dooTerm) Term.doExpr : dooElem
syntax (name := dooParens) "(" dooSeq ")" : dooElem
syntax (name := dooReturn) &"return " term : dooElem
syntax (name := dooBreak) &"break" : dooElem
syntax (name := dooContinue) &"continue" : dooElem
syntax (name := dooLet) "let " &"mut "? letDecl : dooElem
syntax (name := dooLetArrow) "let " &"mut "? dooIdDecl : dooElem
syntax (name := dooNestedParser) "doo" dooSeq : dooElem

@[dooElem_parser]
meta def dooReassign      := leading_parser
  Term.notFollowedByRedefinedTermToken >> Term.letIdDeclNoBinders

@[dooElem_parser]
meta def dooReassignArrow := leading_parser
  Term.notFollowedByRedefinedTermToken >> dooIdDecl

@[dooElem_parser]
meta def dooIf := leading_parser withResetCache <| withPositionAfterLinebreak <| ppRealGroup <|
  -- ppRealFill (ppIndent ("if " >> doIfCond >> " then") >> ppSpace >> doSeq) >>
  ppRealFill (ppIndent ("if " >> termParser >> " then") >> ppSpace >> dooSeq) >>
  many (checkColGe "'else if' in 'do' must be indented" >>
    -- group (ppDedent ppSpace >> ppRealFill (elseIf >> doIfCond >> " then " >> doSeq))) >>
    group (ppDedent ppSpace >> ppRealFill (Term.elseIf >> termParser >> " then " >> dooSeq))) >>
  optional (checkColGe "'else' in 'do' must be indented" >>
    ppDedent ppSpace >> ppRealFill ("else " >> dooSeq))

meta def getDooElems (dooSeq : TSyntax `dooSeq) : Array (TSyntax `dooElem) :=
  if dooSeq.raw.getKind == ``dooSeqBracketed then
    dooSeq.raw[1].getArgs.map fun arg => ⟨arg[0]⟩
  else if dooSeq.raw.getKind == ``dooSeqIndent then
    dooSeq.raw[0].getArgs.map fun arg => ⟨arg[0]⟩
  else
    #[]

namespace Do

structure MonadInfo where
  /-- The inferred type of the monad of type `Type u → Type v`. -/
  m : Expr
  /-- The `u` in `m : Type u → Type v`. -/
  u : Level
  /-- The `v` in `m : Type u → Type v`. -/
  v : Level
  /-- The cached `PUnit` expression. -/
  cachedPUnit : Expr := mkConst ``PUnit [mkLevelSucc u]

private meta partial def extractBind (expectedType? : Option Expr) : TermElabM (MonadInfo × Expr) := do
  let some expectedType := expectedType? | mkUnknownMonadResult
  let extractStep? (type : Expr) : TermElabM (Option (MonadInfo × Expr)) := do
    let .app m resultType := type.consumeMData | return none
    unless ← isType resultType do return none
    let .succ u ← getLevel resultType | return none
    let .succ v ← getLevel type | return none
    return some ({ m, u, v }, resultType)
  let rec extract? (type : Expr) : TermElabM (Option (MonadInfo × Expr)) := do
    match (← extractStep? type) with
    | some r => return r
    | none =>
      let typeNew ← whnfCore type
      if typeNew != type then
        extract? typeNew
      else
        -- Term.tryPostponeIfMVar typeNew.getAppFn
        if typeNew.getAppFn.isMVar then
          mkUnknownMonadResult
        else match (← unfoldDefinition? typeNew) with
          | some typeNew => extract? typeNew
          | none => return none
  match (← extract? expectedType) with
  | some r => return r
  | none   => throwError "invalid `do` notation, expected type is not a monad application{indentExpr expectedType}\nYou can use the `do` notation in pure code by writing `Id.run do` instead of `do`, where `Id` is the identity monad."
where
  mkUnknownMonadResult : TermElabM (MonadInfo × Expr) := do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let m ← mkFreshExprMVar (← mkArrow (mkSort (mkLevelSucc u)) (mkSort (mkLevelSucc v))) (userName := `m)
    let resultType ← mkFreshExprMVar (mkSort (mkLevelSucc u)) (userName := `α)
    return ({ m, u, v }, resultType)

/--
Information about a success, `return`, `break` or `continue` continuation that will be filled in
after the code using it has been elaborated.
-/
structure ContInfo where
  /--
  The final type of the join point. It depends on which mut variables have been modified in any
  branches where the join point has been used.
  -/
  joinType : MVarId
  /--
  The expression that will jump to the join point.
  It depends on which mut variables have been modified, as well as on whether we immediately inline
  the join point (when it is either small or there is only one jump).
  -/
  jumpExpr : MVarId

structure Context where
  /-- Inferred and cached information about the monad. -/
  monadInfo : MonadInfo
  /-- The mutable variables in declaration order. -/
  mutVars : Array Name := #[]
  /-- The expected type of `e` in `return e`. -/
  earlyReturnType : Expr
  /-- The continuation for an early `return`. -/
  -- returnCont : ContInfo

meta def mkContext (expectedType? : Option Expr) : TermElabM Context := do
  let (monadInfo, resultType) ← extractBind expectedType?
  return { monadInfo, earlyReturnType := resultType }

structure MonadInstanceCache where
  /-- The inferred `Pure` instance of `(← read).monadInfo.m`. -/
  instPure : Option Expr := none
  /-- The inferred `Bind` instance of `(← read).monadInfo.m`. -/
  instBind : Option Expr := none
  /-- The cached `Pure.pure` expression. -/
  cachedPure : Option Expr := none
  /-- The cached `Bind.bind` expression. -/
  cachedBind : Option Expr := none

/--
Information about a jump to a join point that has been emitted.
-/
structure Jump where
  /--
  The current definition of mutable variables at the jump location.
  Any definition that was reassigned wrt. the join point scope need to be passed to the join point.
  Different jump locations have different reassignments in scope, so this array is only a subset of
  parameters that need to be passed to the join point.
  -/
  reassignedMutVars : Array Name
  /--
  The expression capturing the result of the last monadic action before the jump.
  It ends up as the last parameter of the join point.
  -/
  r : Expr
  /--
  The metavariable to be assigned with the jump to the join point.
  Conveniently, its captured local context is that of the jump, in which the new mutable variable
  definitions and `r` are in scope.
  -/
  mv : Expr
  /-- A reference for error reporting. -/
  ref : Syntax
deriving Inhabited

structure State where
  monadInstanceCache : MonadInstanceCache := {}
  jumps : Std.HashMap FVarId (Array Jump) := {}

abbrev DoElabM := ReaderT Context <| StateRefT State TermElabM

meta def mkMonadicType (resultType : Expr) : DoElabM Expr := do
  return mkApp (← read).monadInfo.m resultType

meta def mkPUnit : DoElabM Expr := do
  return (← read).monadInfo.cachedPUnit

meta def mkPUnitUnit : DoElabM Expr := do
  return mkConst ``PUnit.unit [mkLevelSucc (← read).monadInfo.u]

meta def mkPureApp (ref : Syntax) (α e : Expr) : DoElabM Expr := withRef ref do
  let e ← Term.ensureHasType α e
  let s ← get
  if let some cachedPure := s.monadInstanceCache.cachedPure then return mkApp2 cachedPure α e
  let info := (← read).monadInfo
  let instPure ← Term.mkInstMVar (mkApp (mkConst ``Pure [info.u, info.v]) info.m)
  let cachedPure := mkApp2 (mkConst ``Pure.pure [info.u, info.v]) info.m instPure
  set { s with monadInstanceCache := { s.monadInstanceCache with cachedPure := some cachedPure } }
  return mkApp2 cachedPure α e

meta def mkBindApp (ref : Syntax) (α β e k : Expr) : DoElabM Expr := withRef ref do
  let mα ← mkMonadicType α
  let e ← Term.ensureHasType mα e
  let k ← Term.ensureHasType (← mkArrow α (← mkMonadicType β)) k
  let s ← get
  if let some cachedBind := s.monadInstanceCache.cachedBind then return mkApp4 cachedBind α β e k
  let info := (← read).monadInfo
  let instPure ← Term.mkInstMVar (mkApp (mkConst ``Bind [info.u, info.v]) info.m)
  let cachedBind := mkApp2 (mkConst ``Bind.bind [info.u, info.v]) info.m instPure
  set { s with monadInstanceCache := { s.monadInstanceCache with cachedBind := some cachedBind } }
  return mkApp4 cachedBind α β e k

meta def declareMutVar (x : Name) : DoElabM α → DoElabM α :=
  withReader fun ctx => { ctx with mutVars := ctx.mutVars.push x }

meta def declareMutVar? (mutTk? : Option Syntax) (x : Name) (k : DoElabM α) : DoElabM α :=
  if mutTk?.isSome then declareMutVar x k else k

meta def throwUnlessMutVarDeclared (ref : Syntax) (x : Name) : DoElabM Unit := do
  unless (← read).mutVars.contains x do
    throwErrorAt ref "mutable variable `{x}` is not declared"

meta def checkMutVarsForShadowing (ref : Syntax) (x : Name) : DoElabM Unit := do
  if (← read).mutVars.contains x then
    throwErrorAt ref "mutable variable `{x.simpMacroScopes}` cannot be shadowed"

meta def mkLetThen (x : Name) (ty : Expr) (rhs : Expr) (k : Expr → DoElabM Expr) : DoElabM Expr := do
  withLetDecl x ty rhs fun x => do mkLetFVars (usedLetOnly := false) #[x] (← k x)

meta def mkFreshResultType : DoElabM Expr := do
  mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.u)) (userName := `α)

meta def mkAndThen (ref : Syntax) (x : Name) (eResultTy e : Expr) (k : Expr → DoElabM Expr) : DoElabM Expr := do
  let (k, kResultTy) ← withLocalDeclD x eResultTy fun x => do
    let body ← k x
    let bodyTy ← inferType body
    let .app _m kResultTy := bodyTy
      | throwError "Expected some monadic type for{indentExpr body}\nbut got{indentExpr bodyTy}"
    return (← mkLambdaFVars #[x] body, kResultTy)
  mkBindApp ref eResultTy kResultTy e k

meta def mkPureUnit (ref : Syntax) : DoElabM Expr := do
  mkPureApp ref (← mkPUnit) (← mkPUnitUnit)

/--
A variant of `Term.elabType` that takes the universe of the monad into account, unless
`freshLevel` is set.
-/
meta def elabType (ty? : Option (TSyntax `term)) (freshLevel := false) : DoElabM Expr := do
  let u ← if freshLevel then mkFreshLevelMVar else (mkLevelSucc ·.monadInfo.u) <$> read
  let sort := mkSort u
  match ty? with
  | none => mkFreshExprMVar sort
  | some ty => Term.elabTermEnsuringType ty sort

meta def addJump (jp : FVarId) (jump : Jump) : DoElabM Unit :=
  modify fun s => { s with jumps := s.jumps.alter jp (fun arr => arr.getD #[] |>.push jump) }

meta def getAndClearJumps (jp : FVarId) : DoElabM (Array Jump) :=
  modifyGet fun s => (s.jumps.get? jp |>.getD #[], { s with jumps := s.jumps.erase jp })

/--
This data type communicates to `do` element elaborators whether they are the last element of the
`do` block. When it's not the last element, there's a continuation for elaborating the remaining
`do` elements of the block.

For the last element, the `do` element elaborator needs to generate a closed expression on its own.
This step depends on the particular `do` element, which is why `elabElem` needs to be told with via
this data type:

* For `return`, we discard the continuation unconditionally.
* When binding constructs such as `let x := 3` or `x ← pure 3` come last, we finish with `pure ()`.
  In general, the semantics of any binding construct `x := e` is as if it was finished into a
  closed expression element `x := e; pure ()`; we just omit `pure () >>= fun _ => ...` in the
  non-last case.
* For general expressions elements `e`, the expected type is `Unit` when it does not come last,
  and the elaborator needs to concat the code generated by the continuation with `>>`.
  Furthermore, to support `let $x ← $e:term; pure $x`, the continuation `pure $x` of the arrow
  element needs a way to refer to the result of `e`, so the `.cont` case receives an inaccessible
  FVar `r†` that refers to the monadic result of `e`, generating the code `$e >>= fun r† => pure r†`.
  So the elaborator for `let $x ← …` connects `x` to `r†` (via `let` or renaming the inaccessible),
  so that `pure $x` finds `r†` as `x` in its local context.
-/
inductive DoElemCont where
  /--
  The `do` element under elaboration is the last of its `do` block and has the given return type.
  -/
  | last : (resultType : Expr) → DoElemCont

  /--
  The `do` element under elaboration is followed by other elements in the `do` block,
  and they can be elaborated using `k`. `k` expects to receive an expression `r` referring to the
  result of the previous element.

  Example: when the previous element is an  expression `e`, then `r` is the inaccessible FVar in
  `e >>= fun r† => …`, and the `DoElemCont` is supposed to fill in `…` given `r†` as `r`.

  Note that `r` is *not* the FVar representing an assigned user name as in a binding construct such
  as `let $x ← $doElem`. In fact, for binding constructs, `r` is `PUnit.unit`, because `x := e` is
  the same as `x := e; pure ()`.
  It's much cleaner to pass `()` as `r` than to generate `e >>= fun x => let r† := (); …` for every
  arrow element.
  Another way to think about this: User level binding constructs such as `let $x ← $doElem` are
  *syntax*, but the notion of "result of previous element" in `DoElemCont` is a *semantic* concept.
  -/
  | cont : (resultName : Name) → (resultType : Expr) → (k : (r : Expr) → DoElabM Expr) → DoElemCont

meta def DoElemCont.resultType (k : DoElemCont) : Expr :=
  match k with
  | .last resultType => resultType
  | .cont _ resultType _ => resultType

meta def DoElemCont.mkThenUnlessLast (ref : Syntax) (k : DoElemCont) (e : Expr) : DoElabM Expr :=
  if let .cont resultName resultType k := k then do
    mkAndThen ref resultName resultType e k
  else
    return e

meta def DoElemCont.continueWithUnit (ref : Syntax) (k : DoElemCont) : DoElabM Expr := withRef ref do
  let unit ← mkPUnitUnit
  discard <| Term.ensureHasType k.resultType unit
  match k with
  | .cont n resultType k => do withLetDecl n resultType unit fun x => do
    let e ← k x
    let e ← elimMVarDeps #[x] e
    return e.replaceFVar x unit
  | .last _ => mkPureUnit ref

meta def filterReassigned (mutVars : Array Name) (oldCtx newCtx : LocalContext) : MetaM (Array Name) := do
  let get ctx name := match ctx.findFromUserName? name with
    | some d => return d
    | none   => throwError "Could not find mutable variable `{name}`"
  let oldDefs ← mutVars.mapM (get oldCtx)
  let newDefs ← mutVars.mapM (get newCtx)
  return oldDefs.zip newDefs
    |>.filter (Function.uncurry (·.toExpr != ·.toExpr))
    |>.map (·.1.userName)

meta def captureLCtxAndMutVarDefs (k : (Expr → (Array Name → DoElabM Expr) → DoElabM Expr) → DoElabM Expr) : DoElabM Expr := do
  let mutVars := (← read).mutVars
  let lctx ← getLCtx
  k <| fun r k => do
    -- Find the subset of mut vars that are reassigned.
    let reassignedMutVars ← filterReassigned mutVars lctx (← getLCtx)
    let reassignedMutVarDefs ← reassignedMutVars.mapM (getFVarFromUserName ·)
    -- Tunnel mut vars and result into the outer context:
    let tunnelDecls ← reassignedMutVarDefs
      |>.push r
      |>.mapM (·.fvarId!.getDecl)
    -- Forget the value of every ldecl.
    let tunnelDecls := tunnelDecls.map fun decl =>
      .cdecl 0 decl.fvarId decl.userName decl.type decl.binderInfo decl.kind
    withLCtx' lctx do
    withExistingLocalDecls tunnelDecls.toList do
    withReader (fun ctx => { ctx with mutVars }) do
    k reassignedMutVars

meta def DoElemCont.withDuplicableCont (dec : DoElemCont) (caller : DoElemCont → DoElabM Expr) : DoElabM Expr := do
  let .cont rName resultType nondupK := dec | caller dec -- assumption: .last continuations are always duplicable
  let mα ← mkMonadicType (← read).earlyReturnType
  let joinTy ← mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.v)) (userName := `joinTy)
  let joinRhs ← mkFreshExprMVar joinTy (userName := `joinRhs)
  withLetDecl (← mkFreshUserName `__do_jp) joinTy joinRhs (kind := .implDetail) fun jp => do
  captureLCtxAndMutVarDefs fun restoreLCtx => do
    let duplicableDec := DoElemCont.cont rName resultType fun r => restoreLCtx r fun reassignedMutVars => do
      let mv ← mkFreshExprMVar mα (userName := `jumpPlaceholder)
      addJump jp.fvarId! { reassignedMutVars, r, mv, ref := (← getRef) }
      return mv
    let e ← caller duplicableDec

    -- Now determine whether we need to realize the join point.
    let jumps ← getAndClearJumps jp.fvarId!
    if jumps.isEmpty then
      -- Do nothing. No MVar needs to be assigned.
      pure ()
    else if let #[j] := jumps then
      -- Linear use of the continuation. Do not introduce a join point; just emit the continuation
      -- directly.
      j.mv.mvarId!.withContext do withRef j.ref do
      let res ← nondupK j.r
      discard <| isDefEq j.mv res
    else -- jumps.size > 1
      -- Non-linear use of the continuation. Introduce a join point and fill all MVars with jumps to
      -- it.
      --
      -- First compute the union of all reassigned mut vars. These + `r` constitute the parameters
      -- of the join point. We take a little care to preserve the declaration order that is manifest
      -- in the array `(← read).mutVars`.
      let reassignedMutVars := Std.HashSet.ofArray (jumps.flatMap (·.reassignedMutVars))
      let ctx ← read
      let reassignedMutVars := ctx.mutVars.filter reassignedMutVars.contains

      -- Assign the `joinTy` based on the types of the reassigned mut vars and the result type.
      let reassignedDecls ← reassignedMutVars.mapM (getLocalDeclFromUserName ·)
      let reassignedTys := reassignedDecls.map (·.type)
      let resTy ← do
        let j := jumps[0]!
        j.mv.mvarId!.withContext (inferType j.r)
      discard <| isDefEq joinTy (← mkArrowN (reassignedTys.push resTy) mα)

      -- Assign the `joinRhs` with the result of the continuation.
      let rhs ← joinRhs.mvarId!.withContext do
        withLocalDeclsDND (reassignedDecls.map (fun d => (d.userName, d.type)) |>.push (rName, resTy)) fun xs => do
          mkLambdaFVars xs (← nondupK xs.back!)
      discard <| isDefEq joinRhs rhs

      -- Finally, assign the MVars with the jump to `jp`.
      for j in jumps do
        j.mv.mvarId!.withContext do withRef j.ref do
        let mut jump := jp
        for name in reassignedMutVars do
          let newDefn ← getLocalDeclFromUserName name
          jump := mkApp jump newDefn.toExpr
        jump := mkApp jump (← Term.ensureHasType resTy j.r "Mismatched result type for match arm. It")
        discard <| isDefEq j.mv jump

    mkLetFVars #[jp] (usedLetOnly := true) (← Term.ensureHasType mα e)

/-
One hand, we want to elaborate `do foo a b c` in terminal position simply as `foo a b c`.
In non-terminal position, we want `do foo a b c; bar` to elaborate as `foo a b c >>= fun () => bar`.

On the other hand, we want to elaborate `do let x ← bar a b c` in terminal position as
`bar a b c >>= fun x => pure ()`. In non-terminal position, we want `do let x ← bar a b c; foo` to
elaborate as `bar a b c >>= fun x => foo`.
Similarly for `let`, `:=`.
I think this is for *binding constructs*. Even if these run any monadic actions, we do not want
the result of these actinos to be the final result of the block.
So whenever we have something like `let` in terminal position, we want to insert an implicit
`pure ()` at the end.
If we do so, we may assume in `elabTerminalElem` that no binding constructs remain. It will be easy
to always produce a closed `Expr`.

Another way to see this: We want turn any binding construct `let * x * e` into a terminal element
`(do let * x * e; ???)` such that
`(do let * x * e; rest) = (do let * x * e; ???; rest)` and `??? := pure ()` solves the equation.
However it would be very ugly to insert that many `pure ()`s.
So we do so once at the end for binding constructs.
-/

mutual
  meta def elabElem (dooElem : TSyntax `dooElem) (k : DoElemCont) : DoElabM Expr := withRef dooElem do
    match dooElem with
    | `(dooElem| return $e) =>
      -- NB: The `earlyReturnType` can be different than `resultType` when `return` is not the last
      -- element of the block
      let e ← Term.elabTermEnsuringType e (← read).earlyReturnType
      mkPureApp dooElem (← read).earlyReturnType e
      -- NB: discard continuation `k?`, unconditionally
    | `(dooElem| $e:term) =>
      let mα ← mkMonadicType k.resultType
      -- We cannot use `Term.elabTermEnsuringType` directly here, because it seems to force
      -- synthesis of `Pure` and `Bind` instances when `#check`-ing a `do` block without expected
      -- type. So instead we elaborate and then only do `ensureHasType` if `?m` is not ultimately an
      -- MVar.
      let e ← Term.elabTerm e mα
      logInfo m!"e: {e}, mα: {mα}, isMVarApp: {← Term.isMVarApp mα}"
      let e ← Term.ensureHasType mα e
      k.mkThenUnlessLast dooElem e
    | `(dooElem| let $[mut%$mutTk?]? $x:ident $[: $xType?]? ← $rhs) =>
      checkMutVarsForShadowing dooElem x.getId
      let xType ← elabType xType?
      captureLCtxAndMutVarDefs fun restoreLCtx =>
        elabElem rhs <| .cont x.getId xType fun xdefn => restoreLCtx xdefn fun _reassignments => do
          declareMutVar? mutTk? x.getId (k.continueWithUnit x)
    | `(dooElem| $x:ident ← $rhs) =>
      let xType := (← getLocalDeclFromUserName x.getId).type
      captureLCtxAndMutVarDefs fun restoreLCtx =>
        elabElem rhs <| .cont x.getId xType fun xdefn => restoreLCtx xdefn fun _reassignments =>
          k.continueWithUnit x
    | `(dooElem| let $[mut%$mutTk?]? $x:ident $[: $xType?]? := $rhs) =>
      checkMutVarsForShadowing dooElem x.getId
      -- We want to allow `do let foo : Nat = Nat := rfl; pure (foo ▸ 23)`. Note that the type of
      -- foo has sort `Sort 0`, whereas the sort of the monadic result type `Nat` is `Sort 1`.
      -- Hence `freshLevel := true` (yes, even for `mut` vars; why not?).
      let xType ← elabType xType? (freshLevel := true)
      let rhs ← Term.elabTermEnsuringType rhs xType
      mkLetThen x.getId xType rhs fun _xdefn => declareMutVar? mutTk? x.getId (k.continueWithUnit x)
    | `(dooElem| $x:ident := $rhs) =>
      let xType := (← getLocalDeclFromUserName x.getId).type
      let rhs ← Term.elabTermEnsuringType rhs xType
      mkLetThen x.getId xType rhs fun _xdefn => k.continueWithUnit x
    | `(dooElem| if $cond then $thenDooSeq $[else $elseDooSeq?]?) =>
      k.withDuplicableCont fun k => do
        let then_ ← elabElems1 (getDooElems thenDooSeq) k
        let else_ ← match elseDooSeq? with
          | none => k.continueWithUnit dooElem
          | some elseDooSeq => elabElems1 (getDooElems elseDooSeq) k
        let then_ ← Term.exprToSyntax then_
        let else_ ← Term.exprToSyntax else_
        Term.elabTerm (← `(if $cond then $then_ else $else_)) none
    | `(dooElem| break) | `(dooElem| continue) =>
      throwErrorAt dooElem "`return`, `break`, or `continue` must be the last element of a do block"
    | _ => throwErrorAt dooElem "unexpected do element {dooElem}"

  meta def elabElems1 (dooElems : Array (TSyntax `dooElem)) (k : DoElemCont) : DoElabM Expr := do
    let last := dooElems.back!
    let init := dooElems.pop
    let unit ← mkPUnit
    let r ← mkFreshUserName `r
    init.foldr (init := elabElem last k) fun el k => elabElem el <| .cont r unit fun _ => k

end

meta def elabDooBlock (dooSeq : TSyntax `dooSeq) (expectedType? : Expr) : TermElabM Expr := do
  trace[Elab.do] "Doo block: {dooSeq}, expectedType?: {expectedType?}"
  Term.tryPostponeIfNoneOrMVar expectedType?
  let ctx ← mkContext expectedType?
  let res ← elabElems1 (getDooElems dooSeq) (.last ctx.earlyReturnType) |>.run ctx |>.run' {}
  -- logInfo m!"res: {res}"
  pure res

elab_rules : term <= expectedType?
  | `(dooBlock| doo $dooSeq) => elabDooBlock dooSeq expectedType?

set_option trace.Elab.do true in
set_option pp.raw false in
#check Id.run (α := Nat) doo
  let mut x ← pure 42
  let y ←
    if true then
      pure ()
    else
      pure ()
  x := x + 3
  return x
set_option pp.mvars.delayed false in
set_option trace.Meta.synthInstance true in
set_option trace.Elab.step false in
set_option trace.Elab.do true in
set_option trace.Elab.postpone true in
set_option pp.raw false in
#check doo pure (); return 42
#check doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
#check doo let mut x : Nat := 0; if true then {pure ()} else {pure ()}; pure 13
#check doo let x : Nat := 0; if true then {pure ()} else {pure ()}; pure 13
#check Id.run doo
  let mut x ← pure 42
  let mut z := 0
  z ←
    if true then
      return z
    else
      pure 4
  x := x + 3
  return x

example : (Id.run doo pure 42)
        = (Id.run  do pure 42) := by rfl
example : (Id.run doo return 42)
        = (Id.run  do return 42) := by rfl
example {e : Id PUnit} : (Id.run doo e)
                       = (Id.run  do e) := by rfl
example {e : Id PUnit} : (Id.run doo e; return 42)
                       = (Id.run  do e; return 42) := by rfl
example : (Id.run doo let x := 42; return x + 13)
        = (Id.run  do let x := 42; return x + 13) := by rfl
example : (Id.run doo let x ← pure 42; return x + 13)
        = (Id.run  do let x ← pure 42; return x + 13) := by rfl
example : (Id.run doo let mut x := 42; x := x + 1; return x + 13)
        = (Id.run  do let mut x := 42; x := x + 1; return x + 13) := by rfl
example : (Id.run doo let mut x ← pure 42; x := x + 1; return x + 13)
        = (Id.run  do let mut x ← pure 42; x := x + 1; return x + 13) := by rfl
example : (Id.run doo let mut x ← pure 42; if true then {x := x + 1; return x} else {x := x + 3}; x := x + 13; return x)
        = (Id.run  do let mut x ← pure 42; if true then {x := x + 1; return x} else {x := x + 3}; x := x + 13; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut _x ← if true then {x := x + 1; let y ← pure 3; return y}; x := x + 13; return x)
        = (Id.run  do let mut x ← pure 42; let mut _x ← if true then {x := x + 1; let y ← pure 3; return y}; x := x + 13; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; x ← if true then {x := x + 1; return x} else {x := x + 2; pure 4}; return x)
        = (Id.run  do let mut x ← pure 42; x ← if true then {x := x + 1; return x} else {x := x + 2; pure 4}; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut z := 0; let mut _x ← if true then {z := z + 1; let y ← pure 3; return y} else {z := z + 2; pure 4}; x := x + z; return x)
        = (Id.run  do let mut x ← pure 42; let mut z := 0; let mut _x ← if true then {z := z + 1; let y ← pure 3; return y} else {z := z + 2; pure 4}; x := x + z; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut z := 0; z ← if true then {x := x + 1; return z} else {x := x + 2; pure 4}; x := x + z; return x)
        = (Id.run  do let mut x ← pure 42; let mut z := 0; z ← if true then {x := x + 1; return z} else {x := x + 2; pure 4}; x := x + z; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x)
        = (Id.run  do let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x) := by rfl
example : Nat := Id.run doo let mut foo : Nat = Nat := rfl; pure (foo ▸ 23)

-- Additional comprehensive tests

-- Test: Nested if-then-else with multiple mutable variables
example : (Id.run doo
  let mut x := 0
  let mut y := 1
  if true then
    if false then
      x := 10
      y := 20
    else
      x := 5
      y := 15
  else
    x := 100
  return x + y)
= (Id.run do
  let mut x := 0
  let mut y := 1
  if true then
    if false then
      x := 10
      y := 20
    else
      x := 5
      y := 15
  else
    x := 100
  return x + y) := by rfl

-- Test: Multiple reassignments in sequence
example : (Id.run doo
  let mut x := 10
  x := x + 1
  x := x * 2
  x := x - 3
  return x)
= (Id.run do
  let mut x := 10
  x := x + 1
  x := x * 2
  x := x - 3
  return x) := by rfl

-- Test: Monadic bind with complex RHS
example : (Id.run doo
  let x ← (do let y := 5; pure (y + 3))
  return x * 2)
= (Id.run do
  let x ← (do let y := 5; pure (y + 3))
  return x * 2) := by rfl
#print Eq.casesOn

-- Test: Mutable variable reassignment through monadic bind
set_option trace.Meta.isDefEq true in
example : (Id.run doo
  let mut x := 1
  x ← pure (x + 10)
  x ← pure (x * 2)
  return x)
= (Id.run do
  let mut x := 1
  x ← pure (x + 10)
  x ← pure (x * 2)
  return x) := by rfl

-- Test: Multiple mutable variables with different reassignment patterns
example : (Id.run doo
  let mut a := 1
  let mut b := 2
  let mut c := 3
  if true then
    a := a + 1
  else
    b := b + 1
  c := a + b
  return (a, b, c))
= (Id.run do
  let mut a := 1
  let mut b := 2
  let mut c := 3
  if true then
    a := a + 1
  else
    b := b + 1
  c := a + b
  return (a, b, c)) := by rfl

-- Test: Let binding followed by mutable reassignment
example : (Id.run doo
  let x := 5
  let mut y := x
  y := y * 2
  return (x, y))
= (Id.run do
  let x := 5
  let mut y := x
  y := y * 2
  return (x, y)) := by rfl

-- Test: Early return in else branch
example : (Id.run doo
  let mut x := 0
  if false then
    x := 10
  else
    return 42
  x := 20
  return x)
= (Id.run do
  let mut x := 0
  if false then
    x := 10
  else
    return 42
  x := 20
  return x) := by rfl

-- Test: Both branches return
example : (Id.run doo
  let mut x := 0
  if true then
    return 1
  else
    return 2)
= (Id.run do
  let mut x := 0
  if true then
    return 1
  else
    return 2) := by rfl

-- Test: Three-level nested if with mutable variables
example : (Id.run doo
  let mut x := 0
  if true then
    if true then
      if false then
        x := 1
      else
        x := 2
    else
      x := 3
  else
    x := 4
  return x)
= (Id.run do
  let mut x := 0
  if true then
    if true then
      if false then
        x := 1
      else
        x := 2
    else
      x := 3
  else
    x := 4
  return x) := by rfl

-- Test: Mutable variable used in condition
example : (Id.run doo
  let mut x := 5
  if x > 3 then
    x := x * 2
  else
    x := x + 1
  return x)
= (Id.run do
  let mut x := 5
  if x > 3 then
    x := x * 2
  else
    x := x + 1
  return x) := by rfl

-- Test: Multiple monadic binds in sequence
example : (Id.run doo
  let a ← pure 1
  let b ← pure (a + 1)
  let c ← pure (a + b)
  return (a + b + c))
= (Id.run do
  let a ← pure 1
  let b ← pure (a + 1)
  let c ← pure (a + b)
  return (a + b + c)) := by rfl

-- Test: Mutable bind in if condition position
example : (Id.run doo
  let mut x := 0
  let y ← if x == 0 then pure 1 else pure 2
  x := y
  return x)
= (Id.run do
  let mut x := 0
  let y ← if x == 0 then pure 1 else pure 2
  x := y
  return x) := by rfl

-- Test: Empty else branch behavior
example : (Id.run doo
  let mut x := 5
  if false then
    x := 10
  return x)
= (Id.run do
  let mut x := 5
  if false then
    x := 10
  return x) := by rfl

/-
Postponing Monad instance resolution appropriately
-/

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Pure ?m.8
-/
#guard_msgs (error) in
example := doo return 42
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Bind ?m.11
-/
#guard_msgs (error) in
example := doo let x <- ?z; ?y
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Pure ?m.12
-/
#guard_msgs (error) in
example := do return 42
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Bind ?m.16
-/
#guard_msgs (error) in
example := do let x <- ?z; ?y

-- This tests that inferred types are correctly propagated outwards.
example {e : Id Nat} := doo if true then e else pure 13
-- We do want to be able to `#check` the following example (including the last `pure`) without an
-- expected monad, ...
#check doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
-- As well as fully resolve all instances in the following example where the expected monad is
-- known. The next example wouldn't work without `Id.run`.
example := Id.run doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run doo let mut x := 42; x := x - 7; let x := x + 4; return x + 13)

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure true
-/
#guard_msgs (error) in
example := (Id.run doo pure true; pure ())

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure true
---
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure false
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure true} else {pure false}; pure ())

/--
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure false
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure ()} else {pure false}; pure ())

-- Additional error tests

/-- error: unknown local declaration `foo` -/
#guard_msgs (error) in
example := (Id.run doo foo := 42; pure ())

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run doo let mut x := 1; if true then {let mut x := 2; pure ()} else {pure ()}; pure x)

-- Regression test cases of what's currently broken in the do elaborator:
example : Unit := (Id.run do  let n ← if true then pure 3 else pure 42)
example : Unit := (Id.run doo let n ← if true then pure 3 else pure 42)

/--
info: let x := 0;
let y := 0;
if true = true then pure 3
else
  let x := x + 5;
  let y_1 := 3;
  pure (x + y) : ?m Nat
-/
#guard_msgs (info) in
#check doo
  let mut x : Nat := 0
  let y := 0
  if true then
    return 3
  else
    x := x + 5
    let y := 3
  return x + y

/--
info: let x := 0;
let y := 0;
let __do_jp := fun x r => pure (x + y);
if true = true then
  let x := x + 7;
  let y := 3;
  __do_jp x PUnit.unit
else
  let x := x + 5;
  __do_jp x PUnit.unit : ?m Nat
-/
#guard_msgs (info) in
#check doo
  let mut x : Nat := 0
  let y := 0
  if true then
    x := x + 7
    let y := 3
  else
    x := x + 5
  return x + y

/-
import Std.Data.Iterators
import Std.Tactic.Do

open Std.Iterators
open Std.Do

def SRel : List Type → Type
| [] => Prop
| t :: ts => t → t → SRel ts

#reduce (types := true) SRel [Nat, Bool]

example (measure : Nat → Bool → Nat) : SRel [Nat, Bool] :=
  fun n1 n2 b1 b2 => measure n1 b1 < measure n2 b2

--example [Monad m] [WPMonad m ps]
--  (rel : SRel (PostShape.args ps)) (f : Unit → m (Except Unit Unit)) :
--  ⦃⦄ f () ⦃⇓r =>
--    match r with
--    | ForInStep.done _ => ⌜True⌝
--    | ForInStep.yield _ => rel⦄ := sorry

class WPAdequacy (m : Type u → Type v) (ps : PostShape.{u}) where
  elim :
    ⦃⌜True⌝⦄ prog ⦃⇓r => ⌜p r⌝⦄ →
    ∃ (prog' : m (Subtype p)), prog' = Subtype.val <$> prog := sorry

structure Loop' (β : Type u) where
  wf : WellFoundedRelation β

@[inline]
def Loop'.forIn {β : Type u} {m : Type u → Type v} [Monad m] (l : Loop' β) (init : β) (f : Unit → β → m β) : m β :=
  let rec @[specialize] loop (b : β) (acc : Acc l.wf.rel b) : m β := do
    blub fun decreaseHere => do
    f () b >>= fun b' (h : l.wf.rel.rel b' b) =>
    match h : acc with
      | .intro b h' => decreaseHere (loop b' (h' b' _))
  loop init (l.wf.wf.apply init)


def Iterator.step
    [Monad m]
    (step : Unit → β → m (ForInStep β))
    (measure : β → Nat)
    (it : IterM (α := β) m Unit) :
    m (IterStep (IterM (α := β) m Unit) Unit) := do
  match ← step () it.internalState with
  | ForInStep.done b => .done
  | ForInStep.yield next =>
    if measure next < measure it.internalState then
      .yield ⟨⟨next, it.internalState.upperBound⟩⟩ next
    else
      .done



def fix (f : (α → α) → α → α) (a : α) : α := runST fun σ => do
  let x : ST.Ref σ (ST σ (α → α)) ← ST.mkRef (pure id)
  x.set do
    let y ← x.get
    (f ·) <$> y
  let y : ST σ (α → α) ← x.get
  (· a) <$> y

-- #eval fix (fun f => fun n => if n == 0 then 1 else n * f (n-1)) 5
-/
