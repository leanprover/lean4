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
    let .app m returnType := type.consumeMData | return none
    unless ← isType returnType do return none
    let .succ u ← getLevel returnType | return none
    let .succ v ← getLevel type | return none
    return some ({ m, u, v }, returnType)
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
    let returnType ← mkFreshExprMVar (mkSort (mkLevelSucc u)) (userName := `α)
    return ({ m, u, v }, returnType)

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
  /--
  The current definition for each mutable variable. A definition is either a `FVarId` or a closed,
  atomic `Expr` (e.g. `PUnit.unit`).
  -/
  mutVarDefs : Std.HashMap Name Expr := {}
--  /--
--  The mutable variables that have been reassigned since this field has last been restoreLCtx.
--  Recall that `elabElem1` uses CPS, so previous `do` elems will have populated this field with their
--  reassigned mut vars before calling the continuation.
--  -/
--  reassignedMutVars : Std.HashSet Name := {}
  /-- The expected type of `e` in `return e`. -/
  earlyReturnType : Expr
  /-- The continuation for an early `return`. -/
  -- returnCont : ContInfo

meta def mkContext (expectedType? : Option Expr) : TermElabM Context := do
  let (monadInfo, returnType) ← extractBind expectedType?
  return { monadInfo, earlyReturnType := returnType }

abbrev MVarUses := Std.HashMap MVarId Lean.Elab.Tactic.Do.Uses

def MVarUses.add (a b : MVarUses) : MVarUses :=
  a.fold (init := b) fun acc k v => acc.alter k fun
    | none => some v
    | some v' => some (v + v')

namespace CollectMVarUses

end CollectMVarUses

structure MonadInstanceCache where
  /-- The inferred `Pure` instance of `(← read).monadInfo.m`. -/
  instPure : Option Expr := none
  /-- The inferred `Bind` instance of `(← read).monadInfo.m`. -/
  instBind : Option Expr := none
  /-- The cached `Pure.pure` expression. -/
  cachedPure : Option Expr := none
  /-- The cached `Bind.bind` expression. -/
  cachedBind : Option Expr := none

structure State where
  monadInstanceCache : MonadInstanceCache := {}
  jumpLabelOccs : MVarUses := {}
  jumps : Std.HashMap FVarId (Array (Array LocalDecl × Expr × Expr)) := {}

instance : Add MVarUses where
  add := MVarUses.add

abbrev DoElabM := ReaderT Context <| StateRefT State TermElabM

meta def mkMonadicType (returnType : Expr) : DoElabM Expr := do
  return mkApp (← read).monadInfo.m returnType

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

meta def mkBindApp (α β e k : Expr) : DoElabM Expr := do
  let mα ← mkMonadicType α
  let e ← Term.ensureHasType mα e
  let s ← get
  if let some cachedBind := s.monadInstanceCache.cachedBind then return mkApp4 cachedBind α β e k
  let info := (← read).monadInfo
  let instPure ← Term.mkInstMVar (mkApp (mkConst ``Bind [info.u, info.v]) info.m)
  let cachedBind := mkApp2 (mkConst ``Bind.bind [info.u, info.v]) info.m instPure
  set { s with monadInstanceCache := { s.monadInstanceCache with cachedBind := some cachedBind } }
  return mkApp4 cachedBind α β e k

meta def declareMutVar (x : Name) (defn : Expr) : DoElabM α → DoElabM α :=
  withReader fun ctx =>
    { ctx with mutVars := ctx.mutVars.push x, mutVarDefs := ctx.mutVarDefs.insert x defn }

meta def declareMutVar? (mutTk? : Option Syntax) (x : Name) (defn : Expr) (k : DoElabM α) : DoElabM α :=
  if mutTk?.isSome then declareMutVar x defn k else k

meta def reassignMutVar (ref : Syntax) (x : Name) (defn : Expr) (k : DoElabM α) : DoElabM α := do
  unless (← read).mutVarDefs.contains x do
    throwErrorAt ref "mutable variable `{x}` is not declared"
  withReader (fun ctx => { ctx with
    mutVarDefs := ctx.mutVarDefs.insert x defn,
  }) k

meta def checkMutVarsForShadowing (ref : Syntax) (x : Name) : DoElabM Unit := do
  if (← read).mutVarDefs.contains x then
    throwErrorAt ref "mutable variable `{x.simpMacroScopes}` cannot be shadowed"

meta def mkLetThen (x : Name) (ty : Expr) (rhs : Expr) (k : Expr → DoElabM Expr) : DoElabM Expr := do
  withLetDecl x ty (← Term.ensureHasType ty rhs) fun x => do
    mkLetFVars (usedLetOnly := false) #[x] (← k x)

meta def mkFreshReturnType : DoElabM Expr := do
  mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.u)) (userName := `α)

meta def mkAndThen (x : Name) (eReturnTy e : Expr) (k : Expr → DoElabM Expr) : DoElabM Expr := do
  let k ← withLocalDeclD x eReturnTy (fun x => do mkLambdaFVars #[x] (← k x))
  let e ← Term.ensureHasType (← mkMonadicType eReturnTy) e
  let kReturnTy ← mkFreshReturnType
  let k ← Term.ensureHasType (← mkArrow eReturnTy (← mkMonadicType kReturnTy)) k
  mkBindApp eReturnTy kReturnTy e k

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
  | last : (returnType : Expr) → DoElemCont

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
  | cont : (resultName : Name) → (k : (r : Expr) → DoElabM Expr) → DoElemCont

meta def DoElemCont.mkThenUnlessLast (k : DoElemCont) (e : Expr) : DoElabM Expr :=
  if let .cont resultName k := k then do
    mkAndThen resultName (← mkFreshReturnType) e k
  else
    return e

meta def DoElemCont.continueWithUnit (ref : Syntax) (k : DoElemCont) : DoElabM Expr := do
  match k with
  | .cont _ k => k (← mkPUnitUnit)
  | .last ty => discard <| Term.ensureHasType ty (← mkPUnitUnit); mkPureUnit ref

meta def DoElemCont.mkReturnTypeForThisElem (k : DoElemCont) : DoElabM Expr :=
  if let .last returnType := k then do pure returnType else mkFreshReturnType

meta def updatedMutVarDef? (mutVarDefsOrig : Std.HashMap Name Expr) (mutVarDefs : Std.HashMap Name Expr) (x : Name) : Option Expr :=
  let fv := mutVarDefs.get! x
  if fv == mutVarDefsOrig.get! x then none else some fv

/-
Challenges:

* De-nesting the RHS of a `letArrow` requires passing `.cont` instead of `.last` and then resetting
  the LCtx, adding any reassignments.
* Control-flow constructs such as `if` need join points
* (Reassignments in the RHS of a `letArrow` need join points) No, not per se! Denesting and adjusting LCtx is enough.

So `letArrow` just denests. Often no join points are needed. But it appears that join point creation
is just as complicated as denesting, in that join point creation also needs to fumble with the LCtx.
-/

meta def captureLCtxAndMutVarDefs (k : (Expr → (Array LocalDecl → DoElabM Expr) → DoElabM Expr) → DoElabM Expr) : DoElabM Expr := do
  let mutVarsOrig := (← read).mutVars
  let mutVarDefsOrig := (← read).mutVarDefs
  let lctx ← getLCtx
  k <| fun r k => do
    -- logInfo m!"old context {lctx.decls.toArray.filterMap (·.map fun decl => (decl.toExpr, decl.fvarId.name))}"
    -- logInfo m!"new context {(← getLCtx).decls.toArray.filterMap (·.map fun decl => (decl.toExpr, decl.fvarId.name))}"
    -- NB: Callers may pass closed atomic expressions such as `()` as `r`, so it's not always an
    -- `FVarId`.
    -- Need to account for that below:
    -- * We don't push non-FVars as tunnel decls (there are no definitions), so the join point
    --   won't abstract over them.
    -- * But in return, we need to introduce a `let r := ();` in the join point LCtx so that
    --   `x.getId` has a definition to refer to.
    let mutVarDefs := (← read).mutVarDefs
    let tunnelDecls ← mutVarsOrig
      |>.filterMap (updatedMutVarDef? mutVarDefsOrig mutVarDefs)
      |>.push r
      |>.filterMapM (·.fvarId?.mapM (·.getDecl)) -- NB: this filters out any non-FVar definitions
    -- Forget the value of every ldecl
    let tunnelDecls := tunnelDecls.map fun decl =>
      .cdecl 0 decl.fvarId decl.userName decl.type decl.binderInfo decl.kind
    -- logInfo m!"tunnelDecls {tunnelDecls.map (·.toExpr)}"
    let mutVarDefs := mutVarDefs.filter fun k _ => mutVarDefsOrig.contains k
    withLCtx' lctx do
    withExistingLocalDecls tunnelDecls.toList do
    withReader (fun ctx => { ctx with mutVars := mutVarsOrig, mutVarDefs }) do
    let reassignments := if (·.toExpr) <$> tunnelDecls.back? == r then tunnelDecls.pop else tunnelDecls
    k reassignments

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
      -- NB: The `earlyReturnType` can be different than `returnType` when `return` is not the last
      -- element of the block
      let e ← Term.elabTermEnsuringType e (← read).earlyReturnType
      mkPureApp dooElem (← read).earlyReturnType e
      -- NB: discard continuation `k?`, unconditionally
    | `(dooElem| $e:term) =>
      let mα ← mkMonadicType (← k.mkReturnTypeForThisElem)
      -- We cannot use `Term.elabTermEnsuringType` directly here, because it seems to force
      -- synthesis of `Pure` and `Bind` instances when `#check`-ing a `do` block without expected
      -- type. So instead we elaborate and then only do `ensureHasType` if `?m` is not ultimately an
      -- MVar.
      let e ← Term.elabTerm e none
      -- logInfo m!"e: {e}, mα: {mα}, isMVarApp: {← Term.isMVarApp mα}"
      let e ← if ← Term.isMVarApp mα then pure e else Term.ensureHasType mα e
      k.mkThenUnlessLast e
    | `(dooElem| let $[mut%$mutTk?]? $x:ident $[: $xType?]? ← $rhs) =>
      checkMutVarsForShadowing dooElem x.getId
      let xType ← elabType xType?
      captureLCtxAndMutVarDefs fun restoreLCtx =>
        elabElem rhs <| .cont x.getId fun xdefn => restoreLCtx xdefn fun _reassignments => do
          declareMutVar? mutTk? x.getId (← Term.ensureHasType xType xdefn) (k.continueWithUnit x)
    | `(dooElem| $x:ident ← $rhs) =>
      let decl ← getLocalDeclFromUserName x.getId
      captureLCtxAndMutVarDefs fun restoreLCtx =>
        elabElem rhs <| .cont x.getId fun xdefn => restoreLCtx xdefn fun _reassignments => do
          reassignMutVar dooElem x.getId (← Term.ensureHasType decl.type xdefn) (k.continueWithUnit x)
    | `(dooElem| let $[mut%$mutTk?]? $x:ident $[: $xType?]? := $rhs) =>
      checkMutVarsForShadowing dooElem x.getId
      -- We want to allow `do let foo : Nat = Nat := rfl; pure (foo ▸ 23)`. Note that the type of
      -- foo has sort `Sort 0`, whereas the sort of the monadic result type `Nat` is `Sort 1`.
      -- Hence `freshLevel := true` (yes, even for `mut` vars; why not?).
      let xType ← elabType xType? (freshLevel := true)
      let rhs ← Term.elabTermEnsuringType rhs xType
      mkLetThen x.getId xType rhs fun xdefn => do
        declareMutVar? mutTk? x.getId xdefn (k.continueWithUnit x)
    | `(dooElem| $x:ident := $rhs) =>
      let decl ← getLocalDeclFromUserName x.getId
      let rhs ← Term.elabTermEnsuringType rhs decl.type
      mkLetThen x.getId decl.type rhs fun xdefn => do
        reassignMutVar dooElem x.getId xdefn (k.continueWithUnit x)
    | `(dooElem| if $cond then $thenDooSeq $[else $elseDooSeq?]?) =>
      let α ← mkFreshReturnType
      let mα ← mkMonadicType α
      let joinTy ← mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.v)) (userName := `joinTy)
      let joinRhs ← mkFreshExprMVar joinTy (userName := `joinRhs)
      withLetDecl `__do_jp joinTy joinRhs (kind := .implDetail) fun jp => do
      mkLetFVars #[jp] (usedLetOnly := true) (← captureLCtxAndMutVarDefs fun restoreLCtx => do
        let rName ← mkFreshUserName `r
        let duplicableCont := DoElemCont.cont rName fun r => restoreLCtx r fun tunnelDecls => do
          let s ← get
          let mv ← mkFreshExprMVar mα (userName := `thenJump)
          let s := { s with jumps := s.jumps.alter jp.fvarId! (fun arr => arr.getD #[] |>.push (tunnelDecls, r, mv))}
          set s
          return mv

        let then_ ← elabElems1 (getDooElems thenDooSeq) duplicableCont
        let else_ ← match elseDooSeq? with
          | none => k.continueWithUnit dooElem
          | some elseDooSeq => elabElems1 (getDooElems elseDooSeq) duplicableCont
        let s ← get
        let jumps := s.jumps.get? jp.fvarId! |>.getD #[]
        logInfo m!"jumps to {jp}: {jumps.map (fun (decls, ret) => (decls.map LocalDecl.toExpr, ret))}"
        let reassignedVars := Std.HashSet.ofArray (jumps.flatMap (fun (decls, _) => decls.map LocalDecl.userName))
        let ctx ← read
        let reassignments := ctx.mutVars.filter reassignedVars.contains |>.map (fun n => (n, ctx.mutVarDefs.get! n))
        logInfo m!"reassignments: {reassignments}"
        if jumps.size > 1 && k matches .cont _ _ then
          let .cont name k := k | unreachable!
          let tys ← liftMetaM <| reassignments.mapM (inferType ·.2)
          let resTy ← jumps[0]!.2.2.mvarId!.withContext (inferType jumps[0]!.2.1)
          joinTy.mvarId!.assign (← mkArrowN (tys.push resTy) mα)
          let joinRhs := joinRhs.mvarId!
          let rhs ← joinRhs.withContext do
            withLocalDeclsDND (reassignments.map (·.1) |>.zip tys |>.push (name, resTy)) fun xs => do
              mkLambdaFVars xs (← k xs.back!)
          joinRhs.assign rhs
          logInfo m!"join point {jp} has type {joinTy} and definition {rhs}"
          for (decls, r, mv) in jumps do
            let mv := mv.mvarId!
            mv.withContext do
            let mut jump := jp
            for (name, oldDefn) in reassignments do
              let newDefn ← getLocalDeclFromUserName name
              jump := mkApp jump newDefn.toExpr
            jump := mkApp jump r
            -- logInfo m!"assigning {mkMVar mv} with {jump}"
            discard <| isDefEq (mkMVar mv) jump
        else if jumps.size == 1 || k matches .last _ then
          logInfo m!"no join point needed for {jumps.map (fun (decls, ret) => (decls.map LocalDecl.toExpr, ret))}"
          for (decls, r, mv) in jumps do
            let mv := mv.mvarId!
            mv.withContext do
            let res ←
              withReader (fun ctx => { ctx with mutVarDefs := decls.foldr (init := ctx.mutVarDefs) (fun decl acc => acc.insert decl.userName decl.toExpr)  }) do
              match k with
              | .last returnType => mkPureApp dooElem returnType r
              | .cont name k => k r -- TODO name?
            -- logInfo m!"assigning {mkMVar mv} with {res}"
            discard <| isDefEq (mkMVar mv) res

        logInfo m!"then {← instantiateMVars then_} else {← instantiateMVars else_}"
        let then_ ← Term.exprToSyntax then_
        let else_ ← Term.exprToSyntax else_
        logInfo m!"then {then_} else {else_}"
        Term.elabTermEnsuringType (← `(if $cond then $then_ else $else_)) mα
          )
    | `(dooElem| break) | `(dooElem| continue) =>
      throwErrorAt dooElem "`return`, `break`, or `continue` must be the last element of a do block"
    | _ => throwErrorAt dooElem "unexpected do element {dooElem}"

  meta def elabElems1 (dooElems : Array (TSyntax `dooElem)) (k : DoElemCont) : DoElabM Expr := do
    let last := dooElems.back!
    let init := dooElems.pop
    let unit ← mkPUnit
    init.foldr (init := elabElem last k) fun el k =>
      elabElem el (.cont `_ (fun r => do discard <| Term.ensureHasType unit r; k))

end

meta def elabDooBlock (dooSeq : TSyntax `dooSeq) (expectedType? : Expr) : TermElabM Expr := do
  trace[Elab.do] "Doo block: {dooSeq}, expectedType?: {expectedType?}"
  Term.tryPostponeIfNoneOrMVar expectedType?
  let ctx ← mkContext expectedType?
  let res ← elabElems1 (getDooElems dooSeq) (.last ctx.earlyReturnType) |>.run ctx |>.run' {}
  logInfo m!"res: {res}"
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
  Bind ?m.16
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
error: Type mismatch
  pure true
has type
  Id Bool
but is expected to have type
  Id PUnit
-/
#guard_msgs (error) in
example := (Id.run doo pure true; pure ())

/--
error: Type mismatch
  pure true
has type
  Id Bool
but is expected to have type
  Id PUnit
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure true} else {pure false}; pure ())

-- Regression test cases of what's currently broken in the do elaborator:
example : Unit := (Id.run do  let n ← if true then pure 3 else pure 42)
example : Unit := (Id.run doo let n ← if true then pure 3 else pure 42)

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
