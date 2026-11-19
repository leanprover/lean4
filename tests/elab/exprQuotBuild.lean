import Lean

/-!
# Comprehensive Tests for Term-Position `` `(expr[rel]| t) `` Building

Covers spec §4 requirements:
- Compile-time closed templates with runtime `$e` splice substitution (`MetaM`, `TacticM`,
  `TermElabM`, `StateT`, polymorphic `[MonadLiftT MetaM m]`).
- Zero beta-reduction (`$P $y` stays `.app`), pointer sharing (`$x + $x`), zero runtime mvar
  allocation for splices, and preservation of caller metavariables inside splices.
- `refine` hole semantics (`?h`, `?_`, shared `?h`, distinct `?_`, fresh per call, `Prop` &
  dependent hole types).
- Strict compile-time errors on unintended `_`, unresolved implicits/universes, failed concrete TC,
  non-splice-dependent stuck TC, unannotated `?h`, out-of-scope `$x`, non-`MetaM` targets, `/sym`.
- Runtime splice type checking under `rel` (defaulting to `defeq`, adjusted by `/reducible`,
  `/instances`, `/structural`, `[±items]`, `[$d]`, `±flags`) and dependent instance synthesis.
- Template deduplication (`exprTmplExt`), closed `ResolvedExprMatchRel` hoisting, and
  `subterms`/`match`/`ctx.fill` round-trips.
-/

namespace ExprQuotBuildTest

open Lean Meta Elab Tactic

private def check (cond : Bool) (msg : String) : MetaM Unit := do
  unless cond do
    throwError msg

private def tryBuild (x : MetaM Expr) : MetaM (Except String Expr) := do
  try
    return .ok (← x)
  catch ex =>
    return .error (← ex.toMessageData.toString)

/-! ## 1. Compile-time strictness errors (`#guard_msgs`) -/

/--
error: don't know how to synthesize placeholder
context:
⊢ Nat
-/
#guard_msgs in
def badUnderscore : MetaM Expr := `(expr| (_ : Nat) + 1)

/-- error: Failed to infer type of binder `x` -/
#guard_msgs in
def badUnannotatedLam : MetaM Expr := `(expr| fun x => x)

/--
error: don't know how to synthesize implicit argument `α`
  @List.nil ?m.1
context:
⊢ Type ?u.2
-/
#guard_msgs in
def badImplicitNil : MetaM Expr := `(expr| List.nil)

/--
error: invalid `expr` quotation: unresolved universe level metavariables in
  Sort ?u.2
-/
#guard_msgs in
def badSortLevel : MetaM Expr := `(expr| Sort _)

/--
error: invalid `expr` quotation: unresolved universe level metavariables in
  PUnit
-/
#guard_msgs in
def badPUnitLevel : MetaM Expr := `(expr| PUnit)

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.5

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
def badConcreteTC : MetaM Expr := `(expr| 1 + "hello")

/--
error: failed to synthesize
  ToString ?m.1

Hint: Additional diagnostic information may be available using the
`set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
def badStuckTCUnderscore : MetaM Expr := `(expr| toString _)

/--
error: failed to synthesize
  ToString ?m.1

Hint: Additional diagnostic information may be available using the
`set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
def badStuckTCHole : MetaM Expr := `(expr| toString ?h)

/--
error: invalid `expr` quotation: hole `?h` has unresolved type; add a type annotation `(?h : T)`
-/
#guard_msgs in
def badUnannotatedHole : MetaM Expr := `(expr| ?h)

/--
error: invalid `expr` quotation: hole `?_` has unresolved type; add a type annotation `(?_ : T)`
-/
#guard_msgs in
def badUnannotatedAnonHole : MetaM Expr := `(expr| ?_)

/--
error: don't know how to synthesize placeholder for argument `tail`
context:
⊢ List ?m.1
-/
#guard_msgs in
def badConsTailHole (x : Expr) : MetaM Expr := `(expr| @List.cons _ $x _)

/--
error: don't know how to synthesize placeholder for argument `isLt`
context:
⊢ 0 < 3
-/
#guard_msgs in
def badFinProofHole : MetaM Expr := `(expr| @Fin.mk 3 0 _)

/-- error: unknown identifier `missingSplice` in `$`-pin (did you mean `?missingSplice`?) -/
#guard_msgs in
def badUnknownSplice : MetaM Expr := `(expr| $missingSplice + 1)

/-- error: expected `$e` splice; use `?_` for a metavariable hole -/
#guard_msgs in
def badDollarUnderscore : MetaM Expr := `(expr| $_ + 1)

/--
error: type mismatch
  `(expr| 1 + 2)
has type
  MetaM Expr
but is expected to have type
  Id Expr
-/
#guard_msgs in
def badWrongMonadId : Id Expr := `(expr| 1 + 2)

/--
error: type mismatch
  `(expr| 1 + 2)
has type
  MetaM Expr
but is expected to have type
  CoreM Expr
-/
#guard_msgs in
def badWrongMonadCore : CoreM Expr := `(expr| 1 + 2)

/--
error: expr quotation `/sym` requires a `[MonadSym]` monad (e.g. `SymM` or `GrindTacticM`),
got expected type
  MetaM Expr
-/
#guard_msgs (whitespace := lax) in
def badSymWrongMonad : MetaM Expr := `(expr/sym| 1 + 2)

def myDefAlias := Nat

/--
error: invalid relation item `-ExprQuotBuildTest.myDefAlias`:
`structural` does not unfold `ExprQuotBuildTest.myDefAlias` by default
-/
#guard_msgs (whitespace := lax) in
def badStructuralNegItem (a : Expr) : MetaM Expr :=
  `(expr/structural [-myDefAlias]| ($a : Nat))

/-! ## 2. Zero beta-reduction, pointer sharing, dedup, and monad lifting -/

/-! ### Zero beta-reduction on `$P $y` and `fun x => $P x` -/

section ZeroBetaReduction

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  let pFun := mkLambda `x .default natTy (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkNatLit 1))
  let y := mkNatLit 41
  let appExpr ← `(expr| $pFun $y)
  check (appExpr.isApp && ptrEq appExpr.appFn! pFun && ptrEq appExpr.appArg! y)
    "$P $y must preserve exact .app node without beta-reduction"
  Meta.check appExpr

  let hoLam ← `(expr| fun x => $pFun x)
  match hoLam with
  | .lam _ dom (.app fn (.bvar 0)) _ =>
    check (dom == natTy && ptrEq fn pFun) "fun x => $P x domain/body mismatch"
  | _ => throwError "expected unreduced .lam body (.app pFun (.bvar 0)), got {hoLam}"
  Meta.check hoLam

  -- Explicit normalization outside the quotation still works cleanly.
  let reduced ← Core.betaReduce appExpr
  check (reduced == mkApp2 (mkConst ``Nat.add) (mkNatLit 41) (mkNatLit 1))
    "explicit Core.betaReduce mismatch"

end ZeroBetaReduction

/-! ### Pointer sharing (`$x + $x`) and zero runtime mvar allocation -/

section PointerSharingAndZeroMVars

#guard_msgs in
#eval show MetaM Unit from do
  let x := mkNatLit 7
  let dbl ← `(expr| $x + $x)
  match dbl with
  | .app (.app _ a1) a2 =>
    check (ptrEq x a1 && ptrEq x a2) "repeated `$x` must preserve pointer sharing"
  | _ => throwError "expected binary app for `$x + $x`, got {dbl}"

  let a := mkNatLit 1
  let b := mkNatLit 2
  let mvsBefore := (← getMCtx).mvarCounter
  let typedAdd ← `(expr| ($a : Nat) + ($b : Nat))
  let mvsAfter := (← getMCtx).mvarCounter
  check (mvsAfter == mvsBefore) "typed splice build must allocate zero runtime metavariables"
  Meta.check typedAdd

end PointerSharingAndZeroMVars

/-! ### Nested splice build -/

section NestedSpliceBuild

def nestedSpliceBuild (a b c : Expr) : MetaM Expr := do
  `(expr| Nat.mul $(← `(expr| Nat.add $a $b)) $c)

#guard_msgs in
#eval show MetaM Unit from do
  let nested ← nestedSpliceBuild (mkNatLit 2) (mkNatLit 3) (mkNatLit 4)
  let expected :=
    mkApp2 (mkConst ``Nat.mul) (mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 3)) (mkNatLit 4)
  check (nested == expected) "nested splice build mismatch"

end NestedSpliceBuild

/-! ### Template deduplication and closed relation hoisting (`sharedTmplDedup`) -/

section SharedTemplateDedup

def sharedTmplDedup (a b x y : Expr) : MetaM (Expr × Expr) := do
  let e1 ← `(expr| Nat.add $a $b)
  let e2 ← `(expr/structural| Nat.add $x $y)
  return (e1, e2)

private partial def collectTmplPayloads (e : Expr) (st : Nat × Array String) :
    Nat × Array String :=
  let st := match e with
    | .app (.const fn _) (.lit (.strVal s)) =>
      if fn == ``ExprTemplate.decode then
        (st.1 + 1, if st.2.contains s then st.2 else st.2.push s)
      else
        st
    | _ => st
  match e with
  | .app f a         => collectTmplPayloads a (collectTmplPayloads f st)
  | .lam _ t b _     => collectTmplPayloads b (collectTmplPayloads t st)
  | .forallE _ t b _ => collectTmplPayloads b (collectTmplPayloads t st)
  | .letE _ t v b _  => collectTmplPayloads b (collectTmplPayloads v (collectTmplPayloads t st))
  | .mdata _ b       => collectTmplPayloads b st
  | .proj _ _ b      => collectTmplPayloads b st
  | _                => st

#guard_msgs in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut tmplCount := 0
  for (n, _) in env.constants do
    if (``sharedTmplDedup).isPrefixOf n && n.toString.contains "exprTmpl" then
      tmplCount := tmplCount + 1
  check (tmplCount == 0) s!"expected 0 extra exprTmpl consts, got {tmplCount}"
  let some dedupVal := (env.find? ``sharedTmplDedup).bind (·.value?)
    | throwError "expected value for sharedTmplDedup"
  let (tmplCalls, tmplPayloads) := collectTmplPayloads dedupVal (0, #[])
  check (tmplCalls == 2 && tmplPayloads.size == 1)
    s!"expected 2 decode calls and 1 unique payload in sharedTmplDedup, \
       got calls={tmplCalls} uniq={tmplPayloads.size}"
  let hasClosedIR := (Array.range 32).any fun i =>
    (Lean.IR.findEnvDecl env (``sharedTmplDedup ++ (`_closed).appendIndexAfter i)).isSome
  check hasClosedIR "expected ExtractClosed `_closed_` IR decl for sharedTmplDedup"

end SharedTemplateDedup

/-! ### Polymorphic & monad-lifted builders -/

section MonadLifting

def polyBuild [Monad m] [MonadLiftT MetaM m] (a b : Expr) : m Expr :=
  `(expr| $a + $b)

def tacBuild (a b : Expr) : TacticM Expr :=
  `(expr| $a + $b)

def termBuild (a b : Expr) : TermElabM Expr :=
  `(expr| $a + $b)

def stateBuild (a b : Expr) : StateT Nat MetaM Expr := do
  modify (· + 1)
  `(expr| $a + $b)

#guard_msgs in
#eval show MetaM Unit from do
  let a := mkNatLit 1
  let b := mkNatLit 2
  let typedAdd ← `(expr| ($a : Nat) + ($b : Nat))
  check ((← polyBuild a b) == typedAdd) "polyBuild mismatch"
  let (stRes, stCnt) ← (stateBuild a b).run 0
  check (stRes == typedAdd && stCnt == 1) "stateBuild mismatch"

#guard_msgs in
#eval show TermElabM Unit from do
  let a := mkNatLit 1
  let b := mkNatLit 2
  let typedAdd ← `(expr| ($a : Nat) + ($b : Nat))
  check ((← termBuild a b) == typedAdd) "termBuild mismatch"

#guard_msgs in
example : True := by
  run_tac do
    let a := mkNatLit 1
    let b := mkNatLit 2
    let typedAdd ← `(expr| ($a : Nat) + ($b : Nat))
    check ((← tacBuild a b) == typedAdd) "tacBuild mismatch"
    closeMainGoal `tacBuild (mkConst ``True.intro)

end MonadLifting

/-! ## 3. `refine` holes and caller metavariables -/

/-! ### Named (`?h`), anonymous (`?_`), fresh per call, and `Prop`-typed holes -/

section RefineHolesBasic

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  let holeNamed ← `(expr| (?h : Nat) + (?h : Nat))
  let mvsNamed ← getMVars holeNamed
  let [mvH] := mvsNamed.toList
    | throwError "expected 1 shared mvar for `?h + ?h`, got {mvsNamed.size}"
  let dH ← mvH.getDecl
  check (dH.userName == `h && dH.kind matches .syntheticOpaque && dH.type == natTy)
    "`?h` must be `.syntheticOpaque` named `h : Nat`"

  let holeAnon ← `(expr| (?_ : Nat) + (?_ : Nat))
  let mvsAnon ← getMVars holeAnon
  let [mvA0, mvA1] := mvsAnon.toList
    | throwError "expected 2 anon mvars for `?_ + ?_`, got {mvsAnon.size}"
  check (mvA0 != mvA1) "two `?_` holes must be distinct metavariables"
  for mv in [mvA0, mvA1] do
    let d ← mv.getDecl
    check (d.userName == .anonymous && d.kind matches .syntheticOpaque)
      "`?_` must be anonymous `.syntheticOpaque`"

  let holeCall1 ← `(expr| (?h : Nat))
  let holeCall2 ← `(expr| (?h : Nat))
  check (holeCall1 != holeCall2) "separate quotation calls must allocate fresh hole mvars"

  let propP := mkConst ``True
  let hProp ← `(expr| (?hp : $propP))
  check (hProp.isMVar && (← hProp.mvarId!.getDecl).kind matches .syntheticOpaque &&
    (← inferType hProp) == propP) "`(?hp : $propP)` failed for `Prop` splice"

end RefineHolesBasic

/-! ### Dependent hole types (`@Sigma.mk` and earlier-hole binders) -/

section RefineHolesDependent

#guard_msgs in
#eval show MetaM Unit from do
  let depHoles ← `(expr| @Sigma.mk Nat Fin ?n ?f)
  let depMVs ← getMVars depHoles
  let [mvN, mvF] := depMVs.toList
    | throwError "expected 2 dependent Sigma holes, got {depMVs.size}"
  check ((← mvN.getDecl).userName == `n && (← mvF.getDecl).userName == `f)
    "dependent Sigma hole names mismatch"
  check ((← instantiateMVars (← mvF.getDecl).type) == mkApp (mkConst ``Fin) (mkMVar mvN))
    "dependent `?f` type must reference `?n`"
  Meta.check depHoles

  -- Earlier hole placeholder remains valid inside a later hole's type.
  let priorHoleDep ← `(expr| (fun (A : Type) (x : A) => x) ?A ?x)
  let priorHoleMVs ← getMVars priorHoleDep
  let [mvA, mvX] := priorHoleMVs.toList
    | throwError "expected 2 holes for priorHoleDep, got {priorHoleMVs.size}"
  check ((← mvA.getDecl).userName == `A && (← mvX.getDecl).userName == `x)
    "priorHoleDep hole names mismatch"
  check ((← instantiateMVars (← mvX.getDecl).type) == mkMVar mvA)
    "later `?x` hole type must reference outer `?A` metavariable"
  Meta.check priorHoleDep

end RefineHolesDependent

/-! ### Runtime hole-type resolution failures (`withNewMCtxDepth`, no mvar leak) -/

section HoleResolutionTagFailures

@[reducible] def IdNatPoly (_ : Type u) : Type := Nat
@[reducible] def IdNat0 (_ : Type) : Type := Nat
opaque polyHoleTag {α : Type u} (x : IdNatPoly α) (h : α) : Nat
opaque monoHoleTag {α : Type} (x : IdNat0 α) (h : α) : Nat

#guard_msgs in
#eval show MetaM Unit from do
  let a := mkNatLit 1
  let mvsBeforeHoleFail := (← getMCtx).mvarCounter
  match ← tryBuild `(expr/reducible| polyHoleTag $a ?h) with
  | .ok _ => throwError "expected runtime failure for unresolved universe level in hole type"
  | .error msg =>
    check (msg.contains "expr quotation failed to resolve")
      s!"unexpected polyHoleTag failure message: {msg}"
  match ← tryBuild `(expr/reducible| monoHoleTag $a ?h) with
  | .ok _ => throwError "expected runtime failure for unresolved implicit type in hole type"
  | .error msg =>
    check (msg.contains "expr quotation failed to resolve")
      s!"unexpected monoHoleTag failure message: {msg}"
  check ((← getMCtx).mvarCounter == mvsBeforeHoleFail)
    "failed runtime hole resolution must not leak metavariables"

end HoleResolutionTagFailures

/-! ### Runtime hole-type level-param failure on `ExprTemplate` (`MetaM` & `SymM`) -/

section HoleResolutionTemplateFailures

#guard_msgs in
#eval show MetaM Unit from do
  let mvsBeforeHoleFail := (← getMCtx).mvarCounter
  let polyHoleTmpl : ExprTemplate := {
    levelParams := [`u]
    lam         := mkLambda `h .default (mkSort (.succ (.param `u))) (mkBVar 0)
    varKinds    := #[.hole (some `h)]
  }
  match ← tryBuild (polyHoleTmpl.instantiate {} #[]) with
  | .ok _ => throwError "expected runtime failure for ExprTemplate level param in hole type"
  | .error msg =>
    check (msg.contains "expr quotation failed to resolve")
      s!"unexpected polyHoleTmpl MetaM failure message: {msg}"
  let symFail ← Lean.Meta.Sym.SymM.run do
    try
      discard <| polyHoleTmpl.instantiateSymSite `testPolyHole {} #[]
      return none
    catch ex =>
      return some (← ex.toMessageData.toString)
  match symFail with
  | none => throwError "expected runtime failure for Sym ExprTemplate level param in hole type"
  | some msg =>
    check (msg.contains "expr quotation failed to resolve")
      s!"unexpected polyHoleTmpl SymM failure message: {msg}"
  check ((← getMCtx).mvarCounter == mvsBeforeHoleFail)
    "failed runtime hole resolution must not leak metavariables"

end HoleResolutionTemplateFailures

/-! ### Caller metavariable preservation inside splices -/

section CallerMVarPreservation

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  let callerMV ← mkFreshExprMVar (some natTy) .natural `callerHole
  let builtCaller ← `(expr| ($callerMV : Nat) + 1)
  check (!(← callerMV.mvarId!.isAssigned)) "caller metavariable must remain unassigned"
  match builtCaller with
  | .app (.app _ lhs) _ => check (ptrEq lhs callerMV) "caller mvar pointer must stay intact"
  | _ => throwError "expected binary app for builtCaller"

end CallerMVarPreservation

/-! ## 4. Runtime splice type checking under configured relations & flags -/

/-! ### Transparency levels and named relation items (`[±items]`) -/

namespace SpliceRelationItems

def myDefAlias := Nat
abbrev myRedAlias := Nat

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `aDef (mkConst ``myDefAlias) fun aDef =>
  withLocalDeclD `aRed (mkConst ``myRedAlias) fun aRed => do
    check (← tryBuild `(expr| ($aDef : Nat))).isOk "default `.defeq` must accept myDefAlias"
    check (!(← tryBuild `(expr[-myDefAlias]| ($aDef : Nat))).isOk)
      "`[-myDefAlias]` must reject myDefAlias"
    check (!(← tryBuild `(expr/reducible| ($aDef : Nat))).isOk)
      "`/reducible` must reject semireducible myDefAlias"
    check (← tryBuild `(expr/reducible [+myDefAlias]| ($aDef : Nat))).isOk
      "`/reducible [+myDefAlias]` must accept myDefAlias"
    check (← tryBuild `(expr/reducible| ($aRed : Nat))).isOk
      "`/reducible` must accept reducible myRedAlias"
    check (!(← tryBuild `(expr/structural| ($aRed : Nat))).isOk)
      "`/structural` must reject reducible myRedAlias"
    check (← tryBuild `(expr/structural [myDefAlias]| ($aDef : Nat))).isOk
      "`/structural [myDefAlias]` must accept myDefAlias"

end SpliceRelationItems

/-! ### Beta and zeta reduction flags (`±beta`, `-zeta`, `[$d]`) -/

section SpliceBetaZetaFlags

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  let betaTy := mkApp (mkLambda `z .default (mkSort 1) natTy) natTy
  withLocalDeclD `aBeta betaTy fun aBeta => do
    check (← tryBuild `(expr| ($aBeta : Nat))).isOk "default `/defeq` must reduce beta in type"
    check (!(← tryBuild `(expr/defeq -beta| ($aBeta : Nat))).isOk)
      "`/defeq -beta` must reject unreduced beta type"
    check (← tryBuild `(expr/structural +beta| ($aBeta : Nat))).isOk
      "`/structural +beta` must reduce beta in type"

  withLetDecl `D (mkSort 1) natTy fun d =>
  withLocalDeclD `xd d fun xd => do
    check (!(← tryBuild `(expr/defeq -zeta| ($xd : Nat))).isOk)
      "`/defeq -zeta` must block local let unfolding"
    check (← tryBuild `(expr/defeq [$d] -zeta| ($xd : Nat))).isOk
      "`/defeq [$d] -zeta` must allow unfolding `$d`"
    check (← tryBuild `(expr/defeq [$(d)] -zeta| ($xd : Nat))).isOk
      "`/defeq [$(d)] -zeta` must allow unfolding `$(d)`"

end SpliceBetaZetaFlags

/-! ## 5. Dependent type-class synthesis and runtime splice error checks -/

/-! ### Dependent type-class synthesis successes -/

section DependentTCSuccess

#guard_msgs in
#eval show MetaM Unit from do
  let a := mkNatLit 1
  let b := mkNatLit 2
  let eAdd ← `(expr| $a + $b)
  let eEq ← `(expr| $a == $b)
  let eIte ← `(expr| if $(mkConst ``True) then $a else $b)
  let eStr ← `(expr| toString $a)
  let eCons ← `(expr| List.cons $a [])
  for built in [eAdd, eEq, eIte, eStr, eCons] do
    Meta.check built

  let three := mkNatLit 3
  withLocalDeclD `fa (mkApp (mkConst ``Fin) three) fun fa =>
  withLocalDeclD `fb (mkApp (mkConst ``Fin) three) fun fb => do
    Meta.check (← `(expr| ($fa : Fin $three) + ($fb : Fin $three)))
    Meta.check (← `(expr| ($fa : Fin $three) == ($fb : Fin $three)))

  withLocalDeclD `α (mkSort 1) fun α =>
  withLocalDeclD `instAdd (mkApp (mkConst ``Add [0]) α) fun _ =>
  withLocalDeclD `xα α fun xα =>
  withLocalDeclD `yα α fun yα => do
    let builtLocalTC ← `(expr| ($xα : $α) + ($yα : $α))
    Meta.check builtLocalTC

end DependentTCSuccess

/-! ### Runtime splice type mismatches and dependent TC failures -/

section RuntimeSpliceAndTCFailures

#guard_msgs in
#eval show MetaM Unit from do
  let a := mkNatLit 1
  let b := mkNatLit 2
  let three := mkNatLit 3
  let four := mkNatLit 4
  withLocalDeclD `fa (mkApp (mkConst ``Fin) three) fun fa =>
  withLocalDeclD `fc (mkApp (mkConst ``Fin) four) fun fc => do
    match ← tryBuild `(expr| ($fa : Fin $three) == ($fc : Fin $three)) with
    | .ok _ => throwError "expected runtime splice mismatch for Fin 4 vs Fin 3"
    | .error msg =>
      check (msg.contains "expr quotation splice type mismatch")
        s!"unexpected Fin mismatch message: {msg}"

  let sHi := mkStrLit "hi"
  match ← tryBuild `(expr| $a == $sHi) with
  | .ok _ => throwError "expected runtime splice type mismatch for `1 == \"hi\"`"
  | .error msg =>
    check (msg.contains "expr quotation splice type mismatch")
      s!"unexpected splice mismatch message: {msg}"

  let natTy := mkConst ``Nat
  let pFun := mkLambda `x .default natTy (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkNatLit 1))
  match ← tryBuild `(expr| toString $pFun) with
  | .ok _ => throwError "expected runtime TC failure for `toString (Nat → Nat)`"
  | .error msg =>
    check (msg.contains "expr quotation failed to synthesize dependent instance")
      s!"unexpected runtime TC failure message: {msg}"

  match ← tryBuild `(expr| if $a then $a else $b) with
  | .ok _ => throwError "expected runtime Prop type mismatch on `if 1 ...`"
  | .error msg =>
    check (msg.contains "expr quotation splice type mismatch")
      s!"unexpected ite condition mismatch message: {msg}"

end RuntimeSpliceAndTCFailures

/-! ### Loose-bvar splice precheck and unknown-type caller metavariables -/

section SpliceHygieneChecks

#guard_msgs in
#eval show MetaM Unit from do
  let a := mkNatLit 1
  let loose := mkBVar 0
  match ← tryBuild `(expr| $loose + $a) with
  | .ok _ => throwError "expected runtime error for loose bound variable splice"
  | .error msg =>
    check (msg.contains "expr quotation splice expression contains loose bound variable")
      s!"unexpected loose-bvar error message: {msg}"

  let unkTy ← mkFreshTypeMVar
  let unkMV ← mkFreshExprMVar (some unkTy)
  match ← tryBuild `(expr| ($unkMV : Nat) + $a) with
  | .ok _ => throwError "expected runtime splice type mismatch for unknown-type caller mvar"
  | .error msg =>
    check (msg.contains "expr quotation splice type mismatch")
      s!"unexpected unknown-type caller mvar message: {msg}"
    check (!(← unkMV.mvarId!.isAssigned) && !(← unkTy.mvarId!.isAssigned))
      "failed splice check must not mutate caller metavariables or their types"

end SpliceHygieneChecks

/-! ## 6. Round-trip, tactic integration, and pretty-printing -/

/-! ### Round-trip `subterms` + pattern `match` + term-position build + `ExprContext.fill` -/

section SubtermsFillRoundTrip

#guard_msgs in
#eval show MetaM Unit from do
  let mulExpr := mkApp2 (mkConst ``Nat.mul) (mkNatLit 2) (mkNatLit 3)
  let root := mkApp2 (mkConst ``Nat.add) mulExpr (mkNatLit 4)
  let mut rewritten := root
  for (sub, ctx) in subterms root do
    if let `(expr| Nat.mul ?u ?v) := sub then
      let repl ← `(expr| Nat.add $v $u)
      rewritten := ctx.fill repl
      break
  let expectedRewritten :=
    mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) (mkNatLit 3) (mkNatLit 2)) (mkNatLit 4)
  check (rewritten == expectedRewritten) "subterms + match + build + fill round-trip failed"
  Meta.check rewritten

end SubtermsFillRoundTrip

/-! ### Tactic integration (`TacticM`) -/

section TacticIntegration

theorem tacticBuildAndRefine (n : Nat) : n + 0 = n := by
  run_tac do
    let nExpr := (← getLocalDeclFromUserName `n).toExpr
    let pat ← `(expr| @Nat.add_zero $nExpr)
    let goal ← getMainGoal
    goal.assign pat

end TacticIntegration

/-! ### Pretty-printer spacing for relation items and flags (`ppSpace`) -/

section PrettyPrinterSpacing

/--
info: "`(expr/reducible [+Nat.add, -Nat.mul] -eta| 1 + 2)"
"match (modulo := defeq [+Nat.add] +zeta) (0 : Nat) with\n| _ => 1"
"match (modulo := [+Nat.add] +zeta) (0 : Nat) with\n| _ => 1"
"match (modulo := +zeta -eta) (0 : Nat) with\n| _ => 1"
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let env ← getEnv
  for src in [
    "`(expr/reducible[+Nat.add, -Nat.mul]-eta| 1 + 2)",
    "match (modulo := defeq[+Nat.add]+zeta) (0 : Nat) with | _ => 1",
    "match (modulo := [+Nat.add]+zeta) (0 : Nat) with | _ => 1",
    "match (modulo := +zeta -eta) (0 : Nat) with | _ => 1"
  ] do
    let .ok stx := Parser.runParserCategory env `term src | throwError "parse failed: {src}"
    IO.println (repr (← PrettyPrinter.ppTerm ⟨stx⟩).pretty)

end PrettyPrinterSpacing

end ExprQuotBuildTest
