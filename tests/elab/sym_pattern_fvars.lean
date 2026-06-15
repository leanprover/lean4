import Lean.Meta.Sym
open Lean Meta Sym

/-!
Tests for `mkPatternFVars`, exercising how it abstracts the locally nameless variables of the
ambient context into a `Sym.Pattern`: an array mixing free variables (from `forallTelescope`) and
metavariables (from `forallMetaTelescope`), the `usedOnly` option, binders opened by lambda and let
telescopes, and a metavariable wildcard (`Nat.succ ?m`) used as a simproc trigger pattern.
-/

opaque a : Nat
opaque q : Nat → Nat → Prop
axiom qax (x y : Nat) : q x y
axiom hax (x : Nat) (h : x = x) : q x x

/--
Open the first binder of `∀ x y, q x y` as a metavariable and the second as a free variable, then
abstract over the mixed array. The result must equal the all-free-variable pattern from
`mkPatternFromDecl`, and match a concrete application.
-/
def testMixed : SymM Unit := do
  let type := (← getConstInfo ``qax).type
  let (mvars, _, body) ← forallMetaBoundedTelescope type 1
  forallTelescope body fun fvars key => do
    let pMixed ← mkPatternFVars (mvars ++ fvars) key
    let pAll ← mkPatternFromDecl ``qax
    unless pMixed.pattern == pAll.pattern do
      throwError "pattern mismatch:{indentExpr pMixed.pattern}\n!={indentExpr pAll.pattern}"
    unless pMixed.varTypes.size == pAll.varTypes.size do
      throwError "varTypes size mismatch: {pMixed.varTypes.size} != {pAll.varTypes.size}"
    let tgt ← shareCommon (mkApp2 (mkConst ``q) (mkConst ``a) (mkNatLit 7))
    let some r ← pMixed.match? tgt | throwError "match failed"
    logInfo <| mkAppN (mkConst ``q) r.args

/-- info: q a 7 -/
#guard_msgs in
#eval SymM.run testMixed

/--
In `∀ (x : Nat) (h : x = x), q x x` the hypothesis `h` does not occur in the conclusion, so
`usedOnly := true` drops it. The surviving count matches `mkForallFVars (usedOnly := true)`.
-/
def testUsedOnly : SymM Unit := do
  let type := (← getConstInfo ``hax).type
  forallTelescope type fun xs body => do
    let pKeep ← mkPatternFVars xs body
    let pUsed ← mkPatternFVars xs body (usedOnly := true)
    let mkForall ← forallTelescope (← mkForallFVars xs body (usedOnly := true)) fun ys _ => pure ys.size
    logInfo m!"keep={pKeep.varTypes.size} used={pUsed.varTypes.size} mkForallFVars={mkForall}"
    let tgt ← shareCommon (mkApp2 (mkConst ``q) (mkConst ``a) (mkConst ``a))
    let some r ← pUsed.match? tgt | throwError "match failed"
    unless r.args.size == 1 do throwError "expected 1 pattern variable, got {r.args.size}"

/-- info: keep=2 used=1 mkForallFVars=1 -/
#guard_msgs in
#eval SymM.run testUsedOnly

/-- Build a pattern from the body of a `fun` via `lambdaTelescope`. -/
def testLambda : SymM Unit := do
  let e := Expr.lam `x (mkConst ``Nat) (mkApp2 (mkConst ``q) (.bvar 0) (.bvar 0)) .default
  lambdaTelescope e fun xs body => do
    let p ← mkPatternFVars xs body
    let tgt ← shareCommon (mkApp2 (mkConst ``q) (mkConst ``a) (mkConst ``a))
    let some r ← p.match? tgt | throwError "match failed"
    logInfo r.args[0]!

/-- info: a -/
#guard_msgs in
#eval SymM.run testLambda

/-- Build a pattern from the body of a `let` via `lambdaLetTelescope`. -/
def testLet : SymM Unit := do
  let e := Expr.letE `x (mkConst ``Nat) (mkNatLit 1) (mkApp2 (mkConst ``q) (.bvar 0) (.bvar 0)) false
  lambdaLetTelescope e fun xs body => do
    let p ← mkPatternFVars xs body
    let tgt ← shareCommon (mkApp2 (mkConst ``q) (mkConst ``a) (mkConst ``a))
    let some r ← p.match? tgt | throwError "match failed"
    logInfo r.args[0]!

/-- info: a -/
#guard_msgs in
#eval SymM.run testLet

/--
`mkPatternFVars` abstracts a metavariable wildcard (`Nat.succ ?m`) directly into a pattern variable,
producing the discrimination-tree keys `[Nat.succ, *]` that match `Nat.succ 42`. This is the shape
of a simproc trigger pattern.
-/
def testMVarWildcard : MetaM Unit := do
  let natMVar ← mkFreshExprMVar (mkConst ``Nat)
  let e := mkApp (mkConst ``Nat.succ) natMVar
  let pattern ← mkPatternFVars #[natMVar] e
  let d : DiscrTree Bool := Sym.insertPattern {} pattern true
  let tgt := mkApp (mkConst ``Nat.succ) (mkNatLit 42)
  logInfo m!"keys: {pattern.mkDiscrTreeKeys}\nmatch: {Sym.getMatch d tgt}\nover-applied: {Sym.getMatchWithExtra d tgt}"

/--
info: keys: [Nat.succ, *]
match: [true]
over-applied: [(true, 0)]
-/
#guard_msgs in
#eval testMVarWildcard
