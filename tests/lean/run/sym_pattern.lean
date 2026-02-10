import Lean.Meta.Sym
open Lean Meta Sym Grind
set_option sym.debug true
opaque p : Nat → Prop
opaque q : Nat → Nat → Prop
axiom pax : p x
def ex := ∃ x : Nat, p x ∧ x = .zero

def test1 : SymM Unit := do
  let pEx ← mkPatternFromDecl ``Exists.intro
  let pAnd ← mkPatternFromDecl ``And.intro
  let pEq ← mkPatternFromDecl ``Eq.refl
  let e ← shareCommon (← getConstInfo ``ex).value!
  let some r₁ ← pEx.match? e | throwError "failed"
  logInfo <| mkAppN (mkConst ``Exists.intro r₁.us) r₁.args
  let some r₂ ← pAnd.match? (← Sym.inferType r₁.args[3]!) | failure
  logInfo <| mkAppN (mkConst ``And.intro r₂.us) r₂.args
  let some r₃ ← pEq.unify? (← Sym.inferType r₂.args[3]!) | failure
  logInfo <| mkAppN (mkConst ``Eq.refl r₃.us) r₃.args

/--
info: @Exists.intro Nat (fun x => And (p x) (@Eq Nat x Nat.zero)) ?m.1 ?m.2
---
info: @And.intro (p ?m.1) (@Eq Nat ?m.1 Nat.zero) ?m.3 ?m.4
---
info: @Eq.refl Nat Nat.zero
-/
#guard_msgs in
set_option pp.explicit true in
#eval SymM.run test1

def test2 : SymM Unit := do
  let ruleEx   ← mkBackwardRuleFromDecl ``Exists.intro
  let ruleAnd  ← mkBackwardRuleFromDecl ``And.intro
  let ruleRefl ← mkBackwardRuleFromDecl ``Eq.refl
  let rulePax  ← mkBackwardRuleFromDecl ``pax
  let mvar ← mkFreshExprMVar (← getConstInfo ``ex).value!
  let mvarId ← preprocessMVar mvar.mvarId!
  let .goals [mvarId, _] ← ruleEx.apply mvarId | failure
  let .goals [mvarId₁, mvarId₂] ← ruleAnd.apply mvarId | failure
  let .goals [] ← rulePax.apply mvarId₁ | failure
  let .goals [] ← ruleRefl.apply mvarId₂ | failure
  logInfo mvar

/--
info: @Exists.intro Nat (fun x => And (p x) (@Eq Nat x Nat.zero)) Nat.zero
  (@And.intro (p Nat.zero) (@Eq Nat Nat.zero Nat.zero) (@pax Nat.zero) (@Eq.refl Nat Nat.zero))
-/
#guard_msgs in
set_option pp.explicit true in
#eval SymM.run test2

opaque a : Nat
opaque bla : Nat → Nat → Nat
opaque foo : Type → Nat → Nat
axiom pFoo (x : Nat) : p (foo Prop (bla x 1))

def test3 : SymM Unit := do
  withLetDecl `x (.sort 1) (.sort 0) fun x =>
  withLetDecl `y (mkConst ``Nat) (mkNatLit 1) fun y => do
  let target := mkApp (mkConst ``p) (mkApp2 (mkConst ``foo) x (mkApp2 (mkConst ``bla) (mkNatAdd (mkNatLit 3) y) y))
  let mvar ← mkFreshExprMVar target
  let mvarId ← preprocessMVar mvar.mvarId!
  let rule ← mkBackwardRuleFromDecl ``pFoo
  let .goals [] ← rule.apply mvarId | failure
  logInfo mvar

/-- info: pFoo (3 + y) -/
#guard_msgs in
#eval SymM.run test3

def test4 : SymM Unit := do
  withLetDecl `x (.sort 1) (.sort 0) fun x =>
  withLetDecl `y (mkConst ``Nat) (mkNatLit 1) fun y => do
  let e := mkApp2 (mkConst ``bla) (mkNatAdd (mkNatLit 3) y) y
  let m1 ← mkFreshExprMVar (mkConst ``Nat)
  assert! (← isDefEq m1 e)
  let target := mkApp (mkConst ``p) (mkApp2 (mkConst ``foo) x m1)
  let target ← shareCommon target
  let p ← mkPatternFromDecl ``pFoo
  let some r ← p.match? target | failure
  logInfo <| mkAppN (mkConst ``pFoo r.us) r.args

/-- info: pFoo (3 + y) -/
#guard_msgs in
#eval SymM.run test4

def ex₂ := ∃ x : Nat, True ∧ x = .zero

def test5 : SymM Unit := do
  let ruleEx   ← mkBackwardRuleFromExpr <| mkApp (mkConst ``Exists.intro [1]) Nat.mkType
  let ruleAnd  ← mkBackwardRuleFromExpr <| mkApp (mkConst ``And.intro) (mkConst ``True)
  let ruleTrue ← mkBackwardRuleFromExpr <| (mkConst ``True.intro)
  let ruleRefl ← mkBackwardRuleFromDecl ``Eq.refl
  let mvar ← mkFreshExprMVar (← getConstInfo ``ex₂).value!
  let mvarId ← preprocessMVar mvar.mvarId!
  let .goals [mvarId, _] ← ruleEx.apply mvarId | failure
  let .goals [mvarId₁, mvarId₂] ← ruleAnd.apply mvarId | failure
  let .goals [] ← ruleTrue.apply mvarId₁ | failure
  let .goals [] ← ruleRefl.apply mvarId₂ | failure
  logInfo mvar

/--
info: @Exists.intro Nat (fun x => And True (@Eq Nat x Nat.zero)) Nat.zero
  (@And.intro True (@Eq Nat Nat.zero Nat.zero) True.intro (@Eq.refl Nat Nat.zero))
-/
#guard_msgs in
set_option pp.explicit true in
#eval SymM.run test5

def ex₃ := (Nat × Type) × (Nat × Prop)

def test6 : SymM Unit := do
  let ruleProd ← mkBackwardRuleFromDecl ``Prod.mk
  -- `u` is universe parameter in the following rule
  let ruleProdNat ← mkBackwardRuleFromExpr (mkApp (mkConst ``Prod.mk [0, mkLevelParam `u]) Nat.mkType) [`u]
  let mvar ← mkFreshExprMVar (← getConstInfo ``ex₃).value!
  let mvarId ← preprocessMVar mvar.mvarId!
  let .goals [mvarId₁, mvarId₂] ← ruleProd.apply mvarId | failure
  logInfo mvarId₁
  logInfo mvarId₂
  -- **Note**: `ruleProdNat` is applied with different `u`s in the following two applications
  let .goals [mvarId₁₁, mvarId₁₂] ← ruleProdNat.apply mvarId₁ | failure
  let .goals [mvarId₂₁, mvarId₂₂] ← ruleProdNat.apply mvarId₂ | failure
  mvarId₁₁.assign (mkNatLit 0)
  mvarId₂₁.assign (mkNatLit 1)
  mvarId₁₂.assign Nat.mkType
  mvarId₂₂.assign (mkConst ``True)
  logInfo mvar
  check (← instantiateMVars mvar)

/--
info: ⊢ Prod.{0, 1} Nat Type
---
info: ⊢ Prod.{0, 0} Nat Prop
---
info: Prod.mk.{1, 0} (Prod.mk.{0, 1} 0 Nat) (Prod.mk.{0, 0} 1 True)
-/
#guard_msgs in
set_option pp.universes true in
#eval SymM.run test6
