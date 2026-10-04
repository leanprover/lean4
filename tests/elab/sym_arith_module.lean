import Lean

/-!
Additive equality certificates for modules over natural numbers or integers.
Multiplication and symbolic scalar multiplication remain atoms. In particular,
the carrier need not have cancellation, a multiplicative identity, or associative multiplication.
-/

open Lean Meta Elab Tactic Sym

elab "module_nf" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let r ← SymM.run do
      let target ← shareCommon target
      Simp.SimpM.run' (Simp.simp target) { post := fun e => Arith.normalizeAdd? e }
    match r with
    | .rfl .. => throwError "no additive expression changed"
    | .step target proof .. => replaceMainGoal [← g.replaceTargetEq target proof]

elab "module_eq" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some proof ← SymM.run (Arith.proveAddEq? target)
      | throwError "the additive normal forms differ"
    unless ← isDefEq (← inferType proof) target do
      throwError "unexpected certificate type"
    g.assign proof
    replaceMainGoal []

open Lean.Grind

example {M : Type u} [NatModule M] (a b c : M) :
    a + (b + c) = c + a + b := by module_eq

example {M : Type u} [NatModule M] (a b : M) :
    2 • (a + b) + a = 3 • a + 2 • b := by module_eq

example {M : Type u} [NatModule M] (a : M) : 0 • a + a = a := by module_eq

example {M : Type u} [NatModule M] : (0 : M) + 0 = 0 := by module_eq

example {M : Type u} [IntModule M] (a b : M) :
    a + b + b - a = (2 : Int) • b := by module_eq

example {M : Type u} [IntModule M] (a b : M) :
    -((3 : Nat) • a) + (2 : Int) • (a - b) = -a - (2 : Int) • b := by module_eq

example {M : Type u} [IntModule M] (a : M) : a + -a = 0 := by module_eq

example {M : Type u} [NatModule M] [Mul M] (a b : M) :
    a * b + a * b + b * a = 2 • (a * b) + b * a := by module_eq

private abbrev alias {M : Type u} (a : M) := a

example {M : Type u} [NatModule M] [Mul M] (a b : M) :
    alias (a * b) + a * b = 2 • (a * b) := by module_eq

example {M : Type u} [NatModule M] (a : M) :
    letI : SMul Nat M := ⟨fun _ a => a⟩
    2 • a = a + a → 2 • a = a + a := by
  intro h
  fail_if_success module_eq
  exact h

example {M : Type u} [IntModule M] [Mul M] (a b c : M)
    (h : a * (b * c) = (a * b) * c) : a * (b * c) = (a * b) * c := by
  fail_if_success module_eq
  exact h

example {M : Type u} [NatModule M] [Mul M] (a b : M) (h : a * b = b * a) :
    a * b = b * a := by
  fail_if_success module_eq
  exact h

example {M : Type u} [NatModule M] (a b : M) (n : Nat) :
    n • a + b = b + n • a := by module_eq

example (a b : Nat) (h : a - b + b = a) : a - b + b = a := by
  fail_if_success module_eq
  exact h

example {M : Type u} [NatModule M] (a b : M) :
    letI : HAdd M M M := ⟨fun a _ => a⟩
    a + b = b + a → a + b = b + a := by
  intro h
  fail_if_success module_eq
  exact h

example (a b : Bool) (h : a = b) : a = b := by
  fail_if_success module_eq
  exact h

example {M : Type u} [NatModule M] (f : M → M) (a b : M) :
    f (a + b) = f (b + a) := by module_nf; rfl

example {M : Type u} [IntModule M] (P : M → Prop) (a b : M) (h : P b) :
    P (a + b - a) := by module_nf; exact h

example {M : Type u} [NatModule M] [Mul M] (a b : M) (P : M → Prop)
    (h : P (2 • (a * b))) : P (a * b + a * b) := by module_nf; exact h

example {M : Type u} [IntModule M] (a b : M) : a + b + a = a + a + b := by
  module_nf
  fail_if_success module_nf
  rfl
