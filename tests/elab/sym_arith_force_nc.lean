import Lean

/-!
Tests for explicitly noncommutative arithmetic normalization on commutative
carriers, including classification caches shared between the two modes.
-/

open Lean Meta Elab Tactic Sym

private def normalizeGoal (commutative : Bool) (g : MVarId) : MetaM MVarId := g.withContext do
  let e ← instantiateMVars (← g.getType)
  let r ← SymM.run do
    let e ← shareCommon (← Sym.canon e)
    Arith.normalize? e (fun _ => pure .rfl) (commutative := commutative)
  match r with
  | .rfl .. => return g
  | .step e h .. => g.replaceTargetEq e h

elab "noncomm_norm" : tactic => do
  replaceMainGoal [← normalizeGoal false (← getMainGoal)]

elab "comm_norm" : tactic => do
  replaceMainGoal [← normalizeGoal true (← getMainGoal)]

section
open Lean.Grind

example {R : Type u} [CommRing R] (a b : R) : a * b = b * a := by
  fail_if_success (noncomm_norm; rfl)
  comm_norm
  rfl

example {R : Type u} [CommRing R] (a b c : R) :
    (a + b) * c = a * c + b * c := by noncomm_norm; rfl

example {R : Type u} [CommRing R] (a b : R) :
    (a + b)^2 = a^2 + a * b + b * a + b^2 := by noncomm_norm; rfl

example {R : Type u} [CommRing R] (a b c : R) (h : b * a = c) :
    a * b + b * a = a * b + c := by
  noncomm_norm
  exact h

example {R : Type u} [CommSemiring R] (a b : R) : a * b = b * a := by
  fail_if_success (noncomm_norm; rfl)
  comm_norm
  rfl

example {R : Type u} [CommSemiring R] (a b c : R) :
    (a + b) * c = a * c + b * c := by noncomm_norm; rfl

example {R : Type u} [Ring R] (a b : R) :
    (a - b)^2 = a^2 - a * b - b * a + b^2 := by noncomm_norm; rfl

example {R : Type u} [CommRing R] [IsCharP R 4] (a b : R) :
    (a - b)^2 = a^2 - a * b - b * 5 * a + b^2 := by noncomm_norm; rfl

end

-- Integer gcd certificates must not compare noncommutative monomials with a commutative polynomial.
example (a b : Int) (h : False) : 2 * a * b + 2 * b * a ≤ 3 := by
  noncomm_norm
  exact h.elim

example (a b : Int) (h : False) : 2 * a * b + 2 * b * a = 3 := by
  noncomm_norm
  exact h.elim

run_meta SymM.run do
  let type ← Sym.canon (mkConst ``Int)
  let .commRing _ ← Arith.classify? type | throwError "expected a commutative ring"
  let .nonCommRing id ← Arith.classify? type (commutative := false)
    | throwError "expected a noncommutative ring view"
  let .commRing _ ← Arith.classify? type | throwError "default classification was changed"
  let .nonCommRing id' ← Arith.classify? type (commutative := false)
    | throwError "expected a cached noncommutative view"
  unless id == id' do throwError "noncommutative classification was not cached"

run_meta SymM.run do
  let type ← Sym.canon (mkConst ``Nat)
  let .nonCommSemiring id ← Arith.classify? type (commutative := false)
    | throwError "expected a noncommutative semiring view"
  let .commSemiring _ ← Arith.classify? type | throwError "default classification was changed"
  let .nonCommSemiring id' ← Arith.classify? type (commutative := false)
    | throwError "expected a cached noncommutative view"
  unless id == id' do throwError "noncommutative classification was not cached"
