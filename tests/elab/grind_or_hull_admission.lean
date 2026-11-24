module

public meta import Lean
public meta import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

/-!
Test Nat casts introduced by the arithmetic hull. Unproductive nested disjunctions should
leave their unused atoms alone, and flat alternatives should retain casts used by E-matching.
-/

namespace OrHullAdmission

opaque unused : Nat
opaque other : Nat

open Lean Meta Elab Tactic Grind

syntax (name := checkDeadAtom) "check_dead_atom" : grind

@[grind_tactic checkDeadAtom] public meta def evalCheckDeadAtom : GrindTactic := fun _ => withMainContext do
  liftGoalM do
    let a ← shareCommon (mkConst ``unused)
    let s ← Arith.Cutsat.get'
    if s.natToIntMap.contains { expr := a } then
      throwError "the hull converted the unused atom to Int"

example (s t u p q : Prop) (x : Int)
    (_h : ((u ∨ unused = other) ∧ x ≤ 2 ∧ s) ∨ (x ≤ 3 ∧ t))
    (h₁ : p ∨ q) (h₂ : ¬p ∨ q) (h₃ : p ∨ ¬q) (h₄ : ¬p ∨ ¬q) : False := by
  grind only => check_dead_atom; finish

-- The inner bounds have different directions, so their disjunction supplies no bound.
example (s t p q : Prop) (x y : Int)
    (_h : ((x ≤ 1 ∨ y ≤ 1) ∧ s) ∨ (unused = other ∧ t))
    (h₁ : p ∨ q) (h₂ : ¬p ∨ q) (h₃ : p ∨ ¬q) (h₄ : ¬p ∨ ¬q) : False := by
  grind only => check_dead_atom; finish

example (s t p q : Prop) (x y : Int)
    (_h : (unused = other ∧ t) ∨ ((x ≤ 1 ∨ y ≤ 1) ∧ s))
    (h₁ : p ∨ q) (h₂ : ¬p ∨ q) (h₃ : p ∨ ¬q) (h₄ : ¬p ∨ ¬q) : False := by
  grind only => check_dead_atom; finish

-- The outer bound on z survives, but its left alternative contains a disjunction with no bound.
example (s t p q : Prop) (x y z : Int)
    (_h : (((unused = other ∧ t) ∨ ((x ≤ 3 ∨ y ≤ 4) ∧ s)) ∧ z ≤ 1) ∨ z ≤ 2)
    (h₁ : p ∨ q) (h₂ : ¬p ∨ q) (h₃ : p ∨ ¬q) (h₄ : ¬p ∨ ¬q) : False := by
  grind only => check_dead_atom; finish

-- An arbitrary order on Nat does not make its sibling equality relevant to the outer bound.
example (s t p q : Prop) (x : Int) (ord : LE Nat) (a b : Nat)
    (_h : ((@LE.le Nat ord a b ∨ unused = other) ∧ x ≤ 2 ∧ s) ∨ (x ≤ 3 ∧ t))
    (h₁ : p ∨ q) (h₂ : ¬p ∨ q) (h₃ : p ∨ ¬q) (h₄ : ¬p ∨ ¬q) : False := by
  grind only => check_dead_atom; finish

opaque Ready : Int → Prop
opaque P : Prop
axiom fire (k : Nat) : Ready (k : Int)
grind_pattern fire => (k : Int)

-- A cast introduced by either flat alternative supplies the matching term for fire.
example (a b c d : Nat) (_h : a = b ∨ c = d) (finish : ∀ z, Ready z → P) : P := by
  grind (branches := 0)

end OrHullAdmission
