import Lean

/-!
Tests for the `[grind hom]`/`[grind hom_pred]` engine: homomorphism rules are applied
during internalization (to fixpoint, outside the E-graph), and predicates are
instantiated for terms in homomorphism normal form.
-/

/-! A custom domain with opaque operations: the goals below are only provable through
the homomorphism into `Int`. -/

axiom W : Type
axiom wadd : W → W → W
axiom wu : W → Int

axiom wu_add (x y : W) : wu (wadd x y) = wu x + wu y
axiom wu_eq (x y : W) : (x = y) ↔ (wu x = wu y)
axiom wu_pos (x : W) : 0 ≤ wu x

attribute [grind hom] wu_add wu_eq
attribute [grind hom_pred] wu_pos

example (x y z : W) : wadd (wadd x y) z = wadd x (wadd y z) := by grind
example (x y : W) : wadd x y = wadd y x := by grind

/-- The predicate `wu_pos` provides the bounds. -/
example (x y : W) (h : wu (wadd x y) ≤ 0) : wu x ≤ 0 := by grind

/-- The engine is disabled by `-hom`. -/
example (x y : W) : wadd x y = wadd y x := by
  fail_if_success grind -hom
  grind

/-! Goals over stdlib types closed through the `Init.Grind.Homo` rules. -/

example (a b : UInt8) : a + b = b + a := by grind
example (n : Nat) (a b : Fin n) : a + b = b + a := by grind
example (a b : UInt8) (h : a ≤ b) : a.toNat ≤ b.toNat := by grind
example (x y : BitVec 8) : (x + y).toNat < 256 := by grind
example (a b : Int64) (h : a < b) : a.toInt < b.toInt := by grind

/-! Equalities asserted as hypotheses have no `Eq` term in the E-graph; they are
translated by the `newEq` hook (one fact per union). -/

example (x y z : W) (h : x = wadd y z) (h' : wu x ≤ 0) : wu y ≤ 0 := by grind

/-! Injectivity: `grind` works by contradiction, so the goal `x = y` becomes a
disequality, the `newDiseq` hook asserts the translated disequality, and the target
solver closes. This is the backward direction of the `=`-injection. -/

example (x y : W) (h : wu x = 0) (h' : wu y = 0) : x = y := by grind

/-- The `grind_fin_zero` shape: an asserted `Fin` equality with no `val` occurrences.
The source types are derived from the rule set, so the stdlib rules work without a
stage0 update. -/
example {n a : Nat} [NeZero n] {ha : a < n} (h₁ : a ≠ 0) (h₂ : (⟨a, ha⟩ : Fin n) = 0) : False := by
  grind
