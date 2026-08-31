import Lean
set_option linter.unusedVariables false
set_option warn.sorry false
/-! Tests for `mkTheoremFromDecl` adaptation of non-equality theorems -/

opaque p : Nat → Prop
opaque q : Nat → Prop

-- Equality theorem (no adaptation needed)
theorem eq_thm : p x = q x := sorry

-- Negation theorem: `¬ p x` adapted to `p x = False`
theorem neg_thm : ¬ p x := sorry

-- Iff theorem: `p x ↔ q x` adapted to `p x = q x`
theorem iff_thm : p x ↔ q x := sorry

-- Proposition theorem: `p x` adapted to `p x = True`
theorem prop_thm : p x := sorry

-- Quantified negation: `∀ x, ¬ p x` adapted to `∀ x, p x = False`
theorem quant_neg : ∀ x, ¬ p x := sorry

-- Quantified prop: `∀ x, p x` adapted to `∀ x, p x = True`
theorem quant_prop : ∀ x, p x := sorry

-- Test: `simp` with a proposition theorem (`h : p x`) rewrites `p x` to `True`
register_sym_simp propSimp where
  post := ground >> rewrite [prop_thm]

example : p x = True := by
  sym => simp propSimp

-- Test: `simp` with a negation theorem (`h : ¬ p x`) rewrites `p x` to `False`
register_sym_simp negSimp where
  post := ground >> rewrite [neg_thm]

example : p x = False := by
  sym => simp negSimp

-- Test: `simp` with an iff theorem (`h : p x ↔ q x`) rewrites `p x` to `q x`
register_sym_simp iffSimp where
  post := ground >> rewrite [iff_thm]

example : p x = q x := by
  sym => simp iffSimp

-- Test: quantified prop still works
register_sym_simp quantPropSimp where
  post := ground >> rewrite [quant_prop]

example (y : Nat) : p y = True := by
  sym => simp quantPropSimp

-- Test: quantified negation still works
register_sym_simp quantNegSimp where
  post := ground >> rewrite [quant_neg]

example (y : Nat) : p y = False := by
  sym => simp quantNegSimp

register_sym_simp simple where
  post := ground

example (x : Nat) : p x := by
  sym => simp simple [quant_prop]

example (x : Nat) : ¬ p x := by
  sym => simp simple [quant_neg]

example (x : Nat) : p x = q x := by
  sym => simp simple [iff_thm]

-- Tests for local hypothesis support in `simp [h]`

-- Local hypothesis `h : p x` rewrites `p x` to `True`
example (x : Nat) (h : p x) : p x = True := by
  sym => simp simple [h]

-- Local hypothesis `h : ¬ p x` rewrites `p x` to `False`
example (x : Nat) (h : ¬ p x) : p x = False := by
  sym => simp simple [h]

-- Local hypothesis `h : p x ↔ q x` rewrites `p x` to `q x`
example (x : Nat) (h : p x ↔ q x) : p x = q x := by
  sym => simp simple [h]

-- Local hypothesis `h : p x = q x` (already an equality)
example (x : Nat) (h : p x = q x) : p x = q x := by
  sym => simp simple [h]

-- Local hypothesis with intro
example (x : Nat) : p x → p x = True := by
  sym =>
    intro h
    simp simple [h]

example (h : ∀ x, p x = q x) : p a = q a ∧ p b = q b := by
  sym => simp simple [h, and_true]
