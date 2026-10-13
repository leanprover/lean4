import Lean
/-!
Tests the `discharger` field of `register_sym_simp`: the discharger used for the side
conditions of the extra theorems provided at use time (`simp myVariant [thm₁, thm₂, ...]`).
-/

opaque f : Nat → Nat
opaque g : Nat → Nat
axiom f_idem (a : Nat) (_h : 0 < a) : f (f a) = f a

register_sym_simp withGrind where
  post := ground
  discharger := grind

register_sym_simp withSelf where
  post := ground
  discharger := self

register_sym_simp withoutDischarger where
  post := ground

-- Ground side condition `0 < 3`.
example : f (f 3) = f 3 := by
  sym =>
    simp withGrind [f_idem]

example : f (f 3) = f 3 := by
  sym =>
    simp withSelf [f_idem]

-- Without a discharger, the conditional theorem never fires.
/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example : f (f 3) = f 3 := by
  sym =>
    simp withoutDischarger [f_idem]

-- The side condition `0 < n` follows from `h : 5 ≤ n` by linear arithmetic.
example (n : Nat) (h : 5 ≤ n) : f (f n) = f n := by
  sym =>
    simp withGrind [f_idem]

-- `self` simplifies the side condition with the variant itself, which cannot use `h`.
/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example (n : Nat) (h : 5 ≤ n) : f (f n) = f n := by
  sym =>
    simp withSelf [f_idem]

-- The side condition `0 < g n` requires instantiating the quantified hypothesis `h`.
example (n : Nat) (h : ∀ x, 0 < g x) : f (f (g n)) = f (g n) := by
  sym =>
    simp withGrind [f_idem]

-- Hypotheses introduced inside the `sym =>` block are available too.
example (n : Nat) : 5 ≤ n → f (f n) = f n := by
  sym =>
    intro h
    simp withGrind [f_idem]

-- The side condition `0 < n` cannot be discharged, so `f_idem` must not be applied.
-- `Nat.add_zero` still fires, so `Sym.simp` makes progress and leaves the goal below.
/--
error: `sym` failed
case grind
n : Nat
⊢ f (f n) = f n
[grind] Goal diagnostics
  [facts] Asserted facts
-/
#guard_msgs in
example (n : Nat) : f (f n) + 0 = f n + 0 := by
  sym =>
    simp withGrind [f_idem, Nat.add_zero]
