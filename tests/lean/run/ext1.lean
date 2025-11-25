axiom mySorry {α : Sort _} : α

structure A (n : Nat) where
  a : Nat

example (a b : A n) : a = b ∨ True := by
  fail_if_success
    apply Or.inl; ext
  exact Or.inr trivial

structure B (n) extends A n where
  b : Nat
  h : b > 0
  i : Fin b

@[ext] structure C (n) extends B n where
  c : Nat

example (a b : C n) : a = b := by
  ext
  guard_target = a.a = b.a; exact mySorry
  guard_target = a.b = b.b; exact mySorry
  guard_target = a.i ≍ b.i; exact mySorry
  guard_target = a.c = b.c; exact mySorry

@[ext (flat := false)] structure C' (n) extends B n where
  c : Nat

example (a b : C' n) : a = b := by
  ext
  guard_target = a.toB = b.toB; exact mySorry
  guard_target = a.c = b.c; exact mySorry

open Lean.Elab.Tactic.Ext
example (f g : Nat × Nat → Nat) : f = g := by
  ext ⟨x, y⟩
  guard_target = f (x, y) = g (x, y); exact mySorry

-- Check that we generate a warning if there are too many patterns.
-- /-- warning: `ext` did not consume the patterns: [j] [linter.unusedRCasesPattern] -/
-- #guard_msgs in
-- example (f g : Nat → Nat) (h : f = g) : f = g := by
--  ext i j
--  exact h ▸ rfl

-- allow more specific ext theorems
@[ext high] theorem Fin.zero_ext (a b : Fin 0) : True → a = b := by cases a.isLt
example (a b : Fin 0) : a = b := by ext; exact True.intro

def Set (α : Type u) := α → Prop
@[ext] structure LocalEquiv (α : Type u) (β : Type v) where
  source : Set α
@[ext] structure Pretrivialization {F : Type u} (proj : Z → β) extends LocalEquiv Z (β × F) where
  baseSet : Set β
  source_eq : source = baseSet ∘ proj

structure MyUnit

@[ext (iff := false) high] theorem MyUnit.ext1 (x y : MyUnit) (_h : 0 = 1) : x = y := rfl
@[ext high] theorem MyUnit.ext2 (x y : MyUnit) (_h : 1 = 1) : x = y := rfl
@[ext (iff := false)] theorem MyUnit.ext3 (x y : MyUnit) (_h : 2 = 1) : x = y := rfl

example (x y : MyUnit) : x = y := by ext; rfl

-- Check that we don't generate a warning when `x` only uses a pattern in one branch:
example (f : ℕ × (ℕ → ℕ)) : f = f := by
  ext x
  · rfl
  · guard_target = (f.2) x = (f.2) x
    rfl

example (f : Empty → Empty) : f = f := by
  ext ⟨⟩

@[ext (iff := false)] theorem ext_intros {n m : Nat} (w : ∀ n m : Nat, n = m) : n = m := by apply w

example : 3 = 7 := by
  ext : 1
  rename_i n m
  guard_target = n = m
  admit

example : 3 = 7 := by
  ext n m : 1
  guard_target = n = m
  admit

section erasing_ext_attribute

def f (p : Int × Int) : Int × Int := (p.2, p.1)

example : f ∘ f = id := by
  ext ⟨a, b⟩
  · simp [f]
  · simp [f]

attribute [-ext] Prod.ext

example : f ∘ f = id := by
  ext ⟨a, b⟩
  simp [f]

end erasing_ext_attribute
