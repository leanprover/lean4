import Lean.Meta.Sym
import Std.WP

/-!
`sym =>` tactics must see through metavariables that are assigned after the goal mentioning them
was created. Each section creates such a goal differently, and each example then runs a tactic
that reads the metavariable. `X` stands for the value of the metavariable, e.g., `(a, b).fst = 0`.
The control section runs the same scripts on goals without metavariables.
-/
set_option linter.unusedVariables false
open Lean.Order Std.Internal.Order

theorem le_of_imp (p q : Prop) (h : p → q) : p ⊑ q := h
theorem fst_mk (a b : Nat) : (a, b).fst = a := rfl

def W (p : Prop) : Prop := p
/-- The pattern is `W (∀ x : β, q x)`, and its `∀` is a pending constraint. -/
theorem w_forall {β : Sort u} (q : β → Prop) (h : ∀ x, q x) : W (∀ x, q x) := h
theorem w_forall_plift {β : Sort u} (q : β → Prop) (h : ∀ x : PLift β, q x.down) : W (∀ x, q x) :=
  fun x => h ⟨x⟩
theorem trans_le (a b c : Prop) (h₁ : a ⊑ b) (h₂ : b ⊑ c) : a ⊑ c := fun h => h₂ (h₁ h)
theorem trans_imp (a b c : Prop) (h₁ : a ⊑ b) (h₂ : b → c) : a ⊑ c := fun h => h₂ (h₁ h)
theorem trans_imp' (a b c : Prop) (h₂ : b → c) (h₁ : a ⊑ b) : a ⊑ c := fun h => h₂ (h₁ h)
theorem trans_and (a b c : Prop) (h₁ : a ⊑ b) (h₂ : b ∧ True → c) : a ⊑ c :=
  fun h => h₂ ⟨h₁ h, trivial⟩
theorem use_imp (a b : Prop) (h₁ : a → b) (h₂ : a) : b := h₁ h₂
theorem body_rule (a b c : Prop) (h₁ : b → c) (h₂ : a → b) : W (a → c) := fun x => h₁ (h₂ x)
theorem let_dom (a c : Prop) (v : Nat) (h₁ : a ⊑ (v = 0)) (h₂ : (let y := v; y = 0) → c) : a ⊑ c :=
  fun h => h₂ (h₁ h)
theorem let_dom' (a c : Prop) (v : Nat) (h₂ : (let y := v; y = 0) → c) (h₁ : a ⊑ (v = 0)) : a ⊑ c :=
  fun h => h₂ (h₁ h)
theorem app_sib (x : Nat) (c : Prop) (q : Nat → Prop) (h₁ : ∀ y, q y) (h₂ : q x → c) :
    c ∧ x = x := ⟨h₂ (h₁ x), rfl⟩
theorem app_or (x : Nat) (c : Prop) (q : Nat → Prop) (h₂ : q x ∨ c) (h₁ : q x → c) :
    c ∧ x = x := ⟨h₂.elim h₁ id, rfl⟩
theorem let_sib (a c : Prop) (v : Nat) (h₁ : a ⊑ (v = 0)) (h₂ : let y := v; y = 0 → c) : a ⊑ c :=
  fun h => h₂ (h₁ h)

class MyC (p : Prop) : Prop where
  out : p

/-!
## Control

`⊢ X → C` without metavariables.
-/

-- ctrl/intro_exact
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    intro x
    exact h x

-- ctrl/intro_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    intro x
    apply h
    apply x

-- ctrl/introL_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    intro~ x
    apply h
    apply x

-- ctrl/intros_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    intros
    finish

-- ctrl/intro_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    intro x
    finish

-- ctrl/introL_int_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    intro~ x
    internalize_all
    finish

-- ctrl/finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    finish

-- ctrl/simp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    simp [fst_mk]
    intro x
    exact h x

-- ctrl/dsimp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    dsimp [fst_mk]
    intro x
    exact h x

-- ctrl/rw
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    rw [fst_mk]
    intro x
    exact h x

-- ctrl/cbv
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    (a, b).fst = 0 → P := by
  sym =>
    cbv
    intro x
    exact h x

-- ctrl/intro_lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    a + 1 ≤ b → a < b := by
  sym =>
    intro x
    lia

-- ctrl/lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    a + 1 ≤ b → a < b := by
  sym =>
    lia

-- ctrl/by_contra
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    a + 1 ≤ b → a < b := by
  sym =>
    by_contra
    try lia

-- ctrl/intro_inst
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    MyC c → c := by
  sym =>
    intro x
    exact MyC.out

-- ctrl/intro_apply_imp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (hq : Q) :
    (Q → R) → R := by
  sym =>
    intro x
    apply x
    apply hq

-- ctrl/intro_simp_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    a = 0 → f a = f 0 := by
  sym =>
    intro x
    simp [x]

-- ctrl/intro_rw_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    a = 0 → f a = f 0 := by
  sym =>
    intro x
    rw [x]
    try exact rfl

-- ctrl/intro_finish_or
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    Q ∨ R → R ∨ Q := by
  sym =>
    intro x
    finish

-- ctrl/let_to_have
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    (let y := a; y = 0) → P := by
  sym =>
    let_to_have
    intro x
    exact h x

/-!
## Assigned by `apply` itself

`apply w_forall` creates `⊢ ∀ x : ?β, ?q x` before assigning `?β := X` and `?q := fun _ => C`.
-/

-- A/intro_exact
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    intro x
    exact h x

-- A/intro_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    intro x
    apply h
    apply x

-- A/introL_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    intro~ x
    apply h
    apply x

-- A/intros_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    intros
    finish

-- A/intro_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    intro x
    finish

-- A/introL_int_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    intro~ x
    internalize_all
    finish

-- A/finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    finish

-- A/simp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    simp [fst_mk]
    intro x
    exact h x

-- A/dsimp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    dsimp [fst_mk]
    intro x
    exact h x

-- A/rw
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    rw [fst_mk]
    intro x
    exact h x

-- A/cbv
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall
    cbv
    intro x
    exact h x

-- A/intro_lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    W (a + 1 ≤ b → a < b) := by
  sym =>
    apply w_forall
    intro x
    lia

-- A/lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    W (a + 1 ≤ b → a < b) := by
  sym =>
    apply w_forall
    lia

-- A/by_contra
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    W (a + 1 ≤ b → a < b) := by
  sym =>
    apply w_forall
    by_contra
    try lia

-- A/intro_inst
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    W (MyC c → c) := by
  sym =>
    apply w_forall
    intro x
    exact MyC.out

-- A/intro_apply_imp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (hq : Q) :
    W ((Q → R) → R) := by
  sym =>
    apply w_forall
    intro x
    apply x
    apply hq

-- A/intro_simp_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    W (a = 0 → f a = f 0) := by
  sym =>
    apply w_forall
    intro x
    simp [x]

-- A/intro_rw_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    W (a = 0 → f a = f 0) := by
  sym =>
    apply w_forall
    intro x
    rw [x]
    try exact rfl

-- A/intro_finish_or
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) :
    W (Q ∨ R → R ∨ Q) := by
  sym =>
    apply w_forall
    intro x
    finish

-- A/let_to_have
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P) :
    W ((let y := a; y = 0) → P) := by
  sym =>
    apply w_forall
    let_to_have
    intro x
    exact h x

/-!
## Copied by `apply` from the target

After `apply h₁` assigns `?b := X`, `apply le_of_imp` on `⊢ True ⊑ ?b` creates `⊢ ?b → C`.
-/

-- B/intro_exact
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro x
    exact h x

-- B/intro_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro x
    apply h
    apply x

-- B/introL_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro~ x
    apply h
    apply x

-- B/intros_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intros
    finish

-- B/intro_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro x
    finish

-- B/introL_int_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro~ x
    internalize_all
    finish

-- B/finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    finish

-- B/simp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    simp [fst_mk]
    intro x
    exact h x

-- B/dsimp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    dsimp [fst_mk]
    intro x
    exact h x

-- B/rw
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    rw [fst_mk]
    intro x
    exact h x

-- B/cbv
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    cbv
    intro x
    exact h x

-- B/intro_lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a + 1 ≤ b)) :
    (True : Prop) ⊑ (a < b) := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro x
    lia

-- B/lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a + 1 ≤ b)) :
    (True : Prop) ⊑ (a < b) := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    lia

-- B/by_contra
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a + 1 ≤ b)) :
    (True : Prop) ⊑ (a < b) := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    by_contra
    try lia

-- B/intro_inst
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (MyC c)) :
    (True : Prop) ⊑ c := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro x
    exact MyC.out

-- B/intro_apply_imp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (hq : Q) (h₁ : (True : Prop) ⊑ (Q → R)) :
    (True : Prop) ⊑ R := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro x
    apply x
    apply hq

-- B/intro_simp_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a = 0)) :
    (True : Prop) ⊑ (f a = f 0) := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro x
    simp [x]

-- B/intro_rw_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a = 0)) :
    (True : Prop) ⊑ (f a = f 0) := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro x
    rw [x]
    try exact rfl

-- B/intro_finish_or
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (Q ∨ R)) :
    (True : Prop) ⊑ (R ∨ Q) := by
  sym =>
    apply trans_le
    apply h₁
    apply le_of_imp
    intro x
    finish

/-!
## Assigned by a sibling goal (`apply`)

`apply trans_imp` creates `⊢ ?b → C`, and the sibling goal `apply h₁` assigns `?b := X`.
-/

-- C/intro_exact
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    intro x
    exact h x

-- C/intro_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    intro x
    apply h
    apply x

-- C/introL_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    intro~ x
    apply h
    apply x

-- C/intros_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    intros
    finish

-- C/intro_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    intro x
    finish

-- C/introL_int_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    intro~ x
    internalize_all
    finish

-- C/finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    finish

-- C/simp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    simp [fst_mk]
    intro x
    exact h x

-- C/dsimp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    dsimp [fst_mk]
    intro x
    exact h x

-- C/rw
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    rw [fst_mk]
    intro x
    exact h x

-- C/cbv
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    apply h₁
    cbv
    intro x
    exact h x

-- C/intro_lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a + 1 ≤ b)) :
    (True : Prop) ⊑ (a < b) := by
  sym =>
    apply trans_imp
    apply h₁
    intro x
    lia

-- C/lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a + 1 ≤ b)) :
    (True : Prop) ⊑ (a < b) := by
  sym =>
    apply trans_imp
    apply h₁
    lia

-- C/by_contra
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a + 1 ≤ b)) :
    (True : Prop) ⊑ (a < b) := by
  sym =>
    apply trans_imp
    apply h₁
    by_contra
    try lia

-- C/intro_inst
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (MyC c)) :
    (True : Prop) ⊑ c := by
  sym =>
    apply trans_imp
    apply h₁
    intro x
    exact MyC.out

-- C/intro_apply_imp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (hq : Q) (h₁ : (True : Prop) ⊑ (Q → R)) :
    (True : Prop) ⊑ R := by
  sym =>
    apply trans_imp
    apply h₁
    intro x
    apply x
    apply hq

-- C/intro_simp_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a = 0)) :
    (True : Prop) ⊑ (f a = f 0) := by
  sym =>
    apply trans_imp
    apply h₁
    intro x
    simp [x]

-- C/intro_rw_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a = 0)) :
    (True : Prop) ⊑ (f a = f 0) := by
  sym =>
    apply trans_imp
    apply h₁
    intro x
    rw [x]
    try exact rfl

-- C/intro_finish_or
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (Q ∨ R)) :
    (True : Prop) ⊑ (R ∨ Q) := by
  sym =>
    apply trans_imp
    apply h₁
    intro x
    finish

/-!
## Assigned by a sibling goal (`exact`)

`apply trans_imp` creates `⊢ ?b → C`, and the sibling goal `exact h₁` assigns `?b := X`.
-/

-- E/intro_exact
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    intro x
    exact h x

-- E/intro_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    intro x
    apply h
    apply x

-- E/introL_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    intro~ x
    apply h
    apply x

-- E/intros_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    intros
    finish

-- E/intro_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    intro x
    finish

-- E/introL_int_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    intro~ x
    internalize_all
    finish

-- E/finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    finish

-- E/simp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    simp [fst_mk]
    intro x
    exact h x

-- E/dsimp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    dsimp [fst_mk]
    intro x
    exact h x

-- E/rw
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    rw [fst_mk]
    intro x
    exact h x

-- E/cbv
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    cbv
    intro x
    exact h x

-- E/intro_lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a + 1 ≤ b)) :
    (True : Prop) ⊑ (a < b) := by
  sym =>
    apply trans_imp
    exact h₁
    intro x
    lia

-- E/lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a + 1 ≤ b)) :
    (True : Prop) ⊑ (a < b) := by
  sym =>
    apply trans_imp
    exact h₁
    lia

-- E/by_contra
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a + 1 ≤ b)) :
    (True : Prop) ⊑ (a < b) := by
  sym =>
    apply trans_imp
    exact h₁
    by_contra
    try lia

-- E/intro_inst
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (MyC c)) :
    (True : Prop) ⊑ c := by
  sym =>
    apply trans_imp
    exact h₁
    intro x
    exact MyC.out

-- E/intro_apply_imp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (hq : Q) (h₁ : (True : Prop) ⊑ (Q → R)) :
    (True : Prop) ⊑ R := by
  sym =>
    apply trans_imp
    exact h₁
    intro x
    apply x
    apply hq

-- E/intro_simp_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a = 0)) :
    (True : Prop) ⊑ (f a = f 0) := by
  sym =>
    apply trans_imp
    exact h₁
    intro x
    simp [x]

-- E/intro_rw_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a = 0)) :
    (True : Prop) ⊑ (f a = f 0) := by
  sym =>
    apply trans_imp
    exact h₁
    intro x
    rw [x]
    try exact rfl

-- E/intro_finish_or
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (Q ∨ R)) :
    (True : Prop) ⊑ (R ∨ Q) := by
  sym =>
    apply trans_imp
    exact h₁
    intro x
    finish

-- E/let_to_have
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ (let y := a; y = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp
    exact h₁
    let_to_have
    intro x
    exact h x

/-!
## The whole target

`apply use_imp` creates `⊢ ?a`, and the sibling goal `exact k` assigns `?a := X → C`.
-/

-- T/intro_exact
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro x
    exact h x

-- T/intro_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro x
    apply h
    apply x

-- T/introL_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro~ x
    apply h
    apply x

-- T/intros_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intros
    finish

-- T/intro_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro x
    finish

-- T/introL_int_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro~ x
    internalize_all
    finish

-- T/finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    finish

-- T/simp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    simp [fst_mk]
    intro x
    exact h x

-- T/dsimp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    dsimp [fst_mk]
    intro x
    exact h x

-- T/rw
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    rw [fst_mk]
    intro x
    exact h x

-- T/cbv
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (k : ((a, b).fst = 0 → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    cbv
    intro x
    exact h x

-- T/intro_lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (k : (a + 1 ≤ b → a < b) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro x
    lia

-- T/lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (k : (a + 1 ≤ b → a < b) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    lia

-- T/by_contra
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (k : (a + 1 ≤ b → a < b) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    by_contra
    try lia

-- T/intro_inst
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (k : (MyC c → c) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro x
    exact MyC.out

-- T/intro_apply_imp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (hq : Q) (k : ((Q → R) → R) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro x
    apply x
    apply hq

-- T/intro_simp_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (k : (a = 0 → f a = f 0) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro x
    simp [x]

-- T/intro_rw_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (k : (a = 0 → f a = f 0) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro x
    rw [x]
    try exact rfl

-- T/intro_finish_or
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (k : (Q ∨ R → R ∨ Q) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    intro x
    finish

-- T/let_to_have
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (k : ((let y := a; y = 0) → P) → Pk) :
    Pk := by
  sym =>
    apply use_imp
    exact k
    let_to_have
    intro x
    exact h x

/-!
## Assigned after `intro`

`intro x` adds `x : ?b` while `?b` is unassigned, and the sibling goal `apply h₁` assigns
`?b := X` afterwards.
-/

-- D/intro_exact
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp'
    intro x
    any_goals apply h₁
    exact h x

-- D/intro_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp'
    intro x
    any_goals apply h₁
    apply h
    apply x

-- D/introL_apply
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : (a, b).fst = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp'
    intro~ x
    any_goals apply h₁
    apply h
    apply x

-- D/intros_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp'
    intros
    any_goals apply h₁
    finish

-- D/intro_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp'
    intro x
    any_goals apply h₁
    finish

-- D/introL_int_finish
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h : a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_imp'
    intro~ x
    any_goals apply h₁
    internalize_all
    finish

-- D/intro_lia
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a + 1 ≤ b)) :
    (True : Prop) ⊑ (a < b) := by
  sym =>
    apply trans_imp'
    intro x
    any_goals apply h₁
    lia

-- D/intro_apply_imp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (hq : Q) (h₁ : (True : Prop) ⊑ (Q → R)) :
    (True : Prop) ⊑ R := by
  sym =>
    apply trans_imp'
    intro x
    any_goals apply h₁
    apply x
    apply hq

-- D/intro_simp_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a = 0)) :
    (True : Prop) ⊑ (f a = f 0) := by
  sym =>
    apply trans_imp'
    intro x
    any_goals apply h₁
    simp [x]

-- D/intro_rw_hyp
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (a = 0)) :
    (True : Prop) ⊑ (f a = f 0) := by
  sym =>
    apply trans_imp'
    intro x
    any_goals apply h₁
    rw [x]
    try exact rfl

-- D/intro_finish_or
example (a b : Nat) (P Q R c Pk : Prop) (f : Nat → Nat) (h₁ : (True : Prop) ⊑ (Q ∨ R)) :
    (True : Prop) ⊑ (R ∨ Q) := by
  sym =>
    apply trans_imp'
    intro x
    any_goals apply h₁
    finish

/-!
## Other positions and sources

Nested domains, bodies, `let` values and universe levels.
-/

-- misc/sebastian1
example (a b : Nat) (P : Prop) (h : (a, b).fst = 0 → P) : (True : Prop) ⊑ ((a, b).fst = 0 → P) := by
  sym =>
    apply le_forall
    intro x
    apply le_of_imp
    intro _
    apply h
    apply x

-- misc/sebastian2
example (a b : Nat) (P : Prop) (h : a = 0 → P) : (True : Prop) ⊑ ((a, b).fst = 0 → P) := by
  sym =>
    apply le_forall
    simp [fst_mk]
    intro x
    finish

-- misc/sebastian3_inst
example (c : Prop) : (True : Prop) ⊑ (MyC c → c) := by
  sym =>
    apply le_forall
    intro x
    tactic => exact fun _ => MyC.out

-- misc/lift_lets_ctrl
example (a : Nat) : True ∧ (let y := a; y = a) := by
  sym =>
    lift_lets
    intro y
    exact ⟨trivial, rfl⟩

-- misc/lift_lets_T
example (a : Nat) (Pk : Prop) (k : (True ∧ (let y := a; y = a)) → Pk) : Pk := by
  sym =>
    apply use_imp
    exact k
    lift_lets
    intro y
    exact ⟨trivial, rfl⟩

-- misc/nested_simp
example (a b : Nat) (P : Prop) (h : a = 0 → P) (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_and
    apply h₁
    simp [fst_mk]
    intro x
    finish

-- misc/nested_intro_apply
example (a b : Nat) (P : Prop) (h : (a, b).fst = 0 ∧ True → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) : (True : Prop) ⊑ P := by
  sym =>
    apply trans_and
    apply h₁
    intro x
    apply h
    apply x

-- misc/nested_intro_finish
example (a b : Nat) (P : Prop) (h : a = 0 → P) (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply trans_and
    apply h₁
    intro x
    finish

-- misc/type_domain_lia
example : W (∀ n : Nat, n + 0 = n) := by
  sym =>
    apply w_forall
    intro n
    lia

-- misc/type_domain_simp
example : W (∀ n : Nat, (n, 0).fst = n) := by
  sym =>
    apply w_forall
    simp [fst_mk]

-- misc/plift_intro
example (a b : Nat) (P : Prop) (h : (a, b).fst = 0 → P) : W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall_plift
    intro x
    apply h
    tactic => exact x.down

-- misc/plift_simp
example (a b : Nat) (P : Prop) (h : a = 0 → P) : W ((a, b).fst = 0 → P) := by
  sym =>
    apply w_forall_plift
    simp [fst_mk]
    intro x
    exact h x.down

-- misc/body_A_simp
example (a b : Nat) (h : a = 0) : W (True → (a, b).fst = 0) := by
  sym =>
    apply w_forall
    intro x
    simp [fst_mk]
    exact h

-- misc/body_A_rw
example (a b : Nat) (h : a = 0) : W (True → (a, b).fst = 0) := by
  sym =>
    apply w_forall
    intro x
    rw [fst_mk]
    exact h

-- misc/body_sibling_simp
example (a b : Nat) (Q C : Prop) (h : a = 0) (hXC : (a, b).fst = 0 → C) : W (Q → C) := by
  sym =>
    apply body_rule
    exact hXC
    intro q
    simp [fst_mk]
    exact h

-- misc/body_sibling_rw
example (a b : Nat) (Q C : Prop) (h : a = 0) (hXC : (a, b).fst = 0 → C) : W (Q → C) := by
  sym =>
    apply body_rule
    exact hXC
    intro q
    rw [fst_mk]
    exact h

-- misc/body_sibling_dsimp
example (a b : Nat) (Q C : Prop) (h : a = 0) (hXC : (a, b).fst = 0 → C) : W (Q → C) := by
  sym =>
    apply body_rule
    exact hXC
    intro q
    dsimp [fst_mk]
    exact h

-- misc/body_sibling_cbv
example (a b : Nat) (Q C : Prop) (h : a = 0) (hXC : (a, b).fst = 0 → C) : W (Q → C) := by
  sym =>
    apply body_rule
    exact hXC
    intro q
    cbv
    exact h

-- misc/body_sibling_apply
example (a b : Nat) (Q C : Prop) (h : (a, b).fst = 0) (hXC : (a, b).fst = 0 → C) : W (Q → C) := by
  sym =>
    apply body_rule
    exact hXC
    intro q
    apply h

-- misc/let_value_simp
example (a b : Nat) (P : Prop) (h : a = 0 → P) (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply let_sib
    apply h₁
    simp [fst_mk]
    intro x
    finish

-- misc/let_value_intro_apply
example (a b : Nat) (P : Prop) (h : (a, b).fst = 0 → P) (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply let_sib
    apply h₁
    intro y x
    apply h
    apply x

-- misc/let_domain_value_apply: `x : let y := ?v; y = 0`, and zeta-reducing its type exposes `?v`
example (a b : Nat) (P : Prop) (h : (a, b).fst = 0 → P) (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply let_dom
    apply h₁
    intro x
    apply h
    apply x

-- misc/let_domain_value_late_apply: same, but `?v` is assigned after `intro x`
example (a b : Nat) (P : Prop) (h : (a, b).fst = 0 → P) (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ P := by
  sym =>
    apply let_dom'
    intro x
    any_goals apply h₁
    apply h
    apply x

-- misc/simp_stale_cache: `simp` first runs while `?b` is unassigned
example (a b : Nat) (P : Prop) (h : a = 0 → a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ ((a, b).fst = 0 → P) := by
  sym =>
    apply trans_imp'
    simp [fst_mk]
    any_goals apply h₁
    simp [fst_mk]
    exact h

-- misc/simp_app_head: `?q a` with `?q := fun y => (y, b).fst = 0`
example (a b : Nat) (P : Prop) (hq : ∀ y, (y, b).fst = 0) (h : a = 0 → P) : P ∧ a = a := by
  sym =>
    apply app_sib
    exact hq
    simp [fst_mk]
    exact h

-- misc/simp_delayed_head: the first `simp` turns `?q a` into `?aux a`, where `?aux` is delayed
-- assigned by `intro y`, and the second `simp` runs after its pending goal is solved
example (a b : Nat) (P : Prop) (ha : a = 0) (h : (a, b).fst = 0 → P) : P ∧ a = a := by
  sym =>
    apply app_or
    any_goals intro y
    simp [fst_mk]
    any_goals apply ((y, b).fst = 0)
    simp [fst_mk]
    exact Or.inl ha
    exact h y

-- misc/dsimp_stale_cache: `dsimp` first runs while `?b` is unassigned
example (a b : Nat) (P : Prop) (h : a = 0 → a = 0 → P)
    (h₁ : (True : Prop) ⊑ ((a, b).fst = 0)) :
    (True : Prop) ⊑ ((a, b).fst = 0 → P) := by
  sym =>
    apply trans_imp'
    dsimp [fst_mk]
    any_goals apply h₁
    dsimp [fst_mk]
    exact h

-- misc/dsimp_app_head: `?q a` with `?q := fun y => (y, b).fst = 0`
example (a b : Nat) (P : Prop) (hq : ∀ y, (y, b).fst = 0) (h : a = 0 → P) : P ∧ a = a := by
  sym =>
    apply app_sib
    exact hq
    dsimp [fst_mk]
    exact h

-- misc/dsimp_delayed_head: the first `dsimp` turns `?q a` into `?aux a`, where `?aux` is delayed
-- assigned by `intro y`, and the second `dsimp` runs after its pending goal is solved
example (a b : Nat) (P : Prop) (ha : a = 0) (h : (a, b).fst = 0 → P) : P ∧ a = a := by
  sym =>
    apply app_or
    any_goals intro y
    dsimp [fst_mk]
    any_goals apply ((y, b).fst = 0)
    dsimp [fst_mk]
    exact Or.inl ha
    exact h y

-- misc/intro_body_binder: `intro q x` on `Q → ?b` with `?b := X → X`
example (a b : Nat) (Q C : Prop) (hXC : ((a, b).fst = 0 → (a, b).fst = 0) → C) : W (Q → C) := by
  sym =>
    apply body_rule
    exact hXC
    intro q x
    exact x

-- misc/intros_body_binder: same with `intros`
example (a b : Nat) (Q C : Prop) (hXC : ((a, b).fst = 0 → (a, b).fst = 0) → C) : W (Q → C) := by
  sym =>
    apply body_rule
    exact hXC
    intros
    rename_i x
    exact x
