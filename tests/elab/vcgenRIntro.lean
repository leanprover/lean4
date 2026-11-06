import Std.WP
import Std.Data.HashSet

/-!
`vcgen` destructures a binder with the rules registered by `@[vcgen_rintro]`. The rules
`forall_mem_cons_intro` and `forall_mem_nil_intro` split a binder
`∀ x, x ∈ l → G x` over a literal list `l` into one goal `G a` per element `a` of `l`.
-/

open Std.WP Lean.Order
set_option experimental.vcgen true

abbrev M := StateM Nat

theorem forall_mem_cons_intro {α : Type _} {G : α → Prop} {a : α} {l : List α}
    (ha : G a) (hl : ∀ x, x ∈ l → G x) : ∀ x, x ∈ a :: l → G x :=
  List.forall_mem_cons.mpr ⟨ha, hl⟩

theorem forall_mem_nil_intro {α : Type _} {G : α → Prop} : ∀ x, x ∈ ([] : List α) → G x :=
  fun _ h => nomatch h

/-! Without a registered rule, `vcgen` introduces the membership hypothesis. -/

/--
trace: case vc1
G : Nat → Prop
n✝ : Nat
a✝ : n✝ ∈ [1, 2, 3]
s✝ : Nat
⊢ G n✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Prop) :
    ∀ n, n ∈ [1, 2, 3] → ⦃ fun _ => True ⦄ (pure n : M Nat) ⦃ fun r _ => G r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

attribute [vcgen_rintro] forall_mem_cons_intro forall_mem_nil_intro

/-! The rules split the binder `∀ n, n ∈ [1, 2, 3] → …` into one goal per element. -/

/--
trace: case vc1
G : Nat → Prop
s✝ : Nat
⊢ G 1

case vc2
G : Nat → Prop
s✝ : Nat
⊢ G 2

case vc3
G : Nat → Prop
s✝ : Nat
⊢ G 3
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Prop) :
    ∀ n, n ∈ [1, 2, 3] → ⦃ fun _ => True ⦄ (pure n : M Nat) ⦃ fun r _ => G r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! The binders before the destructured variable are introduced. -/

/--
trace: case vc1
G : Nat → Prop
k✝ s✝ : Nat
⊢ G k✝

case vc2
G : Nat → Prop
k✝ s✝ : Nat
⊢ G (k✝ + 1)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Prop) :
    ∀ k n, n ∈ [k, k + 1] → ⦃ fun _ => True ⦄ (pure n : M Nat) ⦃ fun r _ => G r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! The binder over the empty list leaves no goal. -/

example (G : Nat → Prop) :
    ∀ n, n ∈ ([] : List Nat) → ⦃ fun _ => True ⦄ (pure n : M Nat) ⦃ fun r _ => G r ⦄ := by
  vcgen

/-! A binder `x` whose premise mentions `x` falls back to plain introduction, since `G x` cannot
abstract the premise. -/

/--
trace: case vc1
G : (x : Nat) → x ∈ [1, 2] → Prop
x✝ : Nat
h✝ : x✝ ∈ [1, 2]
s✝ : Nat
⊢ G x✝ h✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : (x : Nat) → x ∈ [1, 2] → Prop) :
    ∀ x (h : x ∈ [1, 2]), ⦃ fun _ => True ⦄ (pure x : M Nat) ⦃ fun _ _ => G x h ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! Membership in a `Std.HashSet` matches no rule and falls back to plain introduction. -/

/--
trace: case vc1
G : Nat → Prop
s : Std.HashSet Nat
x✝ : Nat
a✝ : x✝ ∈ s
s✝ : Nat
⊢ G x✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Prop) (s : Std.HashSet Nat) :
    ∀ x, x ∈ s → ⦃ fun _ => True ⦄ (pure x : M Nat) ⦃ fun r _ => G r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! A list variable `l` falls back to plain introduction, after the rules split off the literal
elements in front of `l`. -/

/--
trace: case vc1
G : Nat → Prop
l : List Nat
x✝ : Nat
a✝ : x✝ ∈ l
s✝ : Nat
⊢ G x✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Prop) (l : List Nat) :
    ∀ x, x ∈ l → ⦃ fun _ => True ⦄ (pure x : M Nat) ⦃ fun r _ => G r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/--
trace: case vc1
G : Nat → Prop
a : Nat
l : List Nat
s✝ : Nat
⊢ G a

case vc2
G : Nat → Prop
a : Nat
l : List Nat
x✝ : Nat
a✝ : x✝ ∈ l
s✝ : Nat
⊢ G x✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Prop) (a : Nat) (l : List Nat) :
    ∀ x, x ∈ a :: l → ⦃ fun _ => True ⦄ (pure x : M Nat) ⦃ fun r _ => G r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! Nested binders split into one goal per pair of elements. -/

/--
trace: case vc1
G : Nat → Nat → Prop
s✝ : Nat
⊢ G 1 3

case vc2
G : Nat → Nat → Prop
s✝ : Nat
⊢ G 1 4

case vc3
G : Nat → Nat → Prop
s✝ : Nat
⊢ G 2 3

case vc4
G : Nat → Nat → Prop
s✝ : Nat
⊢ G 2 4
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Nat → Prop) :
    ∀ x, x ∈ [1, 2] → ∀ y, y ∈ [3, 4] →
      ⦃ fun _ => True ⦄ (pure x : M Nat) ⦃ fun r _ => G r y ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! The binders and premises before the destructured variable are introduced. -/

/--
trace: case vc1
G : Nat → Nat → Prop
s✝¹ s✝ : Nat
⊢ G s✝¹ 1

case vc2
G : Nat → Nat → Prop
s✝¹ s✝ : Nat
⊢ G s✝¹ 2
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Nat → Prop) :
    ∀ s, ∀ x, x ∈ [1, 2] → ⦃ fun _ => True ⦄ (pure x : M Nat) ⦃ fun r _ => G s r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/--
trace: case vc1
P : Nat → Prop
G : Nat → Nat → Prop
s✝¹ : Nat
a✝ : P s✝¹
s✝ : Nat
⊢ G s✝¹ 1

case vc2
P : Nat → Prop
G : Nat → Nat → Prop
s✝¹ : Nat
a✝ : P s✝¹
s✝ : Nat
⊢ G s✝¹ 2
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P : Nat → Prop) (G : Nat → Nat → Prop) :
    ∀ s, P s → ∀ x, x ∈ [1, 2] → ⦃ fun _ => True ⦄ (pure x : M Nat) ⦃ fun r _ => G s r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! Rules for the two binders `x y` of a membership in a list of pairs. -/

theorem forall_pair_mem_cons_intro {α β : Type _} {G : α → β → Prop} {a : α} {b : β}
    {l : List (α × β)} (hab : G a b) (hl : ∀ x y, (x, y) ∈ l → G x y) :
    ∀ x y, (x, y) ∈ (a, b) :: l → G x y := by
  intro x y h
  cases h with
  | head => exact hab
  | tail _ h => exact hl x y h

theorem forall_pair_mem_nil_intro {α β : Type _} {G : α → β → Prop} :
    ∀ x y, (x, y) ∈ ([] : List (α × β)) → G x y :=
  fun _ _ h => nomatch h

attribute [vcgen_rintro] forall_pair_mem_cons_intro forall_pair_mem_nil_intro

/-! The rule `forall_pair_mem_cons_intro` destructures the binders `x y` of a membership in a list of
pairs, next to the rules for one binder. -/

/--
trace: case vc1
G : Nat → Nat → Prop
s✝ : Nat
⊢ G 1 2

case vc2
G : Nat → Nat → Prop
s✝ : Nat
⊢ G 3 4
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Nat → Prop) :
    ∀ x y, (x, y) ∈ [(1, 2), (3, 4)] →
      ⦃ fun _ => True ⦄ (pure x : M Nat) ⦃ fun r _ => G r y ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! The binders `y x` in the order opposite to `(x, y)` fall back to plain introduction. -/

/--
trace: case vc1
G : Nat → Nat → Prop
y✝ x✝ : Nat
a✝ : (x✝, y✝) ∈ [(1, 2)]
s✝ : Nat
⊢ G x✝ y✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Nat → Prop) :
    ∀ y x, (x, y) ∈ [(1, 2)] → ⦃ fun _ => True ⦄ (pure x : M Nat) ⦃ fun r _ => G r y ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! Rules keyed by `LT.lt` split the bound `n < 3` into one goal per smaller number. -/

theorem forall_lt_succ_intro {G : Nat → Prop} {k : Nat} (hk : G k) (hl : ∀ n, n < k → G n) :
    ∀ n, n < k + 1 → G n := fun n h => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
  · exact hl n h
  · exact hk

theorem forall_lt_zero_intro {G : Nat → Prop} : ∀ n, n < 0 → G n :=
  fun _ h => absurd h (Nat.not_lt_zero _)

attribute [vcgen_rintro] forall_lt_succ_intro forall_lt_zero_intro

/--
trace: case vc1
G : Nat → Prop
s✝ : Nat
⊢ G 2

case vc2
G : Nat → Prop
s✝ : Nat
⊢ G 1

case vc3
G : Nat → Prop
s✝ : Nat
⊢ G 0
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Prop) :
    ∀ n, n < 3 → ⦃ fun _ => True ⦄ (pure n : M Nat) ⦃ fun r _ => G r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! The built-in rule `Prod.forall_intro` destructures a binder over a pair. The registered rules
`PUnit.forall_intro` and `True.forall_intro` destructure a binder over `Unit` or `True`. -/

/--
trace: case vc1
G : Nat → Nat → Prop
a✝ b✝ s✝ : Nat
⊢ G a✝ b✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Nat → Prop) :
    ∀ p : Nat × Nat, ⦃ fun _ => True ⦄ (pure p : M (Nat × Nat)) ⦃ fun r _ => G r.1 r.2 ⦄ := by
  vcgen
  trace_state
  all_goals sorry

@[vcgen_rintro] theorem PUnit.forall_intro {G : PUnit → Prop} (h : G ⟨⟩) : ∀ u, G u :=
  fun ⟨⟩ => h

@[vcgen_rintro] theorem True.forall_intro {G : True → Prop} (h : G trivial) : ∀ h, G h :=
  fun ⟨⟩ => h

/--
trace: case vc1
G : PUnit → Prop
s✝ : Nat
⊢ G PUnit.unit
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Unit → Prop) :
    ∀ u : Unit, ⦃ fun _ => True ⦄ (pure u : M Unit) ⦃ fun r _ => G r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/--
trace: case vc1
G : True → Prop
s✝ : Nat
⊢ G trivial
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : True → Prop) :
    ∀ h : True, ⦃ fun _ => True ⦄ (pure () : M Unit) ⦃ fun _ _ => G h ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! A rule needs a conclusion that is a `∀`. -/

theorem not_forall {G : Nat → Prop} (h : G 0) : G 0 := h

/--
error: `@[vcgen_rintro]`: the conclusion of `not_forall` is not a `∀`
-/
#guard_msgs in
attribute [vcgen_rintro] not_forall
