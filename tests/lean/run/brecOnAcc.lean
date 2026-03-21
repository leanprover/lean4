/-! This test ensures that `below` and `brecOn` auxiliary definitions are not made using `IndPredBelow` when the inductive predicate is a (recursive) subsingleton (i.e such as `Acc`). We verify that motive for `below` and `brecOn` eliminate to `Sort u` instead of only `Prop`, and that structural recursion works correctly on such types when eliminating to `Type`s. -/

/--
info: @[reducible] protected def Acc.below.{u_1, u} : {α : Sort u} →
  {r : α → α → Prop} → {motive : (a : α) → Acc r a → Sort u_1} → {a : α} → Acc r a → Sort (max (max 1 u) u_1) :=
fun {α} {r} {motive} {a} t => Acc.rec (fun x h h_ih => (y : α) → (a : r y x) → motive y ⋯ ×' h_ih y a) t
-/
#guard_msgs in
#print Acc.below

/--
info: Acc.brecOn.{u_1, u} {α : Sort u} {r : α → α → Prop} {motive : (a : α) → Acc r a → Sort u_1} {a✝ : α} (t : Acc r a✝)
  (F_1 : (a : α) → (t : Acc r a) → Acc.below t → motive a t) : motive a✝ t
-/
#guard_msgs in
#check Acc.brecOn

variable (P : Nat → Prop)
def R (x y : Nat) : Prop := x = y+1 /\ ¬ P y

def witness_of_Acc [h : DecidablePred P] (a : Acc (R P) n) : {n : Nat // P n} :=
  match a with
  | .intro k ak =>
    match h k with
      | isTrue h => ⟨k,h⟩
      | isFalse h =>
        witness_of_Acc (ak (k+1) ⟨rfl, h⟩)
termination_by structural a

-- Makes sure the auxiliary lemmas for `witness_of_Acc` are correctly generated

#guard_msgs(drop info) in
#check witness_of_Acc.eq_1

#guard_msgs(drop info) in
#check witness_of_Acc.eq_def

#guard_msgs(drop info) in
#check witness_of_Acc.induct

#guard_msgs(drop info) in
#check witness_of_Acc.induct_unfolding

inductive Acc' {α : Sort u} {β : Sort v} (R₁ : α → α → Prop) (R₂ : β → β → Prop) : α → β → Prop where
  | intro (a : α) (b : β) (h₁ : (y : α) → R₁ y a → Acc' R₁ R₂ y b) (h₂ : (y : β) → R₂ y b → Acc' R₁ R₂ a y) : Acc' R₁ R₂ a b

/--
info: Acc'.below.{u_1, u, v} {α : Sort u} {β : Sort v} {R₁ : α → α → Prop} {R₂ : β → β → Prop}
  {motive : (a : α) → (a_1 : β) → Acc' R₁ R₂ a a_1 → Sort u_1} {a✝ : α} {a✝¹ : β} (t : Acc' R₁ R₂ a✝ a✝¹) :
  Sort (max (max (max 1 u) v) u_1)
-/
#guard_msgs in
#check Acc'.below
/--
info: Acc'.brecOn.{u_1, u, v} {α : Sort u} {β : Sort v} {R₁ : α → α → Prop} {R₂ : β → β → Prop}
  {motive : (a : α) → (a_1 : β) → Acc' R₁ R₂ a a_1 → Sort u_1} {a✝ : α} {a✝¹ : β} (t : Acc' R₁ R₂ a✝ a✝¹)
  (F_1 : (a : α) → (a_1 : β) → (t : Acc' R₁ R₂ a a_1) → Acc'.below t → motive a a_1 t) : motive a✝ a✝¹ t
-/
#guard_msgs in
#check Acc'.brecOn
