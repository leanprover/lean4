--

/-- info: And.intro {a b : Prop} (left : a) (right : b) : a ∧ b -/
#guard_msgs in
#check And.intro

/--
info: @Or.rec : ∀ {a b : Prop} {motive : a ∨ b → Prop},
  (∀ (h : a), motive ⋯) → (∀ (h : b), motive ⋯) → ∀ (t : a ∨ b), motive t
-/
#guard_msgs in
#check @Or.rec

/-- info: Eq.{u_1} {α : Sort u_1} : α → α → Prop -/
#guard_msgs in
#check Eq

/--
info: @Eq.rec : {α : Sort u_2} →
  {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u_1} → motive a ⋯ → {a_1 : α} → (t : a = a_1) → motive a_1 t
-/
#guard_msgs in
#check @Eq.rec
