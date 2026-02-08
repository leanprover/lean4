axiom thm.{u_1, u_2} {α : Type u_1} {β : Type u_2} (f : α → β)
  (motive : List α → List β → Prop) (case1 : motive [] [])
  (case2 : ∀ (a : α) (as : List α), motive (a :: as) (f a :: List.map f as)) (l : List α) : motive l (List.map f l)

theorem map_isNil (f : α → β) (l : List α) :
  List.map f l = [] ↔ l = [] := by
  cases l using thm f <;> simp
