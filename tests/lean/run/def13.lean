variable {α} (p : α → Prop) [DecidablePred p]

def filter : List α → List α
| []    => []
| a::as => if p a then a :: filter as else filter as

theorem filter_nil : filter p [] = [] :=
rfl

theorem filter_cons (a : α) (as : List α) : filter p (a :: as) = if p a then a :: filter p as else filter p as :=
rfl

theorem filter_cons_of_pos {a : α} (as : List α) (h : p a) : filter p (a :: as) = a :: filter p as := by
rw [filter_cons];
rw [if_pos h]

theorem filter_cons_of_neg {a : α} (as : List α) (h : ¬ p a) : filter p (a :: as) = filter p as := by
rw [filter_cons];
rw [if_neg h]
