namespace List

@[simp] theorem filter_nil {p : α → Bool} : filter p [] = [] := by
  simp [filter, filterAux, reverse, reverseAux]

theorem cons_eq_append (a : α) (as : List α) : a :: as = [a] ++ as := rfl

theorem filter_cons (a : α) (as : List α) :
  filter p (a :: as) = if p a then a :: filter p as else filter p as :=
  sorry

@[simp] theorem filter_append {as bs : List α} {p : α → Bool} :
  filter p (as ++ bs) = filter p as ++ filter p bs :=
  match as with
  | []      => by simp
  | a :: as => by
    rw [filter_cons, cons_append, filter_cons]
    cases p a
    simp [filter_append]
    simp [filter_append]

-- the previous contains a more complicated version of
def f : Nat → Nat
  | 0 => 1
  | i+1 => (fun x => f x) i
