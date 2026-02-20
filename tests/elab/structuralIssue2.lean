namespace List

@[simp] theorem filter_append' {as bs : List α} {p : α → Bool} :
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
