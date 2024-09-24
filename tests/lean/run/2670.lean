example {α β : Type} {f : α × β → β → β} (h : ∀ p : α × β, f p p.2 = p.2)
  (a : α) (b : β) : f (a, b) b = b := by
  simp [h] -- should not fail

example {α β : Type} {f : α × β → β → β}
  (a : α) (b : β) (h : f (a,b) (a,b).2 = (a,b).2) : f (a, b) b = b := by
  simp [h] -- should not fail

def enumFromTR' (n : Nat) (l : List α) : List (Nat × α) :=
  let arr := l.toArray
  (arr.foldr (fun a (n, acc) => (n-1, (n-1, a) :: acc)) (n + arr.size, [])).2

open List in
theorem enumFrom_eq_enumFromTR' : @enumFrom = @enumFromTR' := by
  funext α n l; simp only [enumFromTR']
  let f := fun (a : α) (n, acc) => (n-1, (n-1, a) :: acc)
  let rec go : ∀ l n, l.foldr f (n + l.length, []) = (n, enumFrom n l)
    | [], n => rfl
    | a::as, n => by
      rw [← show _ + as.length = n + (a::as).length from Nat.succ_add .., List.foldr, go as]
      simp [enumFrom, f]
  rw [Array.foldr_eq_foldr_toList]
  simp [go] -- Should close the goal
