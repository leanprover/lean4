def filter (p : α → Prop) [DecidablePred p] (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' => if p x then x :: filter p xs' else filter p xs'

attribute [simp] filter

set_option pp.explicit true

/--
info: filter.eq_2.{u_1} {α : Type u_1} (p : α → Prop) [@DecidablePred α p] (x : α) (xs' : List α) :
  @Eq (List α) (@filter α p inst✝ (@List.cons α x xs'))
    (@ite (List α) (p x) (inst✝ x) (@List.cons α x (@filter α p inst✝ xs')) (@filter α p inst✝ xs'))
-/
#guard_msgs in
#check filter.eq_2 -- We should not have terms of the form `@filter α p (fun x => inst✝ x) xs'`


def filter_length (p : α → Prop) [DecidablePred p] : (filter p xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    simp only [filter]
    split <;> simp only [List.length] <;> omega
