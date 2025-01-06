example : False := by
  have h : if True then True else True := trivial
  split h

example : False := by
  have t : True := trivial
  have dep : if 1 ≥ 0 then True else False := by simp
  have use_dep : dep = dep := rfl
  set_option trace.split.failure true in
  split at *

-- example (n : Nat) : n.casesOn True (fun _ => True) = True := by
example (n : Nat) (h : (match h : (decide $ n = n) with | true => of_decide_eq_true h | false => Eq.refl n) = .refl n) : True := by
-- example (n : Nat) (h : (if n = n then true else false)) : True := by
  let x := if true then 3 else 4
  set_option trace.split.failure true in
  split at x
