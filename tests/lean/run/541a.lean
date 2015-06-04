import data.list data.nat
open nat list eq.ops

section

variable {Q : Type}

definition f : list Q → ℕ  -- default if l is empty, else max l
  | []        := 0
  | (h :: t)  := f t + 1

theorem f_foo : ∀{l : list Q}, ∀{q : Q}, q ∈ l → f l ≥ 1
  | []                := take q, assume Hq, absurd Hq !not_mem_nil
  | [h]               := take q, assume Hq, nat.le_of_eq !rfl
  | (h :: (h' :: t))  := take q, assume Hq,
    have Hor : q = h ∨ q ∈ (h' :: t),   from iff.mp !mem_cons_iff Hq,
    have H   : f (h' :: t) ≥ 1,         from f_foo (mem_cons h' t),
    have H1  : 1 + 1 ≤ f (h' :: t) + 1, from nat.add_le_add_right H 1,
    calc
      f (h :: h' :: t) = f (h' :: t) + 1 : rfl
                   ... ≥ 1 + 1           : H1
                   ... = 1               : sorry
end
