def combine : PSum Unit (p → q) → PSum Unit p → PSum Unit q
  | PSum.inr f, PSum.inr proof => PSum.inr $ f proof
  | _, _ => PSum.inl ()

def tst : String :=
  let f : PSum Unit (True → True) := .inr id
  let v : PSum Unit True := .inr .intro
  match combine f v with
  | .inr _ => "inr"
  | .inl _ => "inl"

#eval tst
