def allPairsAux (xs: List α) (ys: List β) (accum: List (α × β)) :=
  match xs, ys with
  | _, [] => accum
  | [], _ => accum
  | x::xs, y::ys => allPairsAux xs ys ((x, y)::accum)
