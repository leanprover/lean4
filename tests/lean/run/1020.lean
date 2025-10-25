def allPairs (xs : List α) (ys : List β) : List (α × β) :=
  let rec aux
  | [], r => r
  | x::xs, r =>
    let rec aux₂
    | [], r => r
    | y::ys, r => (x, y) :: r
    aux₂ ys (aux xs r)
  aux xs []

def allPairsFixed (xs : List α) (ys : List β) : List (α × β) :=
  let rec aux
  | [], r => r
  | x::xs, r =>
    let rec aux₂
    | [], r => r
    | y::ys, r => aux₂ ys ((x, y) :: r)
    aux₂ ys (aux xs r)
  aux xs []

example : (allPairsFixed [1, 2, 3] ['a', 'b']) = [(1, 'b'), (1, 'a'), (2, 'b'), (2, 'a'), (3, 'b'), (3, 'a')] :=
  rfl

example : (allPairsFixed (List.range 3) (List.range 4) |>.length) = 12 :=
  rfl
