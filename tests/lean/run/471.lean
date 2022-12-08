inductive vec : Nat → Type where
  | nil : vec 0
  | cons : Int → vec n → vec n.succ

def vec_len : vec n → Nat
  | vec.nil => 0
  | x@(vec.cons h t) => vec_len t + 1

def vec_len' : {n : Nat} → vec n → Nat
  | _, vec.nil => 0
  | _, x@(vec.cons h t) => vec_len' t + 1

def tst1 : vec (n+1) → Int × vec (n+1) × vec n
  | x@(vec.cons h t) => (h, x, t)

def tst2 : vec n → Option (Int × vec n)
  | x@(vec.cons h t) => some (h, x)
  | _ => none

example (a : Int) (x : vec n) : tst2 (vec.cons a x) = some (a, vec.cons a x) :=
  rfl

def vec_len_non_as : vec n → Nat
  | vec.nil => 0
  | vec.cons h t => vec_len_non_as t + 1

def list_len : List Int → Nat
  | List.nil => 0
  | x@(List.cons h t) => list_len t + 1
