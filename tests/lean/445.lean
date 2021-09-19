def f : Nat → Bool
  | 0 => true
  | n + 1 => (match n with
    | 0 => true
    | _ + 1 => true) && f n

#print f._sunfold

def g (i j : Nat) : Nat :=
  if i < 5 then 0 else
  match j with
  | Nat.zero => 1
  | Nat.succ j => g i j

#print g._sunfold
