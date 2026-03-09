instance : HMul Nat Bool Nat where
  hMul
    | x, true  => x
    | x, false => 0

#check (10:Nat) * true

#check fun x => x * 1
