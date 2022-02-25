@[simp] def Stream.hasLength [Stream stream value] (n : Nat) (s : stream) : Bool :=
  match n, Stream.next? s with
  | 0, none => true
  | n + 1, some (_, s') => hasLength n s'
  | _, _ => false

#check @Stream.hasLength._eq_1
#check @Stream.hasLength._eq_2
#check @Stream.hasLength._eq_3
