@[simp] def Std.Stream.hasLength [Stream stream value] (n : Nat) (s : stream) : Bool :=
  match n, Stream.next? s with
  | 0, none => true
  | n + 1, some (_, s') => hasLength n s'
  | _, _ => false

#check @Std.Stream.hasLength.eq_1
#check @Std.Stream.hasLength.eq_2
#check @Std.Stream.hasLength.eq_3
