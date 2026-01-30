/--
trace: [Compiler.saveMono] size: 7
    def foo f x : Option Nat :=
      let _x.1 := f x;
      cases _x.1 : Option Nat
      | Option.some val.2 =>
        let _x.3 := Nat.add val.2 val.2;
        let _x.4 := some ◾ _x.3;
        return _x.4
      | _ =>
        let _x.5 := none ◾;
        return _x.5
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def foo (f : Nat → Option Nat) (x : Nat) : Option Nat :=
  if let some val := f x then
    if let some val2 := f x then
      some <| val + val2
    else
      none
  else
    none
