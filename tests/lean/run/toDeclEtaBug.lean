import Lean

@[inline] def f (c b : Bool) (x : Nat) : Nat :=
  if c && b then
    x + 1
  else
    x + 2

/--
trace: [Compiler.saveMono] size: 2
    def g c : Nat :=
      let _x.1 := 2;
      let _x.2 := Nat.add c _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def g (c : Nat) : Nat :=
  f true false c
