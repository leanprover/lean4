module

/-! This test demonstrates basic coalescing capabilities of the RC optimizer -/

public section

@[extern "foo"]
opaque foo (x : String) (n : Nat) : Nat


/--
trace: [Compiler.coalesceRc] size: 18
    def test x : tobj :=
      let _x.1 := 0;
      inc[3][ref] x;
      let a := foo x _x.1;
      let _x.2 := 1;
      let _x.3 := foo x _x.2;
      let a := Nat.add a _x.3;
      dec _x.3;
      dec a;
      let _x.4 := 2;
      let _x.5 := foo x _x.4;
      let a := Nat.add a _x.5;
      dec _x.5;
      dec a;
      let _x.6 := 3;
      let _x.7 := foo x _x.6;
      let a := Nat.add a _x.7;
      dec _x.7;
      dec a;
      return a
-/
#guard_msgs in
set_option trace.Compiler.coalesceRc true in
def test (x : String) : Nat :=
  let a := foo x 0
  let a := a + foo x 1
  let a := a + foo x 2
  let a := a + foo x 3
  a
