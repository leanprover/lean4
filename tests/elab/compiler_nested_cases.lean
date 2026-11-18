module

public section

/-! Double cases on the same let bound variable should be simplified by the compiler. -/

/--
trace: [Compiler.saveBase] size: 6
    def test x y : Nat :=
      let b := Nat.beq x y;
      cases b : Nat
      | Bool.false =>
        let _x.1 := 3;
        return _x.1
      | Bool.true =>
        let _x.2 := 1;
        return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def test (x y : Nat) : Nat :=
  let b := Nat.beq x y
  match b with
  | true =>
    match b with
    | true => 1
    | false => 2
  | false => 3
