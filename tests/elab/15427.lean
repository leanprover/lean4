module

public section

/-! Regression test for `macro_inline` on `Decidable`, issue #15427 -/


@[noinline] def touch (n : Nat) : Nat := dbg_trace s!"evaluated touch {n}"; n


/--
trace: [Compiler.saveMono] size: 8
    def plain n : Bool :=
      let _x.1 := 0;
      let _x.2 := Nat.decEq n _x.1;
      cases _x.2 : Bool
      | Bool.false =>
        return _x.2
      | Bool.true =>
        let _x.3 := touch n;
        let _x.4 := 5;
        let _x.5 := Nat.decEq _x.3 _x.4;
        return _x.5
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def plain (n : Nat) : Bool := decide (n = 0 ∧ touch n = 5)

/--
trace: [Compiler.saveMono] size: 12
    def compound n : Bool :=
      let _x.1 := 0;
      let _x.2 := Nat.decEq n _x.1;
      cases _x.2 : Bool
      | Bool.false =>
        return _x.2
      | Bool.true =>
        let _x.3 := touch n;
        let _x.4 := 5;
        let _x.5 := Nat.decEq _x.3 _x.4;
        cases _x.5 : Bool
        | Bool.false =>
          return _x.2
        | Bool.true =>
          let _x.6 := false;
          return _x.6
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def compound (n : Nat) : Bool := decide (n = 0 ∧ ¬ touch n = 5)

/--
trace: [Compiler.saveMono] size: 12
    def viaBand n : Bool :=
      let _x.1 := 0;
      let _x.2 := Nat.decEq n _x.1;
      cases _x.2 : Bool
      | Bool.false =>
        return _x.2
      | Bool.true =>
        let _x.3 := touch n;
        let _x.4 := 5;
        let _x.5 := Nat.decEq _x.3 _x.4;
        cases _x.5 : Bool
        | Bool.false =>
          return _x.2
        | Bool.true =>
          let _x.6 := false;
          return _x.6
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def viaBand (n : Nat) : Bool := decide (n = 0) && !decide (touch n = 5)

/--
info: evaluated touch 0
---
info: [false, false, false]
-/
#guard_msgs in
#eval (List.range 3).map plain

/--
info: evaluated touch 0
---
info: [true, false, false]
-/
#guard_msgs in
#eval (List.range 3).map compound

/--
info: evaluated touch 0
---
info: [true, false, false]
-/
#guard_msgs in
#eval (List.range 3).map viaBand
