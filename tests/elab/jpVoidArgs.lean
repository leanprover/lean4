module

/-!
This test checks that the compiler successfully removes void arguments from join points in the
impure phase.
-/

set_option compiler.postponeCompile false

public section

inductive Enum where
  | A | B | C

/--
trace: [Compiler.saveMono] size: 25
    def test x y a.1 : ST.Out lcAny Nat :=
      jp _jp.2 _y.3 : ST.Out lcAny Nat :=
        let _x.4 := 3;
        let _x.5 := y _x.4 _y.3;
        cases _x.5 : ST.Out lcAny Nat
        | ST.Out.mk val.6 state.7 =>
          let _x.8 := 0;
          let _x.9 := @ST.Out.mk ◾ ◾ _x.8 state.7;
          return _x.9;
      cases x : ST.Out lcAny Nat
      | Enum.A =>
        let _x.10 := 0;
        let _x.11 := y _x.10 a.1;
        cases _x.11 : ST.Out lcAny Nat
        | ST.Out.mk val.12 state.13 =>
          goto _jp.2 state.13
      | Enum.B =>
        let _x.14 := 1;
        let _x.15 := y _x.14 a.1;
        cases _x.15 : ST.Out lcAny Nat
        | ST.Out.mk val.16 state.17 =>
          goto _jp.2 state.17
      | Enum.C =>
        let _x.18 := 2;
        let _x.19 := y _x.18 a.1;
        cases _x.19 : ST.Out lcAny Nat
        | ST.Out.mk val.20 state.21 =>
          goto _jp.2 state.21
[Compiler.saveImpure] size: 19
    def test x y a.1 : tobj :=
      jp _jp.2 : tobj :=
        let _x.3 := 3;
        let _x.4 := y _x.3 ◾;
        let _x.5 := 0;
        return _x.5;
      cases x : tobj
      | Enum.A =>
        let _x.6 := 0;
        inc y;
        let _x.7 := y _x.6 ◾;
        goto _jp.2
      | Enum.B =>
        let _x.8 := 1;
        inc y;
        let _x.9 := y _x.8 ◾;
        goto _jp.2
      | Enum.C =>
        let _x.10 := 2;
        inc y;
        let _x.11 := y _x.10 ◾;
        goto _jp.2
[Compiler.saveImpure] size: 2
    def test._boxed x y a.1 : tobj :=
      let x.boxed := unbox x;
      let res := test x.boxed y a.1;
      return res
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
set_option trace.Compiler.saveImpure true in
def test (x : Enum) (y : Nat → BaseIO Unit) : BaseIO Nat := do
  match x with
  | .A => y 0
  | .B => y 1
  | .C => y 2
  y 3
  return 0
