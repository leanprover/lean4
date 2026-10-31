/-!
Test various edge cases of efficient computation of `ctorIdx`.
-/

inductive Test where
  | a
  | b (n : Nat)
  | c
  | d (n m : Nat)
  | e

/--
trace: [Compiler.result] size: 1
    def test1 : tobj :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test1 : Nat := Test.a.ctorIdx

/--
trace: [Compiler.result] size: 1
    def test2 : tobj :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test2 : Nat := (Test.b 11).ctorIdx

/--
trace: [Compiler.result] size: 1
    def test3 @&v : tobj :=
      let _x.1 := getObjTagNat ◾ v;
      return _x.1
[Compiler.result] size: 2
    def test3._boxed v : tobj :=
      let res := test3 v;
      dec v;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test3 (v : Test) : Nat := v.ctorIdx

inductive Enum where
  | one
  | two
  | three

/--
trace: [Compiler.result] size: 1
    def test4 : tobj :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test4 : Nat := Enum.one.ctorIdx

/--
trace: [Compiler.result] size: 1
    def test5 : tobj :=
      let _x.1 := 2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test5 : Nat := Enum.three.ctorIdx

/--
trace: [Compiler.result] size: 3
    def test6 v : tobj :=
      let _x.1 := box v;
      let _x.2 := getObjTagNat ◾ _x.1;
      dec _x.1;
      return _x.2
[Compiler.result] size: 2
    def test6._boxed v : tobj :=
      let v.boxed := unbox v;
      let res := test6 v.boxed;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test6 (v : Enum) : Nat := v.ctorIdx

structure Trivial where
  enum : Enum
  h : True

/--
trace: [Compiler.result] size: 1
    def test7._redArg _dummy : tobj :=
      let _x.1 := 0;
      return _x.1
[Compiler.result] size: 1
    def test7._redArg._boxed _dummy : tobj :=
      let res := test7._redArg _dummy;
      return res
[Compiler.result] size: 1
    def test7 t : tobj :=
      let _x.1 := 0;
      return _x.1
[Compiler.result] size: 2
    def test7._boxed t : tobj :=
      let t.boxed := unbox t;
      let res := test7 t.boxed;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test7 (t : Trivial) : Nat := t.ctorIdx

/--
trace: [Compiler.result] size: 1
    def test8 @&n : tobj :=
      let _x.1 := Nat.ctorIdx n;
      return _x.1
[Compiler.result] size: 2
    def test8._boxed n : tobj :=
      let res := test8 n;
      dec n;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test8 (n : Nat) : Nat := n.ctorIdx

/--
trace: [Compiler.result] size: 1
    def test9 : tobj :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test9 : Nat := Nat.zero |>.ctorIdx


/--
trace: [Compiler.result] size: 1
    def test10 : tobj :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test10 : Nat := Nat.succ .zero |>.ctorIdx

def main : IO Unit := do
  let values : Array Test := #[
    .a,
    .b 37,
    .c,
    .d 42 11,
    .e
  ]

  check Test.ctorIdx values

  let enumValues : Array Enum := #[
    .one,
    .two,
    .three
  ]

  check Enum.ctorIdx enumValues

  let natValues : Array Nat := #[
    0,
    37
  ]

  check Nat.ctorIdx natValues

  let intValues : Array Int := #[
    0,
    -1
  ]

  check Int.ctorIdx intValues
where
  @[noinline, nospecialize]
  check {α : Type} (toCtorIdx : α → Nat) (values : Array α) : IO Unit :=
    for h : idx in 0...values.size do
      if idx != toCtorIdx values[idx] then
        throw <| .userError s!"Value at {idx} is wrong"
