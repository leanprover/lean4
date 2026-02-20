set_option trace.Compiler.explicitRc true in
/--
trace: [Compiler.explicitRc] size: 3
    def test._redArg @&xs i : UInt8 :=
      let _x.1 := 5;
      let _x.2 := Array.ugetBorrowed ◾ xs i ◾;
      let _x.3 := Nat.decLt _x.1 _x.2;
      return _x.3
[Compiler.explicitRc] size: 5
    def test._redArg._boxed xs i : tagged :=
      let i.boxed := unbox i;
      dec i;
      let res := test._redArg xs i.boxed;
      dec xs;
      let r := box res;
      return r
[Compiler.explicitRc] size: 1
    def test @&xs i h : UInt8 :=
      let _x.1 := test._redArg xs i;
      return _x.1
[Compiler.explicitRc] size: 5
    def test._boxed xs i h : tagged :=
      let i.boxed := unbox i;
      dec i;
      let res := test xs i.boxed h;
      dec xs;
      let r := box res;
      return r
-/
#guard_msgs in
@[noinline] def test (xs : @& Array Nat) (i : USize) (h : i.toNat < xs.size) : Bool :=
  xs.uget i h > 5

/-- info: true -/
#guard_msgs in
#eval test #[1, 2, 10] 2 (by native_decide)
