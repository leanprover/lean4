set_option trace.Compiler.explicitRc true in
/--
trace: [Compiler.explicitRc] size: 3
    def test @&xs i : UInt8 :=
      let _x.1 := Array.ugetBorrowed xs i ◾;
      let _x.2 := Nat.blt 5 _x.1;
      return _x.2
[Compiler.explicitRc] size: 4
    def test._boxed xs i : tagged :=
      let i := unbox i;
      let res := test xs i;
      dec xs;
      let r := box res;
      return r
-/
#guard_msgs in
@[noinline] def test (xs : @& Array Nat) (i : USize) (h : i.toNat < xs.size) : Bool :=
  xs.uget i h > 5

/-- info: true -/
#guard_msgs in
#eval test #[1, 2, 10] 2 (by omega)
