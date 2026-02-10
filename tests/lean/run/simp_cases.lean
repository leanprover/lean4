/-! This test asserts the basic behavior of the simpCases pass. In particular this pass is capable
  of de-duplicating some branches that simp can't at the current moment. -/

inductive Foo where
  | a (n : Nat)
  | b (n : Nat)
  | c (n : Nat)

@[noinline]
def aux (n : Nat) : Nat := n

/--
trace: [Compiler.saveMono] size: 7
    def test f : Nat :=
      cases f : Nat
      | Foo.a n.1 =>
        let _x.2 := aux n.1;
        return _x.2
      | Foo.b n.3 =>
        let _x.4 := aux n.3;
        return _x.4
      | Foo.c n.5 =>
        let _x.6 := aux n.5;
        return _x.6
[Compiler.simpCase] size: 2
    def test f : tobj :=
      let n.1 := proj[0] f;
      let _x.2 := aux n.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
set_option trace.Compiler.simpCase true in
def test (f : Foo) : Nat :=
  match f with
  | .a n => aux n
  | .b n => aux n
  | .c n => aux n
