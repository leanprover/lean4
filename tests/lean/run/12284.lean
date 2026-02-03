set_option trace.Compiler.init true
/--
trace: [Compiler.init] size: 3
    def test x y : Bool :=
      cases x : Bool
      | PUnit.unit =>
        let a := y;
        return a
-/
#guard_msgs in
def test (x : Unit) (y : Bool) : Bool :=
  x.casesOn (fun a => a) y
