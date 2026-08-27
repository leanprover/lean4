module

public section

/--
trace: [Compiler.saveMono] size: 1
    def test : String :=
      let _x.1 := "1 2 3 84";
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def test : String := s!"{1} {2} {3} {42 * 2}"
