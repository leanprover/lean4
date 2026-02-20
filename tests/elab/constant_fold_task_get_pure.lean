/-! This test asserts that we detect the pattern of calling `get` on a `Task.pure` and remove
  `Task.pure` in order to avoid interaction with the runtime. -/

/--
trace: [Compiler.saveMono] size: 0
    def test n : Nat :=
      return n
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def test (n : Nat) : Nat :=
  (Task.pure n).get
