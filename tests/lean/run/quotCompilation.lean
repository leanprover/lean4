/-! This test file verifies that `Quot α` is correctly erased to `α` instead of `lcAny`-/

set_option trace.Compiler.saveBase true
set_option trace.Compiler.saveMono true
set_option pp.letVarTypes true

def SquashNat := Quot (fun (_ _ : Nat) => True)


/-In `saveBase`, `Quot.mk` is not yet erased, but `Quot α _` has been effectively translated into `α`.
  In `saveMono`, both `Quot.mk` has furthermore been removed too.-/
/--
trace: [Compiler.saveBase] size: 1
    def SquashNat.mk x : Nat :=
      let _x.1 : Nat := @Quot.mk _ ◾ x;
      return _x.1
[Compiler.saveMono] size: 0
    def SquashNat.mk x : Nat :=
      return x
-/
#guard_msgs in
def SquashNat.mk (x : Nat) : SquashNat := Quot.mk _ x
