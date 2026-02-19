/-! This test file verifies that `Quot α` is correctly erased to `α` instead of `lcAny`, and that `Quot.mk`/`Quot.lift` are also erased correctly-/

set_option trace.Compiler.saveBase true
set_option pp.letVarTypes true

-- def SquashNat := Quot (fun (_ _ : Nat) => True)
abbrev SquashNat := Squash Nat

/--
trace: [Compiler.saveBase] size: 0
    def SquashNat.mk x : Nat :=
      return x
-/
#guard_msgs in
def SquashNat.mk (x : Nat) : SquashNat := Quot.mk _ x

/--
warning: declaration uses `sorry`
---
trace: [Compiler.saveBase] size: 1
    def SquashNat.out x : Bool :=
      let _x.1 : Bool := true;
      return _x.1
-/
#guard_msgs  in
def SquashNat.out (x : SquashNat) : Bool := Quot.lift (fun _ => true) sorry x
#check @Quot.mk
