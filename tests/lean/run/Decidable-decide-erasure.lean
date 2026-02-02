import Lean.Compiler
import Lean.Compiler.LCNF.Probing

open Lean.Compiler.LCNF

/--
trace: [Compiler.saveBase] size: 3
    def f a : Bool :=
      let _x.1 := 1;
      let _x.2 := instDecidableEqNat a _x.1;
      let _x.3 := decide ◾ _x.2;
      return _x.3
[Compiler.saveMono] size: 2
    def f a : Bool :=
      let _x.1 := 1;
      let _x.2 := Nat.decEq a _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
set_option trace.Compiler.saveMono true in
def f (a : Nat) : Bool :=
  decide (a = 1)
