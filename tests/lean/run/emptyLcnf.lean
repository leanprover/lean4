import Lean

inductive MyEmpty

def f (x : MyEmpty) : Nat :=
  MyEmpty.casesOn _ x

set_option trace.Compiler.result true
/--
trace: [Compiler.result] size: 0
    def f x : Nat :=
      ⊥
-/
#guard_msgs in
run_meta Lean.Compiler.compile #[``f]
