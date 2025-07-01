import Lean

/-!
Tests that lazy_delta_reduction_step treats projection applications like constant applications.
-/

structure Foo where
  f : (a : Nat) → a < 0 → Nat
  x : Nat

def mkFoo (n : Nat) (x : Nat) : Foo :=
  match n with
  | 0 => { f := fun a _ => a + x, x  }
  | n+1 => mkFoo n (x+1)

axiom my_sorry1 {α : Prop} : α
axiom my_sorry2 {α : Prop} : α

def c := 10000000 -- previously, the type checker would unfold mkFoo in the lhs and rhs `c`-times

-- We use `run_tac` to only exercise the kernel, not the elaborator
theorem ex : (mkFoo c a).f b my_sorry1 = (mkFoo c a).f b my_sorry2 := by run_tac do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.assign (← Lean.Meta.mkEqRefl ((← goal.getType').appArg!))
