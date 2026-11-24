/-!
Tests the deprecated option `backward.eqns.deepRecursiveSplit`, for functions defined by
well-founded and structural recursion. The same functions without the option are tested in
`elab/wfEqns5.lean`.
-/

set_option backward.eqns.deepRecursiveSplit false in
def bar : Nat → Nat → Nat
  | 0, m => match m with | 0 => 0 | m => m
  | n+1, m => bar n m
termination_by n => n

/--
info: equations:
theorem bar.eq_1 : ∀ (x : Nat),
  bar 0 x =
    match x with
    | 0 => 0
    | m => m
theorem bar.eq_2 : ∀ (x n : Nat), bar n.succ x = bar n x
-/
#guard_msgs in
#print equations bar

/--
info: bar.eq_def (x✝ x✝¹ : Nat) :
  bar x✝ x✝¹ =
    match x✝, x✝¹ with
    | 0, m =>
      match m with
      | 0 => 0
      | m => m
    | n.succ, m => bar n m
-/
#guard_msgs in
#check bar.eq_def

namespace Structural

set_option backward.eqns.deepRecursiveSplit false in
def bar : Nat → Nat → Nat
  | 0, m => match m with | 0 => 0 | m => m
  | n+1, m => bar n m
termination_by n => n

/--
info: equations:
theorem Structural.bar.eq_1 : ∀ (x : Nat),
  bar 0 x =
    match x with
    | 0 => 0
    | m => m
theorem Structural.bar.eq_2 : ∀ (x n : Nat), bar n.succ x = bar n x
-/
#guard_msgs in
#print equations bar

/--
info: Structural.bar.eq_def (x✝ x✝¹ : Nat) :
  bar x✝ x✝¹ =
    match x✝, x✝¹ with
    | 0, m =>
      match m with
      | 0 => 0
      | m => m
    | n.succ, m => bar n m
-/
#guard_msgs in
#check bar.eq_def

end Structural
