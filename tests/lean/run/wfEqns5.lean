
def foo : Nat → Nat → Nat
  | 0, m => match m with | 0 => 0 | m => m
  | n+1, m => foo n m
termination_by n => n

/--
info: equations:
theorem foo.eq_1 : foo 0 0 = 0
theorem foo.eq_2 : ∀ (x : Nat), (x = 0 → False) → foo 0 x = x
theorem foo.eq_3 : ∀ (x n : Nat), foo n.succ x = foo n x
-/
#guard_msgs in
#print equations foo

/--
info: foo.eq_def (x✝ x✝¹ : Nat) :
  foo x✝ x✝¹ =
    match x✝, x✝¹ with
    | 0, m =>
      match m with
      | 0 => 0
      | m => m
    | n.succ, m => foo n m
-/
#guard_msgs in
#check foo.eq_def

/-- error: unknown identifier 'foo.eq_4' -/
#guard_msgs in
#check foo.eq_4


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

-- Now the same for structural recursion

namespace Structural

def foo : Nat → Nat → Nat
  | 0, m => match m with | 0 => 0 | m => m
  | n+1, m => foo n m
termination_by structural n => n

/--
info: equations:
theorem Structural.foo.eq_1 : foo 0 0 = 0
theorem Structural.foo.eq_2 : ∀ (x : Nat), (x = 0 → False) → foo 0 x = x
theorem Structural.foo.eq_3 : ∀ (x n : Nat), foo n.succ x = foo n x
-/
#guard_msgs in
#print equations foo

/--
info: Structural.foo.eq_def (x✝ x✝¹ : Nat) :
  foo x✝ x✝¹ =
    match x✝, x✝¹ with
    | 0, m =>
      match m with
      | 0 => 0
      | m => m
    | n.succ, m => foo n m
-/
#guard_msgs in
#check foo.eq_def

/-- error: unknown identifier 'foo.eq_4' -/
#guard_msgs in
#check Structural.foo.eq_4


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
