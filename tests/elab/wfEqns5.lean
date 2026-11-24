/-!
Tests the equational theorems generated for functions defined by well-founded and structural
recursion with a nested `match`.
-/

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

/-- error: Unknown identifier `foo.eq_4` -/
#guard_msgs in
#check foo.eq_4

/--
info: foo._unary.eq_def (_x : (_ : Nat) ×' Nat) :
  foo._unary _x =
    PSigma.casesOn _x fun a a_1 =>
      match a, a_1 with
      | 0, m =>
        match m with
        | 0 => 0
        | m => m
      | n.succ, m => foo._unary ⟨n, m⟩
-/
#guard_msgs in
#check foo._unary.eq_def

-- Now the same for structural recursion

namespace Structural

def foo : Nat → Nat → Nat
  | 0, m => match m with | 0 => 0 | m => m
  | n+1, m => foo n m
termination_by structural n => n

/--
info: equations:
@[backward_defeq] theorem Structural.foo.eq_1 : foo 0 0 = 0
theorem Structural.foo.eq_2 : ∀ (x : Nat), (x = 0 → False) → foo 0 x = x
@[backward_defeq] theorem Structural.foo.eq_3 : ∀ (x n : Nat), foo n.succ x = foo n x
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

/-- error: Unknown identifier `Structural.foo.eq_4` -/
#guard_msgs in
#check Structural.foo.eq_4

end Structural
