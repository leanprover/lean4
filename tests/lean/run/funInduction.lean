namespace Ex1

variable (P : Nat → Prop)

def ackermann : (Nat × Nat) → Nat
  | (0, m) => m + 1
  | (n+1, 0) => ackermann (n, 1)
  | (n+1, m+1) => ackermann (n, ackermann (n + 1, m))
termination_by p => p

/--
error: tactic 'fail' failed
case case1
P : Nat → Prop
m✝ : Nat
⊢ P (ackermann (0, m✝))

case case2
P : Nat → Prop
n✝ : Nat
ih1✝ : P (ackermann (n✝, 1))
⊢ P (ackermann (n✝.succ, 0))

case case3
P : Nat → Prop
n✝ m✝ : Nat
ih2✝ : P (ackermann (n✝ + 1, m✝))
ih1✝ : P (ackermann (n✝, ackermann (n✝ + 1, m✝)))
⊢ P (ackermann (n✝.succ, m✝.succ))
-/
#guard_msgs in
example : P (ackermann p) := by
  fun_induction ackermann p
  fail

/-- error: tactic 'Lean.Parser.Tactic.funCases' has not been implemented -/
#guard_msgs in
example : P (ackermann p) := by
  fun_cases ackermann p
  fail

/--
error: unsolved goals
case case1
P : Nat → Prop
n m m✝ : Nat
⊢ P (ackermann (0, m✝))

case case2
P : Nat → Prop
n m n✝ : Nat
ih1✝ : P (ackermann (n✝, 1))
⊢ P (ackermann (n✝.succ, 0))

case case3
P : Nat → Prop
n m n✝ m✝ : Nat
ih2✝ : P (ackermann (n✝ + 1, m✝))
ih1✝ : P (ackermann (n✝, ackermann (n✝ + 1, m✝)))
⊢ P (ackermann (n✝.succ, m✝.succ))
-/
#guard_msgs in
example : P (ackermann (n, m)) := by
  fun_induction ackermann (n, m)

/-- error: tactic 'Lean.Parser.Tactic.funCases' has not been implemented -/
#guard_msgs in
example : P (ackermann (n, m)) := by
  fun_cases ackermann (n, m)

end Ex1

namespace Ex2

variable (P : Nat → Prop)

def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n+1, 0 => ackermann n 1
  | n+1, m+1 => ackermann n (ackermann (n + 1) m)
termination_by n m => (n, m)

/--
error: unexpected number of arguments at motive type
  Nat
-/
#guard_msgs in
example : P (ackermann n m) := by
  fun_induction ackermann n m

/--
error: fun_induction got confused trying to use ackermann.induct. Does it take 1 or 2 targets?
-/
#guard_msgs in
example : P (ackermann n m) := by
  fun_induction ackermann n

/-- error: no arguments? TODO! -/
#guard_msgs in
example : P (ackermann n m) := by
  fun_induction ackermann

end Ex2

namespace Ex3

variable (P : List α → Prop)

def ackermann {α} (inc : List α) : List α → List α → List α
  | [], ms => ms ++ inc
  | _::ns, [] => ackermann inc ns inc
  | n::ns, _::ms => ackermann inc ns (ackermann inc (n::ns) ms)
termination_by ns ms => (ns, ms)

/--
error: unexpected number of arguments at motive type
  List α
-/
#guard_msgs in
example : P (ackermann inc n m) := by
  fun_induction ackermann inc n m

/--
error: fun_induction got confused trying to use ackermann.induct. Does it take 1 or 2 targets?
-/
#guard_msgs in
example : P (ackermann inc n m) := by
  fun_induction ackermann inc n

/--
error: fun_induction got confused trying to use ackermann.induct. Does it take 1 or 2 targets?
-/
#guard_msgs in
example : P (ackermann inc n m) := by
  fun_induction ackermann inc

end Ex3
