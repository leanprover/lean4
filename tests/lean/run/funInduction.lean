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
error: unsolved goals
case case1
P : Nat → Prop
m✝ : Nat
⊢ P (ackermann 0 m✝)

case case2
P : Nat → Prop
n✝ : Nat
ih1✝ : P (ackermann n✝ 1)
⊢ P (ackermann n✝.succ 0)

case case3
P : Nat → Prop
n✝ m✝ : Nat
ih2✝ : P (ackermann (n✝ + 1) m✝)
ih1✝ : P (ackermann n✝ (ackermann (n✝ + 1) m✝))
⊢ P (ackermann n✝.succ m✝.succ)
-/
#guard_msgs in
example : P (ackermann n m) := by
  fun_induction ackermann n m

/--
error: Expected fully applied application of ackermann with 2 arguments, but found 1 arguments
-/
#guard_msgs in
example : P (ackermann n m) := by
  fun_induction ackermann n

/--
error: Expected fully applied application of ackermann with 2 arguments, but found 0 arguments
-/
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
error: unsolved goals
case case1
α : Type u_1
P : List α → Prop
inc ms✝ : List α
⊢ P (ackermann inc [] ms✝)

case case2
α : Type u_1
P : List α → Prop
inc : List α
head✝ : α
ns✝ : List α
ih1✝ : P (ackermann inc ns✝ inc)
⊢ P (ackermann inc (head✝ :: ns✝) [])

case case3
α : Type u_1
P : List α → Prop
inc : List α
n✝ : α
ns✝ : List α
head✝ : α
ms✝ : List α
ih2✝ : P (ackermann inc (n✝ :: ns✝) ms✝)
ih1✝ : P (ackermann inc ns✝ (ackermann inc (n✝ :: ns✝) ms✝))
⊢ P (ackermann inc (n✝ :: ns✝) (head✝ :: ms✝))
-/
#guard_msgs in
example : P (ackermann inc n m) := by
  fun_induction ackermann inc n m

/--
error: Expected fully applied application of ackermann with 4 arguments, but found 3 arguments
-/
#guard_msgs in
example : P (ackermann inc n m) := by
  fun_induction ackermann inc n

/--
error: Expected fully applied application of ackermann with 4 arguments, but found 2 arguments
-/
#guard_msgs in
example : P (ackermann inc n m) := by
  fun_induction ackermann inc

end Ex3
