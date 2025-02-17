import Lean

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

/--
error: tactic 'fail' failed
case case1
P : Nat → Prop
m✝ : Nat
⊢ P (ackermann (0, m✝))

case case2
P : Nat → Prop
n✝ : Nat
⊢ P (ackermann (n✝.succ, 0))

case case3
P : Nat → Prop
n✝ m✝ : Nat
⊢ P (ackermann (n✝.succ, m✝.succ))
-/
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

/--
error: unsolved goals
case case1
P : Nat → Prop
n m m✝ : Nat
⊢ P (ackermann (0, m✝))

case case2
P : Nat → Prop
n m n✝ : Nat
⊢ P (ackermann (n✝.succ, 0))

case case3
P : Nat → Prop
n m n✝ m✝ : Nat
⊢ P (ackermann (n✝.succ, m✝.succ))
-/
#guard_msgs in
example : P (ackermann (n, m)) := by
  fun_cases ackermann (n, m)

-- Testing Generalization:

/--
error: unsolved goals
case case1
P : Nat → Prop
n m m✝ : Nat
⊢ P (ackermann (n, m))

case case2
P : Nat → Prop
n m n✝ : Nat
⊢ P (ackermann (n, m))

case case3
P : Nat → Prop
n m n✝ m✝ : Nat
⊢ P (ackermann (n, m))
-/
#guard_msgs in
example : P (ackermann (n, m)) := by
  fun_cases ackermann (n+n, m)

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
error: Expected fully applied application of 'ackermann' with 2 arguments, but found 1 arguments
-/
#guard_msgs in
example : P (ackermann n m) := by
  fun_induction ackermann n

/--
error: Expected fully applied application of 'ackermann' with 2 arguments, but found 0 arguments
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
error: Expected fully applied application of 'ackermann' with 4 arguments, but found 3 arguments
-/
#guard_msgs in
example : P (ackermann inc n m) := by
  fun_induction ackermann inc n

/--
error: Expected fully applied application of 'ackermann' with 4 arguments, but found 2 arguments
-/
#guard_msgs in
example : P (ackermann inc n m) := by
  fun_induction ackermann inc

end Ex3

namespace Structural

variable (P : Nat → Prop)

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
termination_by structural x => x

/--
error: tactic 'fail' failed
case case1
P : Nat → Prop
⊢ P (fib 0)

case case2
P : Nat → Prop
⊢ P (fib 1)

case case3
P : Nat → Prop
n✝ : Nat
ih2✝ : P (fib n✝)
ih1✝ : P (fib (n✝ + 1))
⊢ P (fib n✝.succ.succ)
-/
#guard_msgs in
example : P (fib n) := by
  fun_induction fib n
  fail

example : n ≤ fib (n + 2) := by
  fun_induction fib n
  case case1 => simp [fib]
  case case2 => simp [fib]
  case case3 n ih1 ih2 => simp_all [fib]; omega

example : n ≤ fib (n + 2) := by
  fun_induction fib n with
  | case1 | case2 => simp [fib]
  | case3  => simp_all [fib]; omega


end Structural

namespace StructuralWithOmittedParam

variable (P : Nat → Prop)

variable (inc : Nat)
def fib : Nat → Nat
  | 0 => 0
  | 1 => inc
  | n+2 => fib n + fib (n+1)
termination_by structural x => x

/--
info: StructuralWithOmittedParam.fib.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1)
  (case3 : ∀ (n : Nat), motive n → motive (n + 1) → motive n.succ.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check fib.induct -- NB: No inc showing up

/--
error: tactic 'fail' failed
case case1
P : Nat → Prop
inc : Nat
⊢ P (fib 2 0)

case case2
P : Nat → Prop
inc : Nat
⊢ P (fib 2 1)

case case3
P : Nat → Prop
inc n✝ : Nat
ih2✝ : P (fib 2 n✝)
ih1✝ : P (fib 2 (n✝ + 1))
⊢ P (fib 2 n✝.succ.succ)
-/
#guard_msgs in
example : P (fib 2 n) := by
  fun_induction fib 3 n
  fail

/--
error: tactic 'fail' failed
case case1
P : Nat → Prop
inc : Nat
⊢ P (fib 2 0)

case case2
P : Nat → Prop
inc : Nat
⊢ P (fib 2 1)

case case3
P : Nat → Prop
inc n✝ : Nat
ih2✝ : P (fib 2 n✝)
ih1✝ : P (fib 2 (n✝ + 1))
⊢ P (fib 2 n✝.succ.succ)
-/
#guard_msgs in
example : P (fib 2 n) := by
  fun_induction fib _ n
  fail

end StructuralWithOmittedParam

namespace StructuralIndices

-- Testing recursion on an indexed data type
inductive Finn : Nat → Type where
  | fzero : {n : Nat} → Finn n
  | fsucc : {n : Nat} → Finn n → Finn (n+1)

def Finn.min (x : Bool) {n : Nat} (m : Nat) : Finn n → (f : Finn n) → Finn n
  | fzero, _ => fzero
  | _, fzero => fzero
  | fsucc i, fsucc j => fsucc (Finn.min (not x) (m + 1) i j)
termination_by structural i => i

def Finn.min' (x : Bool) {n : Nat} (m : Nat) : Finn n → (f : Finn n) → Finn n
  | fzero, _ => fzero
  | _, fzero => fzero
  | fsucc i, fsucc j => fsucc (Finn.min' (not x) (m + 1) i j)
termination_by structural _ j => j

def Finn.min'' (x : Bool) {n : Nat} (m : Nat) : Finn n → (f : Finn n) → Finn n
  | fzero, _ => fzero
  | _, fzero => fzero
  | fsucc i, fsucc j => fsucc (Finn.min'' (not x) (m + 1) i j)
termination_by structural n

def Finn.le : Finn n → Finn n → Bool
  | fzero, _ => true
  | _, fzero => false
  | fsucc i, fsucc j => Finn.le i j

theorem Finn.min_le_right₀ : (Finn.min x m i j).le j := by
  induction x, m, i, j using @Finn.min.induct <;> simp_all [Finn.min, Finn.le]

theorem Finn.min_le_right : (Finn.min x m i j).le j := by
  fun_induction Finn.min x m i j <;> simp_all [Finn.min, Finn.le]

theorem Finn.min_le_right' : (Finn.min' x m i j).le j := by
  fun_induction Finn.min' x m i j <;> simp_all [Finn.min', Finn.le]

theorem Finn.min_le_right'' : (Finn.min'' x m i j).le j := by
  fun_induction Finn.min'' x m i j <;> simp_all [Finn.min'', Finn.le]

end StructuralIndices

namespace Nonrec

def foo := 1

/-- error: no functional cases theorem for 'foo', or function is mutually recursive -/
#guard_msgs in
example : True := by
  fun_induction foo


end Nonrec

namespace Mutual

inductive Tree (α : Type u) : Type u where
  | node : α → (Bool → List (Tree α)) → Tree α

-- Recursion over nested inductive

mutual
def Tree.size : Tree α → Nat
  | .node _ tsf => 1 + size_aux (tsf true) + size_aux (tsf false)
termination_by structural t => t
def Tree.size_aux : List (Tree α) → Nat
  | [] => 0
  | t :: ts => size t + size_aux ts
end

/-- error: no functional cases theorem for 'Tree.size', or function is mutually recursive -/
#guard_msgs in
example (t : Tree α) : True := by
  fun_induction Tree.size t

end Mutual
