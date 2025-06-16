-- We re-define these here to avoid stage0 complications
def map (f : α → β) : List α → List β
  | []    => []
  | a::as => f a :: map f as

def zipWith (f : α → β → γ) : (xs : List α) → (ys : List β) → List γ
  | x::xs, y::ys => f x y :: zipWith f xs ys
  | _,     _     => []

def append : (xs ys : List α) → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

namespace ListEx

theorem map_id (xs : List α) : map id xs = xs := by
  fun_induction map <;> simp_all only [map, id]

-- This works because collect ignores `.dropped` arguments

theorem map_map (f : α → β) (g : β → γ) xs :
  map g (map f xs) = map (g ∘ f) xs := by
  fun_induction map <;> simp_all only [map, Function.comp]

-- This should genuinely not work, but have a good error message

/--
error: found more than one suitable call of 'append' in the goal. Please include the desired arguments.
-/
#guard_msgs in
theorem append_assoc :
  append xs (append ys zs) = append (append xs ys) zs := by
  fun_induction append <;> simp_all only [append]

end ListEx

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
  fun_induction ackermann
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
  fun_cases ackermann
  fail

/-- error: could not find suitable call of 'ackermann' in the goal -/
#guard_msgs in
example : P (ackermann (n, m)) := by
  fun_induction ackermann

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
  fun_induction ackermann

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
  fun_induction fib
  fail

/-- error: could not find suitable call of 'fib' in the goal -/
#guard_msgs in
example : n ≤ fib (n + 2) := by
  fun_induction fib

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
  fun_induction fib
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
  fun_induction Finn.min <;> simp_all [Finn.min, Finn.le]

theorem Finn.min_le_right' : (Finn.min' x m i j).le j := by
  fun_induction Finn.min' <;> simp_all [Finn.min', Finn.le]

theorem Finn.min_le_right'' : (Finn.min'' x m i j).le j := by
  fun_induction Finn.min'' <;> simp_all [Finn.min'', Finn.le]

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
  fun_induction Tree.size

end Mutual
