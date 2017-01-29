inductive {u} vec (A : Type u) : nat → Type u
| nil  : vec 0
| cons : ∀ {n}, A → vec n → vec (n+1)

open tactic nat vec

def head {A : Type*} : ∀ {n : nat}, vec A (n+1) → A
| n (cons h t) := h

def tail {A : Type*} : ∀ {n : nat}, vec A (n+1) → vec A n
| n (cons h t) := t

@[simp] lemma head_cons {A : Type*} {n : nat} (a : A) (v : vec A n) : head (cons a v) = a :=
rfl

@[simp]
lemma tail_cons {A : Type*} {n : nat} (a : A) (v : vec A n) : tail (cons a v) = v :=
rfl

example {A : Type*} {n : nat} (v w : vec A (n+1)) : head v = head w → tail v = tail w → v = w :=
by do
  v ← get_local `v,
  cases_using v [`n', `hv, `tv],
  trace_state,
  w ← get_local `w,
  cases_using w [`n', `hw, `tw],
  trace_state,
  dsimp,
  trace_state,
  Heq1 ← intro1,
  Heq2 ← intro1,
  subst Heq1, subst Heq2,
  reflexivity

print "-------"

example (n : nat) : n ≠ 0 → succ (pred n) = n :=
by do
  H ← intro `H,
  n ← get_local `n,
  cases_using n [`n'],
  trace_state,
  contradiction,
  reflexivity

print "---------"
