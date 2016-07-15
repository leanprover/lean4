inductive vec (A : Type) : nat → Type :=
| nil  : vec A 0
| cons : ∀ {n}, A → vec A n → vec A (n+1)

open tactic nat vec

definition head {A : Type} : ∀ {n : nat}, vec A (n+1) → A
| n (cons h t) := h

definition tail {A : Type} : ∀ {n : nat}, vec A (n+1) → vec A n
| n (cons h t) := t

definition head_cons [defeq] {A : Type} {n : nat} (a : A) (v : vec A n) : head (cons a v) = a :=
rfl

definition tail_cons [defeq] {A : Type} {n : nat} (a : A) (v : vec A n) : tail (cons a v) = v :=
rfl

example {A : Type} {n : nat} (v w : vec A (n+1)) : head v = head w → tail v = tail w → v = w :=
by do
  v ← get_local "v",
  cases_using v ["n'", "hv", "tv"],
  trace_state,
  w ← get_local "w",
  cases_using w ["n'", "hw", "tw"],
  trace_state,
  dsimp,
  Heq1 ← intro "_",
  Heq2 ← intro "_",
  subst Heq1, subst Heq2,
  reflexivity

print "-------"

example (n : nat) : n ≠ 0 → succ (pred n) = n :=
by do
  H ← intro "H",
  n ← get_local "n",
  cases_using n ["n'"],
  trace_state,
  contradiction,
  reflexivity

print "---------"
