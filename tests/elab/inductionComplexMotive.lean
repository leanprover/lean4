def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n+1, 0 => ackermann n 1
  | n+1, m+1 => ackermann n (ackermann (n + 1) m)
termination_by n m => (n, m)

-- This is the unfolding induction principle, proven by hand for this test to make
-- it independent of the actual generation code

theorem ackermann_induct_unfolding (motive : Nat → Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m (m + 1))
  (case2 : ∀ (n : Nat), motive n 1 (ackermann n 1) → motive n.succ 0 (ackermann n 1))
  (case3 :
    ∀ (n m : Nat),
      motive (n + 1) m (ackermann (n + 1) m) →
        motive n (ackermann (n + 1) m) (ackermann n (ackermann (n + 1) m)) →
          motive n.succ m.succ (ackermann n (ackermann (n + 1) m)))
  (n m : Nat) : motive n m (ackermann n m) :=
  ackermann.induct (motive := fun n m => motive n m (ackermann n m))
    (fun m => by simpa [ackermann] using case1 m)
    (fun n ih => by simpa [ackermann] using case2 n ih)
    (fun n m ih1 ih2 => by simpa [ackermann] using case3 n m ih1 ih2)
     n m

/--
error: Failed: `fail` tactic was invoked
case case1
m✝ : Nat
⊢ m✝ + 1 ≤ ackermann (0 + 1) m✝

case case2
n✝ : Nat
a✝ : ackermann n✝ 1 ≤ ackermann (n✝ + 1) 1
⊢ ackermann n✝ 1 ≤ ackermann (n✝.succ + 1) 0

case case3
n✝ m✝ : Nat
a✝¹ : ackermann (n✝ + 1) m✝ ≤ ackermann (n✝ + 1 + 1) m✝
a✝ : ackermann n✝ (ackermann (n✝ + 1) m✝) ≤ ackermann (n✝ + 1) (ackermann (n✝ + 1) m✝)
⊢ ackermann n✝ (ackermann (n✝ + 1) m✝) ≤ ackermann (n✝.succ + 1) m✝.succ
-/
#guard_msgs in
theorem ackermann_mono1:
    ackermann n m ≤ ackermann (n+1) m := by
  induction n, m using ackermann_induct_unfolding
  fail

--- Now with cases

theorem ackermann_cases_unfolding (motive : Nat → Nat → Nat → Prop)
  (case1 : ∀ (m : Nat), motive 0 m (m + 1))
  (case2 : ∀ (n : Nat), motive n.succ 0 (ackermann n 1))
  (case3 : ∀ (n m : Nat), motive n.succ m.succ (ackermann n (ackermann (n + 1) m)))
  (n m : Nat) : motive n m (ackermann n m) :=
  ackermann.fun_cases (motive := fun n m => motive n m (ackermann n m))
    (fun m => by simpa [ackermann] using case1 m)
    (fun n => by simpa [ackermann] using case2 n)
    (fun n m => by simpa [ackermann] using case3 n m)
     n m

/--
error: Failed: `fail` tactic was invoked
case case1
m : Nat
⊢ m + 1 ≤ ackermann (0 + 1) m

case case2
n✝ : Nat
⊢ ackermann n✝ 1 ≤ ackermann (n✝.succ + 1) 0

case case3
n✝ m✝ : Nat
⊢ ackermann n✝ (ackermann (n✝ + 1) m✝) ≤ ackermann (n✝.succ + 1) m✝.succ
-/
#guard_msgs(pass trace, all) in
example : ackermann n m ≤ ackermann (n+1) m := by
  cases n, m using ackermann_cases_unfolding
  fail

-- Now an artificial one with multiple complex arguments.

axiom strange_induction
  {motive : Nat → Prop → Nat → Prop}
  (case1 : motive 0 True 42) :
  ∀ n, motive n (n-1 ≤ n) (n+1)

/--
error: Failed: `fail` tactic was invoked
case case1
⊢ True ∧ 0 < 42
-/
#guard_msgs in
example : n -1 ≤ n ∧ n < n +1 := by
  induction n using strange_induction
  fail

/--
error: Failed: `fail` tactic was invoked
case case1
⊢ True ∧ 0 < 42
-/
#guard_msgs in
example : n -1 ≤ n ∧ n < n +1 := by
  cases n using strange_induction
  fail

/--
error: Failed: `fail` tactic was invoked
case case1
n : Nat
⊢ n - 1 ≤ n ∧ n < 0
-/
#guard_msgs in
example : n -1 ≤ n ∧ n < n + 1 := by
  cases n+1 using strange_induction
  fail

-- And now one where abstracting would cause a type error
-- (induction silently skips abstracting over these)

/--
error: Failed: `fail` tactic was invoked
case case1
P : (n : Nat) → n > 0 → Prop
⊢ P (0 + 1) ⋯
-/
#guard_msgs in
example (P : (n : Nat) → (h : n > 0) → Prop) : P (n + 1) (Nat.zero_lt_succ n) := by
  induction n using strange_induction
  fail

/--
error: Failed: `fail` tactic was invoked
case case1
P : (n : Nat) → n > 0 → Prop
⊢ P (0 + 1) ⋯
-/
#guard_msgs in
example (P : (n : Nat) → (h : n > 0) → Prop) : P (n + 1) (Nat.zero_lt_succ n) := by
  cases n using strange_induction
  fail

-- One where the type of the complex argument depends on the other targets

axiom dep_induction
  {motive : (n : Nat) → Fin (n+1) → Prop}
  (case1 : motive 0 0) :
  ∀ n, motive n (Fin.last n)

/--
error: Failed: `fail` tactic was invoked
case case1
P : (n : Nat) → Fin (n + 1) → Prop
⊢ P 0 0
-/
#guard_msgs in
example (P : (n : Nat) → Fin (n+1) → Prop) : P n (Fin.last n) := by
  induction n using dep_induction
  fail


-- Using cases does not unfold as expected, due to the dependent motive.
-- This can be improved, but at least it does not error

/--
error: Failed: `fail` tactic was invoked
case case1
P : (n : Nat) → Fin (n + 1) → Prop
⊢ P 0 (Fin.last 0)
-/
#guard_msgs in
example (P : (n : Nat) → Fin (n+1) → Prop) : P n (Fin.last n) := by
  cases n using dep_induction
  fail

-- Using cases does not unfold as expected, due to the dependent motive.
-- This can be improved, but at least it does not error

/--
error: Failed: `fail` tactic was invoked
case case1
P : (n : Nat) → Fin (n + 1) → Prop
⊢ P 0 (Fin.last 0)
-/
#guard_msgs(pass trace, all) in
example (P : (n : Nat) → Fin (n+1) → Prop) : P 10 (Fin.last 10) := by
  cases 10 using dep_induction
  fail
