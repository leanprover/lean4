set_option pp.analyze false

def p (x y : Nat) := x = y

example (x y : Nat) : p (x + y) (y + x + 0) := by
  conv =>
    whnf
    congr
    . skip
    . whnf; skip
  trace_state
  rw [Nat.add_comm]
  rfl

example (x y : Nat) : p (x + y) (y + x + 0) := by
  conv =>
    whnf
    rhs
    whnf
  trace_state
  rw [Nat.add_comm]
  rfl

example (x y : Nat) : p (x + y) (y + x + 0) := by
  conv =>
    whnf
    lhs
    whnf
  conv =>
    rhs
    whnf
  trace_state
  apply Nat.add_comm x y

def f (x y z : Nat) : Nat :=
  y

example (x y : Nat) : f x (x + y + 0) y = y + x := by
  conv =>
    lhs
    arg 2
    whnf
  trace_state
  simp [f]
  apply Nat.add_comm

example (x y : Nat) : f x (x + y + 0) y = y + x := by
  conv =>
    lhs
    arg 2
    change x + y
    trace_state
    rw [Nat.add_comm]

example : id (fun x y => 0 + x + y) = Nat.add := by
  conv =>
    lhs
    arg 1
    ext a b
    trace_state
    rw [Nat.zero_add]
    trace_state

example : id (fun x y => 0 + x + y) = Nat.add := by
  conv =>
    lhs
    arg 1
    intro a b
    rw [Nat.zero_add]

example : id (fun x y => 0 + x + y) = Nat.add := by
  conv =>
    enter [1, 1, a, b]
    trace_state
    rw [Nat.zero_add]

example (p : Nat → Prop) (h : ∀ a, p a) : ∀ a, p (id (0 + a)) := by
  conv =>
    intro x
    trace_state
    arg 1
    trace_state
    simp only [id]
    trace_state
    rw [Nat.zero_add]
  exact h

example (p : Prop) (x : Nat) : (x = x → p) → p := by
  conv =>
    congr
    . trace_state
      congr
      . simp
  trace_state
  conv =>
    lhs
    simp
  intros
  assumption

example : (fun x => 0 + x) = id := by
  conv =>
    lhs
    tactic => funext x
    trace_state
    rw [Nat.zero_add]

example (p : Prop) (x : Nat) : (x = x → p) → p := by
  conv =>
    apply implies_congr
    . apply implies_congr
      simp
  trace_state
  conv =>
    lhs
    simp
  intros; assumption

example (x y : Nat) (f : Nat → Nat → Nat) (g : Nat → Nat) (h₁ : ∀ z, f z z = z) (h₂ : ∀ x y, f (g x) (g y) = y) : f (g (0 + y)) (f (g x) (g (0 + x))) = x := by
  conv =>
    pattern _ + _
    apply Nat.zero_add
  trace_state
  conv =>
    pattern 0 + _
    apply Nat.zero_add
  trace_state
  simp [h₁, h₂]

example (x y : Nat) (h : y = 0) : x + ((y + x) + x) = x + (x + x) := by
  conv =>
    lhs
    rhs
    lhs
    trace_state
    rw [h, Nat.zero_add]

example (p : Nat → Prop) (x y : Nat) (h : y = 0) : p (y + x) := by
  conv => lhs

example (p : Nat → Prop) (x y : Nat) (h : y = 0) : p (y + x) := by
  conv => arg 2

example (p : Prop) : p := by
  conv => rhs

example (p : Nat → Prop) (x y : Nat) (h1 : y = 0) (h2 : p x) : p (y + x) := by
  conv =>
    rhs
    trace_state
    rw [h1]
    apply Nat.zero_add
  exact h2
