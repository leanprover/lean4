/-!
Tests for the `rw` tactic in `sym =>` mode.
`rw` only rewrites the goal target; in `sym =>` mode hypotheses are never modified.
-/

opaque myP : Nat → Prop
opaque myQ : Nat → Prop
opaque myF : Nat → Nat
opaque myG : Nat → Nat

axiom myF_eq (x : Nat) : myF x = myG x
axiom myP_iff (x : Nat) : myP x ↔ myQ x
axiom myF_eq_cond (x : Nat) : myP x → myF x = myG x

/-! Basic rewrite with a local hypothesis -/

/--
trace: case grind
a b : Nat
h : a = b
h' : myP b
⊢ myP b
-/
#guard_msgs in
example (a b : Nat) (h : a = b) (h' : myP b) : myP a := by
  sym =>
    rw [h]
    show_goals
    exact h'

/-! Reverse direction -/

/--
trace: case grind
a b : Nat
h : a = b
h' : myP a
⊢ myP a
-/
#guard_msgs in
example (a b : Nat) (h : a = b) (h' : myP a) : myP b := by
  sym =>
    rw [← h]
    show_goals
    exact h'

/-! Global theorem with universally quantified variables -/

/--
trace: case grind
a : Nat
h : myP (myG a)
⊢ myP (myG a)
-/
#guard_msgs in
example (a : Nat) (h : myP (myG a)) : myP (myF a) := by
  sym =>
    rw [myF_eq]
    show_goals
    exact h

/-! Multiple rules -/

/--
trace: case grind
a b : Nat
h : a = b
h' : myP (myG b)
⊢ myP (myG b)
-/
#guard_msgs in
example (a b : Nat) (h : a = b) (h' : myP (myG b)) : myP (myF a) := by
  sym =>
    rw [myF_eq, h]
    show_goals
    exact h'

/-! Goal closed by reflexivity after rewriting -/

example (a b : Nat) (h : a = b) : myF a = myF b := by
  sym =>
    rw [h]

/-! Iff rewrite -/

/--
trace: case grind
a : Nat
h : myQ a
⊢ myQ a
-/
#guard_msgs in
example (a : Nat) (h : myQ a) : myP a := by
  sym =>
    rw [myP_iff]
    show_goals
    exact h

/-! Conditional rewrite: undischarged premise becomes a new goal -/

/--
trace: case grind
a : Nat
h : myP a
h' : myP (myG a)
⊢ myP (myG a)

case grind
a : Nat
h : myP a
h' : myP (myG a)
⊢ myP a
-/
#guard_msgs in
example (a : Nat) (h : myP a) (h' : myP (myG a)) : myP (myF a) := by
  sym =>
    rw [myF_eq_cond a]
    show_goals
    exact h'
    exact h

/-! Reducible definitions in the rewrite rule are unfolded before matching -/

@[reducible] def myH (x : Nat) : Nat := myF x

axiom myH_eq (x : Nat) : myH x = myG x

/--
trace: case grind
a : Nat
h : myP (myG a)
⊢ myP (myG a)
-/
#guard_msgs in
example (a : Nat) (h : myP (myG a)) : myP (myF a) := by
  sym =>
    rw [myH_eq] -- lhs `myH ?x` must match `myF a` after unfolding `myH`
    show_goals
    exact h

/-! The result is properly normalized: `grind` can consume it via `finish` -/

example (a b : Nat) (h : a = b) (h' : myP b) : myP a := by
  sym =>
    rw [h]
    finish

/-! Error: no occurrence of the pattern -/

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  myG ?x✝
in the target expression
  myP a

case grind
a : Nat
h : myP a
⊢ myP a
-/
#guard_msgs in
example (a : Nat) (h : myP a) : myP a := by
  sym =>
    rw [(myF_eq · |>.symm)]
    exact h

/-! Error: `rw` is only available in `sym =>` mode -/

/--
error: tactic is only available in `sym =>` mode
-/
#guard_msgs in
example (a b : Nat) (h : a = b) (h' : myP b) : myP a := by
  grind => rw [h]
