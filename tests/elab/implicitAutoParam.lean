/-!
# `optParam` and `autoParam` in implicit binders

A default value or auto-param tactic on an implicit binder is only a fallback: the parameter is a
regular metavariable that unification may assign, and the fallback is used only if it is still
unassigned once everything else has been synthesized.
-/

inductive Color where
  | red
  | green

inductive Tagged : Color → Type where
  | mk : Tagged c

/-! ## `autoParam` -/

def tagged {c : Color := by exact .red} : Tagged c := .mk

/-- info: tagged {c : Color := by exact .red} : Tagged c -/
#guard_msgs in
#check tagged

-- Nothing determines `c`, so the tactic runs.
/-- info: @tagged Color.red : Tagged Color.red -/
#guard_msgs in
set_option pp.explicit true in
#check (tagged : Tagged _)

-- The expected type determines `c`, so the tactic does not run.
/-- info: @tagged Color.green : Tagged Color.green -/
#guard_msgs in
set_option pp.explicit true in
#check (tagged : Tagged .green)

-- The expected type of an argument determines it just as well.
def use (_ : Tagged .green) : Nat := 0

/-- info: use (@tagged Color.green) : Nat -/
#guard_msgs in
set_option pp.explicit true in
#check use tagged

-- Named arguments and `@` still work.
/-- info: @tagged Color.green : Tagged Color.green -/
#guard_msgs in
set_option pp.explicit true in
#check (tagged (c := .green))

/-- info: @tagged Color.green : Tagged Color.green -/
#guard_msgs in
set_option pp.explicit true in
#check @tagged .green

-- `..` suppresses the fallback, as it does for explicit binders.
/-- info: @tagged ?_ : Tagged ?_ -/
#guard_msgs in
set_option pp.explicit true in
set_option pp.mvars false in
#check (tagged ..)

/-! ## `optParam` -/

def otagged {c : Color := .red} : Tagged c := .mk

/-- info: otagged {c : Color := Color.red} : Tagged c -/
#guard_msgs in
#check otagged

/-- info: @otagged Color.red : Tagged Color.red -/
#guard_msgs in
set_option pp.explicit true in
#check (otagged : Tagged _)

/-- info: @otagged Color.green : Tagged Color.green -/
#guard_msgs in
set_option pp.explicit true in
#check (otagged : Tagged .green)

/-! ## Proof obligations -/

def firstOf (xs : List Nat) {h : xs ≠ [] := by simp} : Nat := xs.head h

/-- info: 1 -/
#guard_msgs in
#eval firstOf [1, 2, 3]

-- The tactic's own error is reported, not `don't know how to synthesize implicit argument`.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: unsolved goals
⊢ False
---
info: firstOf [] : Nat
-/
#guard_msgs in
#check firstOf []

-- An explicitly supplied proof suppresses the tactic.
/-- info: 7 -/
#guard_msgs in
#eval firstOf [7] (h := by simp)

/-! ## No spurious eta-expansion

A fallback on an implicit binder must not force eta-expansion, which would pin the parameter to the
fallback instead of leaving it to unification. An implicit binder with a fallback therefore behaves
exactly like a plain implicit binder here, while an explicit one still eta-expands.

The raw `autoParam` in the mismatch message is a pre-existing gap: only the signature delaborator
undoes the annotation, not the one for general `forall`s.
-/

def add3 (k : Nat) {n : Nat := by exact 3} : Nat := n + k
def add3' (k : Nat) (n : Nat := by exact 3) : Nat := n + k

/-- info: fun k => add3' k 3 : Nat → Nat -/
#guard_msgs in
#check (add3' : Nat → Nat)

/--
error: Type mismatch
  add3
has type
  Nat → {n : autoParam Nat add3._auto_1} → Nat
but is expected to have type
  Nat → Nat
-/
#guard_msgs in
#check (add3 : Nat → Nat)

/-! ## Metavariable aliases

Unification may not solve the parameter outright but merely alias it to another unassigned
metavariable, as with the `_` below. The fallback still applies, to that metavariable.
-/

def dim {n : Nat := by exact 3} (_v : Vector Nat n) : Nat := n

-- The argument determines `n`.
/-- info: 2 -/
#guard_msgs in
#eval dim #v[10, 20]

-- Nothing does, so the tactic runs and fills the `_` too.
/-- info: 3 -/
#guard_msgs in
#eval dim (Vector.replicate _ 0)

/-! ## Section variables -/

section
variable {k : Nat := by exact 9}

def useK : Nat × Nat := (k, k)

/-- error: cannot update binder annotation of variables with default values/tactics -/
#guard_msgs in
variable (k)

end

/-- info: useK {k : Nat := by exact 9} : Nat × Nat -/
#guard_msgs in
#check useK

/-- info: (9, 9) -/
#guard_msgs in
#eval useK

-- Defaults may refer to earlier parameters.
def pair {a : Nat := 1} {b : Nat := a + 1} : Nat × Nat := (a, b)

/-- info: (1, 2) -/
#guard_msgs in
#eval pair
