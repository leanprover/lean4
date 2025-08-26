/-!
Tests for `partial_fixpoint` with explicit proofs
-/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def nullary (x : Nat) : Option Unit := nullary (x + 1)
partial_fixpoint monotonicity sorry

-- Check for metavariables

set_option pp.mvars.anonymous false in
/--
error: don't know how to synthesize placeholder for argument `a`
context:
⊢ Lean.Order.monotone fun f x => f (x + 1)
-/
#guard_msgs in
def nullarya (x : Nat) : Option Unit := nullarya (x + 1)
partial_fixpoint monotonicity id _

def nullaryb (x : Nat) : Option Unit := nullaryb (x + 1)
partial_fixpoint monotonicity fun _ _ a _ => a _

/-- info: nullaryb.eq_1 (x : Nat) : nullaryb x = nullaryb (x + 1) -/
#guard_msgs in #check nullaryb.eq_1

-- Type error

/--
error: Type mismatch
  ()
has type
  Unit
of sort `Type` but is expected to have type
  Lean.Order.monotone fun f x => f (x + 1)
of sort `Prop`
-/
#guard_msgs in
def nullary2 (x : Nat) : Option Unit := nullary2 (x + 1)
partial_fixpoint monotonicity ()


-- Good indent (bad indents are tested in partial_fixpoint_parseerrors

def nullary4 (x : Nat) : Option Unit := nullary4 (x + 1)
partial_fixpoint monotonicity
  fun _ _ a x => a (x + 1)


-- Tactics

/--
info: Try this:
  exact fun x y a x => a (x + 1)
-/
#guard_msgs in
def nullary6 (x : Nat) : Option Unit := nullary6 (x + 1)
partial_fixpoint monotonicity by
  exact?

#guard_msgs in
def nullary7 (x : Nat) : Option Unit := nullary7 (x + 1)
partial_fixpoint monotonicity by
  apply Lean.Order.monotone_of_monotone_apply
  intro y
  apply Lean.Order.monotone_apply
  apply Lean.Order.monotone_id

-- Mutual

mutual

def mutual1 (x : Nat) : Option Unit := mutual2 (x + 1)
partial_fixpoint monotonicity fun _ _ a x => a.2 (x + 1)

def mutual2 (x : Nat) : Option Unit := mutual1 (x + 1)
partial_fixpoint monotonicity fun _ _ a x => a.1 (x + 1)

end
