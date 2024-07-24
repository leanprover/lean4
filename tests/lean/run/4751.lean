inductive F: Prop where
  | base
  | step (fn: Nat → F)

-- set_option trace.Meta.IndPredBelow.search true
set_option pp.proofs true

/--
error: failed to infer structural recursion:
Cannot use parameter #1:
  could not solve using backwards chaining x✝¹ : F
  x✝ : x✝¹.below
  f : Nat → F
  a✝¹ : ∀ (a : Nat), (f a).below
  a✝ : Nat → True
  ⊢ True
-/
#guard_msgs in
def F.asdf1 : (f : F) → True
  | base => trivial
  | step f => F.asdf1 (f 0)
termination_by structural f => f


def TTrue (_f : F) := True

/--
error: failed to infer structural recursion:
Cannot use parameter #1:
  could not solve using backwards chaining x✝¹ : F
  x✝ : x✝¹.below
  f : Nat → F
  a✝¹ : ∀ (a : Nat), (f a).below
  a✝ : ∀ (a : Nat), TTrue (f a)
  ⊢ TTrue (f 0)
-/
#guard_msgs in
def F.asdf2 : (f : F) → TTrue f
  | base => trivial
  | step f => F.asdf2 (f 0)
termination_by structural f => f



inductive ITrue (f : F) : Prop where | trivial

/--
error: failed to infer structural recursion:
Cannot use parameter #1:
  could not solve using backwards chaining x✝¹ : F
  x✝ : x✝¹.below
  f : Nat → F
  a✝¹ : ∀ (a : Nat), (f a).below
  a✝ : ∀ (a : Nat), ITrue (f a)
  ⊢ ITrue (f 0)
-/
#guard_msgs in
def F.asdf3 : (f : F) → ITrue f
  | base => .trivial
  | step f => F.asdf3 (f 0)
termination_by structural f => f
