inductive F: Prop where
  | base
  | step (fn: Nat → F)

-- set_option trace.Meta.IndPredBelow.search true
set_option pp.proofs true

def F.asdf1 : (f : F) → True
  | base => trivial
  | step f => F.asdf1 (f 0)
termination_by structural f => f

def TTrue (_f : F) := True

def F.asdf2 : (f : F) → TTrue f
  | base => trivial
  | step f => F.asdf2 (f 0)
termination_by structural f => f

inductive ITrue (f : F) : Prop where | trivial

def F.asdf3 : (f : F) → ITrue f
  | base => .trivial
  | step f => F.asdf3 (f 0)
termination_by structural f => f
