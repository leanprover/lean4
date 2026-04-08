inductive F: Prop where
  | base
  | step (fn: Nat → F)

-- set_option trace.Meta.IndPredBelow.search true
-- set_option trace.Elab.definition.structural true
set_option pp.proofs true

def F.asdf1 : (f : F) → True
  | base => trivial
  | step g => match g 1 with
    | base => trivial
    | step h => F.asdf1 (h 1)
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

-- Variants with extra arguments

inductive T : Prop → Prop where
  | base : T True
  | step (fn: Nat → T (True → p)) : T p

def T.foo {P : Prop} : (f : T P) → P
  | base => True.intro
  | step f => foo (f 0) True.intro
termination_by structural f => f

-- The same, but as a non-reflexive data type

inductive T' : Prop → Prop where
  | base : T' True
  | step (t : T' (True → p)) : T' p

def T'.foo {P : Prop} : (f : T' P) → P
  | base => True.intro
  | step t => foo t True.intro
termination_by structural f => f
