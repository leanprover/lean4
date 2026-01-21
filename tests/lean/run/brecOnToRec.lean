module
import all Lean.Elab.PreDefinition.Structural.BRecOnToRec

inductive N where
  | zero : N
  | succ : N → N

-- #check N.brecOn
-- #check N.rec
-- #print N.below

def N.id : N → N
  | N.zero => .zero
  | N.succ a => N.succ (N.id a)
termination_by structural n => n

/-- N.rec -/
#guard_msgs (substring := true) in #print N.id

set_option trace.Elab.definition.structural.brecOnToRec true in
def N.add : N → N → N
  | a, N.zero => a
  | a, N.succ b => N.succ (N.add a b)
termination_by structural _ n => n

/-- N.rec -/
#guard_msgs (substring := true) in #print N.add

inductive Tree α where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def Tree.size {α : Type} : Tree α → N
  | leaf _ => N.succ N.zero
  | node l r => N.add (Tree.size l) (Tree.size r)

/-- Tree.rec -/
#guard_msgs (substring := true) in #print Tree.size
