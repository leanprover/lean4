import Lean
open List Lean

example (l : List α) (h : length l = length l) : length (a::l) = length (a::l) :=
  congrArg (·+1) h

elab:max "(" tm:term ":)" : term => Elab.Term.elabTerm tm none

example (l : List α) (h : length l = length l) : length (a::l) = length (a::l) :=
  (congrArg (·+1) h :)

example (l : List α) (h : length l = length l) : length (a::l) = length (a::l) :=
  have := congrArg (·+1) h; this

example (l : List α) (h : length l = length l) : length (a::l) = length (a::l) := by
  have := congrArg (·+1) h; exact this
