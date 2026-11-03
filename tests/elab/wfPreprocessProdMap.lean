import Lean

inductive Typ where
  | int
  | rcrd (fields : List (Typ × String))

def Typ.simplify : Typ → Typ
  | .int => .int
  | .rcrd fields => .rcrd (fields.map (·.map (·.simplify) id))
decreasing_by
  induction fields
  · grind
  · grind
