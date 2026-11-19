module

import Lean

/-! Regression tests for the Prod.map cases of #14496. -/

inductive Typ where
  | int
  | rcrd (fields : List (Typ × String))

def Typ.simplify : Typ → Typ
  | .int => .int
  | .rcrd fields => .rcrd (fields.map (·.map (·.simplify) id))
decreasing_by
  induction fields <;> grind

def Typ.simplifyComposed : Typ → Typ
  | .int => .int
  | .rcrd fields =>
    .rcrd (fields.map (fun p => (p.map id id).map (·.simplifyComposed) id))
decreasing_by
  induction fields <;> grind

inductive Typ2 where
  | int
  | rcrd (hd : Typ2 × String) (fields : List (Typ2 × String))

def Typ2.simplify : Typ2 → Typ2
  | .int => .int
  | .rcrd hd fields =>
    .rcrd (hd.map (·.simplify) id) (fields.map (·.map (·.simplify) id))
decreasing_by
  · grind
  · induction fields <;> grind

def Typ2.simplifyPair : Typ2 → Typ2
  | .int => .int
  | .rcrd (tp, name) fields =>
    .rcrd ((tp, name).map (·.simplifyPair) id) (fields.map (·.map (·.simplifyPair) id))
decreasing_by
  · grind
  · induction fields <;> grind
