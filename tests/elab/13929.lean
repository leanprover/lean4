module

/-! Private inductives should also generate open-able namespaces. -/

inductive T where
  | a
  | b

structure S where
  c : Unit
  d : Nat

open T
open S

def t1 : T := a
def t2 : T := b
def useProj (s : S) : Nat := s.d
