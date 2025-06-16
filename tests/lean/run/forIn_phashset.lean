import Lean.Data.PersistentHashSet

open Lean

def sum (s : PHashSet Nat) : Nat := Id.run do
  let mut r := 0
  for a in s do
    r := r + a
  return r

def sumIf (s : PHashSet Nat) (p : Nat → Bool) : Nat := Id.run do
  let mut r := 0
  for a in s do
    unless p a do
      continue
    r := r + a
  return r

def mk [Hashable α] [BEq α] (f : Nat → α) (n : Nat) : PHashSet α := Id.run do
  let mut s := {}
  for i in [:n] do
    s := s.insert (f i)
  return s

/-- info: 45 -/
#guard_msgs in
#eval sum (mk id 10)

/-- info: 9900 -/
#guard_msgs in
#eval sum (mk (2*·) 100)

/-- info: 2450 -/
#guard_msgs in
#eval sumIf (mk id 100) (· % 2 == 0)
