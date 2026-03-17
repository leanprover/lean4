example (b : Bool) : (if (if b then true else true) then 1 else 2) = 1 := by
  split
  next h =>
    guard_target =ₛ (if true = true then 1 else 2) = 1
    guard_hyp h : b = true
    simp
  next h =>
    guard_target =ₛ (if true = true then 1 else 2) = 1
    guard_hyp h : ¬b = true
    simp

example (b : Bool) : (if h : (if b then true else true) then 1 else 2) = 1 := by
  split
  next h' =>
    guard_target = (if h : true = true then 1 else 2) = 1
    guard_hyp h' : b = true
    simp
  next h' =>
    guard_target = (if h : true = true then 1 else 2) = 1
    guard_hyp h' : ¬b = true
    simp

opaque f (a : Nat) (h : a > 0) : Nat
axiom fax : f a h = a

example : (if h : (if true then a > 0 else False) then f a (by grind) else a) = a := by
  split
  next =>
    split
    next => simp [fax]
    next => simp
  next => simp

set_option backward.split false

example (b : Bool) : (if (if b then true else true) then 1 else 2) = 1 := by
  split
  next h =>
    guard_target =ₛ (if true = true then 1 else 2) = 1
    guard_hyp h : b = true
    simp
  next h =>
    guard_target =ₛ (if true = true then 1 else 2) = 1
    guard_hyp h : ¬b = true
    simp

example (b : Bool) : (if h : (if b then true else true) then 1 else 2) = 1 := by
  split
  next h' =>
    guard_target = (if h : true = true then 1 else 2) = 1
    guard_hyp h' : b = true
    simp
  next h' =>
    guard_target = (if h : true = true then 1 else 2) = 1
    guard_hyp h' : ¬b = true
    simp

example : (if h : (if true then a > 0 else False) then f a (by grind) else a) = a := by
  split
  next =>
    split
    next => simp [fax]
    next => simp
  next => simp
