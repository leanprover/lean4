mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  decreasing_by
    sorry

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
  decreasing_by
    sorry
end

/-- info: isEven.eq_1 : isEven 0 = true -/
#guard_msgs in
#check @isEven.eq_1
/-- info: isEven.eq_2 : ∀ (n : Nat), isEven n.succ = isOdd n -/
#guard_msgs in
#check @isEven.eq_2
/--
info: isEven.eq_def : ∀ (x : Nat),
  isEven x =
    match x with
    | 0 => true
    | n.succ => isOdd n
-/
#guard_msgs in
#check @isEven.eq_def

/-- info: isEven.eq_2 : ∀ (n : Nat), isEven n.succ = isOdd n -/
#guard_msgs in
#check @isEven.eq_2

/-- info: isOdd.eq_1 : isOdd 0 = false -/
#guard_msgs in
#check @isOdd.eq_1

/-- info: isOdd.eq_2 : ∀ (n : Nat), isOdd n.succ = isEven n -/
#guard_msgs in
#check @isOdd.eq_2

/--
info: isOdd.eq_def : ∀ (x : Nat),
  isOdd x =
    match x with
    | 0 => false
    | n.succ => isEven n
-/
#guard_msgs in
#check @isOdd.eq_def

/-- info: isEven.eq_2 : ∀ (n : Nat), isEven n.succ = isOdd n -/
#guard_msgs in
#check @isEven.eq_2
