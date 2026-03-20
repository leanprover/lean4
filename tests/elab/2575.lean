structure AtLeastThirtySeven where
  val : Nat
  le : 37 ≤ val

theorem AtLeastThirtySeven.lt (x : AtLeastThirtySeven) : 36 < x.val := x.le

/--
info: theorem AtLeastThirtySeven.le : ∀ (self : AtLeastThirtySeven), 37 ≤ self.val :=
fun self => self.2
-/
#guard_msgs in
#print AtLeastThirtySeven.le
