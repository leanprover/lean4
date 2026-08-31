/-!
# Tests of `pp.universe` option
-/

/-!
This used to print `Iff p q`
-/
/-- info: p ↔ q : Prop -/
#guard_msgs in
set_option pp.universes true in
variable (p q : Prop) in
#check p ↔ q

/-!
These used to print `Nat.succ n`
-/
/-- info: n.succ : Nat -/
#guard_msgs in
set_option pp.universes true in
variable (n : Nat) in
#check Nat.succ n
/-- info: n.succ : Nat -/
#guard_msgs in
set_option pp.universes true in
set_option pp.explicit true in
variable (n : Nat) in
#check Nat.succ n
