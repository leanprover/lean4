set_option pp.universes true

inductive Foo1 : Sort (max 1 u) where
  | intro: (h : Nat → Foo1) → Foo1

/--
info: Foo1.below.{u_1, u} {motive : Foo1.{u} → Sort u_1} (t : Foo1.{u}) : Sort (max (max 1 u) u_1)
-/
#guard_msgs in
#check Foo1.below

inductive Foo2 : Sort (max u 1) where
  | intro: (h : Nat → Foo2) → Foo2

/--
info: Foo2.below.{u_1, u} {motive : Foo2.{u} → Sort u_1} (t : Foo2.{u}) : Sort (max (max u 1) u_1)
-/
#guard_msgs in
#check Foo2.below

inductive Foo3 : Sort (u+1) where
  | intro: (h : Nat → Foo3) → Foo3

/-- info: Foo3.below.{u_1, u} {motive : Foo3.{u} → Sort u_1} (t : Foo3.{u}) : Sort (max (u + 1) u_1) -/
#guard_msgs in
#check Foo3.below

inductive Foo4 : Sort (max 1 u) where
  | intro: Foo4 → Foo4

/-- info: Foo4.below.{u_1, u} {motive : Foo4.{u} → Sort u_1} (t : Foo4.{u}) : Sort (max 1 u_1) -/
#guard_msgs in
#check Foo4.below

inductive Foo5 : Sort (max u 1) where
  | intro: Foo5 → Foo5

/-- info: Foo5.below.{u_1, u} {motive : Foo5.{u} → Sort u_1} (t : Foo5.{u}) : Sort (max 1 u_1) -/
#guard_msgs in
#check Foo5.below

inductive Foo6 : Sort (u+1) where
  | intro: Foo6 → Foo6

/-- info: Foo6.below.{u_1, u} {motive : Foo6.{u} → Sort u_1} (t : Foo6.{u}) : Sort (max 1 u_1) -/
#guard_msgs in
#check Foo6.below
