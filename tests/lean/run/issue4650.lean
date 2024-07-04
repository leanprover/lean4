
inductive Foo1 : Sort (max 1 u) where
  | intro: (h : Nat → Foo1) → Foo1

/-- info: Foo1.below.{u_1, u} {motive : Foo1 → Type u_1} (t : Foo1) : Sort (max (u_1 + 1) u) -/
#guard_msgs in
#check Foo1.below

inductive Foo2 : Sort (max u 1) where
  | intro: (h : Nat → Foo2) → Foo2

/-- info: Foo2.below.{u_1, u} {motive : Foo2 → Type u_1} (t : Foo2) : Sort (max (u_1 + 1) u 1) -/
#guard_msgs in
#check Foo2.below

inductive Foo3 : Sort (u+1) where
  | intro: (h : Nat → Foo3) → Foo3

/-- info: Foo3.below.{u_1, u} {motive : Foo3 → Type u_1} (t : Foo3) : Type (max u_1 u) -/
#guard_msgs in
#check Foo3.below

inductive Foo4 : Sort (max 1 u) where
  | intro: Foo4 → Foo4

/-- info: Foo4.below.{u_1, u} {motive : Foo4 → Sort u_1} (t : Foo4) : Sort (max 1 u_1) -/
#guard_msgs in
#check Foo4.below

inductive Foo5 : Sort (max u 1) where
  | intro: Foo5 → Foo5

/-- info: Foo5.below.{u_1, u} {motive : Foo5 → Sort u_1} (t : Foo5) : Sort (max 1 u_1) -/
#guard_msgs in
#check Foo5.below

inductive Foo6 : Sort (u+1) where
  | intro: Foo6 → Foo6

/-- info: Foo6.below.{u_1, u} {motive : Foo6 → Sort u_1} (t : Foo6) : Sort (max 1 u_1) -/
#guard_msgs in
#check Foo6.below
