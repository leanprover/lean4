
namespace Ex1
opaque f : Nat → Nat
axiom fax : f x ≥ f (f x)

grind_pattern fax => f x where
  depth x < 2

/--
trace: [grind.ematch.instance] fax: f a ≥ f (f a)
[grind.ematch.instance] fax: f (f a) ≥ f (f (f a))
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example (h : f a = 0) : False := by
  grind
end Ex1

namespace Ex2
opaque f : Nat → Nat
axiom fax : f x ≥ f (f x)

grind_pattern fax => f x where
  is_ground x
  depth x < 3

opaque b : Nat

-- Theorems containing `a` should not be instantiate since it is a local variable
/--
trace: [grind.ematch.instance] fax: f b ≥ f (f b)
[grind.ematch.instance] fax: f (f b) ≥ f (f (f b))
[grind.ematch.instance] fax: f (f (f b)) ≥ f (f (f (f b)))
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example : f a = 0 → f b = 0 → False := by
  grind
end Ex2

namespace Ex3
def f {α : Type} : α → α → α := fun x _ => x
axiom fax [LE α] (x : α) : f x x ≥ f (f x x) (f x x)

grind_pattern fax => f x x where
  size x < 5

/--
trace: [grind.ematch.instance] fax: f a a ≥ f (f a a) (f a a)
[grind.ematch.instance] fax: f (f a a) (f a a) ≥ f (f (f a a) (f a a)) (f (f a a) (f a a))
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example (a b : List (List Nat)) : f a a = b → False := by
  grind
end Ex3

namespace Ex4
def f {α : Type} : α → α → α := fun x _ => x
axiom fax [LE α] (x : α) : f x x ≥ f (f x x) (f x x)

grind_pattern fax => f x x where
  gen < 2

/--
trace: [grind.ematch.instance] fax: f a a ≥ f (f a a) (f a a)
[grind.ematch.instance] fax: f (f a a) (f a a) ≥ f (f (f a a) (f a a)) (f (f a a) (f a a))
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example (a b : List (List Nat)) : f a a = b → False := by
  grind
end Ex4


namespace Ex5
opaque f : Nat → Nat
axiom fax : f x ≥ f (f x)

grind_pattern fax => f x where
  max_insts < 4

/--
trace: [grind.ematch.instance] fax: f c ≥ f (f c)
[grind.ematch.instance] fax: f b ≥ f (f b)
[grind.ematch.instance] fax: f a ≥ f (f a)
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example : f a = 0 → f b = 0 → f c = 0 → False := by
  grind

end Ex5

namespace Ex6

opaque g : List Nat → Nat
opaque f : List Nat → List Nat
axiom gax (as : List Nat) : g as > g (f as)

grind_pattern gax => g as where
  as =?= _ :: _

/-- trace: [grind.ematch.instance] gax: g [1, 2, 3] > g (f [1, 2, 3]) -/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example (h : g [1, 2, 3] > 0) : False := by
  grind

end Ex6

namespace Ex7

opaque f {α : Type u} : List α × α → Nat
axiom fax : f x > 0

grind_pattern fax => f x where
  is_value x

/--
trace: [grind.ematch.instance] fax: f ([true], false) > 0
[grind.ematch.instance] fax: f ([1, 2], 4) > 0
[grind.ematch.instance] fax: f ([fun x => x], fun x => x) > 0
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example
    : f (as, bs) = f ([1], c) →
      f ([fun x : Nat => x], fun y => y) = d →
      f ([1, 2], 4) = f ([true], false) →
      False := by
  grind

end Ex7

namespace Ex8

opaque f {α : Type u} : List α × α → Nat
axiom fax : f x > 0

grind_pattern fax => f x where
  is_strict_value x

/--
trace: [grind.ematch.instance] fax: f ([true], false) > 0
[grind.ematch.instance] fax: f ([1, 2], 4) > 0
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example
    : f (as, bs) = f ([1], c) →
      f ([fun x : Nat => x], fun y => y) = d →
      f ([1, 2], 4) = f ([true], false) →
      False := by
  grind

end Ex8

namespace Ex9

opaque f : Nat → Nat → Nat
axiom fax : x ≠ y → f x y > 0

grind_pattern fax => f x y where
  guard x ≠ y

/--
trace: [grind.ematch.instance.delayed] `fax` waiting
      ¬x = y
-/
#guard_msgs (trace, drop error) in
example : f x y = 5 → False := by
 set_option trace.grind.ematch.instance true in
 set_option trace.grind.ematch.instance.delayed true in
 grind


/--
trace: [grind.ematch.instance.delayed] `fax` waiting
      ¬x = y
[grind.ematch.instance] fax: x ≠ y → f x y > 0
-/
#guard_msgs in
example : x ≠ y → f x y = 0 → False := by
 set_option trace.grind.ematch.instance true in
 set_option trace.grind.ematch.instance.delayed true in
 grind

end Ex9

namespace Ex10

opaque f : Nat → Nat → Nat
axiom fax : x = y → f x y > 0

grind_pattern fax => f x y where
  check x = y

/--
trace: [grind.ematch.instance.delayed] `fax` waiting
      x = y
[grind.split] x = y, generation: 1
[grind.ematch.instance] fax: x = y → f x y > 0
-/
#guard_msgs (drop error, trace) in
example : f x y = 0 → False := by
 set_option trace.grind.ematch.instance true in
 set_option trace.grind.ematch.instance.delayed true in
 set_option trace.grind.split true in
 grind

end Ex10

namespace Ex11

opaque f : Nat → Nat → Nat
axiom fax : x = y → f x y > 0

grind_pattern fax => f x y where
  guard x = y

-- `grind` will not case-split on `x = y` since `guard` was used instead of `check`
/--
trace: [grind.ematch.instance.delayed] `fax` waiting
      x = y
-/
#guard_msgs (drop error, trace) in
example : f x y = 0 → False := by
 set_option trace.grind.ematch.instance true in
 set_option trace.grind.ematch.instance.delayed true in
 set_option trace.grind.split true in
 grind

end Ex11

namespace Ex12

opaque f : Nat → Nat
axiom fMono : x ≤ y → f x ≤ f y
grind_pattern fMono => f x, f y

-- Many unnecessary instances were generated.
/--
trace: [grind.ematch.instance] fMono: f a ≤ b → f (f a) ≤ f b
[grind.ematch.instance] fMono: f a ≤ c → f (f a) ≤ f c
[grind.ematch.instance] fMono: f a ≤ a → f (f a) ≤ f a
[grind.ematch.instance] fMono: f a ≤ f (f a) → f (f a) ≤ f (f (f a))
[grind.ematch.instance] fMono: f a ≤ f a → f (f a) ≤ f (f a)
[grind.ematch.instance] fMono: f (f a) ≤ b → f (f (f a)) ≤ f b
[grind.ematch.instance] fMono: f (f a) ≤ c → f (f (f a)) ≤ f c
[grind.ematch.instance] fMono: f (f a) ≤ a → f (f (f a)) ≤ f a
[grind.ematch.instance] fMono: f (f a) ≤ f (f a) → f (f (f a)) ≤ f (f (f a))
[grind.ematch.instance] fMono: f (f a) ≤ f a → f (f (f a)) ≤ f (f a)
[grind.ematch.instance] fMono: a ≤ b → f a ≤ f b
[grind.ematch.instance] fMono: a ≤ c → f a ≤ f c
[grind.ematch.instance] fMono: a ≤ a → f a ≤ f a
[grind.ematch.instance] fMono: a ≤ f (f a) → f a ≤ f (f (f a))
[grind.ematch.instance] fMono: a ≤ f a → f a ≤ f (f a)
[grind.ematch.instance] fMono: c ≤ b → f c ≤ f b
[grind.ematch.instance] fMono: c ≤ c → f c ≤ f c
[grind.ematch.instance] fMono: c ≤ a → f c ≤ f a
[grind.ematch.instance] fMono: c ≤ f (f a) → f c ≤ f (f (f a))
[grind.ematch.instance] fMono: c ≤ f a → f c ≤ f (f a)
[grind.ematch.instance] fMono: b ≤ b → f b ≤ f b
[grind.ematch.instance] fMono: b ≤ c → f b ≤ f c
[grind.ematch.instance] fMono: b ≤ a → f b ≤ f a
[grind.ematch.instance] fMono: b ≤ f (f a) → f b ≤ f (f (f a))
[grind.ematch.instance] fMono: b ≤ f a → f b ≤ f (f a)
-/
#guard_msgs in
example : f b = f c → a ≤ f a → f (f a) ≤ f (f (f a)) := by
  set_option trace.grind.ematch.instance true in
  grind

end Ex12

namespace Ex13
-- Same example but using constraints to control theorem/axiom instantiation
opaque f : Nat → Nat
axiom fMono : x ≤ y → f x ≤ f y
grind_pattern fMono => f x, f y where
  guard x ≤ y
  x =/= y

/--
trace: [grind.ematch.instance] fMono: a ≤ f a → f a ≤ f (f a)
[grind.ematch.instance] fMono: f a ≤ f (f a) → f (f a) ≤ f (f (f a))
[grind.ematch.instance] fMono: a ≤ f (f a) → f a ≤ f (f (f a))
-/
#guard_msgs in
example : f b = f c → a ≤ f a → f (f a) ≤ f (f (f a)) := by
  set_option trace.grind.ematch.instance true in
  grind

end Ex13

namespace Ex14

opaque f : Nat → Nat
axiom fax : f x ≤ x
grind_pattern fax => f x where
  not_value x

/-- trace: [grind.ematch.instance] fax: f x ≤ x -/
#guard_msgs in
example : f 1 = a → f 2 = b → x ≤ y → f x ≤ y := by
  set_option trace.grind.ematch.instance true in
  grind

end Ex14
