
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
