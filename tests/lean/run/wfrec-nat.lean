/-!
Tests around the special case of well-founded recursion on Nat.
-/

set_option warn.sorry false

namespace T1

@[semireducible]
def foo : List α → Nat
  | [] => 0
  | _::xs => 1 + (foo xs)
termination_by xs => xs.length

-- Closed terms should evaluate

example : foo ([] : List Unit) = 0 := rfl
example : foo ([] : List Unit) = 0 := by decide
example : foo ([] : List Unit) = 0 := by decide +kernel
example : foo [1,2,3,4,5] = 5 := rfl
example : foo [1,2,3,4,5] = 5 := by decide
example : foo [1,2,3,4,5] = 5 := by decide +kernel

-- Open terms should not (these wouldn't even without the provisions with `WellFounded.Nat.eager`,
-- the fuel does not line up)

example : foo (x::xs) = 1 + foo xs := by (fail_if_success rfl); simp [foo]
example : foo (x::y::z::xs) = 1+ (1+(1+ foo xs)) := by (fail_if_success rfl); simp [foo]

end T1

-- Variant where the fuel does not line up

namespace T2
@[semireducible] def foo : List α → Nat
  | [] => 0
  | _::xs => 1 + (foo xs)
termination_by xs => 2 * xs.length

example : foo ([] : List Unit) = 0 := rfl
example : foo ([] : List Unit) = 0 := by decide
example : foo ([] : List Unit) = 0 := by decide +kernel
example : foo [1,2,3,4,5] = 5 := rfl
example : foo [1,2,3,4,5] = 5 := by decide
example : foo [1,2,3,4,5] = 5 := by decide +kernel

-- Open terms should not (these wouldn't even without the provisions, the fuel does not line up)

example : foo (x::xs) = 1 + foo xs := by (fail_if_success rfl); simp [foo]
example : foo (x::y::z::xs) = 1+ (1 + ( 1+ foo xs)) := by (fail_if_success rfl); simp [foo]

end T2

-- Idiom to switch to `WellFounded.fix`

namespace T3
def foo : List α → Nat
  | [] => 0
  | _::xs => 1 + (foo xs)
termination_by xs => (xs.length, 0)

example : foo ([] : List Unit) = 0 := by (fail_if_success rfl); simp [foo]
example : foo ([] : List Unit) = 0 := by (fail_if_success decide); simp [foo]
example : foo ([] : List Unit) = 0 := by (fail_if_success decide +kernel); simp [foo]
example : foo [1,2,3,4,5] = 5 := by (fail_if_success rfl); simp [foo]
example : foo [1,2,3,4,5] = 5 := by (fail_if_success decide); simp [foo]
example : foo [1,2,3,4,5] = 5 := by (fail_if_success decide +kernel); simp [foo]

-- Open terms should not (these wouldn't even without the provisions, the fuel does not line up)

example : foo (x::xs) = 1 + foo xs := by (fail_if_success rfl); simp [foo]
example : foo (x::y::z::xs) = 1+ (1 + ( 1+ foo xs)) := by (fail_if_success rfl); simp [foo]

end T3

-- Defeq between similar functions

namespace T4

@[semireducible] def foo (b : Bool) : Nat → Nat
  | 0 => 0
  | n+1 => 1 + foo b n
termination_by n => n

@[semireducible] def bar (b : Bool) : Nat → Nat
  | 0 => 0
  | n+1 => cond b 1 2 + bar b n
termination_by n => n

@[semireducible] def baz : Nat → Nat
  | 0 => 0
  | n+1 => 1 + baz n
termination_by n => n

example : foo true n = bar true n := rfl
example : foo true n = baz n := rfl
example : bar true n = baz n := rfl

end T4

-- For comparison: with wfrec

namespace T4wfrec

def foo (b : Bool) : Nat → Nat
  | 0 => 0
  | n+1 => 1 + foo b n
termination_by n => (n, 0)

def bar (b : Bool) : Nat → Nat
  | 0 => 0
  | n+1 => cond b 1 2 + bar b n
termination_by n => (n, 0)

def baz : Nat → Nat
  | 0 => 0
  | n+1 => 1 + baz n
termination_by n => (n, 0)

example : foo true n = bar true n := by (fail_if_success rfl); sorry
example : foo true n = baz n := by (fail_if_success rfl); sorry
example : bar true n = baz n := by (fail_if_success rfl); sorry

unseal foo bar baz

example : foo true n = bar true n := rfl
example : foo true n = baz n := rfl
example : bar true n = baz n := rfl

end T4wfrec
