/-!
Tests around the special case of well-founded recursion on Nat.
-/

namespace T1

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
def foo : List α → Nat
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
