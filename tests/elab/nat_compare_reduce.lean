module

/-!
Checks that `compare` on `Nat`, whose compiled implementation is an `@[extern]` function, still
reduces in the kernel and in the elaborator from another module, and agrees with the interpreter.
-/

example : compare 3 5 = .lt := rfl
example : compare 5 5 = .eq := rfl
example : compare 5 3 = .gt := rfl

example : compare (2^64) (2^64 + 1) = .lt := by decide
example : compare (2^64) (2^64) = .eq := by decide
example : compare (2^64 + 1) (2^64) = .gt := by decide +kernel

example : compare (2^63 - 1) (2^63) = .lt := by decide +kernel

#guard compare 3 5 == .lt
#guard compare (2^64) (2^64) == .eq
#guard compare (2^70) 3 == .gt
#guard compare 3 (2^70) == .lt
