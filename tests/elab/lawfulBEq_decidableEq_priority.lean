/-!
`LawfulBEq α` for a type with `DecidableEq α` must be found through `instLawfulBEq`, not through
the larger instance terms that go through `Ord` and the order classes. With the larger terms, a
goal with twelve `∈` tests exceeds `synthInstance.maxSize`.
-/

def xs : List Nat := [1, 2, 3]

example (op : Nat) : Decidable
    (op ∈ xs ∧ op ∈ xs ∧ op ∈ xs ∧ op ∈ xs ∧ op ∈ xs ∧ op ∈ xs ∧
     op ∈ xs ∧ op ∈ xs ∧ op ∈ xs ∧ op ∈ xs ∧ op ∈ xs ∧ op ∈ xs) :=
  inferInstance

/-- info: instLawfulBEq -/
#guard_msgs in
#synth LawfulBEq Nat
