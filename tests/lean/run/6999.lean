/-!
# List index validity proofs synthesized by unification

https://github.com/leanprover/lean4/issues/6999

The tactic `get_elem_tactic` should not fail if invoked in a situation in which the necessary proof
of index validity has already been filled in during unification.
-/

set_option linter.unusedVariables false

axiom A : Type
axiom B : A → Type
axiom as : List A
axiom fn : (l : Nat) → (_ : l < as.length) → Option (B as[l])

#guard_msgs in
example {l : Nat} {llen : l < as.length} {b : B as[l]}
    (b_mem : b ∈ fn l llen) : True := trivial
