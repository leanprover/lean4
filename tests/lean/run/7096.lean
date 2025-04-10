/-!
# Normalization of imax 1 u

https://github.com/leanprover/lean4/issues/7096

Universe levels of the form `imax 1 u` should normalize to `u`.
-/

example (α : Sort u) : Sort u := Unit → α
