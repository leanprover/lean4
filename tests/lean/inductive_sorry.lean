inductive foo (A : sorry → ℕ)
| mk : foo

inductive foo : sorry → ℕ
| mk : foo 0

inductive foo
| mk : sorry → foo

structure foo (A : sorry → ℕ) := (x : ℕ)

structure foo : Type := (x : bool → sorry)
