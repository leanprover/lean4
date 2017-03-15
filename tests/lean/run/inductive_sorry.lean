inductive foo₁ (A : sorry → ℕ)
| mk : foo₁

inductive foo₂ : sorry → Type
| mk : foo₂ sorry

inductive foo₃
| mk : sorry → foo₃

structure foo₄ (A : sorry → ℕ) := (x : ℕ)
