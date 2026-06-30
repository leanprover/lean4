/- Ensure that non-fixed indices don't get mistakenly promoted to parameter
   See issue `https://github.com/leanprover/lean4/issues/3458`
 -/

set_option autoImplicit false
universe u v w

structure ISignature (I : Type u) : Type (max u v + 1) where
  symbols : I → Type v
  indices : {i : I} → symbols i → List I

inductive All {I : Type u} (P : I → Type v) : List I → Type (max u v) where
  | nil : All P []
  | cons {x xs}: P x → All P xs → All P (x :: xs)

inductive Iμ {I : Type u} (ζ : ISignature.{u,v} I) : I → Type (max u v) where
  | mk : (i : I) → (s : ζ.symbols i) → All (Iμ ζ) (ζ.indices s) → Iμ ζ i
