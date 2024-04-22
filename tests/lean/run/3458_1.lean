/- Ensure that turning off `autoPromoteIndices` stops indices
   from being promoted to parameters in inductive types.
   Because free variables aren't allowed in parameters of nested appearances,
   it is sometimes desirable for fixed indices to not be promoted to parameters.
   See `IInterp`.
   -/

set_option autoImplicit false
universe u v w

structure ISignature (I : Type u) : Type (max u v + 1) where
  symbols : I → Type v
  indices : {i : I} → symbols i → List I

inductive All {I : Type u} (P : I → Type v) : List I → Type (max u v) where
  | nil : All P []
  | cons {x xs}: P x → All P xs → All P (x :: xs)

set_option inductive.autoPromoteIndices false

inductive IInterp {I} (ζ : ISignature.{u,v} I) (P : I → Type w) : I → Type (max u v w) where
  | mk :{i : I} → (s : ζ.symbols i) → All P (ζ.indices s) → IInterp ζ P i

notation:max "I⟦ " ζ " ⟧" => IInterp ζ

inductive Iμ {I : Type u} (ζ : ISignature.{u,v} I) : I → Type (max u v) where
  | mk : (i : I) → I⟦ ζ ⟧ (Iμ ζ) i → Iμ ζ i
