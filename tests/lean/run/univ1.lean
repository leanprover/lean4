import logic

namespace S1
axiom I : Type
definition F (X : Type) : Type := (X → Prop) → Prop
axiom unfold.{l} : I.{l} → F I.{l}
axiom fold.{l}   : F I.{l} → I.{l}
axiom iso1 : ∀x, fold (unfold x) = x
end S1

namespace S2
universe u
axiom I : Type.{u}
definition F (X : Type) : Type := (X → Prop) → Prop
axiom unfold : I → F I
axiom fold   : F I → I
axiom iso1 : ∀x, fold (unfold x) = x
end S2


namespace S3
context
  hypothesis I : Type
  definition F (X : Type) : Type := (X → Prop) → Prop
  hypothesis unfold : I → F I
  hypothesis fold   : F I → I
  hypothesis iso1 : ∀x, fold (unfold x) = x
end
end S3
