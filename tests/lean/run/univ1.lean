import logic

namespace S1
axiom I : Type
definition F (X : Type) : Type := (X → Prop) → Prop
axiom unfoldd.{l} : I.{l} → F I.{l}
axiom foldd.{l}   : F I.{l} → I.{l}
axiom iso1 : ∀x, foldd (unfoldd x) = x
end S1

namespace S2
universe u
axiom I : Type.{u}
definition F (X : Type) : Type := (X → Prop) → Prop
axiom unfoldd : I → F I
axiom foldd   : F I → I
axiom iso1 : ∀x, foldd (unfoldd x) = x
end S2


namespace S3
section
  hypothesis I : Type
  definition F (X : Type) : Type := (X → Prop) → Prop
  hypothesis unfoldd : I → F I
  hypothesis foldd   : F I → I
  hypothesis iso1 : ∀x, foldd (unfoldd x) = x
end
end S3
