import standard

namespace S1
hypothesis I : Type
definition F (X : Type) : Type := (X → Prop) → Prop
hypothesis unfold.{l} : I.{l} → F I.{l}
hypothesis fold.{l}   : F I.{l} → I.{l}
hypothesis iso1 : ∀x, fold (unfold x) = x
end

namespace S2
universe u
hypothesis I : Type.{u}
definition F (X : Type) : Type := (X → Prop) → Prop
hypothesis unfold : I → F I
hypothesis fold   : F I → I
hypothesis iso1 : ∀x, fold (unfold x) = x
end


namespace S3
section
  hypothesis I : Type
  definition F (X : Type) : Type := (X → Prop) → Prop
  hypothesis unfold : I → F I
  hypothesis fold   : F I → I
  hypothesis iso1 : ∀x, fold (unfold x) = x
end
end
