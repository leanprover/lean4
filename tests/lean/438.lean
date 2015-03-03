import algebra.bundled
open algebra

attribute Group.struct [coercion]

section
  parameters {P₀ : Type} [P : group P₀]
  include P

  structure lambda_morphism := (comm : _ = _)

end
