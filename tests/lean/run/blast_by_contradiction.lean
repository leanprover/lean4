constants P Q : Prop

namespace with_classical
open classical

example : Q → (Q → ¬ P → false) → P := by blast
example : Q → (Q → P → false) → ¬ P := by blast
end with_classical

namespace with_decidable
constant P_dec : decidable P
attribute P_dec [instance]

definition foo : Q → (Q → ¬ P → false) → P := by blast
example : Q → (Q → P → false) → ¬ P := by blast
end with_decidable
