import algebra.group data.set
namespace group_hom
open algebra
-- ⁻¹ in eq.ops conflicts with group ⁻¹
-- open eq.ops
open set
open function
local attribute set [reducible]
structure is_subgroup [class] {A : Type} (H : set A) : Type

section
variables {A B : Type}
variable [s1 : group A]
variable [s2 : group B]
include s1
include s2
definition is_hom (f : A → B) := ∀ a b, f (a*b) = (f a)*(f b)

variable f : A → B
variable Hom : is_hom f
definition ker : set A := λ a, (f a) = 1

lemma ker.has_one (Hom : is_hom f) : 1 ∈ ker f := sorry
theorem hom_map_one : f 1 = 1 := sorry
theorem hom_map_mul_closed (Hom : is_hom f) (H : set A) : unit :=
sorry

variable {H : set A}
variable [is_subgH : is_subgroup H]
include is_subgH
end
end group_hom
