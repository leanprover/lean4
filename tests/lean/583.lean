import algebra.group data.set
namespace group_hom
open algebra
-- ⁻¹ in eq.ops conflicts with group ⁻¹
-- open eq.ops
notation H1 ▸ H2 := eq.subst H1 H2
open set
open function
local attribute set [reducible]

section
variables {A B : Type}
variable [s1 : group A]
variable [s2 : group B]
include s1
include s2
variable f : A → B
definition is_hom := ∀ a b, f (a*b) = (f a)*(f b)
definition ker (Hom : is_hom f) : (set A) := {a : A | f a = 1}
theorem hom_map_id (f : A → B) (Hom : is_hom f) : f 1 = 1 :=
        have P : f 1 = (f 1) * (f 1), from
        calc f 1 = f (1*1) : mul_one
        ... = (f 1) * (f 1) : Hom,
        eq.symm (mul.right_inv (f 1) ▸ (mul_inv_eq_of_eq_mul P))

theorem hom_map_inv (Hom : is_hom f) (a : A) : f a⁻¹ = (f a)⁻¹ :=
        assert P : f 1 = 1, from hom_map_id f Hom,
        begin
          rewrite (eq.symm (mul.left_inv a)) at P,
          rewrite (Hom a⁻¹ a) at P,
        end
end
end group_hom
