-- Test [light] annotation
-- Remark: it will take some additional work to get ⁻¹ to rewrite well
-- when there is a proof obligation.
import algebra.simplifier algebra.field data.set data.finset
open algebra simplifier.ac
attribute neg [light 2]
attribute inv [light 2]

attribute add.right_inv [simp]
attribute add_neg_cancel_left [simp]

attribute mul.right_inv [simp]
attribute mul_inv_cancel_left [simp]

namespace ag
universe l
constants (A : Type.{l}) (s1 : add_comm_group A) (s2 : has_one A)
attribute s1 [instance]
attribute s2 [instance]
constants (x y z w v : A)

#simplify eq env 0 x + y + - x + -y + z + -z
#simplify eq env 0 -100 + -v + -v + x + -v + y + - x + -y + z + -z + v + v + v + 100
end ag

namespace mg
universe l
constants (A : Type.{l}) (s1 : comm_group A) (s2 : has_add A)
attribute s1 [instance]
attribute s2 [instance]
constants (x y z w v : A)

#simplify eq env 0 x⁻¹ * y⁻¹ * z⁻¹ * 100⁻¹ * x * y * z * 100

end mg

namespace s
open set
universe l
constants (A : Type.{l}) (x y z v w : set A)
attribute complement [light 1]

-- TODO(dhs, leo): Where do we put this group of simp rules?
attribute union_comp_self [simp]
lemma union_comp_self_left [simp] {X : Type} (s t : set X) : s ∪ (-s ∪ t)= univ := sorry

attribute union.comm [simp]
attribute union.assoc [simp]
attribute union.left_comm [simp]

#simplify eq env 0 x ∪ y ∪ z ∪ -x

attribute inter_comp_self [simp]
lemma inter_comp_self_left [simp] {X : Type} (s t : set X) : s ∩ (-s ∩ t)= empty := sorry

attribute inter.comm [simp]
attribute inter.assoc [simp]
attribute inter.left_comm [simp]

#simplify eq env 0 x ∩ y ∩ z ∩ -x

end s
