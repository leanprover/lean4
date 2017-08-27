universes u

class densely_ordered (α : Type u) [preorder α] : Prop :=
(dense : ∀ a c : α, a < c → ∃ b, a < b ∧ b < c)

-- [preorder α] should be instance implicit in all of the following:
#check @densely_ordered
#check @densely_ordered.mk
#check @densely_ordered.dense
