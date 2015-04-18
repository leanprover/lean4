import logic data.nat
open eq.ops nat

inductive tree (A : Type) :=
| leaf : A → tree A
| node : tree A → tree A → tree A

namespace tree

definition height {A : Type} (t : tree A) : nat :=
tree.rec_on t
  (λ a, zero)
  (λ t₁ t₂ h₁ h₂, succ (max h₁ h₂))

definition height_lt {A : Type} : tree A → tree A → Prop :=
inv_image lt (@height A)

definition height_lt.wf (A : Type) : well_founded (@height_lt A) :=
inv_image.wf height lt.wf

theorem height_lt.node_left {A : Type} (t₁ t₂ : tree A) : height_lt t₁ (node t₁ t₂) :=
lt_succ_of_le (le_max_left (height t₁) (height t₂))

theorem height_lt.node_right {A : Type} (t₁ t₂ : tree A) : height_lt t₂ (node t₁ t₂) :=
lt_succ_of_le (le_max_right (height t₁) (height t₂))

theorem height_lt.trans {A : Type} : transitive (@height_lt A) :=
inv_image.trans lt height @lt.trans

example : height_lt (leaf 2) (node (leaf 1) (leaf 2)) :=
!height_lt.node_right

example : height_lt  (leaf 2) (node (node (leaf 1) (leaf 2)) (leaf 3)) :=
height_lt.trans !height_lt.node_right !height_lt.node_left

end tree
