open nat

inductive tree (A : Type) :=
leaf : A → tree A,
node : tree A → tree A → tree A

-- set_option elaborator.lift_coercions false

definition size {A : Type} (t : tree A) :nat:=
tree.rec (λ a, 1) (λ t₁ t₂ n₁ n₂, n₁ + n₂) t

--set_option elaborator.lift_coercions true

definition size2 {A : Type} (t : tree A) :nat:=
tree.rec (λ a, 1) (λ t₁ t₂ n₁ n₂, n₁ + n₂) t
