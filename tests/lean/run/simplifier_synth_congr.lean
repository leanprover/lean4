open tactic

universe variable l
constants (ss₁ : Type.{l} → Type.{l})
          (ss₂ : Π {A : Type.{l}}, A → Type.{l})
          [sss₁ : ∀ T, subsingleton (ss₁ T)]
          [sss₂ : ∀ T (t : T), subsingleton (ss₂ t)]
          (A B : Type.{l}) (HAB : A = B)
          (ss_A : ss₁ A) (ss_B : ss₁ B)
          (a₁ a₁' a₂ a₂' : A)
          (H₁ : a₁ = a₁') (H₂ : a₂ = a₂')
          (ss_a₁ : ss₂ a₁)
          (ss_a₁' : ss₂ a₁')
          (ss_a₂ : ss₂ a₂)
          (ss_a₂' : ss₂ a₂')
          (f :  Π (X : Type.{l}) (ss_X : ss₁ X) (x₁ x₂ : X) (ss_x₁ : ss₂ x₁) (ss_x₂ : ss₂ x₂), Type.{l})

attribute [instance] sss₁
attribute [instance] sss₂

attribute [simp] HAB
attribute [simp] H₁
attribute [simp] H₂

example : f A ss_A a₁ a₂ ss_a₁ ss_a₂ = f A ss_A a₁' a₂' ss_a₁' ss_a₂' := by simp

attribute [reducible] noncomputable definition c₁' := a₁'
attribute [reducible] noncomputable definition c₂' := a₂'

example : f A ss_A a₁' a₂' ss_a₁' ss_a₂' = f A ss_A c₁' c₂' ss_a₁' ss_a₂' := by simp
example : f A ss_A a₁ a₂ ss_a₁ ss_a₂ = f A ss_A c₁' c₂' ss_a₁' ss_a₂' := by simp
