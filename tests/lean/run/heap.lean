constant heap   : Type
constant ptr    : Type
constant val    : Type
constant pt     : ptr → val → heap
constant hunion : heap → heap → heap
constant is_def : heap → Prop

infix `∙`:60 := hunion
infix `↣`:70 := pt

/-
constant hunion_is_assoc : is_associative heap hunion
constant hunion_is_comm  : is_commutative heap hunion
attribute [instance] hunion_is_comm hunion_is_assoc

axiom noalias : ∀ (h : heap) (y₁ y₂ : ptr) (w₁ w₂ : val), is_def (h ∙ y₁ ↣ w₁ ∙ y₂ ↣ w₂) → y₁ ≠ y₂

-/

-- set_option profiler true

lemma ex
(h₁ h₂ : heap) (x₁ x₂ x₃ x₄ : ptr) (v₁ v₂ v₃ : val)
(hcomm    : ∀ x y, x ∙ y = y ∙ x)
(hassoc   : ∀ x y z, (x ∙ y) ∙ z = x ∙ (y ∙ z))
(hnoalias : ∀ h y₁ y₂ w₁ w₂, is_def (h ∙ y₁ ↣ w₁ ∙ y₂ ↣ w₂) → y₁ ≠ y₂)
: is_def (h₁ ∙ (x₁ ↣ v₁ ∙ x₂ ↣ v₂) ∙ h₂ ∙ (x₃ ↣ v₃)) → x₁ ≠ x₃ ∧ x₁ ≠ x₂ ∧ x₂ ≠ x₃ :=
begin [smt]
  intros,
  smt_tactic.add_lemmas_from_facts,
  iterate { ematch }
end
