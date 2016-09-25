open tactic

namespace synth_congr

universe variable l
constants (ss : Π {A : Type.{l}}, A → Type.{l})
          [ss_ss : ∀ T (t : T), subsingleton (ss t)]
          (A : Type.{l})
          (a₁ a₁' : A) (H₁ : a₁ = a₁')
          (ss₁ : ss a₁)
          (ss₁' : ss a₁')
          (f :  Π (X : Type.{l}) (x₁ : X) (ss_x₁ : ss x₁), Type.{l})

attribute [instance] ss_ss
attribute [simp] H₁

set_option trace.simplifier.subsingleton true
example : f A a₁ ss₁ = f A a₁' ss₁' := by simp

end synth_congr

namespace user_congr

universe variable l
constants (ss : Π {A : Type.{l}}, A → Type.{l})
          [ss_ss : ∀ T (t : T), subsingleton (ss t)]
          (A : Type.{l})
          (a₁ a₁' : A) (H₁ : a₁ = a₁')
          (ss₁ : ss a₁)
          (ss₁' : ss a₁')
          (f :  Π (X : Type.{l}) (x₁ : X) (ss_x₁ : ss x₁), Type.{l})
          (f_congr : Π (X : Type.{l}) (x₁ x₂ : X) (Hx : x₁ = x₂) (ss₁ : ss x₁), f X x₁ ss₁ = f X x₂ (eq.rec ss₁ Hx))

attribute [instance] ss_ss
attribute [simp] H₁
attribute [congr] f_congr


set_option trace.simplifier.subsingleton true
example : f A a₁ ss₁ = f A a₁' ss₁' := by simp

end user_congr

namespace lambda

universe variable l
constants (ss : Π {A : Type.{l}}, A → Type.{l})
          [ss_ss : ∀ (T : Type*) (t : T), subsingleton (ss t)]
          (A : Type.{l}) (a : A)
          (ss₁ ss₂ : ss a)

attribute [instance] ss_ss

set_option trace.simplifier.subsingleton true
example : ss₁ = ss₂ := by simp
example : (λ p : Prop, ss₁) = (λ p : Prop, ss₂) := by simp
example : (λ (A : Type) (a : A), ss₁) = (λ (A : Type) (a : A), ss₂) := by simp

end lambda

namespace dont_crash_when_locals_incompatible

universe variable l
constants (ss : Π {A : Type.{l}}, A → Type.{l})
          [ss_ss : ∀ (T : Type*) (t : T), subsingleton (ss t)]
          (A : Type.{l}) (a : A)
          (ss₁ ss₂ : ss a)

attribute [instance] ss_ss

-- This example works by accident. The first (_ : ss a) it encounters
-- has no locals, and is compatible with the second it finds so it
-- replaces the second with the first.
example : (λ (s : ss a), ss₁) = (λ (s : ss a), s) := by simp

-- This example fails because it finds the (_ : ss a) with the local
-- first. We do however avoid the error of replacing ss₁ with the local s.
-- TODO(dhs): the more robust solution is to maintain a set of canonical (_ : ss a)
-- for each subsingleton type, analogous to the defeq_canonizer.
example : (λ (s : ss a), s) = (λ (s : ss a), ss₁) :=
by do try simp,
      f ← mk_const `funext,
      apply f,
      intro `s,
      simp

end dont_crash_when_locals_incompatible
