/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.sigma.basic init.meta
universes u v
namespace psigma
section
  variables {α : Sort u} {β : α → Sort v}
  variable  (r  : α → α → Prop)
  variable  (s  : ∀ a, β a → β a → Prop)

  -- Lexicographical order based on r and s
  inductive lex : psigma β → psigma β → Prop
  | left  : ∀ {a₁ : α} (b₁ : β a₁) {a₂ : α} (b₂ : β a₂), r a₁ a₂ → lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  | right : ∀ (a : α)  {b₁ b₂ : β a}, s a b₁ b₂ → lex ⟨a, b₁⟩ ⟨a, b₂⟩
end

section
  open well_founded tactic
  parameters {α : Sort u} {β : α → Sort v}
  parameters {r  : α → α → Prop} {s : Π a : α, β a → β a → Prop}
  local infix `≺`:50 := lex r s

  def lex_accessible {a} (aca : acc r a) (acb : ∀ a, well_founded (s a))
                     : ∀ (b : β a), acc (lex r s) ⟨a, b⟩ :=
  acc.rec_on aca
    (λ xa aca (iha : ∀ y, r y xa → ∀ b : β y, acc (lex r s) ⟨y, b⟩),
      λ b : β xa, acc.rec_on (well_founded.apply (acb xa) b)
        (λ xb acb
          (ihb : ∀ (y : β xa), s xa y xb → acc (lex r s) ⟨xa, y⟩),
          acc.intro ⟨xa, xb⟩ (λ p (lt : p ≺ ⟨xa, xb⟩),
            have aux : xa = xa → xb == xb → acc (lex r s) p, from
              @psigma.lex.rec_on α β r s (λ p₁ p₂, p₂.1 = xa → p₂.2 == xb → acc (lex r s) p₁)
                                 p ⟨xa, xb⟩ lt
                (λ (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) (h : r a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ == xb),
                  begin subst eq₂, exact iha a₁ h b₁ end)
                (λ (a : α) (b₁ b₂ : β a) (h : s a b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ == xb),
                  begin
                    subst eq₂,
                    have new_eq₃ := eq_of_heq eq₃,
                    subst new_eq₃,
                    exact ihb b₁ h
                  end),
            aux rfl (heq.refl xb))))

  -- The lexicographical order of well founded relations is well-founded
  def lex_wf (ha : well_founded r) (hb : ∀ x, well_founded (s x)) : well_founded (lex r s) :=
  well_founded.intro $ λ ⟨a, b⟩, lex_accessible (well_founded.apply ha a) hb b
end

section
  parameters {α : Sort u} {β : Sort v}

  def lex_ndep (r : α → α → Prop) (s : β → β → Prop) :=
  lex r (λ a : α, s)

  def lex_ndep_wf {r  : α → α → Prop} {s : β → β → Prop} (ha : well_founded r) (hb : well_founded s)
                  : well_founded (lex_ndep r s) :=
  well_founded.intro $ λ ⟨a, b⟩, lex_accessible (well_founded.apply ha a) (λ x, hb) b
end

section
  variables {α : Sort u} {β : Sort v}
  variable  (r  : α → α → Prop)
  variable  (s  : β → β → Prop)

  -- Reverse lexicographical order based on r and s
  inductive rev_lex : @psigma α (λ a, β) → @psigma α (λ a, β) → Prop
  | left  : ∀ {a₁ a₂ : α} (b : β), r a₁ a₂ → rev_lex ⟨a₁, b⟩ ⟨a₂, b⟩
  | right : ∀ (a₁ : α) {b₁ : β} (a₂ : α) {b₂ : β}, s b₁ b₂ → rev_lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
end

section
  open well_founded tactic
  parameters {α : Sort u} {β : Sort v}
  parameters {r  : α → α → Prop} {s : β → β → Prop}
  local infix `≺`:50 := rev_lex r s

  def rev_lex_accessible {b} (acb : acc s b) (aca : ∀ a, acc r a): ∀ a, acc (rev_lex r s) ⟨a, b⟩ :=
  acc.rec_on acb
    (λ xb acb (ihb : ∀ y, s y xb → ∀ a, acc (rev_lex r s) ⟨a, y⟩),
      λ a, acc.rec_on (aca a)
        (λ xa aca (iha : ∀ y, r y xa → acc (rev_lex r s) (mk y xb)),
          acc.intro ⟨xa, xb⟩ (λ p (lt : p ≺ ⟨xa, xb⟩),
            have aux : xa = xa → xb = xb → acc (rev_lex r s) p, from
              @rev_lex.rec_on α β r s (λ p₁ p₂, fst p₂ = xa → snd p₂ = xb → acc (rev_lex r s) p₁)
                              p ⟨xa, xb⟩ lt
               (λ a₁ a₂ b (h : r a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b = xb),
                 show acc (rev_lex r s) ⟨a₁, b⟩, from
                 have r₁ : r a₁ xa, from eq.rec_on eq₂ h,
                 have aux : acc (rev_lex r s) ⟨a₁, xb⟩, from iha a₁ r₁,
                 eq.rec_on (eq.symm eq₃) aux)
               (λ a₁ b₁ a₂ b₂ (h : s b₁ b₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb),
                 show acc (rev_lex r s) (mk a₁ b₁), from
                 have s₁ : s b₁ xb, from eq.rec_on eq₃ h,
                 ihb b₁ s₁ a₁),
            aux rfl rfl)))

  def rev_lex_wf (ha : well_founded r) (hb : well_founded s) : well_founded (rev_lex r s) :=
  well_founded.intro $ λ ⟨a, b⟩, rev_lex_accessible (apply hb b) (well_founded.apply ha) a
end

section
  def skip_left (α : Type u) {β : Type v} (s : β → β → Prop) : @psigma α (λ a, β) → @psigma α (λ a, β) → Prop :=
  rev_lex empty_relation s

  def skip_left_wf (α : Type u) {β : Type v} {s : β → β → Prop} (hb : well_founded s) : well_founded (skip_left α s) :=
  rev_lex_wf empty_wf hb

  def mk_skip_left {α : Type u} {β : Type v} {b₁ b₂ : β} {s : β → β → Prop}
                   (a₁ a₂ : α) (h : s b₁ b₂) : skip_left α s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ :=
  rev_lex.right _ _ _ h
end

instance has_well_founded {α : Type u} {β : α → Type v} [s₁ : has_well_founded α] [s₂ : ∀ a, has_well_founded (β a)] : has_well_founded (psigma β) :=
{r := lex s₁.r (λ a, (s₂ a).r), wf := lex_wf s₁.wf (λ a, (s₂ a).wf)}

end psigma
