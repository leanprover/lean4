/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.basic init.data.prod

universes u v

inductive acc {α : Sort u} (r : α → α → Prop) : α → Prop
| intro (x : α) (h : ∀ y, r y x → acc y) : acc x

namespace acc
variables {α : Sort u} {r : α → α → Prop}

def inv {x y : α} (h₁ : acc r x) (h₂ : r y x) : acc r y :=
acc.rec_on h₁ (λ x₁ ac₁ ih h₂, ac₁ y h₂) h₂

end acc

inductive well_founded {α : Sort u} (r : α → α → Prop) : Prop
| intro (h : ∀ a, acc r a) : well_founded

class has_well_founded (α : Sort u) : Type u :=
(r : α → α → Prop) (wf : well_founded r)

namespace well_founded
def apply {α : Sort u} {r : α → α → Prop} (wf : well_founded r) : ∀ a, acc r a :=
assume a, well_founded.rec_on wf (λ p, p) a

section
parameters {α : Sort u} {r : α → α → Prop}
local infix `≺`:50    := r

parameter hwf : well_founded r

lemma recursion {C : α → Sort v} (a : α) (h : Π x, (Π y, y ≺ x → C y) → C x) : C a :=
acc.rec_on (apply hwf a) (λ x₁ ac₁ ih, h x₁ ih)

lemma induction {C : α → Prop} (a : α) (h : ∀ x, (∀ y, y ≺ x → C y) → C x) : C a :=
recursion a h

variable {C : α → Sort v}
variable F : Π x, (Π y, y ≺ x → C y) → C x

def fix_F (x : α) (a : acc r x) : C x :=
acc.rec_on a (λ x₁ ac₁ ih, F x₁ ih)

lemma fix_F_eq (x : α) (acx : acc r x) :
  fix_F F x acx = F x (λ (y : α) (p : y ≺ x), fix_F F y (acc.inv acx p)) :=
acc.drec (λ x r ih, rfl) acx
end

variables {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

-- Well-founded fixpoint
def fix (hwf : well_founded r) (F : Π x, (Π y, r y x → C y) → C x) (x : α) : C x :=
fix_F F x (apply hwf x)

-- Well-founded fixpoint satisfies fixpoint equation
lemma fix_eq (hwf : well_founded r) (F : Π x, (Π y, r y x → C y) → C x) (x : α) :
  fix hwf F x = F x (λ y h, fix hwf F y) :=
fix_F_eq F x (apply hwf x)
end well_founded

open well_founded

-- Empty relation is well-founded
def empty_wf {α : Sort u} : well_founded empty_relation :=
well_founded.intro (λ (a : α),
  acc.intro a (λ (b : α) (lt : false), false.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace subrelation
section
  parameters {α : Sort u} {r Q : α → α → Prop}
  parameters (h₁ : subrelation Q r)
  parameters (h₂ : well_founded r)

  def accessible {a : α} (ac : acc r a) : acc Q a :=
  acc.rec_on ac (λ x ax ih,
    acc.intro x (λ (y : α) (lt : Q y x), ih y (h₁ lt)))

  def wf : well_founded Q :=
  ⟨λ a, accessible (apply h₂ a)⟩
end
end subrelation

-- The inverse image of a well-founded relation is well-founded
namespace inv_image
section
  parameters {α : Sort u} {β : Sort v} {r : β → β → Prop}
  parameters (f : α → β)
  parameters (h : well_founded r)

  private def acc_aux {b : β} (ac : acc r b) : ∀ (x : α), f x = b → acc (inv_image r f) x :=
  acc.rec_on ac (λ x acx ih z e,
    acc.intro z (λ y lt, eq.rec_on e (λ acx ih, ih (f y) lt y rfl) acx ih))

  def accessible {a : α} (ac : acc r (f a)) : acc (inv_image r f) a :=
  acc_aux ac a rfl

  def wf : well_founded (inv_image r f) :=
  ⟨λ a, accessible (apply h (f a))⟩
end
end inv_image

-- The transitive closure of a well-founded relation is well-founded
namespace tc
section
  parameters {α : Sort u} {r : α → α → Prop}
  local notation `r⁺` := tc r

  def accessible {z : α} (ac : acc r z) : acc (tc r) z :=
  acc.rec_on ac (λ x acx ih,
    acc.intro x (λ y rel,
      tc.rec_on rel
        (λ a b rab acx ih, ih a rab)
        (λ a b c rab rbc ih₁ ih₂ acx ih, acc.inv (ih₂ acx ih) rab)
        acx ih))

  def wf (h : well_founded r) : well_founded r⁺ :=
  ⟨λ a, accessible (apply h a)⟩
end
end tc

-- less-than is well-founded
def nat.lt_wf : well_founded nat.lt :=
⟨nat.rec
  (acc.intro 0 (λ n h, absurd h (nat.not_lt_zero n)))
  (λ n ih, acc.intro (nat.succ n) (λ m h,
     or.elim (nat.eq_or_lt_of_le (nat.le_of_succ_le_succ h))
        (λ e, eq.substr e ih) (acc.inv ih)))⟩

def measure {α : Sort u} : (α → ℕ) → α → α → Prop :=
inv_image (<)

def measure_wf {α : Sort u} (f : α → ℕ) : well_founded (measure f) :=
inv_image.wf f nat.lt_wf

def sizeof_measure (α : Sort u) [has_sizeof α] : α → α → Prop :=
measure sizeof

def sizeof_measure_wf (α : Sort u) [has_sizeof α] : well_founded (sizeof_measure α) :=
measure_wf sizeof

instance has_well_founded_of_has_sizeof (α : Sort u) [has_sizeof α] : has_well_founded α :=
{r := sizeof_measure α, wf := sizeof_measure_wf α}

namespace prod
open well_founded

section
  variables {α : Type u} {β : Type v}
  variable  (ra  : α → α → Prop)
  variable  (rb  : β → β → Prop)

  -- Lexicographical order based on ra and rb
  inductive lex : α × β → α × β → Prop
  | left  {a₁} (b₁) {a₂} (b₂) (h : ra a₁ a₂) : lex (a₁, b₁) (a₂, b₂)
  | right (a) {b₁ b₂} (h : rb b₁ b₂)         : lex (a, b₁)  (a, b₂)

  -- relational product based on ra and rb
  inductive rprod : α × β → α × β → Prop
  | intro {a₁ b₁ a₂ b₂} (h₁ : ra a₁ a₂) (h₂ : rb b₁ b₂) : rprod (a₁, b₁) (a₂, b₂)
  end

  section
  parameters {α : Type u} {β : Type v}
  parameters {ra  : α → α → Prop} {rb  : β → β → Prop}
  local infix `≺`:50 := lex ra rb

  def lex_accessible {a} (aca : acc ra a) (acb : ∀ b, acc rb b): ∀ b, acc (lex ra rb) (a, b) :=
  acc.rec_on aca (λ xa aca iha b,
    acc.rec_on (acb b) (λ xb acb ihb,
      acc.intro (xa, xb) (λ p lt,
        have aux : xa = xa → xb = xb → acc (lex ra rb) p, from
          @prod.lex.rec_on α β ra rb (λ p₁ p₂, fst p₂ = xa → snd p₂ = xb → acc (lex ra rb) p₁)
                           p (xa, xb) lt
            (λ a₁ b₁ a₂ b₂ h (eq₂ : a₂ = xa) (eq₃ : b₂ = xb), iha a₁ (eq.rec_on eq₂ h) b₁)
            (λ a b₁ b₂ h (eq₂ : a = xa) (eq₃ : b₂ = xb), eq.rec_on eq₂.symm (ihb b₁ (eq.rec_on eq₃ h))),
        aux rfl rfl)))

  -- The lexicographical order of well founded relations is well-founded
  def lex_wf (ha : well_founded ra) (hb : well_founded rb) : well_founded (lex ra rb) :=
  ⟨λ p, cases_on p (λ a b, lex_accessible (apply ha a) (well_founded.apply hb) b)⟩

  -- relational product is a subrelation of the lex
  def rprod_sub_lex : ∀ a b, rprod ra rb a b → lex ra rb a b :=
  λ a b h, prod.rprod.rec_on h (λ a₁ b₁ a₂ b₂ h₁ h₂, lex.left rb b₁ b₂ h₁)

  -- The relational product of well founded relations is well-founded
  def rprod_wf (ha : well_founded ra) (hb : well_founded rb) : well_founded (rprod ra rb) :=
  subrelation.wf (rprod_sub_lex) (lex_wf ha hb)
end

instance has_well_founded {α : Type u} {β : Type v} [s₁ : has_well_founded α] [s₂ : has_well_founded β] : has_well_founded (α × β) :=
{r := lex s₁.r s₂.r, wf := lex_wf s₁.wf s₂.wf}

end prod
