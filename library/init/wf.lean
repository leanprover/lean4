/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.basic

universes u v

set_option codegen false

inductive acc {α : Sort u} (r : α → α → Prop) : α → Prop
| intro (x : α) (h : ∀ y, r y x → acc y) : acc x

@[elab_as_eliminator, inline, reducible]
def {u1 u2} acc.ndrec {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1}
    (m : Π (x : α) (h : ∀ (y : α), r y x → acc r y), (Π (y : α) (a : r y x), C y) → C x)
    {a : α} (n : acc r a) : C a :=
@acc.rec α r (λ α _, C α) m a n

@[elab_as_eliminator, inline, reducible]
def {u1 u2} acc.ndrec_on {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1}
    {a : α} (n : acc r a)
    (m : Π (x : α) (h : ∀ (y : α), r y x → acc r y), (Π (y : α) (a : r y x), C y) → C x)
    : C a :=
@acc.rec α r (λ α _, C α) m a n

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
variables {α : Sort u} {r : α → α → Prop} (hwf : well_founded r)
local infix `≺`:50    := r

theorem recursion {C : α → Sort v} (a : α) (h : Π x, (Π y, y ≺ x → C y) → C x) : C a :=
acc.rec_on (apply hwf a) (λ x₁ ac₁ ih, h x₁ ih)

theorem induction {C : α → Prop} (a : α) (h : ∀ x, (∀ y, y ≺ x → C y) → C x) : C a :=
recursion hwf a h

variable {C : α → Sort v}
variable F : Π x, (Π y, y ≺ x → C y) → C x

def fix_F (x : α) (a : acc r x) : C x :=
acc.rec_on a (λ x₁ ac₁ ih, F x₁ ih)

theorem fix_F_eq (x : α) (acx : acc r x) :
  fix_F F x acx = F x (λ (y : α) (p : y ≺ x), fix_F F y (acc.inv acx p)) :=
acc.rec (λ x r ih, rfl) acx
end

variables {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

-- Well-founded fixpoint
def fix (hwf : well_founded r) (F : Π x, (Π y, r y x → C y) → C x) (x : α) : C x :=
fix_F F x (apply hwf x)

-- Well-founded fixpoint satisfies fixpoint equation
theorem fix_eq (hwf : well_founded r) (F : Π x, (Π y, r y x → C y) → C x) (x : α) :
  fix hwf F x = F x (λ y h, fix hwf F y) :=
fix_F_eq F x (apply hwf x)
end well_founded

open well_founded

-- Empty relation is well-founded
def empty_wf {α : Sort u} : well_founded (@empty_relation α) :=
well_founded.intro (λ (a : α),
  acc.intro a (λ (b : α) (lt : false), false.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace subrelation
variables {α : Sort u} {r Q : α → α → Prop}

def accessible {a : α} (h₁ : subrelation Q r) (ac : acc r a) : acc Q a :=
acc.rec_on ac (λ x ax ih,
  acc.intro x (λ (y : α) (lt : Q y x), ih y (h₁ lt)))

def wf (h₁ : subrelation Q r) (h₂ : well_founded r) : well_founded Q :=
⟨λ a, accessible h₁ (apply h₂ a)⟩
end subrelation

-- The inverse image of a well-founded relation is well-founded
namespace inv_image
variables {α : Sort u} {β : Sort v} {r : β → β → Prop}

private def acc_aux (f : α → β) {b : β} (ac : acc r b) : ∀ (x : α), f x = b → acc (inv_image r f) x :=
acc.ndrec_on ac (λ x acx ih z e,
  acc.intro z (λ y lt, eq.ndrec_on e (λ acx ih, ih (f y) lt y rfl) acx ih))

def accessible {a : α} (f : α → β) (ac : acc r (f a)) : acc (inv_image r f) a :=
acc_aux f ac a rfl

def wf (f : α → β) (h : well_founded r) : well_founded (inv_image r f) :=
⟨λ a, accessible f (apply h (f a))⟩
end inv_image

-- The transitive closure of a well-founded relation is well-founded
namespace tc
variables {α : Sort u} {r : α → α → Prop}
local notation `r⁺` := tc r

def accessible {z : α} (ac : acc r z) : acc (tc r) z :=
acc.ndrec_on ac (λ x acx ih,
  acc.intro x (λ y rel,
    tc.ndrec_on rel
      (λ a b rab acx ih, ih a rab)
      (λ a b c rab rbc ih₁ ih₂ acx ih, acc.inv (ih₂ acx ih) rab)
      acx ih))

def wf (h : well_founded r) : well_founded r⁺ :=
⟨λ a, accessible (apply h a)⟩
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
variables {α : Type u} {β : Type v}
variables {ra  : α → α → Prop} {rb  : β → β → Prop}
local infix `≺`:50 := lex ra rb

def lex_accessible {a} (aca : acc ra a) (acb : ∀ b, acc rb b): ∀ b, acc (lex ra rb) (a, b) :=
acc.ndrec_on aca (λ xa aca iha b,
  acc.ndrec_on (acb b) (λ xb acb ihb,
    acc.intro (xa, xb) (λ p lt,
      have aux : xa = xa → xb = xb → acc (lex ra rb) p, from
        @prod.lex.rec_on α β ra rb (λ p₁ p₂ _, fst p₂ = xa → snd p₂ = xb → acc (lex ra rb) p₁)
                         p (xa, xb) lt
          (λ a₁ b₁ a₂ b₂ h (eq₂ : a₂ = xa) (eq₃ : b₂ = xb), iha a₁ (eq.rec_on eq₂ h) b₁)
          (λ a b₁ b₂ h (eq₂ : a = xa) (eq₃ : b₂ = xb), eq.rec_on eq₂.symm (ihb b₁ (eq.rec_on eq₃ h))),
      aux rfl rfl)))

-- The lexicographical order of well founded relations is well-founded
def lex_wf (ha : well_founded ra) (hb : well_founded rb) : well_founded (lex ra rb) :=
⟨λ p, cases_on p (λ a b, lex_accessible (apply ha a) (well_founded.apply hb) b)⟩

-- relational product is a subrelation of the lex
def rprod_sub_lex : ∀ a b, rprod ra rb a b → lex ra rb a b :=
@prod.rprod.rec _ _ ra rb (λ a b _, lex ra rb a b) (λ a₁ b₁ a₂ b₂ h₁ h₂, lex.left rb b₁ b₂ h₁)

-- The relational product of well founded relations is well-founded
def rprod_wf (ha : well_founded ra) (hb : well_founded rb) : well_founded (rprod ra rb) :=
subrelation.wf (rprod_sub_lex) (lex_wf ha hb)
end

instance has_well_founded {α : Type u} {β : Type v} [s₁ : has_well_founded α] [s₂ : has_well_founded β] : has_well_founded (α × β) :=
{r := lex s₁.r s₂.r, wf := lex_wf s₁.wf s₂.wf}

end prod

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
variables {α : Sort u} {β : α → Sort v}
variables {r  : α → α → Prop} {s : Π a : α, β a → β a → Prop}
local infix `≺`:50 := lex r s

def lex_accessible {a} (aca : acc r a) (acb : ∀ a, well_founded (s a))
                     : ∀ (b : β a), acc (lex r s) ⟨a, b⟩ :=
acc.ndrec_on aca
  (λ xa aca (iha : ∀ y, r y xa → ∀ b : β y, acc (lex r s) ⟨y, b⟩),
    λ b : β xa, acc.ndrec_on (well_founded.apply (acb xa) b)
      (λ xb acb
        (ihb : ∀ (y : β xa), s xa y xb → acc (lex r s) ⟨xa, y⟩),
        acc.intro ⟨xa, xb⟩ (λ p (lt : p ≺ ⟨xa, xb⟩),
          have aux : xa = xa → xb ~= xb → acc (lex r s) p, from
            @psigma.lex.rec_on α β r s (λ p₁ p₂ _, p₂.1 = xa → p₂.2 ~= xb → acc (lex r s) p₁)
                               p ⟨xa, xb⟩ lt
              (λ (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) (h : r a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ ~= xb),
                have aux : (∀ (y : α), r y xa → ∀ (b : β y), acc (lex r s) ⟨y, b⟩) →
                           r a₁ a₂ → ∀ (b₁ : β a₁), acc (lex r s) ⟨a₁, b₁⟩,
                from eq.subst eq₂ (λ iha h b₁, iha a₁ h b₁),
                aux iha h b₁)
              (λ (a : α) (b₁ b₂ : β a) (h : s a b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ ~= xb),
                have aux : ∀ (xb : β xa), (∀ (y : β xa), s xa y xb → acc (s xa) y) →
                             (∀ (y : β xa), s xa y xb → acc (lex r s) ⟨xa, y⟩) →
                             lex r s p ⟨xa, xb⟩ → ∀ (b₁ : β a), s a b₁ b₂ → b₂ ~= xb → acc (lex r s) ⟨a, b₁⟩,
                from eq.subst eq₂ (λ xb acb ihb lt b₁ h eq₃,
                     have new_eq₃ : b₂ = xb, from eq_of_heq eq₃,
                     have aux : (∀ (y : β a), s a y xb → acc (lex r s) ⟨a, y⟩) →
                                ∀ (b₁ : β a), s a b₁ b₂ → acc (lex r s) ⟨a, b₁⟩,
                     from eq.subst new_eq₃ (λ ihb b₁ h, ihb b₁ h),
                     aux ihb b₁ h),
                aux xb acb ihb lt b₁ h eq₃),
          aux rfl (heq.refl xb))))

-- The lexicographical order of well founded relations is well-founded
def lex_wf (ha : well_founded r) (hb : ∀ x, well_founded (s x)) : well_founded (lex r s) :=
well_founded.intro $ λ ⟨a, b⟩, lex_accessible (well_founded.apply ha a) hb b
end

section
variables {α : Sort u} {β : Sort v}

def lex_ndep (r : α → α → Prop) (s : β → β → Prop) :=
lex r (λ a : α, s)

def lex_ndep_wf {r  : α → α → Prop} {s : β → β → Prop} (ha : well_founded r) (hb : well_founded s)
                : well_founded (lex_ndep r s) :=
well_founded.intro $ λ ⟨a, b⟩, lex_accessible (well_founded.apply ha a) (λ x, hb) b
end

section
variables {α : Sort u} {β : Sort v}

-- Reverse lexicographical order based on r and s
inductive rev_lex (r  : α → α → Prop) (s  : β → β → Prop) : @psigma α (λ a, β) → @psigma α (λ a, β) → Prop
| left  : ∀ {a₁ a₂ : α} (b : β), r a₁ a₂ → rev_lex ⟨a₁, b⟩ ⟨a₂, b⟩
| right : ∀ (a₁ : α) {b₁ : β} (a₂ : α) {b₂ : β}, s b₁ b₂ → rev_lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
end

section
open well_founded
variables {α : Sort u} {β : Sort v}
variables {r  : α → α → Prop} {s : β → β → Prop}
local infix `≺`:50 := rev_lex r s

def rev_lex_accessible {b} (acb : acc s b) (aca : ∀ a, acc r a): ∀ a, acc (rev_lex r s) ⟨a, b⟩ :=
acc.rec_on acb
  (λ xb acb (ihb : ∀ y, s y xb → ∀ a, acc (rev_lex r s) ⟨a, y⟩),
    λ a, acc.rec_on (aca a)
      (λ xa aca (iha : ∀ y, r y xa → acc (rev_lex r s) (mk y xb)),
        acc.intro ⟨xa, xb⟩ (λ p (lt : p ≺ ⟨xa, xb⟩),
          have aux : xa = xa → xb = xb → acc (rev_lex r s) p, from
            @rev_lex.rec_on α β r s (λ p₁ p₂ _, fst p₂ = xa → snd p₂ = xb → acc (rev_lex r s) p₁)
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

/- Temporary hack for bootstrapping lean.
   TODO: DELETE!!!!

   This axiom is inconsistent. We can use it to prove that any function terminates.
   We are temporarily using this axiom until the new code generator is ready.
   With the new code generator, we will pre-compile into C/C++ a default
   tactic for proving termination. This tactic is then used to define the Lean compiler.
-/
axiom wf_term_hack {α : Type u} [has_well_founded α] (x y : α) : has_well_founded.r x y
