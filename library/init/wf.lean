/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.basic

universes u v

set_option codegen false

inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop
| intro (x : α) (h : ∀ y, r y x → Acc y) : Acc x

@[elabAsEliminator, inline, reducible]
def Acc.ndrec.{u1, u2} {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1}
    (m : Π (x : α) (h : ∀ (y : α), r y x → Acc r y), (Π (y : α) (a : r y x), C y) → C x)
    {a : α} (n : Acc r a) : C a :=
@Acc.rec α r (λ α _, C α) m a n

@[elabAsEliminator, inline, reducible]
def Acc.ndrecOn.{u1, u2} {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1}
    {a : α} (n : Acc r a)
    (m : Π (x : α) (h : ∀ (y : α), r y x → Acc r y), (Π (y : α) (a : r y x), C y) → C x)
    : C a :=
@Acc.rec α r (λ α _, C α) m a n

namespace Acc
variables {α : Sort u} {r : α → α → Prop}

def inv {x y : α} (h₁ : Acc r x) (h₂ : r y x) : Acc r y :=
Acc.recOn h₁ (λ x₁ ac₁ ih h₂, ac₁ y h₂) h₂

end Acc

inductive WellFounded {α : Sort u} (r : α → α → Prop) : Prop
| intro (h : ∀ a, Acc r a) : WellFounded

class HasWellFounded (α : Sort u) : Type u :=
(r : α → α → Prop) (wf : WellFounded r)

namespace WellFounded
def apply {α : Sort u} {r : α → α → Prop} (wf : WellFounded r) : ∀ a, Acc r a :=
assume a, WellFounded.recOn wf (λ p, p) a

section
variables {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r)

theorem recursion {C : α → Sort v} (a : α) (h : Π x, (Π y, r y x → C y) → C x) : C a :=
Acc.recOn (apply hwf a) (λ x₁ ac₁ ih, h x₁ ih)

theorem induction {C : α → Prop} (a : α) (h : ∀ x, (∀ y, r y x → C y) → C x) : C a :=
recursion hwf a h

variable {C : α → Sort v}
variable F : Π x, (Π y, r y x → C y) → C x

def fixF (x : α) (a : Acc r x) : C x :=
Acc.recOn a (λ x₁ ac₁ ih, F x₁ ih)

theorem fixFEq (x : α) (acx : Acc r x) :
  fixF F x acx = F x (λ (y : α) (p : r y x), fixF F y (Acc.inv acx p)) :=
Acc.rec (λ x r ih, rfl) acx
end

variables {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

-- Well-founded fixpoint
def fix (hwf : WellFounded r) (F : Π x, (Π y, r y x → C y) → C x) (x : α) : C x :=
fixF F x (apply hwf x)

-- Well-founded fixpoint satisfies fixpoint equation
theorem fixEq (hwf : WellFounded r) (F : Π x, (Π y, r y x → C y) → C x) (x : α) :
  fix hwf F x = F x (λ y h, fix hwf F y) :=
fixFEq F x (apply hwf x)
end WellFounded

open WellFounded

-- Empty relation is well-founded
def emptyWf {α : Sort u} : WellFounded (@emptyRelation α) :=
WellFounded.intro (λ (a : α),
  Acc.intro a (λ (b : α) (lt : False), False.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace Subrelation
variables {α : Sort u} {r q : α → α → Prop}

def accessible {a : α} (h₁ : Subrelation q r) (ac : Acc r a) : Acc q a :=
Acc.recOn ac $ λ x ax ih,
  Acc.intro x $ λ (y : α) (lt : q y x), ih y (h₁ lt)

def wf (h₁ : Subrelation q r) (h₂ : WellFounded r) : WellFounded q :=
⟨λ a, accessible @h₁ (apply h₂ a)⟩
end Subrelation

-- The inverse image of a well-founded relation is well-founded
namespace InvImage
variables {α : Sort u} {β : Sort v} {r : β → β → Prop}

private def accAux (f : α → β) {b : β} (ac : Acc r b) : ∀ (x : α), f x = b → Acc (InvImage r f) x :=
Acc.ndrecOn ac $ λ x acx ih z e,
  Acc.intro z  $ λ y lt,
    Eq.ndrecOn e (λ acx ih, ih (f y) lt y rfl) acx ih

def accessible {a : α} (f : α → β) (ac : Acc r (f a)) : Acc (InvImage r f) a :=
accAux f ac a rfl

def wf (f : α → β) (h : WellFounded r) : WellFounded (InvImage r f) :=
⟨λ a, accessible f (apply h (f a))⟩
end InvImage

-- The transitive closure of a well-founded relation is well-founded
namespace TC
variables {α : Sort u} {r : α → α → Prop}

def accessible {z : α} (ac : Acc r z) : Acc (TC r) z :=
Acc.ndrecOn ac $ λ x acx ih,
  Acc.intro x $ λ y rel,
    TC.ndrecOn rel
      (λ a b rab acx ih, ih a rab)
      (λ a b c rab rbc ih₁ ih₂ acx ih, Acc.inv (ih₂ acx ih) rab)
      acx ih

def wf (h : WellFounded r) : WellFounded (TC r) :=
⟨λ a, accessible (apply h a)⟩
end TC

-- less-than is well-founded
def Nat.ltWf : WellFounded Nat.lt :=
⟨Nat.rec
  (Acc.intro 0 (λ n h, absurd h (Nat.notLtZero n)))
  (λ n ih, Acc.intro (Nat.succ n) $ λ m h,
     Or.elim (Nat.eqOrLtOfLe (Nat.leOfSuccLeSucc h))
        (λ e, Eq.substr e ih) (Acc.inv ih))⟩

def measure {α : Sort u} : (α → Nat) → α → α → Prop :=
InvImage (λ a b, a < b)

def measureWf {α : Sort u} (f : α → Nat) : WellFounded (measure f) :=
InvImage.wf f Nat.ltWf

def sizeofMeasure (α : Sort u) [HasSizeof α] : α → α → Prop :=
measure sizeof

def sizeofMeasureWf (α : Sort u) [HasSizeof α] : WellFounded (sizeofMeasure α) :=
measureWf sizeof

instance hasWellFoundedOfHasSizeof (α : Sort u) [HasSizeof α] : HasWellFounded α :=
{r := sizeofMeasure α, wf := sizeofMeasureWf α}

namespace Prod
open WellFounded

section
variables {α : Type u} {β : Type v}
variable  (ra  : α → α → Prop)
variable  (rb  : β → β → Prop)

-- Lexicographical order based on ra and rb
inductive Lex : α × β → α × β → Prop
| left  {a₁} (b₁) {a₂} (b₂) (h : ra a₁ a₂) : Lex (a₁, b₁) (a₂, b₂)
| right (a) {b₁ b₂} (h : rb b₁ b₂)         : Lex (a, b₁)  (a, b₂)

-- relational product based on ra and rb
inductive Rprod : α × β → α × β → Prop
| intro {a₁ b₁ a₂ b₂} (h₁ : ra a₁ a₂) (h₂ : rb b₁ b₂) : Rprod (a₁, b₁) (a₂, b₂)
end

section
variables {α : Type u} {β : Type v}
variables {ra  : α → α → Prop} {rb  : β → β → Prop}

def lexAccessible {a} (aca : Acc ra a) (acb : ∀ b, Acc rb b): ∀ b, Acc (Lex ra rb) (a, b) :=
Acc.ndrecOn aca $ λ xa aca iha b,
  Acc.ndrecOn (acb b) $ λ xb acb ihb,
    Acc.intro (xa, xb)  $ λ p lt,
      have aux : xa = xa → xb = xb → Acc (Lex ra rb) p, from
        @Prod.Lex.recOn α β ra rb (λ p₁ p₂ _, fst p₂ = xa → snd p₂ = xb → Acc (Lex ra rb) p₁)
                         p (xa, xb) lt
          (λ a₁ b₁ a₂ b₂ h (Eq₂ : a₂ = xa) (Eq₃ : b₂ = xb), iha a₁ (Eq.recOn Eq₂ h) b₁)
          (λ a b₁ b₂ h (Eq₂ : a = xa) (Eq₃ : b₂ = xb), Eq.recOn Eq₂.symm (ihb b₁ (Eq.recOn Eq₃ h))),
      aux rfl rfl

-- The lexicographical order of well founded relations is well-founded
def lexWf (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Lex ra rb) :=
⟨λ p, casesOn p $ λ a b, lexAccessible (apply ha a) (WellFounded.apply hb) b⟩

-- relational product is a Subrelation of the Lex
def rprodSubLex : ∀ a b, Rprod ra rb a b → Lex ra rb a b :=
@Prod.Rprod.rec _ _ ra rb (λ a b _, Lex ra rb a b) (λ a₁ b₁ a₂ b₂ h₁ h₂, Lex.left rb b₁ b₂ h₁)

-- The relational product of well founded relations is well-founded
def rprodWf (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Rprod ra rb) :=
Subrelation.wf (rprodSubLex) (lexWf ha hb)
end

instance HasWellFounded {α : Type u} {β : Type v} [s₁ : HasWellFounded α] [s₂ : HasWellFounded β] : HasWellFounded (α × β) :=
{r := Lex s₁.r s₂.r, wf := lexWf s₁.wf s₂.wf}

end Prod

namespace PSigma
section
variables {α : Sort u} {β : α → Sort v}
variable  (r  : α → α → Prop)
variable  (s  : ∀ a, β a → β a → Prop)

-- Lexicographical order based on r and s
inductive Lex : PSigma β → PSigma β → Prop
| left  : ∀ {a₁ : α} (b₁ : β a₁) {a₂ : α} (b₂ : β a₂), r a₁ a₂ → Lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
| right : ∀ (a : α)  {b₁ b₂ : β a}, s a b₁ b₂ → Lex ⟨a, b₁⟩ ⟨a, b₂⟩
end

section
variables {α : Sort u} {β : α → Sort v}
variables {r  : α → α → Prop} {s : Π a : α, β a → β a → Prop}

def lexAccessible {a} (aca : Acc r a) (acb : ∀ a, WellFounded (s a)) : ∀ (b : β a), Acc (Lex r s) ⟨a, b⟩ :=
Acc.ndrecOn aca $ λ xa aca (iha : ∀ y, r y xa → ∀ b : β y, Acc (Lex r s) ⟨y, b⟩) (b : β xa),
  Acc.ndrecOn (WellFounded.apply (acb xa) b) $ λ xb acb (ihb : ∀ (y : β xa), s xa y xb → Acc (Lex r s) ⟨xa, y⟩),
     Acc.intro ⟨xa, xb⟩ $ λ p (lt : Lex r s p ⟨xa, xb⟩),
        have aux : xa = xa → xb ≅ xb → Acc (Lex r s) p, from
          @PSigma.Lex.recOn α β r s (λ p₁ p₂ _, p₂.1 = xa → p₂.2 ≅ xb → Acc (Lex r s) p₁)
                            p ⟨xa, xb⟩ lt
            (λ (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) (h : r a₁ a₂) (Eq₂ : a₂ = xa) (Eq₃ : b₂ ≅ xb),
              have aux : (∀ (y : α), r y xa → ∀ (b : β y), Acc (Lex r s) ⟨y, b⟩) →
                         r a₁ a₂ → ∀ (b₁ : β a₁), Acc (Lex r s) ⟨a₁, b₁⟩,
              from Eq.subst Eq₂ (λ iha h b₁, iha a₁ h b₁),
              aux iha h b₁)
            (λ (a : α) (b₁ b₂ : β a) (h : s a b₁ b₂) (Eq₂ : a = xa) (Eq₃ : b₂ ≅ xb),
              have aux : ∀ (xb : β xa), (∀ (y : β xa), s xa y xb → Acc (s xa) y) →
                           (∀ (y : β xa), s xa y xb → Acc (Lex r s) ⟨xa, y⟩) →
                           Lex r s p ⟨xa, xb⟩ → ∀ (b₁ : β a), s a b₁ b₂ → b₂ ≅ xb → Acc (Lex r s) ⟨a, b₁⟩,
              from Eq.subst Eq₂ $ λ xb acb ihb lt b₁ h Eq₃,
                have newEq₃ : b₂ = xb, from eqOfHeq Eq₃,
                have aux : (∀ (y : β a), s a y xb → Acc (Lex r s) ⟨a, y⟩) →
                           ∀ (b₁ : β a), s a b₁ b₂ → Acc (Lex r s) ⟨a, b₁⟩,
                from Eq.subst newEq₃ (λ ihb b₁ h, ihb b₁ h),
                aux ihb b₁ h,
              aux xb acb ihb lt b₁ h Eq₃),
        aux rfl (Heq.refl xb)

-- The lexicographical order of well founded relations is well-founded
def lexWf (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (Lex r s) :=
WellFounded.intro $ λ ⟨a, b⟩, lexAccessible (WellFounded.apply ha a) hb b
end

section
variables {α : Sort u} {β : Sort v}

def lexNdep (r : α → α → Prop) (s : β → β → Prop) :=
Lex r (λ a : α, s)

def lexNdepWf {r  : α → α → Prop} {s : β → β → Prop} (ha : WellFounded r) (hb : WellFounded s)
                : WellFounded (lexNdep r s) :=
WellFounded.intro $ λ ⟨a, b⟩, lexAccessible (WellFounded.apply ha a) (λ x, hb) b
end

section
variables {α : Sort u} {β : Sort v}

-- Reverse lexicographical order based on r and s
inductive RevLex (r  : α → α → Prop) (s  : β → β → Prop) : @PSigma α (λ a, β) → @PSigma α (λ a, β) → Prop
| left  : ∀ {a₁ a₂ : α} (b : β), r a₁ a₂ → RevLex ⟨a₁, b⟩ ⟨a₂, b⟩
| right : ∀ (a₁ : α) {b₁ : β} (a₂ : α) {b₂ : β}, s b₁ b₂ → RevLex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
end

section
open WellFounded
variables {α : Sort u} {β : Sort v}
variables {r  : α → α → Prop} {s : β → β → Prop}

def revLexAccessible {b} (acb : Acc s b) (aca : ∀ a, Acc r a): ∀ a, Acc (RevLex r s) ⟨a, b⟩ :=
Acc.recOn acb $ λ xb acb (ihb : ∀ y, s y xb → ∀ a, Acc (RevLex r s) ⟨a, y⟩) a,
  Acc.recOn (aca a) $ λ xa aca (iha : ∀ y, r y xa → Acc (RevLex r s) (mk y xb)),
    Acc.intro ⟨xa, xb⟩ $ λ p (lt : RevLex r s p ⟨xa, xb⟩),
      have aux : xa = xa → xb = xb → Acc (RevLex r s) p, from
        @RevLex.recOn α β r s (λ p₁ p₂ _, fst p₂ = xa → snd p₂ = xb → Acc (RevLex r s) p₁)
                            p ⟨xa, xb⟩ lt
          (λ a₁ a₂ b (h : r a₁ a₂) (Eq₂ : a₂ = xa) (Eq₃ : b = xb),
             show Acc (RevLex r s) ⟨a₁, b⟩, from
             have r₁ : r a₁ xa, from Eq.recOn Eq₂ h,
             have aux : Acc (RevLex r s) ⟨a₁, xb⟩, from iha a₁ r₁,
             Eq.recOn (Eq.symm Eq₃) aux)
          (λ a₁ b₁ a₂ b₂ (h : s b₁ b₂) (Eq₂ : a₂ = xa) (Eq₃ : b₂ = xb),
            show Acc (RevLex r s) (mk a₁ b₁), from
            have s₁ : s b₁ xb, from Eq.recOn Eq₃ h,
            ihb b₁ s₁ a₁),
      aux rfl rfl

def revLexWf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
WellFounded.intro $ λ ⟨a, b⟩, revLexAccessible (apply hb b) (WellFounded.apply ha) a
end

section
def skipLeft (α : Type u) {β : Type v} (s : β → β → Prop) : @PSigma α (λ a, β) → @PSigma α (λ a, β) → Prop :=
RevLex emptyRelation s

def skipLeftWf (α : Type u) {β : Type v} {s : β → β → Prop} (hb : WellFounded s) : WellFounded (skipLeft α s) :=
revLexWf emptyWf hb

def mkSkipLeft {α : Type u} {β : Type v} {b₁ b₂ : β} {s : β → β → Prop} (a₁ a₂ : α) (h : s b₁ b₂) : skipLeft α s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ :=
RevLex.right _ _ _ h
end

instance HasWellFounded {α : Type u} {β : α → Type v} [s₁ : HasWellFounded α] [s₂ : ∀ a, HasWellFounded (β a)] : HasWellFounded (PSigma β) :=
{r := Lex s₁.r (λ a, (s₂ a).r), wf := lexWf s₁.wf (λ a, (s₂ a).wf)}

end PSigma
