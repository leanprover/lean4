/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.basic

universes u v

setOption codegen false

inductive acc {α : Sort u} (r : α → α → Prop) : α → Prop
| intro (x : α) (h : ∀ y, r y x → acc y) : acc x

@[elabAsEliminator, inline, reducible]
def {u1 u2} acc.ndrec {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1}
    (m : Π (x : α) (h : ∀ (y : α), r y x → acc r y), (Π (y : α) (a : r y x), C y) → C x)
    {a : α} (n : acc r a) : C a :=
@acc.rec α r (λ α _, C α) m a n

@[elabAsEliminator, inline, reducible]
def {u1 u2} acc.ndrecOn {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1}
    {a : α} (n : acc r a)
    (m : Π (x : α) (h : ∀ (y : α), r y x → acc r y), (Π (y : α) (a : r y x), C y) → C x)
    : C a :=
@acc.rec α r (λ α _, C α) m a n

namespace acc
variables {α : Sort u} {r : α → α → Prop}

def inv {x y : α} (h₁ : acc r x) (h₂ : r y x) : acc r y :=
acc.recOn h₁ (λ x₁ ac₁ ih h₂, ac₁ y h₂) h₂

end acc

inductive wellFounded {α : Sort u} (r : α → α → Prop) : Prop
| intro (h : ∀ a, acc r a) : wellFounded

class hasWellFounded (α : Sort u) : Type u :=
(r : α → α → Prop) (wf : wellFounded r)

namespace wellFounded
def apply {α : Sort u} {r : α → α → Prop} (wf : wellFounded r) : ∀ a, acc r a :=
assume a, wellFounded.recOn wf (λ p, p) a

section
variables {α : Sort u} {r : α → α → Prop} (hwf : wellFounded r)
local infix `≺`:50    := r

theorem recursion {C : α → Sort v} (a : α) (h : Π x, (Π y, y ≺ x → C y) → C x) : C a :=
acc.recOn (apply hwf a) (λ x₁ ac₁ ih, h x₁ ih)

theorem induction {C : α → Prop} (a : α) (h : ∀ x, (∀ y, y ≺ x → C y) → C x) : C a :=
recursion hwf a h

variable {C : α → Sort v}
variable F : Π x, (Π y, y ≺ x → C y) → C x

def fixF (x : α) (a : acc r x) : C x :=
acc.recOn a (λ x₁ ac₁ ih, F x₁ ih)

theorem fixFEq (x : α) (acx : acc r x) :
  fixF F x acx = F x (λ (y : α) (p : y ≺ x), fixF F y (acc.inv acx p)) :=
acc.rec (λ x r ih, rfl) acx
end

variables {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

-- Well-founded fixpoint
def fix (hwf : wellFounded r) (F : Π x, (Π y, r y x → C y) → C x) (x : α) : C x :=
fixF F x (apply hwf x)

-- Well-founded fixpoint satisfies fixpoint equation
theorem fixEq (hwf : wellFounded r) (F : Π x, (Π y, r y x → C y) → C x) (x : α) :
  fix hwf F x = F x (λ y h, fix hwf F y) :=
fixFEq F x (apply hwf x)
end wellFounded

open wellFounded

-- Empty relation is well-founded
def emptyWf {α : Sort u} : wellFounded (@emptyRelation α) :=
wellFounded.intro (λ (a : α),
  acc.intro a (λ (b : α) (lt : false), false.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace subrelation
variables {α : Sort u} {r Q : α → α → Prop}

def accessible {a : α} (h₁ : subrelation Q r) (ac : acc r a) : acc Q a :=
acc.recOn ac (λ x ax ih,
  acc.intro x (λ (y : α) (lt : Q y x), ih y (h₁ lt)))

def wf (h₁ : subrelation Q r) (h₂ : wellFounded r) : wellFounded Q :=
⟨λ a, accessible h₁ (apply h₂ a)⟩
end subrelation

-- The inverse image of a well-founded relation is well-founded
namespace invImage
variables {α : Sort u} {β : Sort v} {r : β → β → Prop}

private def accAux (f : α → β) {b : β} (ac : acc r b) : ∀ (x : α), f x = b → acc (invImage r f) x :=
acc.ndrecOn ac (λ x acx ih z e,
  acc.intro z (λ y lt, eq.ndrecOn e (λ acx ih, ih (f y) lt y rfl) acx ih))

def accessible {a : α} (f : α → β) (ac : acc r (f a)) : acc (invImage r f) a :=
accAux f ac a rfl

def wf (f : α → β) (h : wellFounded r) : wellFounded (invImage r f) :=
⟨λ a, accessible f (apply h (f a))⟩
end invImage

-- The transitive closure of a well-founded relation is well-founded
namespace tc
variables {α : Sort u} {r : α → α → Prop}
local notation `r⁺` := tc r

def accessible {z : α} (ac : acc r z) : acc (tc r) z :=
acc.ndrecOn ac (λ x acx ih,
  acc.intro x (λ y rel,
    tc.ndrecOn rel
      (λ a b rab acx ih, ih a rab)
      (λ a b c rab rbc ih₁ ih₂ acx ih, acc.inv (ih₂ acx ih) rab)
      acx ih))

def wf (h : wellFounded r) : wellFounded r⁺ :=
⟨λ a, accessible (apply h a)⟩
end tc

-- less-than is well-founded
def nat.ltWf : wellFounded nat.lt :=
⟨nat.rec
  (acc.intro 0 (λ n h, absurd h (nat.notLtZero n)))
  (λ n ih, acc.intro (nat.succ n) (λ m h,
     or.elim (nat.eqOrLtOfLe (nat.leOfSuccLeSucc h))
        (λ e, eq.substr e ih) (acc.inv ih)))⟩

def measure {α : Sort u} : (α → ℕ) → α → α → Prop :=
invImage (<)

def measureWf {α : Sort u} (f : α → ℕ) : wellFounded (measure f) :=
invImage.wf f nat.ltWf

def sizeofMeasure (α : Sort u) [hasSizeof α] : α → α → Prop :=
measure sizeof

def sizeofMeasureWf (α : Sort u) [hasSizeof α] : wellFounded (sizeofMeasure α) :=
measureWf sizeof

instance hasWellFoundedOfHasSizeof (α : Sort u) [hasSizeof α] : hasWellFounded α :=
{r := sizeofMeasure α, wf := sizeofMeasureWf α}

namespace prod
open wellFounded

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

def lexAccessible {a} (aca : acc ra a) (acb : ∀ b, acc rb b): ∀ b, acc (lex ra rb) (a, b) :=
acc.ndrecOn aca (λ xa aca iha b,
  acc.ndrecOn (acb b) (λ xb acb ihb,
    acc.intro (xa, xb) (λ p lt,
      have aux : xa = xa → xb = xb → acc (lex ra rb) p, from
        @prod.lex.recOn α β ra rb (λ p₁ p₂ _, fst p₂ = xa → snd p₂ = xb → acc (lex ra rb) p₁)
                         p (xa, xb) lt
          (λ a₁ b₁ a₂ b₂ h (eq₂ : a₂ = xa) (eq₃ : b₂ = xb), iha a₁ (eq.recOn eq₂ h) b₁)
          (λ a b₁ b₂ h (eq₂ : a = xa) (eq₃ : b₂ = xb), eq.recOn eq₂.symm (ihb b₁ (eq.recOn eq₃ h))),
      aux rfl rfl)))

-- The lexicographical order of well founded relations is well-founded
def lexWf (ha : wellFounded ra) (hb : wellFounded rb) : wellFounded (lex ra rb) :=
⟨λ p, casesOn p (λ a b, lexAccessible (apply ha a) (wellFounded.apply hb) b)⟩

-- relational product is a subrelation of the lex
def rprodSubLex : ∀ a b, rprod ra rb a b → lex ra rb a b :=
@prod.rprod.rec _ _ ra rb (λ a b _, lex ra rb a b) (λ a₁ b₁ a₂ b₂ h₁ h₂, lex.left rb b₁ b₂ h₁)

-- The relational product of well founded relations is well-founded
def rprodWf (ha : wellFounded ra) (hb : wellFounded rb) : wellFounded (rprod ra rb) :=
subrelation.wf (rprodSubLex) (lexWf ha hb)
end

instance hasWellFounded {α : Type u} {β : Type v} [s₁ : hasWellFounded α] [s₂ : hasWellFounded β] : hasWellFounded (α × β) :=
{r := lex s₁.r s₂.r, wf := lexWf s₁.wf s₂.wf}

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

def lexAccessible {a} (aca : acc r a) (acb : ∀ a, wellFounded (s a))
                     : ∀ (b : β a), acc (lex r s) ⟨a, b⟩ :=
acc.ndrecOn aca
  (λ xa aca (iha : ∀ y, r y xa → ∀ b : β y, acc (lex r s) ⟨y, b⟩),
    λ b : β xa, acc.ndrecOn (wellFounded.apply (acb xa) b)
      (λ xb acb
        (ihb : ∀ (y : β xa), s xa y xb → acc (lex r s) ⟨xa, y⟩),
        acc.intro ⟨xa, xb⟩ (λ p (lt : p ≺ ⟨xa, xb⟩),
          have aux : xa = xa → xb ≅ xb → acc (lex r s) p, from
            @psigma.lex.recOn α β r s (λ p₁ p₂ _, p₂.1 = xa → p₂.2 ≅ xb → acc (lex r s) p₁)
                               p ⟨xa, xb⟩ lt
              (λ (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) (h : r a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ ≅ xb),
                have aux : (∀ (y : α), r y xa → ∀ (b : β y), acc (lex r s) ⟨y, b⟩) →
                           r a₁ a₂ → ∀ (b₁ : β a₁), acc (lex r s) ⟨a₁, b₁⟩,
                from eq.subst eq₂ (λ iha h b₁, iha a₁ h b₁),
                aux iha h b₁)
              (λ (a : α) (b₁ b₂ : β a) (h : s a b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ ≅ xb),
                have aux : ∀ (xb : β xa), (∀ (y : β xa), s xa y xb → acc (s xa) y) →
                             (∀ (y : β xa), s xa y xb → acc (lex r s) ⟨xa, y⟩) →
                             lex r s p ⟨xa, xb⟩ → ∀ (b₁ : β a), s a b₁ b₂ → b₂ ≅ xb → acc (lex r s) ⟨a, b₁⟩,
                from eq.subst eq₂ (λ xb acb ihb lt b₁ h eq₃,
                     have newEq₃ : b₂ = xb, from eqOfHeq eq₃,
                     have aux : (∀ (y : β a), s a y xb → acc (lex r s) ⟨a, y⟩) →
                                ∀ (b₁ : β a), s a b₁ b₂ → acc (lex r s) ⟨a, b₁⟩,
                     from eq.subst newEq₃ (λ ihb b₁ h, ihb b₁ h),
                     aux ihb b₁ h),
                aux xb acb ihb lt b₁ h eq₃),
          aux rfl (heq.refl xb))))

-- The lexicographical order of well founded relations is well-founded
def lexWf (ha : wellFounded r) (hb : ∀ x, wellFounded (s x)) : wellFounded (lex r s) :=
wellFounded.intro $ λ ⟨a, b⟩, lexAccessible (wellFounded.apply ha a) hb b
end

section
variables {α : Sort u} {β : Sort v}

def lexNdep (r : α → α → Prop) (s : β → β → Prop) :=
lex r (λ a : α, s)

def lexNdepWf {r  : α → α → Prop} {s : β → β → Prop} (ha : wellFounded r) (hb : wellFounded s)
                : wellFounded (lexNdep r s) :=
wellFounded.intro $ λ ⟨a, b⟩, lexAccessible (wellFounded.apply ha a) (λ x, hb) b
end

section
variables {α : Sort u} {β : Sort v}

-- Reverse lexicographical order based on r and s
inductive revLex (r  : α → α → Prop) (s  : β → β → Prop) : @psigma α (λ a, β) → @psigma α (λ a, β) → Prop
| left  : ∀ {a₁ a₂ : α} (b : β), r a₁ a₂ → revLex ⟨a₁, b⟩ ⟨a₂, b⟩
| right : ∀ (a₁ : α) {b₁ : β} (a₂ : α) {b₂ : β}, s b₁ b₂ → revLex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
end

section
open wellFounded
variables {α : Sort u} {β : Sort v}
variables {r  : α → α → Prop} {s : β → β → Prop}
local infix `≺`:50 := revLex r s

def revLexAccessible {b} (acb : acc s b) (aca : ∀ a, acc r a): ∀ a, acc (revLex r s) ⟨a, b⟩ :=
acc.recOn acb
  (λ xb acb (ihb : ∀ y, s y xb → ∀ a, acc (revLex r s) ⟨a, y⟩),
    λ a, acc.recOn (aca a)
      (λ xa aca (iha : ∀ y, r y xa → acc (revLex r s) (mk y xb)),
        acc.intro ⟨xa, xb⟩ (λ p (lt : p ≺ ⟨xa, xb⟩),
          have aux : xa = xa → xb = xb → acc (revLex r s) p, from
            @revLex.recOn α β r s (λ p₁ p₂ _, fst p₂ = xa → snd p₂ = xb → acc (revLex r s) p₁)
                            p ⟨xa, xb⟩ lt
             (λ a₁ a₂ b (h : r a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b = xb),
               show acc (revLex r s) ⟨a₁, b⟩, from
               have r₁ : r a₁ xa, from eq.recOn eq₂ h,
               have aux : acc (revLex r s) ⟨a₁, xb⟩, from iha a₁ r₁,
               eq.recOn (eq.symm eq₃) aux)
             (λ a₁ b₁ a₂ b₂ (h : s b₁ b₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb),
               show acc (revLex r s) (mk a₁ b₁), from
               have s₁ : s b₁ xb, from eq.recOn eq₃ h,
               ihb b₁ s₁ a₁),
          aux rfl rfl)))

def revLexWf (ha : wellFounded r) (hb : wellFounded s) : wellFounded (revLex r s) :=
wellFounded.intro $ λ ⟨a, b⟩, revLexAccessible (apply hb b) (wellFounded.apply ha) a
end

section
def skipLeft (α : Type u) {β : Type v} (s : β → β → Prop) : @psigma α (λ a, β) → @psigma α (λ a, β) → Prop :=
revLex emptyRelation s

def skipLeftWf (α : Type u) {β : Type v} {s : β → β → Prop} (hb : wellFounded s) : wellFounded (skipLeft α s) :=
revLexWf emptyWf hb

def mkSkipLeft {α : Type u} {β : Type v} {b₁ b₂ : β} {s : β → β → Prop}
                   (a₁ a₂ : α) (h : s b₁ b₂) : skipLeft α s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ :=
revLex.right _ _ _ h
end

instance hasWellFounded {α : Type u} {β : α → Type v} [s₁ : hasWellFounded α] [s₂ : ∀ a, hasWellFounded (β a)] : hasWellFounded (psigma β) :=
{r := lex s₁.r (λ a, (s₂ a).r), wf := lexWf s₁.wf (λ a, (s₂ a).wf)}

end psigma

/- Temporary hack for bootstrapping lean.
   TODO: DELETE!!!!

   This axiom is inconsistent. We can use it to prove that any function terminates.
   We are temporarily using this axiom until the new code generator is ready.
   With the new code generator, we will pre-compile into C/C++ a default
   tactic for proving termination. This tactic is then used to define the Lean compiler.
-/
axiom wfTermHack {α : Type u} [hasWellFounded α] (x y : α) : hasWellFounded.r x y
