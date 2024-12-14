/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude

import Init.ByCases
import Init.RCases

namespace Lean.Order

/--
Auxillary definition to help with preserving user-visible names.

The goal is that when solving a goal of, say
```
monotone (fun x => a >>= (fun y => k x y))
```
we end up with the goal
```
y ⊢ monotone (fun x => k x y)
```
where the name `y` matches the name that the user used in the lambda.

If the lemma for `monotone_bind` would have an assumption
```
(h : ∃ z, monotone (fun x => k x y))
```
then the code that applies `monotone_bind` would have to be careful to `intro` with the name found
in the lambda, if present. And the same logic would have to repeated whenever applying a lemma
of this form.

So instead we write the assumption as
```
(h : forall_arg monotone k)
```
and only once, when handling this predicate transformer, we have to the implement the logic of “if
there is a lambda, use the name found there”.

Can be nested (`forall_arg (forall_arg monotone)`).
-/
def forall_arg (P : (α → β) → Prop) (f : α → γ → β) : Prop := ∀ y, P (fun x => f x y)


universe u v

class PartialOrder (α : Type u) where
  /-- The less-defined than relation -/
  rel : α → α → Prop
  rel_refl : ∀ {x}, rel x x
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_antisymm : ∀ {x y}, rel x y → rel y x → x = y


@[inherit_doc] scoped infix:50 " ⊑ " => PartialOrder.rel

section PartialOrder

variable {α  : Type u} [PartialOrder α]

theorem PartialOrder.rel_of_eq {x y : α} (h : x = y) : x ⊑ y := by cases h; apply rel_refl

def chain (c : α → Prop) : Prop := ∀ x y , c x → c y → x ⊑ y ∨ y ⊑ x

end PartialOrder

class CCPO (α : Type u) extends PartialOrder α where
  csup : (α → Prop) → α
  csup_spec {c : α → Prop} (hc : chain c) : csup c ⊑ x ↔ (∀ y, c y → y ⊑ x)

section CCPO

section monotone

variable {α : Type u} [PartialOrder α]
variable {β : Type v} [PartialOrder β]

def monotone (f : α → β) : Prop := ∀ x y, x ⊑ y → f x ⊑ f y

theorem monotone_const (c : β) : monotone (fun (_ : α) => c) :=
  fun _ _ _ => PartialOrder.rel_refl

theorem monotone_id : monotone (fun (x : α) => x) :=
  fun _ _ hxy => hxy

theorem monotone_compose
    {γ : Type w} [PartialOrder γ]
    {f : α → β} {g : β → γ}
    (hf : monotone f) (hg : monotone g) :
   monotone (fun x => g (f x)) := fun _ _ hxy => hg _ _ (hf _ _ hxy)

theorem monotone_letFun.{w} {γ : Sort w}
  (v : γ)
  (k : α → γ → β)
  (hmono : forall_arg monotone k) :
  monotone fun (x : α) => letFun v (k x) := hmono v

theorem monotone_ite
  (c : Prop) [Decidable c]
  (k₁ : α → β)
  (k₂ : α → β)
  (hmono₁ : monotone k₁)
  (hmono₂ : monotone k₂) :
  monotone fun x => if c then k₁ x else k₂ x := by
    split
    · apply hmono₁
    · apply hmono₂

theorem monotone_dite
  (c : Prop) [Decidable c]
  (k₁ : α → c → β)
  (k₂ : α → ¬ c → β)
  (hmono₁ : forall_arg monotone k₁)
  (hmono₂ : forall_arg monotone k₂) :
  monotone fun x => dite c (k₁ x) (k₂ x) := by
    split
    · apply hmono₁
    · apply hmono₂

end monotone

open PartialOrder CCPO

variable {α  : Type u} [CCPO α]

variable {c : α → Prop} (hchain : chain c)

include hchain in
theorem csup_le : (∀ y, c y → y ⊑ x) → csup c ⊑ x :=
  (csup_spec hchain).mpr

include hchain in
theorem le_csup {y} (hy : c y) : y ⊑ csup c :=
  (csup_spec hchain).mp rel_refl y hy

inductive iterates (f : α → α) : α → Prop where
  | step : iterates f x → iterates f (f x)
  | sup {c : α → Prop } (hc : chain c) (hi : ∀ x, c x → iterates f x) : iterates f (csup c)

def bot : α := csup (fun _ => False)

scoped notation "⊥" => bot

theorem bot_le (x : α) : ⊥ ⊑ x := by
  apply csup_le
  · intro x y hx hy; contradiction
  · intro x hx; contradiction

theorem chain_iterates {f : α → α} (hf : monotone f) : chain (iterates f) := by
  intros x y hx hy
  induction hx generalizing y
  case step x hx ih =>
    induction hy
    case step y hy _ =>
      cases ih y hy
      · left; apply hf; assumption
      · right; apply hf; assumption
    case sup c hchain hi ih2 =>
      show f x ⊑ csup c ∨ csup c ⊑ f x
      by_cases h : ∃ z, c z ∧ f x ⊑ z
      · left
        obtain ⟨z, hz, hfz⟩ := h
        apply rel_trans hfz
        apply le_csup hchain hz
      · right
        apply csup_le hchain _
        intro z hz
        rw [not_exists] at h
        specialize h z
        rw [not_and] at h
        specialize h hz
        cases ih2 z hz
        next => contradiction
        next => assumption
  case sup c hchain hi ih =>
    show rel (csup c) y ∨ rel y (csup c)
    by_cases h : ∃ z, c z ∧ rel y z
    · right
      obtain ⟨z, hz, hfz⟩ := h
      apply rel_trans hfz
      apply le_csup hchain hz
    · left
      apply csup_le hchain _
      intro z hz
      rw [not_exists] at h
      specialize h z
      rw [not_and] at h
      specialize h hz
      cases ih z hz y hy
      next => assumption
      next => contradiction

theorem rel_f_of_iterates {f : α → α} (hf : monotone f) {x : α} (hx : iterates f x) : x ⊑ f x := by
  induction hx
  case step ih =>
    apply hf
    assumption
  case sup c hchain hi ih =>
    apply csup_le hchain
    intro y hy
    apply rel_trans (ih y hy)
    apply hf
    apply le_csup hchain hy

set_option linter.unusedVariables false in
-- We include hmono as an assumption already on the definition so that
-- we always have it available when applying `fix_eq`
def fix (f : α → α) (hmono : monotone f) := csup (iterates f)

theorem fix_eq {f : α → α} (hf : monotone f) : fix f hf = f (fix f hf) := by
  apply rel_antisymm
  · apply rel_f_of_iterates hf
    apply iterates.sup (chain_iterates hf)
    exact fun _ h => h
  · apply le_csup (chain_iterates hf)
    apply iterates.step
    apply iterates.sup (chain_iterates hf)
    intro y hy
    exact hy

end CCPO

section fun_order

open PartialOrder

variable {α : Type u}
variable {β : α → Type v}

instance instOrderPi [∀ x, PartialOrder (β x)] : PartialOrder (∀ x, β x) where
  rel f g := ∀ x, f x ⊑ g x
  rel_refl _ := rel_refl
  rel_trans hf hg x := rel_trans (hf x) (hg x)
  rel_antisymm hf hg := funext (fun x => rel_antisymm (hf x) (hg x))

theorem monotone_of_monotone_apply [PartialOrder γ] [∀ x, PartialOrder (β x)] (f : γ → (∀ x, β x))
  (h : ∀ y, monotone (fun x => f x y)) : monotone f :=
  fun x y hxy z => h z x y hxy

theorem monotone_apply [PartialOrder γ] [∀ x, PartialOrder (β x)] (a : α) (f : γ → ∀ x, β x)
    (h : monotone f) :
    monotone (fun x => f x a) := fun _ _ hfg => h _ _ hfg a

-- It seems this lemma can be used to decompose all kind of applications,
-- but the `[Order β]` constraint comes out of no where, so not generally applicable.
theorem monotone_apply_of_monotone -- can `f` be made dependent here?
    {α : Type u} {β : Type v} {γ : Type w}
    [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f: γ → α → β}
    {g: γ → α}
    (hf1 : monotone f)
    (hf2 : ∀ x, monotone (f x))
    (hg : monotone g) :
    monotone (fun (x : γ) => f x (g x)) := by
  intro x y hxy
  apply rel_trans
  apply hf1 _ _ hxy
  apply hf2 y _ _ (hg _ _ hxy)

theorem monotone_apply_of_monotone_arg
    {α : Type u} {β : Type v} {γ : Type w}
    [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f: α → β}
    {g: γ → α}
    (hf : monotone f)
    (hg : monotone g) :
    monotone  (fun (x : γ) => f (g x)) := monotone_compose (hf := hg) (hg := hf)

-- This does not work well, because the instance requirements for the hypotheses
-- are stronger than what we need for the goal, where we just need `[Order (β z)]`
theorem monotone_apply_of_monotone_fun
    {α : Type u} {β : α → Type v} {γ : Type w}
    [∀ x, PartialOrder (β x)] [PartialOrder γ]
    (f : γ → (∀ x, β x)) (z : α)
    (h : monotone f) :
    monotone (fun x => f x z) :=
  fun x y hxy => h x y hxy z

theorem chain_apply [∀ x, PartialOrder (β x)] {c : (∀ x, β x) → Prop} (hc : chain c) (x : α) :
    chain (fun y => ∃ f, c f ∧ f x = y) := by
  intro _ _ ⟨f, hf, hfeq⟩ ⟨g, hg, hgeq⟩
  subst hfeq; subst hgeq
  cases hc f g hf hg
  next h => left; apply h x
  next h => right; apply h x

def fun_csup [∀ x, CCPO (β x)] (c : (∀ x, β x) → Prop) (x : α) :=
  CCPO.csup (fun y => ∃ f, c f ∧ f x = y)

instance instCCPOPi [∀ x, CCPO (β x)] : CCPO (∀ x, β x) where
  csup := fun_csup
  csup_spec := by
    intro f c hc
    constructor
    next =>
      intro hf g hg x
      apply rel_trans _ (hf x); clear hf
      apply le_csup (chain_apply hc x)
      exact ⟨g, hg, rfl⟩
    next =>
      intro h x
      apply csup_le (chain_apply hc x)
      intro y ⟨z, hz, hyz⟩
      subst y
      apply h z hz

end fun_order

section prod_order

open PartialOrder

variable {α : Type u}
variable {β : Type v}

instance [PartialOrder α] [PartialOrder β] : PartialOrder (α ×' β) where
  rel a b := a.1 ⊑ b.1 ∧ a.2 ⊑ b.2
  rel_refl := ⟨rel_refl, rel_refl⟩
  rel_trans ha hb := ⟨rel_trans ha.1 hb.1, rel_trans ha.2 hb.2⟩
  rel_antisymm := fun {a} {b} ha hb => by
    cases a; cases b;
    dsimp at *
    rw [rel_antisymm ha.1 hb.1, rel_antisymm ha.2 hb.2]

theorem monotone_prod [PartialOrder α] [PartialOrder β] {γ : Type w} [PartialOrder γ]
    {f : γ → α} {g : γ → β} (hf : monotone f) (hg : monotone g) :
    monotone (fun x => PProd.mk (f x) (g x)) :=
  fun _ _ h12 => ⟨hf _ _ h12, hg _ _ h12⟩

theorem monotone_fst [PartialOrder α] [PartialOrder β] {γ : Type w} [PartialOrder γ]
    {f : γ → α ×' β} (hf : monotone f) : monotone (fun x => (f x).1) :=
  fun _ _ h12 => (hf _ _ h12).1

theorem monotone_snd [PartialOrder α] [PartialOrder β] {γ : Type w} [PartialOrder γ]
    {f : γ → α ×' β} (hf : monotone f) : monotone (fun x => (f x).2) :=
  fun _ _ h12 => (hf _ _ h12).2

def chain_fst [CCPO α] [CCPO β] (c : α ×' β → Prop) : α → Prop := (fun a => ∃ b, c ⟨a, b⟩)
def chain_snd [CCPO α] [CCPO β] (c : α ×' β → Prop) : β → Prop := (fun b => ∃ a, c ⟨a, b⟩)

theorem chain.fst [CCPO α] [CCPO β] (c : α ×' β → Prop) (hchain : chain c) :
    chain (chain_fst c) := by
  intro a₁ a₂ ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
  cases hchain ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h₁ h₂
  case inl h => left; exact h.1
  case inr h => right; exact h.1

theorem chain.snd [CCPO α] [CCPO β] (c : α ×' β → Prop) (hchain : chain c) :
    chain (chain_snd c) := by
  intro b₁ b₂ ⟨a₁, h₁⟩ ⟨a₂, h₂⟩
  cases hchain ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h₁ h₂
  case inl h => left; exact h.2
  case inr h => right; exact h.2

instance [CCPO α] [CCPO β] : CCPO (α ×' β) where
  csup c := ⟨CCPO.csup (chain_fst c), CCPO.csup (chain_snd c)⟩
  csup_spec := by
    intro ⟨a, b⟩ c hchain
    dsimp
    constructor
    next =>
      intro ⟨h₁, h₂⟩ ⟨a', b'⟩ cab
      dsimp at *
      constructor <;> dsimp
      · apply rel_trans ?_ h₁
        apply le_csup hchain.fst
        exact ⟨b', cab⟩
      · apply rel_trans ?_ h₂
        apply le_csup hchain.snd
        exact ⟨a', cab⟩
    next =>
      intro h
      constructor <;> dsimp
      · apply csup_le hchain.fst
        intro a' ⟨b', hcab⟩
        apply (h _ hcab).1
      · apply csup_le hchain.snd
        intro b' ⟨a', hcab⟩
        apply (h _ hcab).2



end prod_order

section flat_order

variable {α : Type u}
variable [Nonempty α]

set_option linter.unusedVariables false in
def FlatOrder {α : Type u} (b : α) := α

variable {b : α}

inductive FlatOrder.rel : (x y : FlatOrder b) → Prop where
  | bot : rel b x
  | refl : rel x x

instance FlatOrder.instOrder : PartialOrder (FlatOrder b) where
  rel := rel
  rel_refl := .refl
  rel_trans {x y z : α} (hxy : rel x y) (hyz : rel y z) := by
    cases hxy <;> cases hyz <;> constructor
  rel_antisymm {x y : α} (hxy : rel x y) (hyz : rel y x) : x = y := by
    cases hxy <;> cases hyz <;> constructor

open Classical in
private theorem Classical.some_spec₂ {α : Sort _} {p : α → Prop} {h : ∃ a, p a} (q : α → Prop)
    (hpq : ∀ a, p a → q a) : q (choose h) := hpq _ <| choose_spec _

noncomputable def flat_csup (c : FlatOrder b → Prop) : FlatOrder b := by
  by_cases h : ∃ (x : FlatOrder b), c x ∧ x ≠ b
  · exact Classical.choose h
  · exact b

noncomputable instance FlatOrder.instCCPO : CCPO (FlatOrder b) where
  csup := flat_csup
  csup_spec := by
    intro x c hc
    unfold flat_csup
    split
    next hex =>
      apply Classical.some_spec₂ (q := (· ⊑ x ↔ (∀ y, c y → y ⊑ x)))
      clear hex
      intro z ⟨hz, hnb⟩
      constructor
      · intro h y hy
        apply PartialOrder.rel_trans _ h; clear h
        cases hc y z hy hz
        next => assumption
        next h =>
          cases h
          · contradiction
          · constructor
      · intro h
        cases h z hz
        · contradiction
        · constructor
    next hnotex =>
      constructor
      · intro h y hy; clear h
        suffices y = b by rw [this]; exact rel.bot
        rw [not_exists] at hnotex
        specialize hnotex y
        rw [not_and] at hnotex
        specialize hnotex hy
        rw [@Classical.not_not] at hnotex
        assumption
      · intro; exact rel.bot

noncomputable
abbrev TailrecOrder α [Nonempty α] := FlatOrder (@Classical.ofNonempty α _)

end flat_order

section mono_bind

class MonoBind (m : Type u → Type v) [Bind m] [∀ α, PartialOrder (m α)] where
  bind_mono_left (a₁ a₂ : m α) (f : α → m b) (h : a₁ ⊑ a₂) : a₁ >>= f ⊑ a₂ >>= f
  bind_mono_right (a : m α) (f₁ f₂ : α → m b) (h : ∀ x, f₁ x ⊑ f₂ x) : a >>= f₁ ⊑ a >>= f₂

theorem monotone_bind
    (m : Type u → Type v) [Bind m] [∀ α, PartialOrder (m α)] [MonoBind m]
    {α β : Type u}
    {γ : Type w} [PartialOrder γ]
    (f : γ → m α) (g : γ → α → m β)
    (hmono₁ : monotone f)
    (hmono₂ : forall_arg monotone g) :
    monotone (fun (x : γ) => f x >>= g x) := by
  intro x₁ x₂ hx₁₂
  apply PartialOrder.rel_trans
  · apply MonoBind.bind_mono_left _ _ _ (hmono₁ _ _ hx₁₂)
  · apply MonoBind.bind_mono_right _ _ _ (fun y => hmono₂ y _ _ hx₁₂)


instance : PartialOrder (Option α) := inferInstanceAs (PartialOrder (FlatOrder none))
noncomputable instance : CCPO (Option α) := inferInstanceAs (CCPO (FlatOrder none))
noncomputable instance : MonoBind Option where
  bind_mono_left _ _ _ h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right a _ _ h := by
    cases a
    · exact FlatOrder.rel.refl
    · exact h _

instance [Monad m] [inst : ∀ α, PartialOrder (m α)] : PartialOrder (ExceptT ε m α) := inst _
instance [Monad m] [∀ α, PartialOrder (m α)] [inst : ∀ α, CCPO (m α)] : CCPO (ExceptT ε m α) := inst _
instance [Monad m] [∀ α, PartialOrder (m α)] [∀ α, CCPO (m α)] [MonoBind m] : MonoBind (ExceptT ε m) where
  bind_mono_left a₁ a₂ f h₁₂ := by
    apply MonoBind.bind_mono_left (m := m)
    exact h₁₂
  bind_mono_right a₁ a₂ f h₁₂ := by
    apply MonoBind.bind_mono_right (m := m)
    intro x
    cases x
    · apply PartialOrder.rel_refl
    · apply h₁₂

end mono_bind

namespace Example

def findF (P : Nat → Bool) (rec : Nat → Option Nat) (x : Nat) : Option Nat :=
  if P x then
    some x
  else
    rec (x + 1)

noncomputable def find (P : Nat → Bool) : Nat → Option Nat := fix (α := _ → TailrecOrder _) (findF P) <| by
  unfold findF
  apply monotone_of_monotone_apply (β := fun _ => TailrecOrder _)
  intro n
  split
  · apply monotone_const
  · apply monotone_apply
    apply monotone_id

theorem find_eq : find P = findF P (find P) := fix_eq (α := _ → TailrecOrder _) ..

end Example

end Lean.Order
