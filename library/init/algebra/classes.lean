/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.data.ordering.basic
universes u v

@[algebra] class is_symm_op (α : Type u) (β : out_param (Type v)) (op : α → α → β) : Prop :=
(symm_op : ∀ a b, op a b = op b a)

@[algebra] class is_commutative (α : Type u) (op : α → α → α) : Prop :=
(comm : ∀ a b, op a b = op b a)

instance is_symm_op_of_is_commutative (α : Type u) (op : α → α → α) [is_commutative α op] : is_symm_op α α op :=
{symm_op := is_commutative.comm op}

@[algebra] class is_associative (α : Type u) (op : α → α → α) : Prop :=
(assoc : ∀ a b c, op (op a b) c = op a (op b c))

@[algebra] class is_left_id (α : Type u) (op : α → α → α) (o : out_param α) : Prop :=
(left_id : ∀ a, op o a = a)

@[algebra] class is_right_id (α : Type u) (op : α → α → α) (o : out_param α) : Prop :=
(right_id : ∀ a, op a o = a)

@[algebra] class is_left_null (α : Type u) (op : α → α → α) (o : out_param α) : Prop :=
(left_null : ∀ a, op o a = o)

@[algebra] class is_right_null (α : Type u) (op : α → α → α) (o : out_param α) : Prop :=
(right_null : ∀ a, op a o = o)

@[algebra] class is_left_cancel (α : Type u) (op : α → α → α) : Prop :=
(left_cancel : ∀ a b c, op a b = op a c → b = c)

@[algebra] class is_right_cancel (α : Type u) (op : α → α → α) : Prop :=
(right_cancel : ∀ a b c, op a b = op c b → a = c)

@[algebra] class is_idempotent (α : Type u) (op : α → α → α) : Prop :=
(idempotent : ∀ a, op a a = a)

@[algebra] class is_left_distrib (α : Type u) (op₁ : α → α → α) (op₂ : out_param $ α → α → α) : Prop :=
(left_distrib : ∀ a b c, op₁ a (op₂ b c) = op₂ (op₁ a b) (op₁ a c))

@[algebra] class is_right_distrib (α : Type u) (op₁ : α → α → α) (op₂ : out_param $ α → α → α) : Prop :=
(right_distrib : ∀ a b c, op₁ (op₂ a b) c = op₂ (op₁ a c) (op₁ b c))

@[algebra] class is_left_inv (α : Type u) (op : α → α → α) (inv : out_param $ α → α) (o : out_param α) : Prop :=
(left_inv : ∀ a, op (inv a) a = o)

@[algebra] class is_right_inv (α : Type u) (op : α → α → α) (inv : out_param $ α → α) (o : out_param α) : Prop :=
(right_inv : ∀ a, op a (inv a) = o)

@[algebra] class is_cond_left_inv (α : Type u) (op : α → α → α) (inv : out_param $ α → α) (o : out_param α) (p : out_param $ α → Prop) : Prop :=
(left_inv : ∀ a, p a → op (inv a) a = o)

@[algebra] class is_cond_right_inv (α : Type u) (op : α → α → α) (inv : out_param $ α → α) (o : out_param α) (p : out_param $ α → Prop) : Prop :=
(right_inv : ∀ a, p a → op a (inv a) = o)

@[algebra] class is_distinct (α : Type u) (a : α) (b : α) : Prop :=
(distinct : a ≠ b)

/-
-- The following type class doesn't seem very useful, a regular simp lemma should work for this.
class is_inv (α : Type u) (β : Type v) (f : α → β) (g : out β → α) : Prop :=
(inv : ∀ a, g (f a) = a)

-- The following one can also be handled using a regular simp lemma
class is_idempotent (α : Type u) (f : α → α) : Prop :=
(idempotent : ∀ a, f (f a) = f a)
-/

@[algebra] class is_irrefl (α : Type u) (r : α → α → Prop) : Prop :=
(irrefl : ∀ a, ¬ r a a)

@[algebra] class is_refl (α : Type u) (r : α → α → Prop) : Prop :=
(refl : ∀ a, r a a)

@[algebra] class is_symm (α : Type u) (r : α → α → Prop) : Prop :=
(symm : ∀ a b, r a b → r b a)

instance is_symm_op_of_is_symm (α : Type u) (r : α → α → Prop) [is_symm α r] : is_symm_op α Prop r :=
{symm_op := λ a b, propext $ iff.intro (is_symm.symm a b) (is_symm.symm b a)}

@[algebra] class is_asymm (α : Type u) (r : α → α → Prop) : Prop :=
(asymm : ∀ a b, r a b → ¬ r b a)

@[algebra] class is_antisymm (α : Type u) (r : α → α → Prop) : Prop :=
(antisymm : ∀ a b, r a b → r b a → a = b)

@[algebra] class is_trans (α : Type u) (r : α → α → Prop) : Prop :=
(trans  : ∀ a b c, r a b → r b c → r a c)

@[algebra] class is_total (α : Type u) (r : α → α → Prop) : Prop :=
(total : ∀ a b, r a b ∨ r b a)

@[algebra] class is_preorder (α : Type u) (r : α → α → Prop) extends is_refl α r, is_trans α r : Prop.

@[algebra] class is_total_preorder (α : Type u) (r : α → α → Prop) extends is_trans α r, is_total α r : Prop.

instance is_total_preorder_is_preorder (α : Type u) (r : α → α → Prop) [s : is_total_preorder α r] : is_preorder α r :=
{trans := s.trans,
 refl  := λ a, or.elim (is_total.total r a a) id id}

@[algebra] class is_partial_order (α : Type u) (r : α → α → Prop) extends is_preorder α r, is_antisymm α r : Prop.

@[algebra] class is_linear_order (α : Type u) (r : α → α → Prop) extends is_partial_order α r, is_total α r : Prop.

@[algebra] class is_equiv (α : Type u) (r : α → α → Prop) extends is_preorder α r, is_symm α r : Prop.

@[algebra] class is_per (α : Type u) (r : α → α → Prop) extends is_symm α r, is_trans α r : Prop.

@[algebra] class is_strict_order (α : Type u) (r : α → α → Prop) extends is_irrefl α r, is_trans α r : Prop.

@[algebra] class is_incomp_trans (α : Type u) (lt : α → α → Prop) : Prop :=
(incomp_trans : ∀ a b c, (¬ lt a b ∧ ¬ lt b a) → (¬ lt b c ∧ ¬ lt c b) → (¬ lt a c ∧ ¬ lt c a))

@[algebra] class is_strict_weak_order (α : Type u) (lt : α → α → Prop) extends is_strict_order α lt, is_incomp_trans α lt : Prop.

@[algebra] class is_trichotomous (α : Type u) (lt : α → α → Prop) : Prop :=
(trichotomous : ∀ a b, lt a b ∨ a = b ∨ lt b a)

@[algebra] class is_strict_total_order (α : Type u) (lt : α → α → Prop) extends is_trichotomous α lt, is_strict_weak_order α lt.

instance eq_is_equiv (α : Type u) : is_equiv α (=) :=
{symm := @eq.symm _, trans := @eq.trans _, refl := eq.refl}

section
variables {α : Type u} {r : α → α → Prop}
local infix `≺`:50 := r

lemma irrefl [is_irrefl α r] (a : α) : ¬ a ≺ a :=
is_irrefl.irrefl _ a

lemma refl [is_refl α r] (a : α) : a ≺ a :=
is_refl.refl _ a

lemma trans [is_trans α r] {a b c : α} : a ≺ b → b ≺ c → a ≺ c :=
is_trans.trans _ _ _

lemma symm [is_symm α r] {a b : α} : a ≺ b → b ≺ a :=
is_symm.symm _ _

lemma antisymm [is_antisymm α r] {a b : α} : a ≺ b → b ≺ a → a = b :=
is_antisymm.antisymm _ _

lemma asymm [is_asymm α r] {a b : α} : a ≺ b → ¬ b ≺ a :=
is_asymm.asymm _ _

lemma trichotomous [is_trichotomous α r] : ∀ (a b : α), a ≺ b ∨ a = b ∨ b ≺ a :=
is_trichotomous.trichotomous r

lemma incomp_trans [is_incomp_trans α r] {a b c : α} : (¬ a ≺ b ∧ ¬ b ≺ a) → (¬ b ≺ c ∧ ¬ c ≺ b) → (¬ a ≺ c ∧ ¬ c ≺ a) :=
is_incomp_trans.incomp_trans _ _ _

instance is_asymm_of_is_trans_of_is_irrefl [is_trans α r] [is_irrefl α r] : is_asymm α r :=
⟨λ a b h₁ h₂, absurd (trans h₁ h₂) (irrefl a)⟩

section explicit_relation_variants
variable (r)

@[elab_simple]
lemma irrefl_of [is_irrefl α r] (a : α) : ¬ a ≺ a := irrefl a

@[elab_simple]
lemma refl_of [is_refl α r] (a : α) : a ≺ a := refl a

@[elab_simple]
lemma trans_of [is_trans α r] {a b c : α} : a ≺ b → b ≺ c → a ≺ c := trans

@[elab_simple]
lemma symm_of [is_symm α r] {a b : α} : a ≺ b → b ≺ a := symm

@[elab_simple]
lemma asymm_of [is_asymm α r] {a b : α} : a ≺ b → ¬ b ≺ a := asymm

@[elab_simple]
lemma total_of [is_total α r] (a b : α) : a ≺ b ∨ b ≺ a :=
is_total.total _ _ _

@[elab_simple]
lemma trichotomous_of [is_trichotomous α r] : ∀ (a b : α), a ≺ b ∨ a = b ∨ b ≺ a := trichotomous

@[elab_simple]
lemma incomp_trans_of [is_incomp_trans α r] {a b c : α} : (¬ a ≺ b ∧ ¬ b ≺ a) → (¬ b ≺ c ∧ ¬ c ≺ b) → (¬ a ≺ c ∧ ¬ c ≺ a) := incomp_trans

end explicit_relation_variants

end

namespace strict_weak_order
section
parameters {α : Type u} {r : α → α → Prop}
local infix `≺`:50 := r

def equiv (a b : α) : Prop :=
¬ a ≺ b ∧ ¬ b ≺ a

parameter [is_strict_weak_order α r]

local infix ` ≈ `:50 := equiv

lemma erefl (a : α) : a ≈ a :=
⟨irrefl a, irrefl a⟩

lemma esymm {a b : α} : a ≈ b → b ≈ a :=
λ ⟨h₁, h₂⟩, ⟨h₂, h₁⟩

lemma etrans {a b c : α} : a ≈ b → b ≈ c → a ≈ c :=
incomp_trans

lemma not_lt_of_equiv {a b : α} : a ≈ b → ¬ a ≺ b :=
λ h, h.1

lemma not_lt_of_equiv' {a b : α} : a ≈ b → ¬ b ≺ a :=
λ h, h.2

instance : is_equiv α equiv :=
{refl := erefl, trans := @etrans, symm := @esymm}
end

/- Notation for the equivalence relation induced by lt -/
notation a ` ≈[`:50 lt `]` b:50 := @equiv _ lt a b
end strict_weak_order

lemma is_strict_weak_order_of_is_total_preorder {α : Type u} {le : α → α → Prop} {lt : α → α → Prop} [decidable_rel le] [s : is_total_preorder α le]
                                                (h : ∀ a b, lt a b ↔ ¬ le b a) : is_strict_weak_order α lt :=
{
 trans        :=
  λ a b c hab hbc,
    have nba : ¬ le b a, from iff.mp (h _ _) hab,
    have ncb : ¬ le c b, from iff.mp (h _ _) hbc,
    have hab : le a b,   from or.resolve_left (total_of le b a) nba,
    have nca : ¬ le c a, from λ hca : le c a,
       have hcb : le c b, from trans_of le hca hab,
       absurd hcb ncb,
    iff.mpr (h _ _) nca,

 irrefl       := λ a hlt, absurd (refl_of le a) (iff.mp (h _ _) hlt),

 incomp_trans := λ a b c ⟨nab, nba⟩ ⟨nbc, ncb⟩,
    have hba : le b a, from decidable.of_not_not (iff.mp (not_iff_not_of_iff (h _ _)) nab),
    have hab : le a b, from decidable.of_not_not (iff.mp (not_iff_not_of_iff (h _ _)) nba),
    have hcb : le c b, from decidable.of_not_not (iff.mp (not_iff_not_of_iff (h _ _)) nbc),
    have hbc : le b c, from decidable.of_not_not (iff.mp (not_iff_not_of_iff (h _ _)) ncb),
    have hac : le a c, from trans_of le hab hbc,
    have hca : le c a, from trans_of le hcb hba,
    and.intro
      (λ n, absurd hca (iff.mp (h _ _) n))
      (λ n, absurd hac (iff.mp (h _ _) n))
}

lemma lt_of_lt_of_incomp {α : Type u} {lt : α → α → Prop} [is_strict_weak_order α lt] [decidable_rel lt]
                         : ∀ {a b c}, lt a b → (¬ lt b c ∧ ¬ lt c b) → lt a c :=
λ a b c hab ⟨nbc, ncb⟩,
  have nca : ¬ lt c a, from λ hca, absurd (trans_of lt hca hab) ncb,
  decidable.by_contradiction $
    λ nac : ¬ lt a c,
      have ¬ lt a b ∧ ¬ lt b a, from incomp_trans_of lt ⟨nac, nca⟩ ⟨ncb, nbc⟩,
      absurd hab this.1

lemma lt_of_incomp_of_lt {α : Type u} {lt : α → α → Prop} [is_strict_weak_order α lt] [decidable_rel lt]
                         : ∀ {a b c}, (¬ lt a b ∧ ¬ lt b a) → lt b c → lt a c :=
λ a b c ⟨nab, nba⟩ hbc,
  have nca : ¬ lt c a, from λ hca, absurd (trans_of lt hbc hca) nba,
  decidable.by_contradiction $
    λ nac : ¬ lt a c,
      have ¬ lt b c ∧ ¬ lt c b, from incomp_trans_of lt ⟨nba, nab⟩ ⟨nac, nca⟩,
      absurd hbc this.1

lemma eq_of_incomp {α : Type u} {lt : α → α → Prop} [is_trichotomous α lt] {a b} : (¬ lt a b ∧ ¬ lt b a) → a = b :=
λ ⟨nab, nba⟩,
  match trichotomous_of lt a b with
  | or.inl hab          := absurd hab nab
  | or.inr (or.inl hab) := hab
  | or.inr (or.inr hba) := absurd hba nba
  end

lemma eq_of_eqv_lt {α : Type u} {lt : α → α → Prop} [is_trichotomous α lt] {a b} : a ≈[lt] b → a = b :=
eq_of_incomp

lemma incomp_iff_eq {α : Type u} {lt : α → α → Prop} [is_trichotomous α lt] [is_irrefl α lt] (a b) : (¬ lt a b ∧ ¬ lt b a) ↔ a = b :=
iff.intro eq_of_incomp (λ hab, eq.subst hab (and.intro (irrefl_of lt a) (irrefl_of lt a)))

lemma eqv_lt_iff_eq {α : Type u} {lt : α → α → Prop} [is_trichotomous α lt] [is_irrefl α lt] (a b) : a ≈[lt] b ↔ a = b :=
incomp_iff_eq a b

lemma not_lt_of_lt {α : Type u} {lt : α → α → Prop} [is_strict_order α lt] {a b} : lt a b → ¬ lt b a :=
λ h₁ h₂, absurd (trans_of lt h₁ h₂) (irrefl_of lt _)
