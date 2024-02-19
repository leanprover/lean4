/-
Copyright (c) 2024 Lean FRO.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro

This provides additional lemmas about propositional types beyond what is
needed for Core and SimpLemmas.
-/
prelude
import Init.Core
import Init.NotationExtra
set_option linter.missingDocs true -- keep it documented

/-! ## not -/

theorem not_not_em (a : Prop) : ¬¬(a ∨ ¬a) := fun h => h (.inr (h ∘ .inl))

/-! ## and -/

theorem and_self_iff : a ∧ a ↔ a := Iff.of_eq (and_self a)
theorem and_not_self_iff (a : Prop) : a ∧ ¬a ↔ False := iff_false_intro and_not_self
theorem not_and_self_iff (a : Prop) : ¬a ∧ a ↔ False := iff_false_intro not_and_self

theorem And.imp (f : a → c) (g : b → d) (h : a ∧ b) : c ∧ d :=  And.intro (f h.left) (g h.right)
theorem And.imp_left (h : a → b) : a ∧ c → b ∧ c := .imp h id
theorem And.imp_right (h : a → b) : c ∧ a → c ∧ b := .imp id h

theorem and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d :=
  Iff.intro (And.imp h₁.mp h₂.mp) (And.imp h₁.mpr h₂.mpr)
theorem and_congr_left' (h : a ↔ b) : a ∧ c ↔ b ∧ c := and_congr h .rfl
theorem and_congr_right' (h : b ↔ c) : a ∧ b ↔ a ∧ c := and_congr .rfl h

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) := mt And.left
theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) := mt And.right

theorem and_congr_right_eq (h : a → b = c) : (a ∧ b) = (a ∧ c) :=
  propext (and_congr_right (Iff.of_eq ∘ h))
theorem and_congr_left_eq  (h : c → a = b) : (a ∧ c) = (b ∧ c) :=
  propext (and_congr_left  (Iff.of_eq ∘ h))

theorem and_left_comm : a ∧ b ∧ c ↔ b ∧ a ∧ c :=
  Iff.intro (fun ⟨ha, hb, hc⟩ => ⟨hb, ha, hc⟩)
            (fun ⟨hb, ha, hc⟩ => ⟨ha, hb, hc⟩)

theorem and_right_comm : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b :=
  Iff.intro (fun ⟨⟨ha, hb⟩, hc⟩ => ⟨⟨ha, hc⟩, hb⟩)
            (fun ⟨⟨ha, hc⟩, hb⟩ => ⟨⟨ha, hb⟩, hc⟩)

theorem and_rotate : a ∧ b ∧ c ↔ b ∧ c ∧ a := by rw [and_left_comm, @and_comm a c]
theorem and_and_and_comm : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by rw [← and_assoc, @and_right_comm a, and_assoc]
theorem and_and_left  : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by rw [and_and_and_comm, and_self]
theorem and_and_right : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b ∧ c := by rw [and_and_and_comm, and_self]

theorem and_iff_left  (hb : b) : a ∧ b ↔ a := Iff.intro And.left  (And.intro · hb)
theorem and_iff_right (ha : a) : a ∧ b ↔ b := Iff.intro And.right (And.intro ha ·)

/-! ## or -/

theorem or_self_iff : a ∨ a ↔ a := or_self _ ▸ .rfl
theorem not_or_intro {a b : Prop} (ha : ¬a) (hb : ¬b) : ¬(a ∨ b) := (·.elim ha hb)

theorem or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) := ⟨.imp h₁.mp h₂.mp, .imp h₁.mpr h₂.mpr⟩
theorem or_congr_left (h : a ↔ b) : a ∨ c ↔ b ∨ c := or_congr h .rfl
theorem or_congr_right (h : b ↔ c) : a ∨ b ↔ a ∨ c := or_congr .rfl h

theorem or_left_comm  : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) := by rw [← or_assoc, ← or_assoc, @or_comm a b]
theorem or_right_comm : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by rw [or_assoc, or_assoc, @or_comm b]

theorem or_or_or_comm : (a ∨ b) ∨ c ∨ d ↔ (a ∨ c) ∨ b ∨ d := by rw [← or_assoc, @or_right_comm a, or_assoc]

theorem or_or_distrib_left : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by rw [or_or_or_comm, or_self]
theorem or_or_distrib_right : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by rw [or_or_or_comm, or_self]

theorem or_rotate : a ∨ b ∨ c ↔ b ∨ c ∨ a := by simp only [or_left_comm, Or.comm]

theorem or_iff_left  (hb : ¬b) : a ∨ b ↔ a := or_iff_left_iff_imp.mpr  hb.elim
theorem or_iff_right (ha : ¬a) : a ∨ b ↔ b := or_iff_right_iff_imp.mpr ha.elim

/-! ## distributivity -/

theorem not_imp_of_and_not : a ∧ ¬b → ¬(a → b)
  | ⟨ha, hb⟩, h => hb <| h ha

theorem imp_and {α} : (α → b ∧ c) ↔ (α → b) ∧ (α → c) :=
  ⟨fun h => ⟨fun ha => (h ha).1, fun ha => (h ha).2⟩, fun h ha => ⟨h.1 ha, h.2 ha⟩⟩

theorem not_and' : ¬(a ∧ b) ↔ b → ¬a := Iff.trans not_and imp_not_comm

/-- `∧` distributes over `∨` (on the left). -/
theorem and_or_left : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
  Iff.intro (fun ⟨ha, hbc⟩ => hbc.imp (.intro ha) (.intro ha))
            (Or.rec (.imp_right .inl) (.imp_right .inr))

/-- `∧` distributes over `∨` (on the right). -/
theorem or_and_right : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by rw [@and_comm (a ∨ b), and_or_left, @and_comm c, @and_comm c]

/-- `∨` distributes over `∧` (on the left). -/
theorem or_and_left : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
  Iff.intro (Or.rec (fun ha => ⟨.inl ha, .inl ha⟩) (.imp .inr .inr))
            (And.rec <| .rec (fun _ => .inl ·) (.imp_right ∘ .intro))

/-- `∨` distributes over `∧` (on the right). -/
theorem and_or_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := by rw [@or_comm (a ∧ b), or_and_left, @or_comm c, @or_comm c]

theorem or_imp : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
  Iff.intro (fun h => ⟨h ∘ .inl, h ∘ .inr⟩) (fun ⟨ha, hb⟩ => Or.rec ha hb)
theorem not_or : ¬(p ∨ q) ↔ ¬p ∧ ¬q := or_imp

theorem not_and_of_not_or_not (h : ¬a ∨ ¬b) : ¬(a ∧ b) := h.elim (mt (·.1)) (mt (·.2))

/-! ## exists and forall -/

section quantifiers
variable {p q : α → Prop} {b : Prop}

theorem forall_imp (h : ∀ a, p a → q a) : (∀ a, p a) → ∀ a, q a := fun h' a => h a (h' a)

/--
As `simp` does not index foralls, this `@[simp]` lemma is tried on every `forall` expression.
This is not ideal, and likely a performance issue, but it is difficult to remove this attribute at this time.
-/
@[simp] theorem forall_exists_index {q : (∃ x, p x) → Prop} :
    (∀ h, q h) ↔ ∀ x (h : p x), q ⟨x, h⟩ :=
  ⟨fun h x hpx => h ⟨x, hpx⟩, fun h ⟨x, hpx⟩ => h x hpx⟩

theorem Exists.imp (h : ∀ a, p a → q a) : (∃ a, p a) → ∃ a, q a
  | ⟨a, hp⟩ => ⟨a, h a hp⟩

theorem Exists.imp' {β} {q : β → Prop} (f : α → β) (hpq : ∀ a, p a → q (f a)) :
    (∃ a, p a) → ∃ b, q b
  | ⟨_, hp⟩ => ⟨_, hpq _ hp⟩

theorem exists_imp : ((∃ x, p x) → b) ↔ ∀ x, p x → b := forall_exists_index

@[simp] theorem exists_const (α) [i : Nonempty α] : (∃ _ : α, b) ↔ b :=
  ⟨fun ⟨_, h⟩ => h, i.elim Exists.intro⟩

section forall_congr

theorem forall_congr' (h : ∀ a, p a ↔ q a) : (∀ a, p a) ↔ ∀ a, q a :=
  ⟨fun H a => (h a).1 (H a), fun H a => (h a).2 (H a)⟩

theorem exists_congr (h : ∀ a, p a ↔ q a) : (∃ a, p a) ↔ ∃ a, q a :=
  ⟨Exists.imp fun x => (h x).1, Exists.imp fun x => (h x).2⟩

variable {β : α → Sort _}

theorem forall₂_congr {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b ↔ q a b) :
    (∀ a b, p a b) ↔ ∀ a b, q a b :=
  forall_congr' fun a => forall_congr' <| h a

theorem exists₂_congr {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b ↔ q a b) :
    (∃ a b, p a b) ↔ ∃ a b, q a b :=
  exists_congr fun a => exists_congr <| h a

variable {γ : ∀ a, β a → Sort _}
theorem forall₃_congr {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c ↔ q a b c) :
    (∀ a b c, p a b c) ↔ ∀ a b c, q a b c :=
  forall_congr' fun a => forall₂_congr <| h a

theorem exists₃_congr {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c ↔ q a b c) :
    (∃ a b c, p a b c) ↔ ∃ a b c, q a b c :=
  exists_congr fun a => exists₂_congr <| h a

variable {δ : ∀ a b, γ a b → Sort _}
theorem forall₄_congr {p q : ∀ a b c, δ a b c → Prop} (h : ∀ a b c d, p a b c d ↔ q a b c d) :
    (∀ a b c d, p a b c d) ↔ ∀ a b c d, q a b c d :=
  forall_congr' fun a => forall₃_congr <| h a

theorem exists₄_congr {p q : ∀ a b c, δ a b c → Prop} (h : ∀ a b c d, p a b c d ↔ q a b c d) :
    (∃ a b c d, p a b c d) ↔ ∃ a b c d, q a b c d :=
  exists_congr fun a => exists₃_congr <| h a

variable {ε : ∀ a b c, δ a b c → Sort _}
theorem forall₅_congr {p q : ∀ a b c d, ε a b c d → Prop}
    (h : ∀ a b c d e, p a b c d e ↔ q a b c d e) :
    (∀ a b c d e, p a b c d e) ↔ ∀ a b c d e, q a b c d e :=
  forall_congr' fun a => forall₄_congr <| h a

theorem exists₅_congr {p q : ∀ a b c d, ε a b c d → Prop}
    (h : ∀ a b c d e, p a b c d e ↔ q a b c d e) :
    (∃ a b c d e, p a b c d e) ↔ ∃ a b c d e, q a b c d e :=
  exists_congr fun a => exists₄_congr <| h a

end forall_congr

@[simp] theorem not_exists : (¬∃ x, p x) ↔ ∀ x, ¬p x := exists_imp

theorem forall_and : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩

theorem exists_or : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ ∃ x, q x :=
  ⟨fun | ⟨x, .inl h⟩ => .inl ⟨x, h⟩ | ⟨x, .inr h⟩ => .inr ⟨x, h⟩,
   fun | .inl ⟨x, h⟩ => ⟨x, .inl h⟩ | .inr ⟨x, h⟩ => ⟨x, .inr h⟩⟩

@[simp] theorem exists_false : ¬(∃ _a : α, False) := fun ⟨_, h⟩ => h

@[simp] theorem forall_const (α : Sort _) [i : Nonempty α] : (α → b) ↔ b :=
  ⟨i.elim, fun hb _ => hb⟩

theorem Exists.nonempty : (∃ x, p x) → Nonempty α | ⟨x, _⟩ => ⟨x⟩

theorem not_forall_of_exists_not {p : α → Prop} : (∃ x, ¬p x) → ¬∀ x, p x
  | ⟨x, hn⟩, h => hn (h x)

@[simp] theorem forall_eq {p : α → Prop} {a' : α} : (∀ a, a = a' → p a) ↔ p a' :=
  ⟨fun h => h a' rfl, fun h _ e => e.symm ▸ h⟩

@[simp] theorem forall_eq' {a' : α} : (∀ a, a' = a → p a) ↔ p a' := by simp [@eq_comm _ a']

@[simp] theorem exists_eq : ∃ a, a = a' := ⟨_, rfl⟩

@[simp] theorem exists_eq' : ∃ a, a' = a := ⟨_, rfl⟩

@[simp] theorem exists_eq_left : (∃ a, a = a' ∧ p a) ↔ p a' :=
  ⟨fun ⟨_, e, h⟩ => e ▸ h, fun h => ⟨_, rfl, h⟩⟩

@[simp] theorem exists_eq_right : (∃ a, p a ∧ a = a') ↔ p a' :=
  (exists_congr <| by exact fun a => And.comm).trans exists_eq_left

@[simp] theorem exists_and_left : (∃ x, b ∧ p x) ↔ b ∧ (∃ x, p x) :=
  ⟨fun ⟨x, h, hp⟩ => ⟨h, x, hp⟩, fun ⟨h, x, hp⟩ => ⟨x, h, hp⟩⟩

@[simp] theorem exists_and_right : (∃ x, p x ∧ b) ↔ (∃ x, p x) ∧ b := by simp [And.comm]

@[simp] theorem exists_eq_left' : (∃ a, a' = a ∧ p a) ↔ p a' := by simp [@eq_comm _ a']

@[simp] theorem forall_eq_or_imp : (∀ a, a = a' ∨ q a → p a) ↔ p a' ∧ ∀ a, q a → p a := by
  simp only [or_imp, forall_and, forall_eq]

@[simp] theorem exists_eq_or_imp : (∃ a, (a = a' ∨ q a) ∧ p a) ↔ p a' ∨ ∃ a, q a ∧ p a := by
  simp only [or_and_right, exists_or, exists_eq_left]

@[simp] theorem exists_eq_right_right : (∃ (a : α), p a ∧ q a ∧ a = a') ↔ p a' ∧ q a' := by
  simp [← and_assoc]

@[simp] theorem exists_eq_right_right' : (∃ (a : α), p a ∧ q a ∧ a' = a) ↔ p a' ∧ q a' := by
  simp [@eq_comm _ a']

@[simp] theorem exists_prop : (∃ _h : a, b) ↔ a ∧ b :=
  ⟨fun ⟨hp, hq⟩ => ⟨hp, hq⟩, fun ⟨hp, hq⟩ => ⟨hp, hq⟩⟩

@[simp] theorem exists_apply_eq_apply (f : α → β) (a' : α) : ∃ a, f a = f a' := ⟨a', rfl⟩

theorem forall_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∀ h' : p, q h') ↔ q h :=
  @forall_const (q h) p ⟨h⟩

theorem forall_comm {p : α → β → Prop} : (∀ a b, p a b) ↔ (∀ b a, p a b) :=
  ⟨fun h b a => h a b, fun h a b => h b a⟩

theorem exists_comm {p : α → β → Prop} : (∃ a b, p a b) ↔ (∃ b a, p a b) :=
  ⟨fun ⟨a, b, h⟩ => ⟨b, a, h⟩, fun ⟨b, a, h⟩ => ⟨a, b, h⟩⟩

@[simp] theorem forall_apply_eq_imp_iff {f : α → β} {p : β → Prop} :
    (∀ b a, f a = b → p b) ↔ ∀ a, p (f a) := by simp [forall_comm]

@[simp] theorem forall_eq_apply_imp_iff {f : α → β} {p : β → Prop} :
    (∀ b a, b = f a → p b) ↔ ∀ a, p (f a) := by simp [forall_comm]

@[simp] theorem forall_apply_eq_imp_iff₂ {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∀ b a, p a → f a = b → q b) ↔ ∀ a, p a → q (f a) :=
  ⟨fun h a ha => h (f a) a ha rfl, fun h _ a ha hb => hb ▸ h a ha⟩

theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : ¬p) : (∀ h' : p, q h') ↔ True :=
  iff_true_intro fun h => hn.elim h

end quantifiers

/-! ## decidable -/

theorem Decidable.not_not [Decidable p] : ¬¬p ↔ p := ⟨of_not_not, not_not_intro⟩

theorem Decidable.by_contra [Decidable p] : (¬p → False) → p := of_not_not

/-- Construct a non-Prop by cases on an `Or`, when the left conjunct is decidable. -/
protected def Or.by_cases [Decidable p] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hp : p then h₁ hp else h₂ (h.resolve_left hp)

/-- Construct a non-Prop by cases on an `Or`, when the right conjunct is decidable. -/
protected def Or.by_cases' [Decidable q] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hq : q then h₂ hq else h₁ (h.resolve_right hq)

instance exists_prop_decidable {p} (P : p → Prop)
  [Decidable p] [∀ h, Decidable (P h)] : Decidable (∃ h, P h) :=
if h : p then
  decidable_of_decidable_of_iff ⟨fun h2 => ⟨h, h2⟩, fun ⟨_, h2⟩ => h2⟩
else isFalse fun ⟨h', _⟩ => h h'

instance forall_prop_decidable {p} (P : p → Prop)
  [Decidable p] [∀ h, Decidable (P h)] : Decidable (∀ h, P h) :=
if h : p then
  decidable_of_decidable_of_iff ⟨fun h2 _ => h2, fun al => al h⟩
else isTrue fun h2 => absurd h2 h

theorem decide_eq_true_iff (p : Prop) [Decidable p] : (decide p = true) ↔ p := by simp

@[simp] theorem decide_eq_false_iff_not (p : Prop) {_ : Decidable p} : (decide p = false) ↔ ¬p :=
  ⟨of_decide_eq_false, decide_eq_false⟩

@[simp] theorem decide_eq_decide {p q : Prop} {_ : Decidable p} {_ : Decidable q} :
    decide p = decide q ↔ (p ↔ q) :=
  ⟨fun h => by rw [← decide_eq_true_iff p, h, decide_eq_true_iff], fun h => by simp [h]⟩

theorem Decidable.of_not_imp [Decidable a] (h : ¬(a → b)) : a :=
  byContradiction (not_not_of_not_imp h)

theorem Decidable.not_imp_symm [Decidable a] (h : ¬a → b) (hb : ¬b) : a :=
  byContradiction <| hb ∘ h

theorem Decidable.not_imp_comm [Decidable a] [Decidable b] : (¬a → b) ↔ (¬b → a) :=
  ⟨not_imp_symm, not_imp_symm⟩

theorem Decidable.not_imp_self [Decidable a] : (¬a → a) ↔ a := by
  have := @imp_not_self (¬a); rwa [not_not] at this

theorem Decidable.or_iff_not_imp_left [Decidable a] : a ∨ b ↔ (¬a → b) :=
  ⟨Or.resolve_left, fun h => dite _ .inl (.inr ∘ h)⟩

theorem Decidable.or_iff_not_imp_right [Decidable b] : a ∨ b ↔ (¬b → a) :=
  or_comm.trans or_iff_not_imp_left

theorem Decidable.not_imp_not [Decidable a] : (¬a → ¬b) ↔ (b → a) :=
  ⟨fun h hb => byContradiction (h · hb), mt⟩

theorem Decidable.not_or_of_imp [Decidable a] (h : a → b) : ¬a ∨ b :=
  if ha : a then .inr (h ha) else .inl ha

theorem Decidable.imp_iff_not_or [Decidable a] : (a → b) ↔ (¬a ∨ b) :=
  ⟨not_or_of_imp, Or.neg_resolve_left⟩

theorem Decidable.imp_iff_or_not [Decidable b] : b → a ↔ a ∨ ¬b :=
  Decidable.imp_iff_not_or.trans or_comm

theorem Decidable.imp_or [h : Decidable a] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) :=
  if h : a then by
    rw [imp_iff_right h, imp_iff_right h, imp_iff_right h]
  else by
    rw [iff_false_intro h, false_imp_iff, false_imp_iff, true_or]

theorem Decidable.imp_or' [Decidable b] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) :=
  if h : b then by simp [h] else by
    rw [eq_false h, false_or]; exact (or_iff_right_of_imp fun hx x => (hx x).elim).symm

theorem Decidable.not_imp_iff_and_not [Decidable a] : ¬(a → b) ↔ a ∧ ¬b :=
  ⟨fun h => ⟨of_not_imp h, not_of_not_imp h⟩, not_imp_of_and_not⟩

theorem Decidable.peirce (a b : Prop) [Decidable a] : ((a → b) → a) → a :=
  if ha : a then fun _ => ha else fun h => h ha.elim

theorem peirce' {a : Prop} (H : ∀ b : Prop, (a → b) → a) : a := H _ id

theorem Decidable.not_iff_not [Decidable a] [Decidable b] : (¬a ↔ ¬b) ↔ (a ↔ b) := by
  rw [@iff_def (¬a), @iff_def' a]; exact and_congr not_imp_not not_imp_not

theorem Decidable.not_iff_comm [Decidable a] [Decidable b] : (¬a ↔ b) ↔ (¬b ↔ a) := by
  rw [@iff_def (¬a), @iff_def (¬b)]; exact and_congr not_imp_comm imp_not_comm

theorem Decidable.not_iff [Decidable b] : ¬(a ↔ b) ↔ (¬a ↔ b) :=
  if h : b then by
    rw [iff_true_right h, iff_true_right h]
  else by
    rw [iff_false_right h, iff_false_right h]

theorem Decidable.iff_not_comm [Decidable a] [Decidable b] : (a ↔ ¬b) ↔ (b ↔ ¬a) := by
  rw [@iff_def a, @iff_def b]; exact and_congr imp_not_comm not_imp_comm

theorem Decidable.iff_iff_and_or_not_and_not {a b : Prop} [Decidable b] :
    (a ↔ b) ↔ (a ∧ b) ∨ (¬a ∧ ¬b) :=
  ⟨fun e => if h : b then .inl ⟨e.2 h, h⟩ else .inr ⟨mt e.1 h, h⟩,
   Or.rec (And.rec iff_of_true) (And.rec iff_of_false)⟩

theorem Decidable.iff_iff_not_or_and_or_not [Decidable a] [Decidable b] :
    (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) := by
  rw [iff_iff_implies_and_implies a b]; simp only [imp_iff_not_or, Or.comm]

theorem Decidable.not_and_not_right [Decidable b] : ¬(a ∧ ¬b) ↔ (a → b) :=
  ⟨fun h ha => not_imp_symm (And.intro ha) h, fun h ⟨ha, hb⟩ => hb <| h ha⟩

theorem Decidable.not_and_iff_or_not_not [Decidable a] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨fun h => if ha : a then .inr (h ⟨ha, ·⟩) else .inl ha, not_and_of_not_or_not⟩

theorem Decidable.not_and_iff_or_not_not' [Decidable b] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨fun h => if hb : b then .inl (h ⟨·, hb⟩) else .inr hb, not_and_of_not_or_not⟩

theorem Decidable.or_iff_not_and_not [Decidable a] [Decidable b] : a ∨ b ↔ ¬(¬a ∧ ¬b) := by
  rw [← not_or, not_not]

theorem Decidable.and_iff_not_or_not [Decidable a] [Decidable b] : a ∧ b ↔ ¬(¬a ∨ ¬b) := by
  rw [← not_and_iff_or_not_not, not_not]

theorem Decidable.imp_iff_right_iff [Decidable a] : (a → b ↔ b) ↔ a ∨ b :=
  ⟨fun H => (Decidable.em a).imp_right fun ha' => H.1 fun ha => (ha' ha).elim,
   fun H => H.elim imp_iff_right fun hb => iff_of_true (fun _ => hb) hb⟩

theorem Decidable.and_or_imp [Decidable a] : a ∧ b ∨ (a → c) ↔ a → b ∨ c :=
  if ha : a then by simp only [ha, true_and, true_imp_iff]
  else by simp only [ha, false_or, false_and, false_imp_iff]

theorem Decidable.or_congr_left' [Decidable c] (h : ¬c → (a ↔ b)) : a ∨ c ↔ b ∨ c := by
  rw [or_iff_not_imp_right, or_iff_not_imp_right]; exact imp_congr_right h

theorem Decidable.or_congr_right' [Decidable a] (h : ¬a → (b ↔ c)) : a ∨ b ↔ a ∨ c := by
  rw [or_iff_not_imp_left, or_iff_not_imp_left]; exact imp_congr_right h

/-- Transfer decidability of `a` to decidability of `b`, if the propositions are equivalent.
**Important**: this function should be used instead of `rw` on `Decidable b`, because the
kernel will get stuck reducing the usage of `propext` otherwise,
and `decide` will not work. -/
@[inline] def decidable_of_iff (a : Prop) (h : a ↔ b) [Decidable a] : Decidable b :=
  decidable_of_decidable_of_iff h

/-- Transfer decidability of `b` to decidability of `a`, if the propositions are equivalent.
This is the same as `decidable_of_iff` but the iff is flipped. -/
@[inline] def decidable_of_iff' (b : Prop) (h : a ↔ b) [Decidable b] : Decidable a :=
  decidable_of_decidable_of_iff h.symm

instance Decidable.predToBool (p : α → Prop) [DecidablePred p] :
    CoeDep (α → Prop) p (α → Bool) := ⟨fun b => decide <| p b⟩

/-- Prove that `a` is decidable by constructing a boolean `b` and a proof that `b ↔ a`.
(This is sometimes taken as an alternate definition of decidability.) -/
def decidable_of_bool : ∀ (b : Bool), (b ↔ a) → Decidable a
  | true, h => isTrue (h.1 rfl)
  | false, h => isFalse (mt h.2 Bool.noConfusion)

protected theorem Decidable.not_forall {p : α → Prop} [Decidable (∃ x, ¬p x)]
    [∀ x, Decidable (p x)] : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  ⟨Decidable.not_imp_symm fun nx x => Decidable.not_imp_symm (fun h => ⟨x, h⟩) nx,
   not_forall_of_exists_not⟩

protected theorem Decidable.not_forall_not {p : α → Prop} [Decidable (∃ x, p x)] :
    (¬∀ x, ¬p x) ↔ ∃ x, p x :=
  (@Decidable.not_iff_comm _ _ _ (decidable_of_iff (¬∃ x, p x) not_exists)).1 not_exists

protected theorem Decidable.not_exists_not {p : α → Prop} [∀ x, Decidable (p x)] :
    (¬∃ x, ¬p x) ↔ ∀ x, p x := by
  simp only [not_exists, Decidable.not_not]
