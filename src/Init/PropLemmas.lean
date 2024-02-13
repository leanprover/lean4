/-
Copyright (c) 2024 Lean FRO.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro

This provides additional lemmas about propositional types beyond what is
needed for Core and SimpLemmas.
-/
prelude
import Init.NotationExtra
import Init.Classical
set_option linter.missingDocs true -- keep it documented

/-! ## not -/

theorem not_not_em (a : Prop) : ¬¬(a ∨ ¬a) := fun h => h (.inr (h ∘ .inl))

/-! ## and -/

-- TODO: rename and_self to and_self_eq
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

theorem and_congr_right_eq (h : a → b = c) : (a ∧ b) = (a ∧ c) := propext (and_congr_right (Iff.of_eq ∘ h))
theorem and_congr_left_eq  (h : c → a = b) : (a ∧ c) = (b ∧ c) := propext (and_congr_left  (Iff.of_eq ∘ h))

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

theorem Or.resolve_left  (h: a ∨ b) (na : ¬a) : b := h.elim (absurd · na) id
theorem Or.resolve_right (h: a ∨ b) (nb : ¬b) : a := h.elim id (absurd · nb)

theorem Or.neg_resolve_left  (h : ¬a ∨ b) (ha : a) : b := h.elim (absurd ha) id
theorem Or.neg_resolve_right (h : a ∨ ¬b) (nb : b) : a := h.elim id (absurd nb)

theorem or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) := ⟨.imp h₁.1 h₂.1, .imp h₁.2 h₂.2⟩
theorem or_congr_left (h : a ↔ b) : a ∨ c ↔ b ∨ c := or_congr h .rfl
theorem or_congr_right (h : b ↔ c) : a ∨ b ↔ a ∨ c := or_congr .rfl h

theorem or_left_comm  : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) := by rw [← or_assoc, ← or_assoc, @or_comm a b]
theorem or_right_comm : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by rw [or_assoc, or_assoc, @or_comm b]

theorem or_or_or_comm : (a ∨ b) ∨ c ∨ d ↔ (a ∨ c) ∨ b ∨ d := by rw [← or_assoc, @or_right_comm a, or_assoc]

theorem or_or_distrib_left : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by rw [or_or_or_comm, or_self]
theorem or_or_distrib_right : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by rw [or_or_or_comm, or_self]

theorem or_rotate : a ∨ b ∨ c ↔ b ∨ c ∨ a := by simp only [or_left_comm, Or.comm]

theorem or_iff_left (hb : ¬b) : a ∨ b ↔ a := or_iff_left_iff_imp.2 hb.elim
theorem or_iff_right (ha : ¬a) : a ∨ b ↔ b := or_iff_right_iff_imp.2 ha.elim

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
  Iff.intro (fun h => ⟨h ∘ .inl, h ∘ .inr⟩)
            (fun ⟨ha, hb⟩ => Or.rec ha hb)
theorem not_or : ¬(p ∨ q) ↔ ¬p ∧ ¬q := or_imp

theorem not_and_of_not_or_not (h : ¬a ∨ ¬b) : ¬(a ∧ b) := h.elim (mt (·.1)) (mt (·.2))

/-! ## exists and forall -/

section quantifiers
variable {p q : α → Prop} {b : Prop}

theorem forall_imp (h : ∀ a, p a → q a) : (∀ a, p a) → ∀ a, q a :=
fun h' a => h a (h' a)

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

-- Port note: this is `forall_congr` from Lean 3. In Lean 4, there is already something
-- with that name and a slightly different type.
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

/-- Extract an element from a existential statement, using `Classical.choose`. -/
-- This enables projection notation.
@[reducible] noncomputable def Exists.choose (P : ∃ a, p a) : α := Classical.choose P

/-- Show that an element extracted from `P : ∃ a, p a` using `P.choose` satisfies `p`. -/
theorem Exists.choose_spec {p : α → Prop} (P : ∃ a, p a) : p P.choose := Classical.choose_spec P

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

-- this theorem is needed to simplify the output of `List.mem_cons_iff`
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
