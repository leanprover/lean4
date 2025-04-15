
section Mathlib.Order.Defs

variable {α : Type _}

section Preorder

class Preorder (α : Type _) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

end Preorder

section PartialOrder

class PartialOrder (α : Type _) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

end PartialOrder

section LinearOrder

class LinearOrder (α : Type _) extends PartialOrder α, Min α, Max α, Ord α where
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  decidableLE : DecidableRel (· ≤ · : α → α → Prop)
  decidableEq : DecidableEq α
  decidableLT : DecidableRel (· < · : α → α → Prop)
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  min_def : ∀ a b, min a b = if a ≤ b then a else b := by intros; rfl
  max_def : ∀ a b, max a b = if a ≤ b then b else a := by intros; rfl
  compare a b := compareOfLessAndEq a b
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b

end LinearOrder

end Mathlib.Order.Defs

section Mathlib.Order.Notation

class Bot (α : Type _) where
  bot : α

notation "⊥" => Bot.bot

attribute [match_pattern] Bot.bot

end Mathlib.Order.Notation

section Mathlib.Order.Basic

variable {α : Type _}

/-- An order is dense if there is an element between any pair of distinct comparable elements. -/
class DenselyOrdered (α : Type _) [LT α] : Prop where
  /-- An order is dense if there is an element between any pair of distinct elements. -/
  dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂

theorem exists_between [LT α] [DenselyOrdered α] : ∀ {a₁ a₂ : α}, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
  DenselyOrdered.dense _ _

theorem le_of_forall_le_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}
    (h : ∀ a, a₂ < a → a₁ ≤ a) : a₁ ≤ a₂ := sorry

end Mathlib.Order.Basic

section Mathlib.Order.BoundedOrder

universe u

variable {α : Type u}

/-- An order is an `OrderBot` if it has a least element.
We state this using a data mixin, holding the value of `⊥` and the least element constraint. -/
class OrderBot (α : Type u) [LE α] extends Bot α where
  /-- `⊥` is the least element -/
  bot_le : ∀ a : α, ⊥ ≤ a

section OrderBot

variable [LE α] [OrderBot α] {a : α}

@[simp]
theorem bot_le : ⊥ ≤ a :=
  OrderBot.bot_le a

end OrderBot

end Mathlib.Order.BoundedOrder

section Mathlib.Order.TypeTags

variable {α : Type _}

def WithBot (α : Type _) := Option α

namespace WithBot

@[coe, match_pattern] def some : α → WithBot α :=
  Option.some

instance coe : Coe α (WithBot α) :=
  ⟨some⟩

instance bot : Bot (WithBot α) :=
  ⟨none⟩

@[elab_as_elim, induction_eliminator, cases_eliminator]
def recBotCoe {C : WithBot α → Sort _} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ n : WithBot α, C n
  | ⊥ => bot
  | (a : α) => coe a

end WithBot

end Mathlib.Order.TypeTags

variable {α β γ δ : Type _}

namespace WithBot

variable {a b : α}

@[simp, norm_cast]
theorem coe_inj : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj

@[simp]
theorem bot_ne_coe : ⊥ ≠ (a : WithBot α) :=
  nofun

section LE

variable [LE α]

instance (priority := 10) le : LE (WithBot α) :=
  ⟨fun o₁ o₂ => ∀ a : α, o₁ = ↑a → ∃ b : α, o₂ = ↑b ∧ a ≤ b⟩

@[simp, norm_cast]
theorem coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b := by
  simp [LE.le]

instance orderBot : OrderBot (WithBot α) where
  bot_le _ := fun _ h => Option.noConfusion h

theorem le_coe_iff : ∀ {x : WithBot α}, x ≤ b ↔ ∀ a : α, x = ↑a → a ≤ b
  | (b : α) => by simp
  | ⊥ => by simp

end LE

section LT

variable [LT α]

instance (priority := 10) lt : LT (WithBot α) :=
  ⟨fun o₁ o₂ : WithBot α => ∃ b : α, o₂ = ↑b ∧ ∀ a : α, o₁ = ↑a → a < b⟩

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithBot α) < b ↔ a < b := by
  simp [LT.lt]

end LT

instance preorder [Preorder α] : Preorder (WithBot α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := sorry
  le_refl _ a ha := sorry
  le_trans _ _ _ h₁ h₂ a ha := sorry

end WithBot

namespace WithBot

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem le_of_forall_lt_iff_le [LinearOrder α] [DenselyOrdered α]
    {x y : WithBot α} : (∀ z : α, x < z → y ≤ z) ↔ y ≤ x := by
  refine ⟨fun h ↦ ?_, fun h z x_z ↦ sorry⟩
  induction x with
  | bot => sorry
  | coe x =>
    rw [le_coe_iff]
    rintro y rfl
    exact le_of_forall_le_of_dense (by exact_mod_cast h)

end WithBot
