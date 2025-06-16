module

prelude
import Init.Core
import Init.Classical
import Init.Data.Nat.Basic
import Init.Data.Option.Lemmas
import Init.NotationExtra

class UpwardEnumerable (α : Type u) where
  succ? : α → Option α
  succMany? (n : Nat) (a : α) : Option α := Nat.repeat (· >>= succ?) n (some a)

@[expose]
def UpwardEnumerable.le {α : Type u} [UpwardEnumerable α] (a b : α) : Prop :=
  ∃ n, UpwardEnumerable.succMany? n a = some b

@[expose]
def UpwardEnumerable.lt {α : Type u} [UpwardEnumerable α] (a b : α) : Prop :=
  ∃ n, UpwardEnumerable.succMany? (n + 1) a = some b

theorem UpwardEnumerable.le_of_lt {α : Type u} [UpwardEnumerable α] {a b : α}
    (h : UpwardEnumerable.lt a b) : UpwardEnumerable.le a b :=
  ⟨h.choose + 1, h.choose_spec⟩

-- Should we call it `OrderBot?` in analogy to Mathlib? Might be less clear to programmers.
class Least? (α : Type u) extends UpwardEnumerable α where
  least? : Option α

-- class UpwardEnumerableMembership (α : outParam (Type u)) (γ : Type v) [UpwardEnumerable α] where
--   init : γ → Option α
--   Predicate : γ → α → Bool

class LawfulUpwardEnumerable (α : Type u) [UpwardEnumerable α] where
  ne_of_lt (a b : α) : UpwardEnumerable.lt a b → a ≠ b
  succMany?_zero (a : α) : UpwardEnumerable.succMany? 0 a = some a
  succMany?_succ (n : Nat) (a : α) :
    UpwardEnumerable.succMany? (n + 1) a = (UpwardEnumerable.succMany? n a).bind UpwardEnumerable.succ?

theorem UpwardEnumerable.succMany?_add [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (m n : Nat) (a : α) :
    UpwardEnumerable.succMany? (m + n) a = (UpwardEnumerable.succMany? m a).bind (UpwardEnumerable.succMany? n ·) := by
  induction n
  case zero => simp [LawfulUpwardEnumerable.succMany?_zero]
  case succ n ih=>
    rw [← Nat.add_assoc, LawfulUpwardEnumerable.succMany?_succ, ih, Option.bind_assoc]
    simp only [LawfulUpwardEnumerable.succMany?_succ]

theorem LawfulUpwardEnumerable.succMany?_succ_eq_succ_bind_succMany
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (n : Nat) (a : α) :
    UpwardEnumerable.succMany? (n + 1) a = (UpwardEnumerable.succ? a).bind (UpwardEnumerable.succMany? n ·) := by
  rw [Nat.add_comm]
  simp [UpwardEnumerable.succMany?_add, LawfulUpwardEnumerable.succMany?_succ,
    LawfulUpwardEnumerable.succMany?_zero]

theorem UpwardEnumerable.le_refl {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (a : α) : UpwardEnumerable.le a a :=
  ⟨0, LawfulUpwardEnumerable.succMany?_zero a⟩

theorem UpwardEnumerable.le_trans {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b c : α} (hab : UpwardEnumerable.le a b) (hbc : UpwardEnumerable.le b c) :
    UpwardEnumerable.le a c := by
  refine ⟨hab.choose + hbc.choose, ?_⟩
  simp [succMany?_add, hab.choose_spec, hbc.choose_spec]

theorem UpwardEnumerable.not_gt_of_le {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b : α} :
    UpwardEnumerable.le a b → ¬ UpwardEnumerable.lt b a := by
  rintro ⟨n, hle⟩ ⟨m, hgt⟩
  have : UpwardEnumerable.lt a a := by
    refine ⟨n + m, ?_⟩
    rw [Nat.add_assoc, UpwardEnumerable.succMany?_add, hle, Option.bind_some, hgt]
  exact LawfulUpwardEnumerable.ne_of_lt _ _ this rfl

class LawfulUpwardEnumerableLE (α : Type u) [UpwardEnumerable α] [LE α] where
  le_iff (a b : α) : a ≤ b ↔ UpwardEnumerable.le a b

class LawfulUpwardEnumerableLT (α : Type u) [UpwardEnumerable α] [LT α] where
  lt_iff (a b : α) : a < b ↔ UpwardEnumerable.lt a b

class LawfulUpwardEnumerableLeast? (α : Type u) [UpwardEnumerable α] [Least? α] where
  eq_succMany?_least? (a : α) : ∃ init, Least?.least? = some init ∧ UpwardEnumerable.le init a

-- class LawfulUpwardEnumerableMembership (α : Type u) (γ : Type v) [UpwardEnumerable α]
--     [Membership α γ] [UpwardEnumerableMembership α γ] where
--   predicate_of_predicate_of_le (r : γ) (a b : α) : UpwardEnumerableMembership.Predicate r b →
--     UpwardEnumerable.le a b → UpwardEnumerableMembership.Predicate r a
--   mem_iff (a : α) (r : γ) :
--     a ∈ r ↔ ∃ init, UpwardEnumerableMembership.init r = some init ∧ UpwardEnumerable.le init a ∧
--       UpwardEnumerableMembership.Predicate r a
