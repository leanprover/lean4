module

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Option.Basic
import Init.NotationExtra

class UpwardEnumerable (α : Type u) where
  succ? : α → Option α
  succMany? (n : Nat) (a : α) : Option α := Nat.repeat (· >>= succ?) n (some a)

def UpwardEnumerable.le {α : Type u} [UpwardEnumerable α] (a b : α) : Prop :=
  ∃ n, UpwardEnumerable.succMany? n a = some b

def UpwardEnumerable.lt {α : Type u} [UpwardEnumerable α] (a b : α) : Prop :=
  ∃ n, UpwardEnumerable.succMany? (n + 1) a = some b

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

instance : UpwardEnumerable Nat where
  succ? n := some (n + 1)
  succMany? k n := some (n + k)

instance : Least? Nat where
  least? := some 0

instance : LawfulUpwardEnumerableLE Nat where
  le_iff a b := sorry

instance : LawfulUpwardEnumerableLT Nat where
  lt_iff a b := sorry

instance : LawfulUpwardEnumerable Nat where
  succMany?_zero := by simp [UpwardEnumerable.succMany?]
  succMany?_succ := by simp [UpwardEnumerable.succMany?, UpwardEnumerable.succ?, Bind.bind, Nat.add_assoc]
  ne_of_lt a b hlt := by
    rw [← LawfulUpwardEnumerableLT.lt_iff] at hlt
    exact Nat.ne_of_lt hlt
