module

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Option.Basic

class Succ? (α : Type u) where
  succ? : α → Option α
  succAtIdx? (n : Nat) (a : α) : Option α := Nat.repeat (· >>= succ?) n (some a)

class LawfulSucc? (α : Type u) [Succ? α] where
  succAtIdx?_zero {a : α} : Succ?.succAtIdx? 0 a = some a
  succAtIdx?_succ {a : α} : Succ?.succAtIdx? (n + 1) a = Succ?.succAtIdx? n a >>= Succ?.succ?

class LawfulLESucc? (α : Type u) [LE α] [Succ? α] where
  le_rfl : {a : α} → a ≤ a
  le_succ? : {a b : α} → Succ?.succ? a = some b → a ≤ b
  le_succ?_of_le : {a b c : α} → a ≤ b → (h : Succ?.succ? b = some c) → a ≤ c
  le_succAtIdx?_of_le : {a b c : α} → {n : Nat} → a ≤ b → (h : Succ?.succAtIdx? n b = some c) → a ≤ c

class LawfulLTSucc? [LT α] [Succ? α] where
  lt_succ? : {a b : α} → (h : Succ?.succ? a = some b) → a < b
  lt_succ?_of_lt : {a b c : α} → a < b → (h : Succ?.succ? b = some c) → a < c

class HasDownwardUnboundedRanges (α : Type u) where
  min : α

instance : Succ? Nat where
  succ? n := some (n + 1)
  succAtIdx? k n := some (n + k)

instance : LawfulSucc? Nat where
  succAtIdx?_zero := by simp [Succ?.succAtIdx?]
  succAtIdx?_succ := by simp [Succ?.succAtIdx?, Succ?.succ?, Bind.bind, Nat.add_assoc]

instance : LawfulLESucc? Nat where
  le_rfl := Nat.le_refl _
  le_succ? := sorry
  le_succ?_of_le hle h := by
    simp only [Succ?.succ?, Option.some.injEq] at h
    rw [← h]
    exact Nat.le_trans hle (Nat.le_succ _)
  le_succAtIdx?_of_le {a b c n} hle h := by
    simp only [Succ?.succAtIdx?, Option.some.injEq] at h
    rw [← h]
    exact Nat.le_trans hle (Nat.le_add_right _ _)
