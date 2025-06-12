module

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Option.Basic

class Succ? (α : Type u) where
  succ? : α → Option α
  succAtIdx? (n : Nat) (a : α) : Option α := Nat.repeat (· >>= succ?) n (some a)

class LawfulLESucc? (α : Type u) [LE α] [Succ? α] where
  le_rfl : {a : α} → a ≤ a
  le_succ?_of_le : {a b c : α} → a ≤ b → (h : Succ?.succ? b = some c) → a ≤ c
  le_succAtIdx?_of_le : {a b c : α} → {n : Nat} → a ≤ b → (h : Succ?.succAtIdx? n b = some c) → a ≤ c

class LawfulLTSucc? [LT α] [Succ? α] where
  lt_succ? : {a b : α} → (h : Succ?.succ? a = some b) → a < b
  lt_succ?_of_lt : {a b c : α} → a < b → (h : Succ?.succ? b = some c) → a < c

class HasDownwardUnboundedRanges (α : Type u) where
  min : α
