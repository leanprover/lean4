/-!
This benchmark demonstrates creating a definition with many nested `omega` proofs, exercising
components that traverse terms before `abstractProofs` runs.

From https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/slow.20syntax.20linters/near/500291283
By Bhavik Mehta
Extracted originally to dsemonstrate an unused variables linter performance issue.
-/

def Hollom : Type := Nat × Nat × Nat

def ofHollom : Hollom → Nat × Nat × Nat := id

namespace Hollom

inductive HollomOrder : Nat × Nat × Nat → Nat × Nat × Nat → Prop
  | twice {x y n u v m : Nat} : m + 2 ≤ n → HollomOrder (x, y, n) (u, v, m)
  | within {x y u v m : Nat} : x ≤ u → y ≤ v → HollomOrder (x, y, m) (u, v, m)
  | next_min {x y u v m : Nat} : min x y + 1 ≤ min u v → HollomOrder (x, y, m + 1) (u, v, m)
  | next_add {x y u v m : Nat} : x + y ≤ 2 * (u + v) → HollomOrder (x, y, m + 1) (u, v, m)

set_option profiler true
set_option profiler.threshold 10

class Preorder (α : Type) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

class PartialOrder (α : Type) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

def test : PartialOrder Hollom where
  le x y := HollomOrder (ofHollom x) (ofHollom y)
  le_refl x := .within (Nat.le_refl _) (Nat.le_refl _)
  le_trans
  | _, _, _, .twice _, .twice _ => .twice (by omega)
  | _, _, _, .twice _, .within _ _ => .twice (by omega)
  | _, _, _, .twice _, .next_min _ => .twice (by omega)
  | _, _, _, .twice _, .next_add _ => .twice (by omega)
  | _, _, _, .within _ _, .twice _ => .twice (by omega)
  | _, _, _, .within _ _, .within _ _ => .within (by omega) (by omega)
  | _, _, _, .within _ _, .next_min _ => .next_min (by omega)
  | _, _, _, .within _ _, .next_add _ => .next_add (by omega)
  | _, _, _, .next_min _, .twice _ => .twice (by omega)
  | _, _, _, .next_min _, .within _ _ => .next_min (by omega)
  | _, _, _, .next_min _, .next_min _ => .twice (by omega)
  | _, _, _, .next_min _, .next_add _ => .twice (by omega)
  | _, _, _, .next_add _, .twice _ => .twice (by omega)
  | _, _, _, .next_add _, .within _ _ => .next_add (by omega)
  | _, _, _, .next_add _, .next_min _ => .twice (by omega)
  | _, _, _, .next_add _, .next_add _ => .twice (by omega)
  le_antisymm
  | _, _, .twice _, .twice _ => by omega
  | _, (_, _, _), .twice _, .within _ _ => by omega
  | _, _, .twice _, .next_min _ => by omega
  | _, _, .twice _, .next_add _ => by omega
  | _, _, .within _ _, .twice _ => by omega
  | _, _, .within _ _, .within _ _ => by congr 3 <;> omega
  | _, _, .next_min _, .twice _ => by omega
  | _, _, .next_add _, .twice _ => by omega
