import Lean

open Lean
open Lean.Meta
open Lean.Elab.Tactic

universes u
axiom elimEx (motive : Nat → Nat → Sort u) (x y : Nat)
  (diag  : (a : Nat) → motive a a)
  (upper : (delta a : Nat) → motive a (a + delta.succ))
  (lower : (delta a : Nat) → motive (a + delta.succ) a)
  : motive y x

theorem ex1 (p q : Nat) : p ≤ q ∨ p > q := by
  cases p, q using elimEx
  | diag    => apply Or.inl; apply Nat.leRefl
  | lower d => apply Or.inl; show p ≤ p + d.succ; admit
  | upper d => apply Or.inr; show q + d.succ > q; admit

theorem ex2 (p q : Nat) : p ≤ q ∨ p > q := by
  cases p, q using elimEx
  case lower => admit
  case upper => admit
  case diag  => apply Or.inl; apply Nat.leRefl

axiom parityElim (motive : Nat → Sort u)
  (even : (n : Nat) → motive (2*n))
  (odd  : (n : Nat) → motive (2*n+1))
  (n : Nat)
  : motive n

theorem time2Eq (n : Nat) : 2*n = n + n := by
  rw Nat.mulComm
  show (0 + n) + n = n+n
  rw Nat.zeroAdd
  rfl

theorem ex3 (n : Nat) : Exists (fun m => n = m + m ∨ n = m + m + 1) := by
  cases n using parityElim
  | even i =>
    apply Exists.intro i
    apply Or.inl
    rw time2Eq
    rfl
  | odd i =>
    apply Exists.intro i
    apply Or.inr
    rw time2Eq
    rfl
