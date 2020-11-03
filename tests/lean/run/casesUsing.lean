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
