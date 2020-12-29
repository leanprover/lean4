import Lean

@[simp] theorem ex1 (x : Nat) : 2 * x = x + x :=
  sorry

@[simp] theorem ex2 (xs : List α) : xs ++ [] = xs :=
  sorry

@[simp] theorem ex3 (xs ys zs : List α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  sorry

axiom aux {α} (f : List α → List α) (xs ys : List α) : f (xs ++ ys) ++ [] = f (xs ++ ys)

open Lean
open Lean.Meta

def tst1 : MetaM Unit := do
  let s ← Meta.getSimpLemmas
  trace[Meta.debug]! "{fmt s}"

set_option trace.Meta.debug true in
#eval tst1

def tst2 : MetaM Unit := do
  let c ← getConstInfo `aux
  forallTelescopeReducing c.type fun xs type => do
    match type.eq? with
    | none => throwError! "unexpected"
    | some (_, lhs, _) =>
      trace[Meta.debug]! "lhs: {lhs}"
      let s ← Meta.getSimpLemmas
      let m ← s.getMatch lhs
      assert! m.size == 1
      trace[Meta.debug]! "resullt: {m}"

set_option trace.Meta.debug true in
#eval tst2
