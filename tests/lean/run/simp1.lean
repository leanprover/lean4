import Lean

@[simp] theorem ex1 (x : Nat) : 2 * x = x + x :=
  sorry

@[simp] theorem ex2 (xs : List α) : xs ++ [] = xs :=
  sorry

@[simp] theorem ex3 (xs ys zs : List α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  sorry

@[simp] theorem ex5 (p : Prop) : p ∨ True :=
  sorry

@[simp] theorem ex4 (xs : List α) : ¬(x :: xs = []) :=
  sorry

@[simp] theorem ex6 (p q : Prop) : p ∨ q ↔ q ∨ p:=
  sorry

@[simp high] theorem ex7 [Add α] (a b : α) : a + b = b + a :=
  sorry

@[simp↓] theorem ex8 [Add α] (p q : Prop) : (¬ (p ∧ q)) = (¬p ∨ ¬q) :=
  sorry

axiom aux {α} (f : List α → List α) (xs ys : List α) : f (xs ++ ys) ++ [] = f (xs ++ ys)

open Lean
open Lean.Meta

def tst1 : MetaM Unit := do
  let thms  ← Meta.getSimpTheorems
  trace[Meta.debug] "{thms.pre}\n-----\n{thms.post}"

set_option trace.Meta.debug true in
#eval tst1

def tst2 : MetaM Unit := do
  let c ← getConstInfo `aux
  forallTelescopeReducing c.type fun xs type => do
    match type.eq? with
    | none => throwError "unexpected"
    | some (_, lhs, _) =>
      trace[Meta.debug] "lhs: {lhs}"
      let s ← Meta.getSimpTheorems
      let m ← s.post.getMatch lhs {}
      trace[Meta.debug] "result: {m}"
      assert! m.any fun s => s.origin == .decl `ex2


set_option trace.Meta.debug true in
#eval tst2
