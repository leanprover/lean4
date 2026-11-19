import Lean.Meta

/-!
Regression tests that pattern errors inside the new `do` elaborator point at
the offending pattern with the proper diagnostic from the regular pattern-var
collector (e.g. "Invalid pattern: Expected a constructor or constant marked
with `[match_pattern]`", "ambiguous pattern, use fully qualified name") instead
of the catch-all "unsupported pattern in syntax match" used by syntax-quotation
matches.

* https://github.com/leanprover/lean4/issues/2215
* https://github.com/leanprover/lean4/issues/8304
* https://github.com/leanprover/lean4/issues/10393
-/

set_option backward.do.legacy false

inductive A where | a
inductive AA where | a

-- #10393
/-- error: ambiguous pattern, use fully qualified name, possible interpretations [AA.a, A.a] -/
#guard_msgs in
open A in
open AA in
def f (x : Option Nat) : Id Nat := Id.run do
  if let some a := x then
    22
  else
    33

-- #2215
/-- error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]` -/
#guard_msgs in
def foo (bar : Unit → Id Unit): Id Unit := do
  let mut edgeCount : Nat := 0
  match 42 with
  | 42 => bar () edgeCount := 43
  | _ => return ()


open Lean Meta

-- #8304: outside `do`, the proper diagnostic is produced
/--
error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`

Hint: Using one of these would be valid:
  [apply] `Or.inr`
  [apply] `PSum.inr`
  [apply] `Sum.inr`
  [apply] `Sum.Lex.inr`
  [apply] `Sum.LiftRel.inr`
-/
#guard_msgs in
def test1 : Nat :=
  let a : (Sum Nat Nat) := .inr 1
  let b : (Sum Nat Nat) := .inl 1
  let c : (Sum Nat Nat) := .inr 1
  match a, b, c with
  | .inr x , .inl y, inr z => return x+y+z
  | _,_,_ => return 37

-- #8304: inside `do`, the same diagnostic now surfaces too
/--
error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`

Hint: Using one of these would be valid:
  [apply] `Or.inr`
  [apply] `PSum.inr`
  [apply] `Sum.inr`
  [apply] `Sum.Lex.inr`
  [apply] `Sum.LiftRel.inr`
-/
#guard_msgs in
def test2 : MetaM Nat:= do
  let a : MetaM (Sum Nat Nat) := return .inr 1
  let b : MetaM (Sum Nat Nat) := return .inl 1
  let c : MetaM (Sum Nat Nat) := return .inr 1
  match ← a, ← b, ← c with
  | .inr x , .inl y, inr z => return x+y+z
  | _,_,_ => return 37

/--
error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`

Hint: Using one of these would be valid:
  [apply] `Or.inr`
  [apply] `PSum.inr`
  [apply] `Sum.inr`
  [apply] `Sum.Lex.inr`
  [apply] `Sum.LiftRel.inr`
-/
#guard_msgs in
def test3 : MetaM Nat:= do
  let a : MetaM (Sum Nat Nat) := return .inr 1
  let b : MetaM (Sum Nat Nat) := return .inl 1
  let c : MetaM (Sum Nat Nat) := return .inr 1
  let a ← a
  let b ← b
  let c ← c
  match a, b, c with
  | .inr x , .inl y, inr z => return x+y+z
  | _,_,_ => return 37
