/-
Tests for `SymExtension` mechanism.
-/
module
public meta import SymExt.Decl
meta import Lean.Meta.Sym

open Lean Elab Tactic Meta Sym

run_meta SymM.run do
  let c0 ← getMyCounter
  assert! c0 == 0
  incrementMyCounter
  let c1 ← getMyCounter
  assert! c1 == 1
  incrementMyCounter
  let c2 ← getMyCounter
  assert! c2 == 2

run_meta do
  SymM.run do
    incrementMyCounter
    let c ← getMyCounter
    assert! c == 1
  -- Should reset the counter
  SymM.run do
    let c ← getMyCounter
    assert! c == 0
