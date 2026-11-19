import Lean

open Lean
open Lean.Meta

def bug : MetaM Unit := do
  let i := 0
  forallTelescopeReducing default fun ys _ => do
    let mut j := 0
    for y in ys do
      throwError "#{(i+1 : Nat)}"
      j := j + 1
