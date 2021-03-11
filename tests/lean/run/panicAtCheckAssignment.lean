import Lean

open Lean
open Lean.Meta

def bug : MetaM Unit := do
  let i := 0
  forallTelescopeReducing arbitrary fun ys _ => do
    let mut j := 0
    for y in ys do
      throwError "#{i+1}"
      j := j + 1
