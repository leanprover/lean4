/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.Simp.SimpM
import Lean.Compiler.LCNF.Simp.Used

public section

namespace Lean.Compiler.LCNF
namespace Simp

def addDefaultAlt (alts : Array (Alt .pure)) : SimpM (Array (Alt .pure)) := do
  if alts.size <= 1 then
    return alts
  else
    let some (rootAlt, otherAlts) ← chooseRootAlt alts | return alts
    let mut differentAlts := #[]
    let mut eqvAlts := #[]
    for alt in otherAlts do
      if ← hasNoUsedParams alt <&&> (pure <| alt.getCode.alphaEqv rootAlt.getCode) then
        eqvAlts := eqvAlts.push alt
      else
        differentAlts := differentAlts.push alt
    if eqvAlts.isEmpty then return alts
    markSimplified
    eraseParams rootAlt.getParams
    eqvAlts.forM fun alt => do
      eraseParams alt.getParams
      eraseCode alt.getCode
    return differentAlts.push (.default rootAlt.getCode)
where
  chooseRootAlt (alts : Array (Alt .pure)) : SimpM (Option (Alt .pure × Array (Alt .pure))) := do
    let some rootIdx ← chooseRootIdx alts | return none
    let rootAlt := alts[rootIdx]!
    let mut otherAlts := Array.emptyWithCapacity (alts.size - 1)
    for idx in 0...alts.size do
      if idx != rootIdx then
        otherAlts := otherAlts.push alts[idx]!
    return (rootAlt, otherAlts)

  chooseRootIdx (alts : Array (Alt .pure)) : SimpM (Option Nat) := do
    -- if there is a default we *must* compare against it to avoid ending up with 2 defaults.
    if let some defaultIdx := alts.findIdx? (· matches .default ..) then
      return some defaultIdx
    else
      alts.findIdxM? hasNoUsedParams

  hasNoUsedParams (alt : Alt .pure) : SimpM Bool :=
    alt.getParams.allM (fun p => return !(← isUsed p.fvarId))
