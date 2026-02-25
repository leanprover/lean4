/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
import Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
namespace Lean.Meta.Grind.Arith.Linear

partial def cleanupDenominators' (c : α)
    (getPoly : α → CommRing.Poly)
    (updateCnstr : α → CommRing.Poly → Int → Var → Nat → α)
    : LinearM α := do
  let s ← getStruct
  if s.fieldInst?.isNone then return c
  let some (_, char) := s.charInst? | return c
  unless char == 0 do return c
  withRingM <| go c
where
  go (c : α) : CommRing.RingM α := do
    let p := getPoly c
    let some (val, x) ← p.findInvNumeralVar? | return c
    let n := p.maxDegreeOf x
    let p := p.mulConst (val ^ n)
    let p := p.cancelVar val x
    go (updateCnstr c p val x n)

public def RingIneqCnstr.cleanupDenominators (c : RingIneqCnstr) : LinearM RingIneqCnstr :=
  cleanupDenominators' c (·.p) fun c p val x n => { c with p, h := .cancelDen c val x n }

public def RingEqCnstr.cleanupDenominators (c : RingEqCnstr) : LinearM RingEqCnstr :=
  cleanupDenominators' c (·.p) fun c p val x n => { c with p, h := .cancelDen c val x n }

public def RingDiseqCnstr.cleanupDenominators (c : RingDiseqCnstr) : LinearM RingDiseqCnstr := do
  let s ← getStruct
  if s.noNatDivInst?.isNone then return c
  cleanupDenominators' c (·.p) fun c p val x n => { c with p, h := .cancelDen c val x n }

end Lean.Meta.Grind.Arith.Linear
