/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.Linear.Den
import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
import Lean.Meta.Tactic.Grind.Arith.Linear.Proof
namespace Lean.Meta.Grind.Arith.Linear

def isInstOf (fn? : Option Expr) (inst : Expr) : Bool :=
  if let some fn := fn? then
    isSameExpr fn.appArg! inst
  else
    false

public def IneqCnstr.assert (c : IneqCnstr) : LinearM Unit := do
  trace[grind.linarith.assert] "{← c.denoteExpr}"
  match c.p with
  | .nil =>
    if c.strict then
      trace[grind.linarith.unsat] "{← c.denoteExpr}"
      setInconsistent (.lt c)
    else
      trace[grind.linarith.trivial] "{← c.denoteExpr}"
  | .add a x _ =>
    trace[grind.linarith.assert.store] "{← c.denoteExpr}"
    c.p.updateOccs
    if a < 0 then
      modifyStruct fun s => { s with lowers := s.lowers.modify x (·.push c) }
    else
      modifyStruct fun s => { s with uppers := s.uppers.modify x (·.push c) }
    if (← c.satisfied) == .false then
      resetAssignmentFrom x

def propagateCommRingIneq (e : Expr) (lhs rhs : Expr) (strict : Bool) (eqTrue : Bool) : LinearM Unit := do
  let some lhs ← withRingM <| CommRing.reify? lhs (skipVar := false) | return ()
  let some rhs ← withRingM <| CommRing.reify? rhs (skipVar := false) | return ()
  let generation ← getGeneration e
  if eqTrue then
    let p := (lhs.sub rhs).toPoly
    let c : RingIneqCnstr := { p, strict, h := .core e lhs rhs }
    let c ← c.cleanupDenominators
    let p := c.p
    let lhs ← p.toIntModuleExpr generation
    let some lhs ← reify? lhs (skipVar := false) generation | return ()
    let p := lhs.norm
    let c : IneqCnstr := { p, strict, h := .ring c lhs }
    c.assert
  else if (← isLinearOrder) then
    let p := (rhs.sub lhs).toPoly
    let strict := !strict
    let c : RingIneqCnstr := { p, strict, h := .notCore e lhs rhs }
    let c ← c.cleanupDenominators
    let p := c.p
    let lhs ← p.toIntModuleExpr generation
    let some lhs ← reify? lhs (skipVar := false) generation | return ()
    let p := lhs.norm
    let c : IneqCnstr := { p, strict, h := .ring c lhs }
    c.assert
  else
    -- Negation for preorders is not supported
    modifyStruct fun s => { s with ignored := s.ignored.push e }

def propagateIntModuleIneq (e : Expr) (lhs rhs : Expr) (strict : Bool) (eqTrue : Bool) : LinearM Unit := do
  let some lhs ← reify? lhs (skipVar := false) (← getGeneration lhs) | return ()
  let some rhs ← reify? rhs (skipVar := false) (← getGeneration rhs) | return ()
  if eqTrue then
    let p := (lhs.sub rhs).norm
    let c : IneqCnstr := { p, strict, h := .core e lhs rhs }
    c.assert
  else if (← isLinearOrder) then
    let p := (rhs.sub lhs).norm
    let strict := !strict
    let c : IneqCnstr := { p, strict, h := .notCore e lhs rhs }
    c.assert
  else
    -- Negation for preorders is not supported
    modifyStruct fun s => { s with ignored := s.ignored.push e }

def propagateNatModuleIneq (e : Expr) (lhs rhs : Expr) (strict : Bool) (eqTrue : Bool) : OfNatModuleM Unit := do
  let ns ← getNatStruct
  let (lhs₁, _) ← ofNatModule lhs
  let (rhs₁, _) ← ofNatModule rhs
  LinearM.run ns.structId do
  let some lhs₂ ← reify? lhs₁ (skipVar := false) (← getGeneration lhs) | return ()
  let some rhs₂ ← reify? rhs₁ (skipVar := false) (← getGeneration rhs) | return ()
  if eqTrue then
    let p := (lhs₂.sub rhs₂).norm
    let c : IneqCnstr := { p, strict, h := .coreOfNat e ns.id lhs₂ rhs₂ }
    c.assert
  else
    let p := (rhs₂.sub lhs₂).norm
    let strict := !strict
    let c : IneqCnstr := { p, strict, h := .notCoreOfNat e ns.id lhs₂ rhs₂ }
    c.assert

public def propagateIneq (e : Expr) (eqTrue : Bool) : GoalM Unit := do
  unless (← getConfig).linarith do return ()
  let numArgs := e.getAppNumArgs
  unless numArgs == 4 do return ()
  let α := e.getArg! 0 numArgs
  let inst := e.getArg! 1 numArgs
  let lhs := e.getArg! 2 numArgs
  let rhs := e.getArg! 3 numArgs
  if let some structId ← getStructId? α then LinearM.run structId do
    let s ← getStruct
    let strict ← if isInstOf s.leFn? inst then
      pure false
    else if isInstOf s.ltFn? inst then
      pure true
    else
      return ()
    if (← isOrderedCommRing) then
      propagateCommRingIneq e lhs rhs strict eqTrue
    -- TODO: non-commutative ring normalizer
    else
      propagateIntModuleIneq e lhs rhs strict eqTrue
  else if let some natStructId ← getNatStructId? α then OfNatModuleM.run natStructId do
    let s ← getNatStruct
    if s.leInst?.isNone || s.isPreorderInst?.isNone || s.orderedAddInst?.isNone then return ()
    let strict ← if some inst == s.leInst? then
      pure false
    else if some inst == s.ltInst? then
      pure true
    else
      return ()
    if strict && s.lawfulOrderLTInst?.isNone then return ()
    if !eqTrue && s.isLinearInst?.isNone then return ()
    propagateNatModuleIneq e lhs rhs strict eqTrue

end Lean.Meta.Grind.Arith.Linear
