/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductives.Positivity

/-!
# InLean's inductive check: the classes the recursors eliminate

Twin of `ConLeche/Kernel/Inductives/ClassRead.lean`: the recursor family's
prefix read syntactically (motives, minor premises and their inductive
hypotheses), without checking it.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-- Twin of `ClassKey`. -/
structure ClassKey where
  ind : Name
  lvls : List Level
  ds : List Expr
  deriving Inhabited

/-- Twin of `ClassSlot`. -/
inductive ClassSlot where
  | motive (key : ClassKey)
  | minor (cls : Nat) (ctor : Name) (ihs : List (Nat × Nat))
  deriving Inhabited

/-- Twin of `ClassRead`. -/
structure ClassRead where
  slots : List ClassSlot
  recCls : List Nat
  deriving Inhabited

namespace ClassRead

/-- Twin of `ClassRead.classes`. -/
def classes (r : ClassRead) : List ClassKey :=
  r.slots.filterMap fun | .motive k => some k | _ => none

/-- Twin of `ClassRead.motiveSlot`. -/
def motiveSlot (r : ClassRead) (c : Nat) : Option Nat :=
  let ms := (List.range r.slots.length).filter fun s =>
    match r.slots[s]? with | some (.motive _) => true | _ => false
  ms[c]?

end ClassRead

/-- Twin of `classOfMotiveVar`. -/
def classOfMotiveVar (nP : Nat) (motPos : List Nat) (p : Nat) : Option Nat :=
  if nP ≤ p then motPos.findIdx? (· == p - nP) else none

/-- A variable's depth, at a variable head. -/
@[inline] def headDepth? (e : Expr) : Option Nat :=
  match e.getAppFn with
  | .fvar id => EO.fvDepth? id
  | _ => none

/-- Twin of `classReadMinor`. -/
def classReadMinor (nP : Nat) (motPos : List Nat) (d : Nat) (dom : Expr) :
    CheckCM (Option ClassSlot) := do
  let n := (piBinders dom).1.length
  let some (fvs, concl) ← openPisAtFvars n dom d | return none
  let some p := headDepth? concl | return none
  let some c := classOfMotiveVar nP motPos p | return none
  let some lastArg := (appArgs concl).getLast? | return none
  let .const C _ := lastArg.getAppFn | return none
  let mut ihs : List (Nat × Nat) := []
  for q in List.range fvs.length do
    let ty := piResult (← fvarTypeD (fvs.getD q default))
    match headDepth? ty with
    | some p' =>
      match classOfMotiveVar nP motPos p' with
      | some t =>
        match (appArgs ty).getLast? with
        | some a =>
          match headDepth? a with
          | some f => if d ≤ f then ihs := ihs ++ [(f - d, t)]
          | none => pure ()
        | none => pure ()
      | none => pure ()
    | none => pure ()
  return some (.minor c C ihs)

/-- Twin of `classReadSlots`. -/
def classReadSlots (nPc : Name → Nat) (np : Nat) :
    Nat → List Nat → Nat → Expr → CheckCM (Option (List ClassSlot))
  | 0, _, _, _ => pure (some [])
  | n + 1, motPos, d, .forallE _ dom body _ => do
    let slot? : Option ClassSlot ← match piResult dom with
      | .sort _ => pure do
        let (bs, _) := piBinders dom
        let mdom ← bs.getLast?
        let .const I us := mdom.getAppFn | none
        pure (ClassSlot.motive ⟨I, us, (appArgs mdom).take (nPc I)⟩)
      | _ => classReadMinor np motPos d dom
    let some slot := slot? | return none
    let motPos' := match slot with | .motive _ => motPos ++ [d - np] | _ => motPos
    let some rest ← classReadSlots nPc np n motPos' (d + 1) (body.inst1I (← mkFVarM d dom))
      | return none
    return some (slot :: rest)
  | _ + 1, _, _, _ => pure none

/-- Twin of `classRead`. -/
def classRead (nP : Nat) (nPc : Name → Nat) (recs : List RecShape) : CheckCM (Option ClassRead) := do
  let some rc0 := recs.head? | return none
  let some (_, body) ← openPisAtFvars nP rc0.cvR.type 0 | return none
  let some slots ← classReadSlots nPc nP (rc0.rP - nP) [] nP body | return none
  let motPos := (List.range slots.length).filter fun s =>
    match slots[s]? with | some (.motive _) => true | _ => false
  let mut recCls : List Nat := []
  for rc in recs do
    let some (_, concl) ← openPisAtFvars (rc.mI + 1) rc.cvR.type 0 | return none
    let some p := headDepth? concl | return none
    let some c := classOfMotiveVar nP motPos p | return none
    recCls := recCls ++ [c]
  return some ⟨slots, recCls⟩

end Lean.Kernel.InLean
