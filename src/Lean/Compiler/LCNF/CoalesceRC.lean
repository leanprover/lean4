/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF

/-!
# Coalesce Reference Counting Operations

This pass coalesces multiple `inc`/`dec` operations on the same variable within a basic block.
Within a basic block, it is always safe to:
- Move all increments on a variable to the first `inc` location (summing the counts). Because if
  there are later `inc`s no intermediate operation can observe RC=1 (as the value must stay alive
  until the later inc) and thus doing all relevant `inc` in the beginning doesn't change
  semantics.
- Move all decrements on a variable to the last `dec` location (summing the counts). Because the
  value is guaranteed to stay alive until at least the last `dec` anyway so a similiar argument to
  `inc` holds.

Crucially this pass must be placed after `expandResetReuse` as that one relies on `inc`s still being
present in their original location for optimization purposes.
-/

private structure State where
  /-- Total inc count per variable in the current basic block (accumulated going forward). -/
  incTotal : Std.HashMap FVarId Nat := {}
  /-- Total dec count per variable in the current basic block (accumulated going forward). -/
  decTotal : Std.HashMap FVarId Nat := {}
  /--
  Inc count seen so far per variable going backward. When this equals `incTotal`, we've
  reached the first inc and should emit the coalesced operation.
  -/
  incAccum : Std.HashMap FVarId Nat := {}
  /--
  Whether we've already emitted the coalesced dec for a variable (going backward, the first
  dec encountered is the last in the block).
  -/
  decPlaced : Std.HashSet FVarId := {}

private abbrev M := StateRefT State CompilerM

/--
Coalesce inc/dec operations within individual basic blocks.
-/
partial def Code.coalesceRC (code : Code .impure) : CompilerM (Code .impure) := do
  go code |>.run' {}
where
  go (code : Code .impure) : M (Code .impure) := do
    match code with
    | .inc fvarId n check persistent k _ =>
      modify fun s => { s with incTotal := s.incTotal.alter fvarId (fun v? => some ((v?.getD 0) + n)) }
      let k ← go k
      modify fun s => { s with incAccum := s.incAccum.alter fvarId (fun v? => some ((v?.getD 0) + n)) }
      let s ← get
      if s.incAccum[fvarId]! == s.incTotal[fvarId]! then
        return .inc fvarId s.incTotal[fvarId]! check persistent k
      else
        return k
    | .dec fvarId n check persistent k _ =>
      modify fun s => { s with decTotal := s.decTotal.alter fvarId (fun v? => some ((v?.getD 0) + n)) }
      let k ← go k
      let s ← get
      if !s.decPlaced.contains fvarId then
        modify fun s => { s with decPlaced := s.decPlaced.insert fvarId }
        return .dec fvarId s.decTotal[fvarId]! check persistent k
      else
        return k
    | .let _ k =>
      let k ← go k
      return code.updateCont! k
    | .jp decl k =>
      let value ← decl.value.coalesceRC
      let decl ← decl.updateValue value
      let k ← go k
      return code.updateFun! decl k
    | .cases c =>
      let alts ← c.alts.mapMonoM (·.mapCodeM (·.coalesceRC))
      return code.updateAlts! alts
    | .del _ k _ =>
      let k ← go k
      return code.updateCont! k
    | .oset (k := k) .. | .uset (k := k) .. | .sset (k := k) .. | .setTag (k := k) .. =>
      let k ← go k
      return code.updateCont! k
    | .return .. | .jmp .. | .unreach .. => return code

def Decl.coalesceRC (decl : Decl .impure) : CompilerM (Decl .impure) := do
  let value ← decl.value.mapCodeM Code.coalesceRC
  return { decl with value }

public def coalesceRC : Pass :=
  .mkPerDeclaration `coalesceRc .impure Decl.coalesceRC

builtin_initialize
  registerTraceClass `Compiler.coalesceRc (inherited := true)

end Lean.Compiler.LCNF
