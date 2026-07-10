/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Reg

public section

namespace Lean.Compiler.Backend.ARM64

/-!
# Register Classes

Register classes group physical registers by their use case and ABI properties.
This follows oxcaml's reg_class pattern for efficient register allocation.

Key classes:
- GP: General-purpose registers (x0-x30)
- FP: Floating-point/SIMD registers (v0-v31)
- CallerSaved: Registers that may be clobbered by function calls
- CalleeSaved: Registers preserved across function calls
- Scratch: Temporary registers for codegen (subset of caller-saved)
- Argument: Registers used for passing arguments (x0-x7, v0-v7)
-/

/-- Register class identifier -/
inductive RegClassId where
  | gp           -- General-purpose (x registers)
  | fp           -- Floating-point (v/d/s registers)
  | gpCallerSaved
  | gpCalleeSaved
  | fpCallerSaved
  | fpCalleeSaved
  | gpArg        -- GP argument registers (x0-x7)
  | fpArg        -- FP argument registers (v0-v7)
  | scratch      -- Scratch registers for codegen
  deriving Inhabited, BEq, DecidableEq, Repr, Hashable

/-- Register class containing available registers and metadata -/
structure RegClass where
  /-- Class identifier -/
  id : RegClassId
  /-- Available physical registers in this class (order matters for allocation) -/
  regs : Array PhysReg
  deriving Inhabited, Repr

namespace RegClass

/-- All general-purpose registers (x0-x30, excluding sp/xzr) -/
def allGP : Array PhysReg := #[
  .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7,
  .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
  .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23,
  .x24, .x25, .x26, .x27, .x28, .x29, .x30
]

/-- All floating-point registers (v0-v31) -/
def allFP : Array PhysReg := #[
  .v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7,
  .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15,
  .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
  .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31
]

/-- Caller-saved GP registers (x0-x18, clobbered by calls) -/
def gpCallerSaved : Array PhysReg := #[
  .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7,
  .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
  .x16, .x17, .x18
]

/-- Callee-saved GP registers (x19-x28, preserved across calls)
    Note: x29 (fp) and x30 (lr) are handled specially -/
def gpCalleeSaved : Array PhysReg := #[
  .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28
]

/-- Caller-saved FP registers -/
def fpCallerSaved : Array PhysReg := #[
  .v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7,
  .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
  .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31
]

/-- Callee-saved FP registers (lower 64 bits of v8-v15 preserved) -/
def fpCalleeSaved : Array PhysReg := #[
  .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15
]

/-- GP argument registers (x0-x7) -/
def gpArg : Array PhysReg := #[
  .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7
]

/-- FP argument registers (v0-v7) -/
def fpArg : Array PhysReg := #[
  .v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7
]

/-- Scratch registers for temporary values during code generation.
    These are caller-saved and reserved for lowering operations.
    x8 is used as general scratch in getDstReg and other places.
    x9 is used in saveConflict for constructor conflicts.
    x10 is used in Constructor.lean to save x8 across boxing calls.
    DO NOT allocate these to variables - they are for lowering only. -/
def scratch : Array PhysReg := #[
  .x8, .x9, .x10
]

/-- Caller-saved GP registers available for variable allocation.
    These can only be used for variables that do NOT span function calls.
    x11-x15 are safe because they're not used by the lowering code. -/
def allocatableGPCallerSaved : Array PhysReg := #[
  .x11, .x12, .x13, .x14, .x15
]

/-- FP scratch registers for temporary float values -/
def fpScratch : Array PhysReg := #[
  .v16, .v17, .v18, .v19
]

/-- Callee-saved GP registers available for allocation (x19-x28).
    These are preserved across function calls, so can be used for any value. -/
def allocatableGPCalleeSaved : Array PhysReg := #[
  .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28
]

/-- Allocatable GP registers for linear scan.
    Only use callee-saved registers (x19-x28) to avoid clobbering by function calls.
    Caller-saved registers (x9-x15) would require spilling around every call,
    which is more complex to implement correctly. -/
def allocatableGP : Array PhysReg := #[
  -- Callee-saved only - these survive function calls
  .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28
]

/-- Allocatable FP registers for linear scan.
    ONLY use callee-saved (v8-v15) to avoid clobbering by function calls. -/
def allocatableFP : Array PhysReg := #[
  -- Callee-saved only - these survive function calls
  .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15
]

/-- Get register class by ID -/
def ofId : RegClassId → RegClass
  | .gp => { id := .gp, regs := allGP }
  | .fp => { id := .fp, regs := allFP }
  | .gpCallerSaved => { id := .gpCallerSaved, regs := gpCallerSaved }
  | .gpCalleeSaved => { id := .gpCalleeSaved, regs := gpCalleeSaved }
  | .fpCallerSaved => { id := .fpCallerSaved, regs := fpCallerSaved }
  | .fpCalleeSaved => { id := .fpCalleeSaved, regs := fpCalleeSaved }
  | .gpArg => { id := .gpArg, regs := gpArg }
  | .fpArg => { id := .fpArg, regs := fpArg }
  | .scratch => { id := .scratch, regs := scratch }

/-- Get register class for a machine type -/
def forMachineType : MachineType → RegClass
  | .int64 | .int32 | .addr | .val => ofId .gp
  | .float64 | .float32 => ofId .fp

/-- Get allocatable registers for a machine type -/
def allocatableFor : MachineType → Array PhysReg
  | .int64 | .int32 | .addr | .val => allocatableGP
  | .float64 | .float32 => allocatableFP

/-- Check if a register belongs to this class -/
def contains (rc : RegClass) (r : PhysReg) : Bool :=
  rc.regs.contains r

/-- Number of registers in class -/
def size (rc : RegClass) : Nat := rc.regs.size

/-- Get argument register for position (0-7 for GP, 0-7 for FP) -/
def getArgReg (usesFP : Bool) (idx : Nat) : Option PhysReg :=
  if usesFP then
    if idx < 8 then some fpArg[idx]! else none
  else
    if idx < 8 then some gpArg[idx]! else none

/-- Get GP argument register by index -/
def getGPArgReg (idx : Nat) : PhysReg :=
  match idx with
  | 0 => .x0 | 1 => .x1 | 2 => .x2 | 3 => .x3
  | 4 => .x4 | 5 => .x5 | 6 => .x6 | 7 => .x7
  | _ => .x8  -- Fallback for >8 params (should be on stack)

/-- Get FP argument register by index -/
def getFPArgReg (idx : Nat) : PhysReg :=
  match idx with
  | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3
  | 4 => .v4 | 5 => .v5 | 6 => .v6 | 7 => .v7
  | _ => .v16  -- Fallback for >8 params (should be on stack)

end RegClass

/-!
## Register Set

Efficient set representation for register tracking.
-/

/-- Set of physical registers using a bitmap -/
structure PhysRegSet where
  /-- Bitmap for GP registers (bits 0-30 for x0-x30) -/
  gpMask : UInt64 := 0
  /-- Bitmap for FP registers (bits 0-31 for v0-v31) -/
  fpMask : UInt64 := 0
  deriving Inhabited, BEq, Repr

namespace PhysRegSet

/-- Empty register set -/
def empty : PhysRegSet := {}

/-- Check if set is empty -/
def isEmpty (s : PhysRegSet) : Bool := s.gpMask == 0 && s.fpMask == 0

/-- Insert a register -/
def insert (s : PhysRegSet) (r : PhysReg) : PhysRegSet :=
  let n := r.toNat
  if r.isFP then
    { s with fpMask := s.fpMask ||| (1 <<< (n - 32).toUInt64) }
  else
    { s with gpMask := s.gpMask ||| (1 <<< n.toUInt64) }

/-- Check membership -/
def contains (s : PhysRegSet) (r : PhysReg) : Bool :=
  let n := r.toNat
  if r.isFP then
    (s.fpMask >>> (n - 32).toUInt64) &&& 1 == 1
  else
    (s.gpMask >>> n.toUInt64) &&& 1 == 1

/-- Remove a register -/
def erase (s : PhysRegSet) (r : PhysReg) : PhysRegSet :=
  let n := r.toNat
  if r.isFP then
    { s with fpMask := s.fpMask &&& ~~~(1 <<< (n - 32).toUInt64) }
  else
    { s with gpMask := s.gpMask &&& ~~~(1 <<< n.toUInt64) }

/-- Union of two sets -/
def union (s1 s2 : PhysRegSet) : PhysRegSet :=
  { gpMask := s1.gpMask ||| s2.gpMask
  , fpMask := s1.fpMask ||| s2.fpMask }

/-- Intersection of two sets -/
def inter (s1 s2 : PhysRegSet) : PhysRegSet :=
  { gpMask := s1.gpMask &&& s2.gpMask
  , fpMask := s1.fpMask &&& s2.fpMask }

/-- Difference (s1 - s2) -/
def diff (s1 s2 : PhysRegSet) : PhysRegSet :=
  { gpMask := s1.gpMask &&& ~~~s2.gpMask
  , fpMask := s1.fpMask &&& ~~~s2.fpMask }

/-- Create set from array -/
def ofArray (regs : Array PhysReg) : PhysRegSet :=
  regs.foldl insert empty

/-- Convert to array -/
def toArray (s : PhysRegSet) : Array PhysReg := Id.run do
  let mut result := #[]
  for r in RegClass.allGP do
    if s.contains r then result := result.push r
  for r in RegClass.allFP do
    if s.contains r then result := result.push r
  return result

/-- Count set bits in UInt64 -/
private def popCount64 (x : UInt64) : Nat := Id.run do
  let mut n := x
  let mut count := 0
  for _ in [:64] do
    if n == 0 then break
    if n &&& 1 == 1 then count := count + 1
    n := n >>> 1
  return count

/-- Number of registers in set -/
def size (s : PhysRegSet) : Nat :=
  popCount64 s.gpMask + popCount64 s.fpMask

instance : EmptyCollection PhysRegSet := ⟨empty⟩
instance : Membership PhysReg PhysRegSet := ⟨fun r s => PhysRegSet.contains r s⟩

end PhysRegSet

end Lean.Compiler.Backend.ARM64

end
