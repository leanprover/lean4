/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.IR.Basic
public import Lean.Data.Name

public section

namespace Lean.Compiler.Backend.ARM64

/-!
# ARM64 Register Representation

This module provides the register representation for the ARM64 backend,
following patterns from oxcaml's register allocator:
- Physical registers with explicit classification (GP, FP, etc.)
- Location tracking (Unknown, Reg, Stack) for allocation state
- Register classes for efficient allocation by type
-/

/-- Floating-point precision for FP operations -/
inductive FloatPrec where
  | single  -- 32-bit float (s0-s31 register view)
  | double  -- 64-bit double (d0-d31 register view)
  deriving Inhabited, BEq, DecidableEq, Repr, Hashable

instance : ToString FloatPrec where
  toString
    | .single => "s"
    | .double => "d"

/-- ARM64 physical registers. -/
inductive PhysReg where
  -- General purpose registers (X0-X30)
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7
  | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30
  -- Stack pointer / zero register
  | sp
  | xzr
  -- SIMD/FP registers (V0-V31)
  | v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7
  | v8 | v9 | v10 | v11 | v12 | v13 | v14 | v15
  | v16 | v17 | v18 | v19 | v20 | v21 | v22 | v23
  | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31
  deriving Inhabited, BEq, DecidableEq, Repr, Hashable

namespace PhysReg

/-- Convert a register to a numeric identifier. -/
def toNat : PhysReg → Nat
  | x0 => 0 | x1 => 1 | x2 => 2 | x3 => 3 | x4 => 4 | x5 => 5 | x6 => 6 | x7 => 7
  | x8 => 8 | x9 => 9 | x10 => 10 | x11 => 11 | x12 => 12 | x13 => 13 | x14 => 14 | x15 => 15
  | x16 => 16 | x17 => 17 | x18 => 18 | x19 => 19 | x20 => 20 | x21 => 21 | x22 => 22 | x23 => 23
  | x24 => 24 | x25 => 25 | x26 => 26 | x27 => 27 | x28 => 28 | x29 => 29 | x30 => 30
  | sp => 31 | xzr => 31
  | v0 => 32 | v1 => 33 | v2 => 34 | v3 => 35 | v4 => 36 | v5 => 37 | v6 => 38 | v7 => 39
  | v8 => 40 | v9 => 41 | v10 => 42 | v11 => 43 | v12 => 44 | v13 => 45 | v14 => 46 | v15 => 47
  | v16 => 48 | v17 => 49 | v18 => 50 | v19 => 51 | v20 => 52 | v21 => 53 | v22 => 54 | v23 => 55
  | v24 => 56 | v25 => 57 | v26 => 58 | v27 => 59 | v28 => 60 | v29 => 61 | v30 => 62 | v31 => 63

instance : ToString PhysReg where
  toString
    | x0 => "x0" | x1 => "x1" | x2 => "x2" | x3 => "x3" | x4 => "x4" | x5 => "x5" | x6 => "x6" | x7 => "x7"
    | x8 => "x8" | x9 => "x9" | x10 => "x10" | x11 => "x11" | x12 => "x12" | x13 => "x13" | x14 => "x14" | x15 => "x15"
    | x16 => "x16" | x17 => "x17" | x18 => "x18" | x19 => "x19" | x20 => "x20" | x21 => "x21" | x22 => "x22" | x23 => "x23"
    | x24 => "x24" | x25 => "x25" | x26 => "x26" | x27 => "x27" | x28 => "x28" | x29 => "x29" | x30 => "x30"
    | sp => "sp" | xzr => "xzr"
    | v0 => "v0" | v1 => "v1" | v2 => "v2" | v3 => "v3" | v4 => "v4" | v5 => "v5" | v6 => "v6" | v7 => "v7"
    | v8 => "v8" | v9 => "v9" | v10 => "v10" | v11 => "v11" | v12 => "v12" | v13 => "v13" | v14 => "v14" | v15 => "v15"
    | v16 => "v16" | v17 => "v17" | v18 => "v18" | v19 => "v19" | v20 => "v20" | v21 => "v21" | v22 => "v22" | v23 => "v23"
    | v24 => "v24" | v25 => "v25" | v26 => "v26" | v27 => "v27" | v28 => "v28" | v29 => "v29" | v30 => "v30" | v31 => "v31"

/-- Render a general-purpose register using its 32-bit view (`w0`-`w30`). -/
def toGPR32String : PhysReg → String
  | x0 => "w0" | x1 => "w1" | x2 => "w2" | x3 => "w3" | x4 => "w4" | x5 => "w5" | x6 => "w6" | x7 => "w7"
  | x8 => "w8" | x9 => "w9" | x10 => "w10" | x11 => "w11" | x12 => "w12" | x13 => "w13" | x14 => "w14" | x15 => "w15"
  | x16 => "w16" | x17 => "w17" | x18 => "w18" | x19 => "w19" | x20 => "w20" | x21 => "w21" | x22 => "w22" | x23 => "w23"
  | x24 => "w24" | x25 => "w25" | x26 => "w26" | x27 => "w27" | x28 => "w28" | x29 => "w29" | x30 => "w30"
  | xzr => "wzr"
  | sp => "wsp"
  | p => toString p -- fall back for non-GPR registers

/-- Caller-saved registers according to the ARM64 ABI. -/
def isCallerSaved : PhysReg → Bool
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 => true
  | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15 => true
  | x16 | x17 | x18 => true
  | v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7 => true
  | v16 | v17 | v18 | v19 | v20 | v21 | v22 | v23 => true
  | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31 => true
  | _ => false

/-- Callee-saved registers according to the ARM64 ABI. -/
def isCalleeSaved : PhysReg → Bool
  | x19 | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 => true
  | x29 | x30 => true
  | v8 | v9 | v10 | v11 | v12 | v13 | v14 | v15 => true
  | _ => false

/-- Check if register is a floating-point/SIMD register -/
def isFP : PhysReg → Bool
  | v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7 => true
  | v8 | v9 | v10 | v11 | v12 | v13 | v14 | v15 => true
  | v16 | v17 | v18 | v19 | v20 | v21 | v22 | v23 => true
  | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31 => true
  | _ => false

/-- Check if register is a general-purpose register -/
def isGP : PhysReg → Bool
  | sp | xzr => false
  | r => !r.isFP

/-- Render FP register with precision prefix (s for single, d for double) -/
def toFPString (prec : FloatPrec) : PhysReg → String
  | v0 => if prec == .single then "s0" else "d0"
  | v1 => if prec == .single then "s1" else "d1"
  | v2 => if prec == .single then "s2" else "d2"
  | v3 => if prec == .single then "s3" else "d3"
  | v4 => if prec == .single then "s4" else "d4"
  | v5 => if prec == .single then "s5" else "d5"
  | v6 => if prec == .single then "s6" else "d6"
  | v7 => if prec == .single then "s7" else "d7"
  | v8 => if prec == .single then "s8" else "d8"
  | v9 => if prec == .single then "s9" else "d9"
  | v10 => if prec == .single then "s10" else "d10"
  | v11 => if prec == .single then "s11" else "d11"
  | v12 => if prec == .single then "s12" else "d12"
  | v13 => if prec == .single then "s13" else "d13"
  | v14 => if prec == .single then "s14" else "d14"
  | v15 => if prec == .single then "s15" else "d15"
  | v16 => if prec == .single then "s16" else "d16"
  | v17 => if prec == .single then "s17" else "d17"
  | v18 => if prec == .single then "s18" else "d18"
  | v19 => if prec == .single then "s19" else "d19"
  | v20 => if prec == .single then "s20" else "d20"
  | v21 => if prec == .single then "s21" else "d21"
  | v22 => if prec == .single then "s22" else "d22"
  | v23 => if prec == .single then "s23" else "d23"
  | v24 => if prec == .single then "s24" else "d24"
  | v25 => if prec == .single then "s25" else "d25"
  | v26 => if prec == .single then "s26" else "d26"
  | v27 => if prec == .single then "s27" else "d27"
  | v28 => if prec == .single then "s28" else "d28"
  | v29 => if prec == .single then "s29" else "d29"
  | v30 => if prec == .single then "s30" else "d30"
  | v31 => if prec == .single then "s31" else "d31"
  | r => toString r  -- fallback for GP registers

end PhysReg

/-!
## Machine Types

Machine-level types representing how values are stored in registers,
distinct from IR types which are semantic.
-/

/-- Machine-level type for register allocation -/
inductive MachineType where
  | int64   -- 64-bit integer (GP register, x view)
  | int32   -- 32-bit integer (GP register, w view)
  | float64 -- 64-bit float (FP register, d view)
  | float32 -- 32-bit float (FP register, s view)
  | addr    -- Pointer (GP register)
  | val     -- Lean object reference (GP register, reference counted)
  deriving Inhabited, BEq, DecidableEq, Repr, Hashable

namespace MachineType

/-- Check if this type uses a floating-point register -/
def usesFPReg : MachineType → Bool
  | .float64 | .float32 => true
  | _ => false

/-- Check if this type uses a general-purpose register -/
def usesGPReg : MachineType → Bool
  | .int64 | .int32 | .addr | .val => true
  | _ => false

/-- Convert IR type to machine type -/
def ofIRType : IR.IRType → MachineType
  | .float => .float64
  | .float32 => .float32
  | .uint8 | .uint16 | .uint32 => .int32
  | .uint64 | .usize => .int64
  | .object | .tobject | .erased | .void | .tagged => .val
  | .struct _ _ | .union _ _ => .val  -- Structs/unions treated as pointers

instance : ToString MachineType where
  toString
    | .int64 => "i64"
    | .int32 => "i32"
    | .float64 => "f64"
    | .float32 => "f32"
    | .addr => "addr"
    | .val => "val"

end MachineType

/-!
## Stack Slots

Different kinds of stack locations for spilled values and parameters.
Following oxcaml's stack_location type.
-/

/-- Stack slot location types -/
inductive StackSlot where
  | local_ (offset : Nat)    -- Local spill slot in current frame
  | incoming (offset : Nat)  -- Parameter passed by caller (callee's view)
  | outgoing (offset : Nat)  -- Argument to callee (caller's view)
  deriving Inhabited, BEq, DecidableEq, Repr, Hashable

namespace StackSlot

/-- Get the byte offset of a stack slot -/
def byteOffset : StackSlot → Nat
  | .local_ n => n * 8
  | .incoming n => n * 8
  | .outgoing n => n * 8

instance : ToString StackSlot where
  toString
    | .local_ n => s!"[sp, #{n * 8}]"
    | .incoming n => s!"[fp, #{n * 8}]"
    | .outgoing n => s!"[sp, #{n * 8}]"

end StackSlot

/-!
## Location

Register location state following oxcaml's location type.
Tracks where a virtual register's value currently resides.
-/

/-- Location of a register value -/
inductive Location where
  | unknown                -- Not yet allocated
  | reg (r : PhysReg)      -- In a physical register
  | stack (s : StackSlot)  -- On the stack
  deriving Inhabited, BEq, Repr

namespace Location

/-- Check if location is a physical register -/
def isReg : Location → Bool
  | .reg _ => true
  | _ => false

/-- Check if location is on the stack -/
def isStack : Location → Bool
  | .stack _ => true
  | _ => false

/-- Check if location is unknown (not yet allocated) -/
def isUnknown : Location → Bool
  | .unknown => true
  | _ => false

/-- Get physical register if location is a register -/
def getPhysReg? : Location → Option PhysReg
  | .reg r => some r
  | _ => none

/-- Get stack slot if location is on stack -/
def getStackSlot? : Location → Option StackSlot
  | .stack s => some s
  | _ => none

instance : ToString Location where
  toString
    | .unknown => "?"
    | .reg r => toString r
    | .stack s => toString s

end Location

/-!
## Virtual Register (with location tracking)

New register representation that tracks allocation state.
Each register has a unique ID (stamp), machine type, and mutable location.
-/

/-- Virtual register with location tracking -/
structure VReg where
  /-- Unique identifier (stamp) for this register -/
  id : Nat
  /-- Machine type determining register class -/
  ty : MachineType
  /-- Debug name (from IR variable) -/
  name : Option String := none
  /-- Current allocation location -/
  loc : Location := .unknown
  deriving Inhabited, Repr

namespace VReg

/-- Create a new virtual register -/
def mk' (id : Nat) (ty : MachineType) (name : Option String := none) : VReg :=
  { id, ty, name, loc := .unknown }

/-- Check if register has been allocated -/
def isAllocated (r : VReg) : Bool := !r.loc.isUnknown

/-- Check if register is spilled to stack -/
def isSpilled (r : VReg) : Bool := r.loc.isStack

/-- Check if register is in a physical register -/
def isInReg (r : VReg) : Bool := r.loc.isReg

/-- Get physical register if allocated to one -/
def getPhysReg? (r : VReg) : Option PhysReg := r.loc.getPhysReg?

/-- Get stack slot if spilled -/
def getStackSlot? (r : VReg) : Option StackSlot := r.loc.getStackSlot?

/-- Update location -/
def withLoc (r : VReg) (loc : Location) : VReg := { r with loc }

/-- Allocate to a physical register -/
def allocateTo (r : VReg) (phys : PhysReg) : VReg := r.withLoc (.reg phys)

/-- Spill to a stack slot -/
def spillTo (r : VReg) (slot : StackSlot) : VReg := r.withLoc (.stack slot)

instance : BEq VReg where
  beq a b := a.id == b.id

instance : Hashable VReg where
  hash r := hash r.id

instance : ToString VReg where
  toString r :=
    let nameStr := match r.name with
      | some n => n
      | none => s!"v{r.id}"
    let locStr := if r.loc.isUnknown then "" else s!" @ {r.loc}"
    s!"{nameStr}:{r.ty}{locStr}"

end VReg

/-!
## Backward-Compatible Reg Type

The existing Reg type for compatibility with current code.
Will be phased out as we migrate to VReg.
-/

/-- Either a virtual register or a concrete physical register (legacy type) -/
inductive Reg where
  | virt (id : IR.VarId)
  | phys (r : PhysReg)
  deriving Inhabited, BEq, Repr

instance : ToString Reg where
  toString
    | .virt v => s!"vreg{v.idx}"
    | .phys p => toString p

/-- Render a register as a 32-bit general-purpose name when possible. -/
def Reg.toGPR32String : Reg → String
  | .phys p => PhysReg.toGPR32String p
  | .virt v => s!"vreg{v.idx}"

end Lean.Compiler.Backend.ARM64

end
