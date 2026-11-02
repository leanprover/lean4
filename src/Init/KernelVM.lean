/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Init.Data.Int.Basic
public import Init.Data.UInt.Basic
public import Init.Data.Array.Basic

/-!
# A small imperative machine for kernel certificate checking

`Lean.KernelVM.run p inputs fuel` runs the program `p` on the input numerals `inputs` and returns
whether it succeeds. The definitions here are the reference semantics. The kernel evaluates `run`
natively when the program is a closed term and the inputs and fuel are numerals, and the result
must agree with these definitions. A kernel without this acceleration can still unfold them.

Inputs are read-only byte arrays, encoded as natural numbers in little-endian order. The machine
works on 64-bit words. It has registers, indexed by numerals in the program, and a memory indexed
by words. Both start out as all zeros and grow as they are written.

The kernel also evaluates `Nat.getByte` and `Nat.getUInt64` natively, so that proofs by kernel
reduction can read inputs in time proportional to their size.
-/

@[expose] public section

namespace Nat

/-- Byte `i` of `n`, in little-endian order. Evaluated natively by the kernel. -/
def getByte (n i : Nat) : Nat := (n >>> (8 * i)) % 256

/--
The 64-bit word stored at bytes `i` to `i + 7` of `n`, in little-endian order. Evaluated
natively by the kernel.
-/
def getUInt64 (n i : Nat) : Nat := (n >>> (8 * i)) % 2 ^ 64

end Nat

namespace Lean.KernelVM

/--
Binary operations on 64-bit words. Comparisons return `1` for true and `0` for false.

The signed operations interpret words in two's complement. They fail when the mathematical
result does not fit in 64 bits, so that programs can rely on exact integer arithmetic.
-/
inductive BinOp where
  /-- Wrapping addition. -/
  | add
  /-- Wrapping subtraction. -/
  | sub
  /-- Wrapping multiplication. -/
  | mul
  /-- Unsigned division, `x / 0 = 0`. -/
  | udiv
  /-- Unsigned remainder, `x % 0 = x`. -/
  | umod
  /-- Bitwise and. -/
  | and
  /-- Bitwise or. -/
  | or
  /-- Bitwise exclusive or. -/
  | xor
  /-- Left shift by the second operand modulo 64. -/
  | shl
  /-- Logical right shift by the second operand modulo 64. -/
  | shr
  /-- Equality. -/
  | eq
  /-- Unsigned less-than. -/
  | ult
  /-- Unsigned less-or-equal. -/
  | ule
  /-- Signed less-than. -/
  | slt
  /-- Signed less-or-equal. -/
  | sle
  /-- Signed addition, failing on overflow. -/
  | sadd
  /-- Signed subtraction, failing on overflow. -/
  | ssub
  /-- Signed multiplication, failing on overflow. -/
  | smul
  /-- Signed Euclidean division (`Int.ediv`), failing on overflow. -/
  | sdiv
  /-- Signed Euclidean remainder (`Int.emod`). -/
  | smod

/-- Expressions. Evaluating them has no effect on the state, but may fail. -/
inductive Exp where
  /-- The constant `n % 2^64`. -/
  | const (n : Nat)
  /-- The contents of register `i`. -/
  | reg (i : Nat)
  /-- A binary operation. -/
  | bin (op : BinOp) (a b : Exp)
  /-- The memory word at address `addr`. -/
  | load (addr : Exp)
  /-- The word at byte offset `off` of input `k`, see `Nat.getUInt64`. Missing inputs are `0`. -/
  | input (k : Nat) (off : Exp)

/-- Statements. -/
inductive Stmt where
  /-- Do nothing. -/
  | skip
  /-- Set register `r` to the value of `e`. -/
  | set (r : Nat) (e : Exp)
  /-- Store the value of `val` at memory address `addr`. -/
  | store (addr val : Exp)
  /-- Run `s`, then `t`. -/
  | seq (s t : Stmt)
  /-- Run `t` if `c` is nonzero, and `e` otherwise. -/
  | ite (c : Exp) (t e : Stmt)
  /-- Run `body` as long as `c` is nonzero. -/
  | while (c : Exp) (body : Stmt)
  /-- Fail if `c` is zero. -/
  | assert (c : Exp)

/-- A program. -/
structure Prog where
  /-- The statement to run. -/
  body : Stmt

/-- A word as a signed integer, in two's complement. -/
def toSigned (a : UInt64) : Int :=
  if a.toNat < 2 ^ 63 then .ofNat a.toNat else .ofNat a.toNat - .ofNat (2 ^ 64)

/-- The word representing `i`, if `i` fits in a signed 64-bit word. -/
def ofSigned? (i : Int) : Option UInt64 :=
  if -.ofNat (2 ^ 63) ≤ i ∧ i < .ofNat (2 ^ 63) then
    some (UInt64.ofNat (i % .ofNat (2 ^ 64)).toNat)
  else
    none

/-- `1` if `b` holds, `0` otherwise. -/
def ofBool (b : Bool) : UInt64 := if b then 1 else 0

/-- The semantics of binary operations. -/
def BinOp.eval : BinOp → UInt64 → UInt64 → Option UInt64
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .udiv, a, b => some (a / b)
  | .umod, a, b => some (a % b)
  | .and, a, b => some (a &&& b)
  | .or, a, b => some (a ||| b)
  | .xor, a, b => some (a ^^^ b)
  | .shl, a, b => some (a <<< b)
  | .shr, a, b => some (a >>> b)
  | .eq, a, b => some (ofBool (a == b))
  | .ult, a, b => some (ofBool (decide (a < b)))
  | .ule, a, b => some (ofBool (decide (a ≤ b)))
  | .slt, a, b => some (ofBool (decide (toSigned a < toSigned b)))
  | .sle, a, b => some (ofBool (decide (toSigned a ≤ toSigned b)))
  | .sadd, a, b => ofSigned? (toSigned a + toSigned b)
  | .ssub, a, b => ofSigned? (toSigned a - toSigned b)
  | .smul, a, b => ofSigned? (toSigned a * toSigned b)
  | .sdiv, a, b => ofSigned? (toSigned a / toSigned b)
  | .smod, a, b => ofSigned? (toSigned a % toSigned b)

/-- Reads index `i` of `a`, or `0` if it is out of bounds. -/
def readD (a : Array UInt64) (i : Nat) : UInt64 :=
  if h : i < a.size then a[i] else 0

/-- Writes `v` at index `i` of `a`, first extending `a` with zeros if needed. -/
def writeD (a : Array UInt64) (i : Nat) (v : UInt64) : Array UInt64 :=
  if h : i < a.size then a.set i v h else (a ++ Array.replicate (i - a.size) 0).push v

/-- The state of the machine. -/
structure State where
  /-- The registers. -/
  regs : Array UInt64 := #[]
  /-- The memory. -/
  mem : Array UInt64 := #[]

/-- Input `k`, or `0` if there is no such input. -/
def getInput : List Nat → Nat → Nat
  | [], _ => 0
  | n :: _, 0 => n
  | _ :: ns, k + 1 => getInput ns k

/-- The semantics of expressions. -/
def Exp.eval (inputs : List Nat) (st : State) : Exp → Option UInt64
  | .const n => some (UInt64.ofNat n)
  | .reg i => some (readD st.regs i)
  | .bin op a b =>
    match a.eval inputs st, b.eval inputs st with
    | some x, some y => op.eval x y
    | _, _ => none
  | .load addr =>
    match addr.eval inputs st with
    | some a => some (readD st.mem a.toNat)
    | none => none
  | .input k off =>
    match off.eval inputs st with
    | some o => some (UInt64.ofNat ((getInput inputs k).getUInt64 o.toNat))
    | none => none

/--
The semantics of statements. The fuel bounds the nesting depth of the evaluation, where each
iteration of a loop counts as one more level.
-/
def Stmt.exec (inputs : List Nat) : Nat → Stmt → State → Option State
  | 0, _, _ => none
  | _ + 1, .skip, st => some st
  | _ + 1, .set r e, st =>
    match e.eval inputs st with
    | some v => some { st with regs := writeD st.regs r v }
    | none => none
  | _ + 1, .store addr val, st =>
    match addr.eval inputs st, val.eval inputs st with
    | some a, some v => some { st with mem := writeD st.mem a.toNat v }
    | _, _ => none
  | fuel + 1, .seq s t, st =>
    match s.exec inputs fuel st with
    | some st => t.exec inputs fuel st
    | none => none
  | fuel + 1, .ite c t e, st =>
    match c.eval inputs st with
    | some v => if v != 0 then t.exec inputs fuel st else e.exec inputs fuel st
    | none => none
  | fuel + 1, .while c body, st =>
    match c.eval inputs st with
    | some v =>
      if v != 0 then
        match body.exec inputs fuel st with
        | some st => (Stmt.while c body).exec inputs fuel st
        | none => none
      else some st
    | none => none
  | _ + 1, .assert c, st =>
    match c.eval inputs st with
    | some v => if v != 0 then some st else none
    | none => none

/--
Runs `p` on `inputs` and returns whether it succeeds. The kernel evaluates this natively when `p`
is a closed term and `inputs` and `fuel` reduce to numerals.
-/
def run (p : Prog) (inputs : List Nat) (fuel : Nat) : Bool :=
  (p.body.exec inputs fuel {}).isSome

/-!
## Notation for writing programs

`open Lean.KernelVM.DSL` provides short names and infix operators for building expressions and
statements.
-/

namespace DSL

/-- Register `i`. -/
abbrev R (i : Nat) : Exp := .reg i
/-- The constant `n`. -/
abbrev K (n : Nat) : Exp := .const n
/-- The word at byte offset `off` of input `k`. -/
abbrev In (k : Nat) (off : Exp) : Exp := .input k off
/-- The 32-bit word with index `i` of input `k`. -/
abbrev In32 (k : Nat) (i : Exp) : Exp := .bin .and (.input k (.bin .mul i (.const 4))) (.const 4294967295)
/-- The memory word at `a`. -/
abbrev Ld (a : Exp) : Exp := .load a
/-- `1` if `e` is zero, `0` otherwise. -/
abbrev Not' (e : Exp) : Exp := .bin .eq e (.const 0)

scoped infixl:65 " +ᵤ " => Exp.bin BinOp.add
scoped infixl:65 " -ᵤ " => Exp.bin BinOp.sub
scoped infixl:70 " *ᵤ " => Exp.bin BinOp.mul
scoped infixl:65 " +ₛ " => Exp.bin BinOp.sadd
scoped infixl:65 " -ₛ " => Exp.bin BinOp.ssub
scoped infixl:70 " *ₛ " => Exp.bin BinOp.smul
scoped infixl:70 " /ₛ " => Exp.bin BinOp.sdiv
scoped infixl:70 " %ₛ " => Exp.bin BinOp.smod
scoped infixl:60 " &&ᵥ " => Exp.bin BinOp.and
scoped infixl:58 " ^^ᵥ " => Exp.bin BinOp.xor
scoped infix:50 " ==ᵥ " => Exp.bin BinOp.eq
scoped infix:50 " <ᵤ " => Exp.bin BinOp.ult
scoped infix:50 " ≤ᵤ " => Exp.bin BinOp.ule
scoped infix:50 " <ₛ " => Exp.bin BinOp.slt
scoped infix:50 " ≤ₛ " => Exp.bin BinOp.sle

/-- Runs the statements in order. -/
def seqs : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: ss => .seq s (seqs ss)

end DSL

end Lean.KernelVM
