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
public import Init.Data.ByteArray.Basic

/-!
# A small register machine for kernel certificate checking

`Lean.KernelVM.run p inputs fuel` runs the program `p` on `inputs` and returns whether it succeeds.
The definitions here are the reference semantics. The kernel evaluates `run` natively when the
program and fuel reduce to numerals and the inputs to numerals and string literals, and the result
must agree with these definitions. A kernel without this acceleration can still unfold them.

The program is a numeral holding a flat bytecode, see `decode`. It is usually produced from a
structured program by `Lean.KernelVM.Stmt.compile`, which is not part of the semantics.

The machine works on 64-bit words. It has 65536 registers and a memory indexed by words, which start
out as all zeros. Inputs are read-only byte arrays: numerals in little-endian order, and strings in
UTF-8. Reads beyond their end return zero.

The kernel also evaluates `Nat.getByte` and `Nat.getUInt64` natively, so that proofs by kernel
reduction can read numerals in time proportional to their size.
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

/-- The numeral whose little-endian bytes are `b`. Implemented natively. -/
@[extern "lean_byte_array_to_nat_le"]
def ByteArray.toNatLE (b : @& ByteArray) : Nat :=
  b.data.foldr (fun x acc => x.toNat + 256 * acc) 0

namespace Lean.KernelVM

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
  /-- The high 64 bits of the 128-bit product. -/
  | umulh

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
  | .umulh, a, b => some (UInt64.ofNat (a.toNat * b.toNat / 2 ^ 64))


/-- The binary operation with the given code: the index of its constructor. -/
def BinOp.ofCode? : Nat → Option BinOp
  | 0 => some .add | 1 => some .sub | 2 => some .mul | 3 => some .udiv | 4 => some .umod
  | 5 => some .and | 6 => some .or | 7 => some .xor | 8 => some .shl | 9 => some .shr
  | 10 => some .eq | 11 => some .ult | 12 => some .ule | 13 => some .slt | 14 => some .sle
  | 15 => some .sadd | 16 => some .ssub | 17 => some .smul | 18 => some .sdiv | 19 => some .smod
  | 20 => some .umulh
  | _ => none

/-- An input of a program. -/
inductive Input where
  /-- The little-endian bytes of a numeral. -/
  | nat (n : Nat)
  /-- The UTF-8 bytes of a string. -/
  | str (s : String)

/-- Byte `i` of an input, `0` beyond its end. -/
def Input.byte : Input → Nat → Nat
  | .nat n, i => n.getByte i
  | .str s, i => (s.toByteArray.data[i]?.getD 0).toNat

/-- The 64-bit word at bytes `i` to `i + 7` of an input, in little-endian order. -/
def Input.word : Input → Nat → Nat
  | .nat n, i => n.getUInt64 i
  | x, i =>
    x.byte i + 256 * (x.byte (i + 1) + 256 * (x.byte (i + 2) + 256 * (x.byte (i + 3) +
      256 * (x.byte (i + 4) + 256 * (x.byte (i + 5) + 256 * (x.byte (i + 6) + 256 * x.byte (i + 7)))))))

/-- The number of bytes of an input. For a numeral, this does not count high zero bytes. -/
def Input.size : Input → Nat
  | .nat n => if n = 0 then 0 else n.log2 / 8 + 1
  | .str s => s.toByteArray.size

/-- Input `k`, or `.nat 0` if there is no such input. -/
def getInput : List Input → Nat → Input
  | [], _ => .nat 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => getInput xs k

/-- A decoded instruction. -/
structure Instr where
  /-- The opcode. -/
  opc : Nat
  /-- The binary operation, for `bin` and `binI`. -/
  op : Nat
  /-- The destination register. -/
  d : Nat
  /-- The first source register. -/
  a : Nat
  /-- The second source register. -/
  b : Nat
  /-- The immediate operand. -/
  imm : UInt64

/--
The instruction encoded by the words `w` and `imm`. The fields of `w` are, from the least
significant bits on: the opcode (8 bits), the binary operation (8 bits), and the registers `d`, `a`
and `b` (16 bits each).
-/
def Instr.ofWords (w imm : Nat) : Instr :=
  { opc := w % 256, op := (w / 256) % 256, d := (w / 65536) % 65536, a := (w / 4294967296) % 65536,
    b := (w / 281474976710656) % 65536, imm := UInt64.ofNat imm }

/--
The instructions of the program `p`: its first 64-bit word is their number `n`, followed by two
words for each of them, see `Instr.ofWords`.
-/
def decode (p : Nat) : Array Instr :=
  (List.range (p.getUInt64 0)).toArray.map fun i =>
    Instr.ofWords (p.getUInt64 (16 * i + 8)) (p.getUInt64 (16 * i + 16))

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
  /-- The index of the next instruction. -/
  pc : Nat := 0

/-- The result of an instruction. -/
inductive StepResult where
  /-- Continue in this state. -/
  | next (st : State)
  /-- The program succeeds. -/
  | halt
  /-- The program fails. -/
  | fail

/--
The semantics of the instructions. In the following, `r[x]` is register `x`, and addresses wrap
around modulo `2^64`.

* `0`, halt: succeed.
* `1`, fail: fail.
* `2`, const: `r[d] := imm`.
* `3`, bin: `r[d] := op r[a] r[b]`, see `BinOp.ofCode?` and `BinOp.eval`.
* `4`, binI: `r[d] := op r[a] imm`.
* `5`, load: `r[d] := mem[r[a] + imm]`.
* `6`, store: `mem[r[a] + imm] := r[b]`.
* `7`, input: `r[d] :=` the word at byte offset `r[a]` of input `imm`.
* `8`, input size: `r[d] :=` the number of bytes of input `imm`.
* `9`, jump: continue at instruction `imm`.
* `10`, jump if zero: continue at instruction `imm` if `r[a] = 0`.
* `11`, jump if nonzero: continue at instruction `imm` if `r[a] ≠ 0`.
* `12`, assert: fail if `r[a] = 0`.

Other opcodes and binary operations fail.
-/
def Instr.step (i : Instr) (inputs : List Input) (st : State) : StepResult :=
  let r (x : Nat) := readD st.regs x
  let set (v : UInt64) := StepResult.next { st with regs := writeD st.regs i.d v, pc := st.pc + 1 }
  let next := StepResult.next { st with pc := st.pc + 1 }
  match i.opc with
  | 0 => .halt
  | 1 => .fail
  | 2 => set i.imm
  | 3 =>
    match BinOp.ofCode? i.op with
    | some op => match op.eval (r i.a) (r i.b) with
      | some v => set v
      | none => .fail
    | none => .fail
  | 4 =>
    match BinOp.ofCode? i.op with
    | some op => match op.eval (r i.a) i.imm with
      | some v => set v
      | none => .fail
    | none => .fail
  | 5 => set (readD st.mem (r i.a + i.imm).toNat)
  | 6 => .next { st with mem := writeD st.mem (r i.a + i.imm).toNat (r i.b), pc := st.pc + 1 }
  | 7 => set (UInt64.ofNat ((getInput inputs i.imm.toNat).word (r i.a).toNat))
  | 8 => set (UInt64.ofNat (getInput inputs i.imm.toNat).size)
  | 9 => .next { st with pc := i.imm.toNat }
  | 10 => if r i.a = 0 then .next { st with pc := i.imm.toNat } else next
  | 11 => if r i.a ≠ 0 then .next { st with pc := i.imm.toNat } else next
  | 12 => if r i.a = 0 then .fail else next
  | _ => .fail

/--
Runs `code` for at most `fuel` instructions. Running past the last instruction succeeds; running
out of fuel fails.
-/
def exec (code : Array Instr) (inputs : List Input) : Nat → State → Bool
  | 0, _ => false
  | fuel + 1, st =>
    if h : st.pc < code.size then
      match code[st.pc].step inputs st with
      | .next st => exec code inputs fuel st
      | .halt => true
      | .fail => false
    else true

/--
Runs the program `p` on `inputs` for at most `fuel` instructions and returns whether it succeeds.
The kernel evaluates this natively when `p` and `fuel` reduce to numerals and `inputs` to a list of
numerals and string literals.
-/
def run (p : Nat) (inputs : List Input) (fuel : Nat) : Bool :=
  exec (decode p) inputs fuel {}

end Lean.KernelVM
