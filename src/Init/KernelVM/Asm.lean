/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Init.KernelVM
public import Init.Control.State

/-!
# Structured programs for `Lean.KernelVM`

A small structured language, and a compiler to the bytecode of `Lean.KernelVM.run`. The compiler is
not part of the trusted semantics: a program is whatever bytecode it produces.

Expressions compute into temporary registers from `tmpBase` on, so programs should only use the
registers below it.
-/

@[expose] public section

namespace Lean.KernelVM

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
  /-- The word at byte offset `off` of input `k`. -/
  | input (k : Nat) (off : Exp)
  /-- The number of bytes of input `k`. -/
  | inputSize (k : Nat)
  deriving Inhabited

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
  deriving Inhabited

/-- The first temporary register of the compiler. -/
abbrev tmpBase : Nat := 60000

/-- The code of BinOp `op`. -/
def BinOp.code : BinOp → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .udiv => 3 | .umod => 4 | .and => 5 | .or => 6 | .xor => 7
  | .shl => 8 | .shr => 9 | .eq => 10 | .ult => 11 | .ule => 12 | .slt => 13 | .sle => 14
  | .sadd => 15 | .ssub => 16 | .smul => 17 | .sdiv => 18 | .smod => 19

/-- An instruction being assembled: the first word and the immediate operand. -/
structure AsmInstr where
  /-- The first word, see `Instr.ofWords`. -/
  word : Nat
  /-- The immediate operand. -/
  imm : Nat

/-- The monad of the compiler. -/
abbrev AsmM := StateM (Array AsmInstr)

/-- Appends an instruction and returns its index. -/
def emit (opc : Nat) (op d a b imm : Nat := 0) : AsmM Nat := do
  let code ← get
  set (code.push { word := opc + 256 * op + 65536 * d + 4294967296 * a + 281474976710656 * b, imm })
  return code.size

/-- Sets the immediate operand of instruction `i`. -/
def patch (i imm : Nat) : AsmM Unit :=
  modify fun code => code.modify i fun ins => { ins with imm }

/-- The index of the next instruction. -/
def here : AsmM Nat := return (← get).size

/-- Computes `e` into register `dst`, using temporaries from `tmp` on. -/
def Exp.compile (e : Exp) (dst tmp : Nat) : AsmM Unit :=
  match e with
  | .const n => discard <| emit 2 (d := dst) (imm := n)
  | .reg i => if i == dst then pure () else discard <| emit 4 (op := 0) (d := dst) (a := i)
  | .bin op a (.const n) => do
    let ra ← match a with
      | .reg i => pure i
      | a => do a.compile tmp (tmp + 1); pure tmp
    discard <| emit 4 (op := op.code) (d := dst) (a := ra) (imm := n)
  | .bin op a b => do
    let ra ← match a with
      | .reg i => pure i
      | a => do a.compile tmp (tmp + 1); pure tmp
    let rb ← match b with
      | .reg i => pure i
      | b => do b.compile (tmp + 1) (tmp + 2); pure (tmp + 1)
    discard <| emit 3 (op := op.code) (d := dst) (a := ra) (b := rb)
  | .load (.bin .add a (.const n)) => do
    let ra ← match a with
      | .reg i => pure i
      | a => do a.compile tmp (tmp + 1); pure tmp
    discard <| emit 5 (d := dst) (a := ra) (imm := n)
  | .load a => do
    let ra ← match a with
      | .reg i => pure i
      | a => do a.compile tmp (tmp + 1); pure tmp
    discard <| emit 5 (d := dst) (a := ra)
  | .input k off => do
    let ro ← match off with
      | .reg i => pure i
      | off => do off.compile tmp (tmp + 1); pure tmp
    discard <| emit 7 (d := dst) (a := ro) (imm := k)
  | .inputSize k => discard <| emit 8 (d := dst) (imm := k)

/-- Computes `e` into a register, using temporaries from `tmp` on, and returns the register. -/
def Exp.operand (e : Exp) (tmp : Nat) : AsmM Nat :=
  match e with
  | .reg i => pure i
  | e => do e.compile tmp (tmp + 1); pure tmp

/-- Compiles a statement. -/
def Stmt.compileCore : Stmt → AsmM Unit
  | .skip => pure ()
  | .set r e => e.compile r tmpBase
  | .store (.bin .add a (.const n)) val => do
    let ra ← a.operand tmpBase
    let rv ← val.operand (tmpBase + 1)
    discard <| emit 6 (a := ra) (b := rv) (imm := n)
  | .store addr val => do
    let ra ← addr.operand tmpBase
    let rv ← val.operand (tmpBase + 1)
    discard <| emit 6 (a := ra) (b := rv)
  | .seq s t => do s.compileCore; t.compileCore
  | .ite c t e => do
    let rc ← c.operand tmpBase
    let jElse ← emit 10 (a := rc)
    t.compileCore
    let jEnd ← emit 9
    patch jElse (← here)
    e.compileCore
    patch jEnd (← here)
  | .while c body => do
    let top ← here
    let rc ← c.operand tmpBase
    let jEnd ← emit 10 (a := rc)
    body.compileCore
    discard <| emit 9 (imm := top)
    patch jEnd (← here)
  | .assert c => do
    let rc ← c.operand tmpBase
    discard <| emit 12 (a := rc)

/-- The bytecode of `s`, see `Lean.KernelVM.decode`. -/
def Stmt.compile (s : Stmt) : Nat :=
  let code := ((do s.compileCore; discard <| emit 0) : AsmM Unit).run #[] |>.2
  let ws := code.foldl (init := #[code.size]) fun ws i => ws.push i.word |>.push i.imm
  let bytes := ws.foldl (init := ByteArray.emptyWithCapacity (8 * ws.size)) fun b w =>
    (List.range 8).foldl (init := b) fun b j => b.push (UInt8.ofNat (w >>> (8 * j)))
  bytes.toNatLE

/--
Runs `p` like `Lean.KernelVM.run`, and returns the final memory, as little-endian 64-bit words, if
it succeeds. This uses the kernel's implementation, for running programs at elaboration time. It
also fails if the program exceeds the kernel's memory limit.
-/
@[extern "lean_kernel_vm_run_mem"]
opaque runMem (p : @& Nat) (inputs : @& List Input) (fuel : @& Nat) : Option ByteArray

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
scoped infixl:59 " ||ᵥ " => Exp.bin BinOp.or
scoped infixl:58 " ^^ᵥ " => Exp.bin BinOp.xor
scoped infixl:75 " <<<ᵥ " => Exp.bin BinOp.shl
scoped infixl:75 " >>>ᵥ " => Exp.bin BinOp.shr
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
