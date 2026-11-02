/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Init.KernelVM.Asm
public import Init.Data.Int.LinearVM
public import Std.Sat.CNF.Basic
public import Std.Tactic.BVDecide.LRAT.Actions

/-!
# An LRAT checker for `Lean.KernelVM`

`lratVMProg` checks that an LRAT proof derives the empty clause from a CNF, using flat arrays in
the memory of the machine. It supports deletions and RUP steps (no RAT steps).

Both inputs are sequences of 32-bit words. A literal of variable `v` is `2 * (v + 1)` if positive and
`2 * (v + 1) + 1` if negative.

* The CNF (input 0): the number of variables, the largest clause id, the number of clauses, and for each
  clause its length and literals. The clauses have the ids `1, 2, …`.
* The proof (input 1): a sequence of steps, then `0`. A RUP step is `1`, the clause id, the length and
  literals of the clause, and the number of hints and the hints. A deletion is `2`, the number of
  clause ids and the ids.

Memory holds, from address `0` on: for each literal, the stamp of the last RUP check in which it was
false; the start in the clause pool of each clause; for each clause id, `0` if it is not live, or
its length plus one; and the clause pool.
-/

@[expose] public section

namespace Std.Tactic.BVDecide.LRAT.KernelVM

open Lean.KernelVM Lean.KernelVM.DSL

abbrev W0 (i : Exp) : Exp := In32 0 i
abbrev W1 (i : Exp) : Exp := In32 1 i

-- Registers
abbrev nv := 0
abbrev maxId := 1
abbrev nc := 2
abbrev p := 3
abbrev numLits := 4
abbrev startB := 5
abbrev lenB := 6
abbrev top := 7
abbrev id := 8
abbrev len := 9
abbrev k := 10
abbrev l := 11
abbrev q := 12
abbrev tag := 13
abbrev stamp := 14
abbrev done := 15
abbrev n := 16
abbrev c := 17
abbrev cstart := 18
abbrev nh := 19
abbrev conflict := 20
abbrev h := 21
abbrev hl := 22
abbrev hs := 23
abbrev unassigned := 24
abbrev ulit := 25
abbrev j := 26
abbrev sat := 27
abbrev m := 28

/-- Loads the clauses of the CNF into the clause pool. -/
def loadCNF : Stmt := seqs [
  .set nv (W0 (K 0)),
  .set maxId (W0 (K 1)),
  .set nc (W0 (K 2)),
  .set p (K 3),
  .set numLits (R nv +ᵤ R nv +ᵤ K 2),
  .set startB (R numLits),
  .set lenB (R startB +ᵤ R maxId +ᵤ K 1),
  .set top (R lenB +ᵤ R maxId +ᵤ K 1),
  .assert (R nv <ᵤ K 2147483647),
  .assert (R maxId <ᵤ K 4294967295),
  .assert (R nc ≤ᵤ R maxId),
  .set id (K 1),
  .while (R id ≤ᵤ R nc) (seqs [
    .set len (W0 (R p)),
    .set p (R p +ᵤ K 1),
    .store (R startB +ᵤ R id) (R top),
    .store (R lenB +ᵤ R id) (R len +ᵤ K 1),
    .set k (K 0),
    .while (R k <ᵤ R len) (seqs [
      .set l (W0 (R p)),
      .assert (R l <ᵤ R numLits),
      .store (R top) (R l),
      .set top (R top +ᵤ K 1),
      .set p (R p +ᵤ K 1),
      .set k (R k +ᵤ K 1)]),
    .set id (R id +ᵤ K 1)])]

/-- Deletes the clauses of a deletion step at `q`. -/
def delStep : Stmt := seqs [
  .set n (W1 (R q +ᵤ K 1)),
  .set q (R q +ᵤ K 2),
  .set k (K 0),
  .while (R k <ᵤ R n) (seqs [
    .set c (W1 (R q)),
    .assert (R c ≤ᵤ R maxId),
    .store (R lenB +ᵤ R c) (K 0),
    .set q (R q +ᵤ K 1),
    .set k (R k +ᵤ K 1)])]

/-- Processes hint `h` of a RUP check: it must be a unit clause or a conflict. -/
def hintStep : Stmt := seqs [
  .assert (R h ≤ᵤ R maxId),
  .set hl (Ld (R lenB +ᵤ R h)),
  .assert (Not' (R hl ==ᵥ K 0)),
  .set hl (R hl -ᵤ K 1),
  .set hs (Ld (R startB +ᵤ R h)),
  .set unassigned (K 0),
  .set sat (K 0),
  .set j (K 0),
  .while (R j <ᵤ R hl) (seqs [
    .set l (Ld (R hs +ᵤ R j)),
    .ite (Ld (R l) ==ᵥ R stamp) .skip
      (.ite (Ld (R l ^^ᵥ K 1) ==ᵥ R stamp) (.set sat (K 1))
        (seqs [.set unassigned (R unassigned +ᵤ K 1), .set ulit (R l)])),
    .set j (R j +ᵤ K 1)]),
  .assert (R sat ==ᵥ K 0),
  .ite (R unassigned ==ᵥ K 0) (.set conflict (K 1))
    (seqs [.assert (R unassigned ==ᵥ K 1), .store (R ulit ^^ᵥ K 1) (R stamp)])]

/-- Checks and adds the clause of a RUP step at `q`. -/
def rupStep : Stmt := seqs [
  .set id (W1 (R q +ᵤ K 1)),
  .set len (W1 (R q +ᵤ K 2)),
  .set q (R q +ᵤ K 3),
  .assert (R id ≤ᵤ R maxId),
  .assert (Ld (R lenB +ᵤ R id) ==ᵥ K 0),
  .set stamp (R stamp +ᵤ K 1),
  .set cstart (R top),
  .set k (K 0),
  .while (R k <ᵤ R len) (seqs [
    .set l (W1 (R q)),
    .assert (R l <ᵤ R numLits),
    .store (R top) (R l),
    .set top (R top +ᵤ K 1),
    .store (R l) (R stamp),
    .set q (R q +ᵤ K 1),
    .set k (R k +ᵤ K 1)]),
  .set nh (W1 (R q)),
  .set q (R q +ᵤ K 1),
  .set m (R q +ᵤ R nh),
  .set conflict (K 0),
  .while ((R q <ᵤ R m) &&ᵥ Not' (R conflict)) (seqs [
    .set h (W1 (R q)),
    .set q (R q +ᵤ K 1),
    hintStep]),
  .set q (R m),
  .assert (R conflict),
  .store (R startB +ᵤ R id) (R cstart),
  .store (R lenB +ᵤ R id) (R len +ᵤ K 1),
  .ite (R len ==ᵥ K 0) (.set done (K 1)) .skip]

/-- The checker, see `lratVMProg`. -/
def lratVMStmt : Stmt := seqs [
    loadCNF,
    .set q (K 0),
    .set tag (W1 (R q)),
    .while (Not' (R tag ==ᵥ K 0)) (seqs [
      .ite (R tag ==ᵥ K 2) delStep (seqs [.assert (R tag ==ᵥ K 1), rupStep]),
      .set tag (W1 (R q))]),
    .assert (R done)]

/--
The checker: input 0 is the CNF, input 1 the proof. This is `lratVMStmt.compile`, which the test
`kernelVMPrograms` checks.
-/
def lratVMProg : Nat := 0xf0000000c0000000000000039000000000000000900000000ffffffff0000ea60000d050400000000000000010000ea61ea60000700000000000000040000000cea61020400000000000000b60000000000000009000000000000000100000000000f000200000000000000b60000ea600000000a000000000000000000000009ea600a040000000000000000ea61ea6000000006000000000000000100000009ea610004000000000000000000080006ea60000300000000000000000012ea6000000006000000000000000000080005ea6000030000000000000000000000140000000c00000000000000000000001c000c0004000000000000007900000000000000090000000000000000000eea6000000006000000000000000100000019ea60070400000000000000000000ea600000000c000000000000000100000018ea600a0400000000000000aa00000000000000090000000000000001000000000014000200000000000000a60000ea600000000a000000000000000000000018ea600a0400000000000000000000ea600000000c00000000000000000000001bea600a04000000000000008e000000000000000900000000000000010000001a001a000400000000000000000000000b0019000400000000000000010000001800180004000000000000009e0000000000000009000000000000000100000000001b0002000000000000009c0000ea600000000a0000000000000000000eea61ea600a0300000000000000000000ea62ea61000500000000000000010000000bea620704000000000000009e000000000000000900000000000000960000ea600000000a0000000000000000000eea61ea600a0300000000000000000000000bea61000500000000000000000000ea60000b00050000000000000000001a0017ea60000300000000000000a00000ea600000000a00000000000000000016001aea600b03000000000000000000000000001a0002000000000000000000000000001b00020000000000000000000000000018000200000000000000000000ea6000170005000000000000000000150005ea6000030000000000000001000000160016010400000000000000000000ea600000000c00000000000000000000ea61ea600a04000000000000000000000016ea610a0400000000000000000000ea6000160005000000000000000000150006ea60000300000000000000000000ea600000000c000000000000000000010015ea600c0300000000000000010000000c000c000400000000ffffffff0000ea600015050400000000000000010000ea61ea60000700000000000000040000000cea61020400000000000000ab0000ea600000000a0000000000000000ea62ea61ea600503000000000000000000000014ea620a040000000000000000001c000cea610b030000000000000000000000000014000200000000000000000013000c001c000300000000000000010000000c000c000400000000ffffffff0000ea600013050400000000000000010000ea61ea60000700000000000000040000000cea6102040000000000000066000000000000000900000000000000010000000a000a000400000000000000010000000c000c00040000000000000000000e000b00000006000000000000000100000007000700040000000000000000000b00070000000600000000000000000000ea600000000c00000000000000000004000bea600b0300000000ffffffff0000ea60000b050400000000000000010000ea61ea60000700000000000000040000000cea61020400000000000000730000ea600000000a00000000000000000009000aea600b03000000000000000000000000000a00020000000000000000000000070012000400000000000000010000000e000e000400000000000000000000ea600000000c00000000000000000000ea61ea600a0400000000000000000000ea62ea610005000000000000000000080006ea62000300000000000000000000ea600000000c000000000000000000010008ea600c0300000000000000030000000c000c000400000000ffffffff0000ea600009050400000000000000010000ea61ea60000700000000000000040000ea62ea61020400000000000000020000000cea62000400000000ffffffff0000ea600008050400000000000000010000ea61ea60000700000000000000040000ea62ea61020400000000000000010000000cea62000400000000000000000000ea600000000c00000000000000010000000dea600a0400000000000000b600000000000000090000000000000044000000000000000900000000000000010000000a000a000400000000000000010000000c000c00040000000000000000ea61ea6000000006000000000000000000000000ea610002000000000000000000110006ea60000300000000000000000000ea600000000c000000000000000000010011ea600c0300000000ffffffff0000ea600011050400000000000000010000ea61ea60000700000000000000040000000cea61020400000000000000510000ea600000000a00000000000000000010000aea600b03000000000000000000000000000a000200000000000000020000000c000c000400000000ffffffff0000ea600010050400000000000000010000ea61ea60000700000000000000040000ea62ea61020400000000000000010000000cea62000400000000000000520000ea600000000a00000000000000020000000dea600a0400000000000000ba0000ea600000000a00000000000000000000ea61ea600a0400000000000000000000000dea610a0400000000ffffffff0000ea60000d050400000000000000010000ea61ea60000700000000000000040000000cea610204000000000000000000000000000c0002000000000000001b0000000000000009000000000000000100000008000800040000000000000027000000000000000900000000000000010000000a000a000400000000000000010000000300030004000000000000000100000007000700040000000000000000000b00070000000600000000000000000000ea600000000c00000000000000000004000bea600b0300000000ffffffff0000ea60000b050400000000000000000000ea61ea600007000000000000000400000003ea61020400000000000000330000ea600000000a00000000000000000009000aea600b03000000000000000000000000000a00020000000000000000ea61ea6000000006000000000000000100000009ea610004000000000000000000080006ea60000300000000000000000007ea6000000006000000000000000000080005ea6000030000000000000001000000030003000400000000ffffffff0000ea600009050400000000000000000000ea61ea600007000000000000000400000003ea61020400000000000000350000ea600000000a000000000000000000020008ea600c030000000000000001000000000008000200000000000000000000ea600000000c000000000000000000010002ea600c0300000000000000000000ea600000000c00000000ffffffff00000001ea600b0400000000000000000000ea600000000c000000007fffffff00000000ea600b0400000000000000010000ea6000070004000000000000000000010006ea60000300000000000000010000ea6000060004000000000000000000010005ea6000030000000000000000000000040005000400000000000000020000ea6000040004000000000000000000000000ea6000030000000000000003000000000003000200000000ffffffff0000ea600002050400000000000000000000ea61ea60000700000000000000040000ea62ea610204000000000000000200000000ea62000200000000ffffffff0000ea600001050400000000000000000000ea61ea60000700000000000000040000ea62ea610204000000000000000100000000ea62000200000000ffffffff0000ea600000050400000000000000000000ea61ea60000700000000000000040000ea62ea610204000000000000000000000000ea62000200000000000000bc

/-- Fuel for `lratVMProg`, which is more than any run can use up. -/
abbrev lratVMFuel : Nat := 4611686018427387904

/-- Packs 32-bit words into a numeral, least significant first. -/
def words32ToNat (ws : Array Nat) : Nat :=
  Int.Internal.Linear.wordsToNat ws 32

/-- The encoding of a literal. -/
def encLit (v : Nat) (pos : Bool) : Nat := 2 * (v + 1) + if pos then 0 else 1

/-- The encoding of a DIMACS literal. -/
def encIntLit (i : Int) : Nat := 2 * i.natAbs + if i > 0 then 0 else 1

/-- The encoding of a CNF for `lratVMProg`, whose proof uses clause ids up to `maxId`. -/
def encodeCNF (cnf : Std.Sat.CNF Nat) (maxId : Nat) : Nat := Id.run do
  let mut nv := 0
  let mut body : Array Nat := #[]
  for cl in cnf.clauses do
    body := body.push cl.atoms.size
    for lit in cl do
      nv := max nv (lit.1 + 1)
      body := body.push (encLit lit.1 lit.2)
  words32ToNat (#[nv, max maxId cnf.clauses.size, cnf.clauses.size] ++ body)

/-- The largest clause id in a proof. -/
def maxActionId (proof : Array IntAction) : Nat :=
  proof.foldl (init := 0) fun m a =>
    match a with
    | .addEmpty id _ | .addRup id _ _ | .addRat id _ _ _ _ => max m id
    | .del _ => m

/-- The encoding of a proof for `lratVMProg`, or `none` if it has RAT steps. -/
def encodeProof (proof : Array IntAction) : Option Nat := Id.run do
  let mut ws : Array Nat := #[]
  for a in proof do
    match a with
    | .addEmpty id hints =>
      ws := (ws.push 1 |>.push id |>.push 0 |>.push hints.size) ++ hints
    | .addRup id c hints =>
      ws := (ws.push 1 |>.push id |>.push c.size) ++ c.map encIntLit
      ws := ws.push hints.size ++ hints
    | .addRat .. => return none
    | .del ids => ws := (ws.push 2 |>.push ids.size) ++ ids
  return some (words32ToNat (ws.push 0))

end Std.Tactic.BVDecide.LRAT.KernelVM
