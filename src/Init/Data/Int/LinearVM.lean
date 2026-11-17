/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Init.Data.Int.Linear
public import Init.KernelVM.Asm

/-!
# Checking linear arithmetic certificates with `Lean.KernelVM`

A cutting-planes refutation of a list of linear constraints `p ≤ 0` and `p = 0` is checked by a
single run of `linCheckProg`. The constraints are given as an encoded numeral `s`, which the kernel
compares with the constraints by `encOk_k`. The certificate is a numeral that the kernel never
inspects: it only feeds it to `linCheckProg`.

Encoding of the constraints, as a sequence of 64-bit words: the number of variables, then for each
constraint its kind (`1` for `≤`, `2` for `=`), the pairs `v + 1, a` for its terms `a * x_v`, `0`, and
its constant; and finally `0`. Integers are in two's complement.

Encoding of the certificate: the number of steps, then for each step the number of terms, the pairs
`c, i` of the multiplier `c` and the row `i` of each term, and the divisor (`1` for none); and finally
`g`. Rows are the constraints followed by the steps. A step is the sum of its terms, where rows of
kind `≤` have nonnegative multipliers, divided by the divisor. The last row is contradictory if
`g ≤ 1` and it is a nonzero constant (positive for `≤`), or if it is an equality and `g` divides its
coefficients but not its constant.
-/

@[expose] public section

namespace Int.Internal.Linear

/-- A linear constraint for `linCheckProg`. -/
inductive VMCnstr where
  /-- `p ≤ 0` -/
  | le (p : Poly)
  /-- `p = 0` -/
  | eq (p : Poly)

/-- The meaning of a constraint. -/
noncomputable abbrev VMCnstr.holds (ctx : Context) : VMCnstr → Prop
  | .le p => p.denote' ctx ≤ 0
  | .eq p => p.denote' ctx = 0

/-- All constraints hold. -/
noncomputable abbrev VMCnstr.allHold (ctx : Context) : List VMCnstr → Prop
  | [] => True
  | c :: cs => c.holds ctx ∧ allHold ctx cs

/-- Whether the 64-bit word `w` is the two's complement encoding of `k`. -/
noncomputable def encIntOk_k (k : Int) (w : Nat) : Bool :=
  Int.rec (fun n => (Nat.blt n 9223372036854775808).and (Nat.beq w n))
    (fun n => (Nat.blt n 9223372036854775808).and (Nat.beq w (Nat.sub 18446744073709551615 n))) k

/-- Whether the words of `s` from byte `off` on start with the encoding of `p`. -/
noncomputable def Poly.encOk_k (p : Poly) (s : Nat) : Nat → Bool :=
  Poly.rec (fun k off => (Nat.beq (s.getUInt64 off) 0).and (encIntOk_k k (s.getUInt64 (Nat.add off 8))))
    (fun k v _ ih off => (Nat.beq (s.getUInt64 off) (Nat.succ v)).and
      ((encIntOk_k k (s.getUInt64 (Nat.add off 8))).and (ih (Nat.add off 16))))
    p

/-- The number of bytes of the encoding of `p`. -/
noncomputable def Poly.encSize_k (p : Poly) : Nat :=
  Poly.rec (fun _ => 16) (fun _ _ _ ih => Nat.add ih 16) p

/--
Whether the words of `s` from byte `off` on are the encoding of `cs`. This is evaluated by the
kernel, using `Nat.getUInt64` to read `s` in constant time.
-/
noncomputable def VMCnstr.encOk_k (s : Nat) (cs : List VMCnstr) : Nat → Bool :=
  List.rec (fun off => Nat.beq (s.getUInt64 off) 0)
    (fun c _ ih off =>
      VMCnstr.rec
        (fun p => (Nat.beq (s.getUInt64 off) 1).and ((p.encOk_k s (Nat.add off 8)).and
          (ih (Nat.add (Nat.add off 8) p.encSize_k))))
        (fun p => (Nat.beq (s.getUInt64 off) 2).and ((p.encOk_k s (Nat.add off 8)).and
          (ih (Nat.add (Nat.add off 8) p.encSize_k))))
        c)
    cs

/--
The numeral whose `bits`-bit words, from the least significant one on, are `ws` (each modulo
`2^bits`). `bits` must be a multiple of 8.
-/
def wordsToNat (ws : Array Nat) (bits : Nat := 64) : Nat :=
  let n := bits / 8
  let bytes := ws.foldl (init := ByteArray.emptyWithCapacity (n * ws.size)) fun b w =>
    pushBytes b w n
  bytes.toNatLE
where
  /-- Appends the `n` low bytes of `w`, least significant first. -/
  pushBytes (b : ByteArray) (w : Nat) : Nat → ByteArray
    | 0 => b
    | n + 1 => pushBytes (b.push (UInt8.ofNat w)) (w >>> 8) n

/-- The two's complement word of `k`. -/
def intToWord (k : Int) : Nat := (k % 18446744073709551616).toNat

/-- The words encoding `p`. -/
def Poly.encodeWords : Poly → List Nat
  | .num k => [0, intToWord k]
  | .add k v p => (v + 1) :: intToWord k :: p.encodeWords

/-- The words encoding `cs`. -/
def VMCnstr.encodeWords : List VMCnstr → List Nat
  | [] => [0]
  | .le p :: cs => 1 :: (p.encodeWords ++ encodeWords cs)
  | .eq p :: cs => 2 :: (p.encodeWords ++ encodeWords cs)

/-- The encoding of the constraints `cs` over `nv` variables, see `VMCnstr.encOk_k`. -/
def VMCnstr.encode (nv : Nat) (cs : List VMCnstr) : Nat :=
  wordsToNat (nv :: VMCnstr.encodeWords cs).toArray

/-- A step of a certificate: the multipliers and rows of its terms, and the divisor. -/
structure LinCertStep where
  /-- Pairs of multipliers and rows. -/
  terms : Array (Int × Nat)
  /-- The divisor, `1` for none. -/
  div : Int := 1

/-- The words encoding `st`, followed by `rest`. -/
def LinCertStep.encodeWords (st : LinCertStep) (rest : List Nat) : List Nat :=
  st.terms.size :: st.terms.foldr (fun (c, i) acc => intToWord c :: i :: acc) (intToWord st.div :: rest)

/-- The encoding of a certificate with the steps `steps` and the final divisor `g`. -/
def encodeLinCert (steps : Array LinCertStep) (g : Int) : Nat :=
  wordsToNat (steps.size :: steps.foldr LinCertStep.encodeWords [intToWord g]).toArray

namespace LinCheck
open Lean.KernelVM Lean.KernelVM.DSL

abbrev In0 (off : Exp) : Exp := .input 0 off
abbrev In1 (off : Exp) : Exp := .input 1 off


-- Registers
abbrev pos0 := 0
abbrev nv := 1
abbrev S := 2
abbrev r := 3
abbrev base := 4
abbrev kind := 5
abbrev v := 6
abbrev pos1 := 7
abbrev ns := 8
abbrev step := 9
abbrev nt := 10
abbrev j := 11
abbrev coef := 12
abbrev idx := 13
abbrev src := 14
abbrev isLe := 15
abbrev k := 16
abbrev d := 17
abbrev g := 18

/-- Loads the constraints of input 0 into rows `0, 1, …` of memory, each `nv + 2` words long: the
constant, the coefficients, and the kind. -/
def loadCnstrs : Stmt := seqs [
  .set nv (In0 (K 0)),
  .set S (R nv +ₛ K 2),
  .set pos0 (K 8),
  .set kind (In0 (R pos0)),
  .while (Not' (R kind ==ᵥ K 0)) (seqs [
    .assert (R kind ≤ᵤ K 2),
    .set base (R r *ₛ R S),
    .store (R base +ₛ R S -ₛ K 1) (R kind),
    .set pos0 (R pos0 +ₛ K 8),
    .set v (In0 (R pos0)),
    .while (Not' (R v ==ᵥ K 0)) (seqs [
      .assert (R v ≤ᵤ R nv),
      .store (R base +ₛ R v) (Ld (R base +ₛ R v) +ₛ In0 (R pos0 +ₛ K 8)),
      .set pos0 (R pos0 +ₛ K 16),
      .set v (In0 (R pos0))]),
    .store (R base) (In0 (R pos0 +ₛ K 8)),
    .set pos0 (R pos0 +ₛ K 16),
    .set r (R r +ₛ K 1),
    .set kind (In0 (R pos0))])]

/-- Adds `coef` times row `idx` to the row at `base`. -/
def addRow : Stmt := seqs [
  .assert (R idx <ᵤ R r),
  .set src (R idx *ₛ R S),
  .ite (Ld (R src +ₛ R S -ₛ K 1) ==ᵥ K 1)
    (seqs [.assert (K 0 ≤ₛ R coef), .set isLe (K 1)]) .skip,
  .set k (K 0),
  .while (R k <ᵤ R S -ₛ K 1) (seqs [
    .store (R base +ₛ R k) (Ld (R base +ₛ R k) +ₛ R coef *ₛ Ld (R src +ₛ R k)),
    .set k (R k +ₛ K 1)])]

/-- Divides the row at `base` by `d`. -/
def divRow : Stmt := seqs [
  .set k (K 1),
  .while (R k <ᵤ R S -ₛ K 1) (seqs [
    .assert (Ld (R base +ₛ R k) %ₛ R d ==ᵥ K 0),
    .store (R base +ₛ R k) (Ld (R base +ₛ R k) /ₛ R d),
    .set k (R k +ₛ K 1)]),
  .ite (R isLe)
    (.store (R base) (K 0 -ₛ ((K 0 -ₛ Ld (R base)) /ₛ R d)))
    (seqs [.assert (Ld (R base) %ₛ R d ==ᵥ K 0), .store (R base) (Ld (R base) /ₛ R d)])]

/-- Derives the rows of the steps of the certificate in input 1. -/
def derive : Stmt := seqs [
  .set ns (In1 (K 0)),
  .set pos1 (K 8),
  .while (R step <ᵤ R ns) (seqs [
    .set nt (In1 (R pos1)),
    .set pos1 (R pos1 +ₛ K 8),
    .set base (R r *ₛ R S),
    .set isLe (K 0),
    .set j (K 0),
    .while (R j <ᵤ R nt) (seqs [
      .set coef (In1 (R pos1)),
      .set idx (In1 (R pos1 +ₛ K 8)),
      .set pos1 (R pos1 +ₛ K 16),
      addRow,
      .set j (R j +ₛ K 1)]),
    .store (R base +ₛ R S -ₛ K 1) (K 2 -ₛ R isLe),
    .set d (In1 (R pos1)),
    .set pos1 (R pos1 +ₛ K 8),
    .ite (K 1 <ₛ R d) divRow .skip,
    .set r (R r +ₛ K 1),
    .set step (R step +ₛ K 1)])]

/-- Checks that the last row is contradictory. -/
def checkLast : Stmt := seqs [
  .set g (In1 (R pos1)),
  .assert (K 0 <ᵤ R r),
  .set base ((R r -ₛ K 1) *ₛ R S),
  .set kind (Ld (R base +ₛ R S -ₛ K 1)),
  .set k (K 1),
  .ite (K 1 <ₛ R g)
    (seqs [
      .assert (R kind ==ᵥ K 2),
      .while (R k <ᵤ R S -ₛ K 1) (seqs [
        .assert (Ld (R base +ₛ R k) %ₛ R g ==ᵥ K 0),
        .set k (R k +ₛ K 1)]),
      .assert (Not' (Ld (R base) %ₛ R g ==ᵥ K 0))])
    (seqs [
      .while (R k <ᵤ R S -ₛ K 1) (seqs [
        .assert (Ld (R base +ₛ R k) ==ᵥ K 0),
        .set k (R k +ₛ K 1)]),
      .ite (R kind ==ᵥ K 1)
        (.assert (K 0 <ₛ Ld (R base)))
        (.assert (Not' (Ld (R base) ==ᵥ K 0)))])]

/-- The certificate checker, see `linCheckProg`. -/
def linCheckStmt : Stmt := seqs [loadCnstrs, derive, checkLast]

/--
The certificate checker: input 0 are the constraints, input 1 the certificate. This is
`linCheckStmt.compile`, which the test `kernelVMPrograms` checks.
-/
def linCheckProg : Nat := 0xea600000000c00000000000000000000ea61ea600a0400000000000000000000ea62ea610a04000000000000000000000004ea62000500000000000000b4000000000000000900000000000000000000ea600000000c0000000000000000ea62ea61ea600d03000000000000000000000004ea620005000000000000000000000000ea61000200000000000000b00000ea600000000a000000000000000100000005ea600a0400000000000000a0000000000000000900000000000000010000001000100f0400000000000000000000ea600000000c00000000000000000000ea61ea600a0400000000000000000000ea62ea610005000000000000000000100004ea620f0300000000000000a90000ea600000000a0000000000000000ea620010ea600b03000000000000000100000002ea62100400000000000000b4000000000000000900000000000000000000ea600000000c00000000000000000000ea61ea600a0400000000000000000000ea62ea610a0400000000000000000012ea63ea621303000000000000000000000004ea6300050000000000000090000000000000000900000000000000010000001000100f0400000000000000000000ea600000000c00000000000000000000ea61ea600a0400000000000000000012ea62ea61130300000000000000000000ea63ea620005000000000000000000100004ea630f03000000000000009a0000ea600000000a0000000000000000ea620010ea600b03000000000000000100000002ea62100400000000000000000000ea600000000c000000000000000200000005ea600a0400000000000000a00000ea600000000a00000000000000000012ea61ea600d03000000000000000100000000ea6100020000000000000001000000000010000200000000000000000000ea600005000500000000000000010000ea61ea601004000000000000000000020004ea610f0300000000000000000002ea6000041103000000000000000100000003ea60100400000000000000000000ea600000000c00000000000000000003ea61ea600b03000000000000000000000000ea610002000000000000000100000007001200070000000000000029000000000000000900000000000000010000000900090f0400000000000000010000000300030f04000000000000007e00000000000000090000000000000000ea6100040000000600000000000000000011ea62ea611203000000000000000000000004ea62000500000000000000000000ea600000000c00000000000000000000ea61ea600a0400000000000000000011ea62ea611303000000000000000000000004ea620005000000000000007d00000000000000090000000000000000ea610004000000060000000000000000ea63ea62ea61100300000000000000000011ea64ea6312030000000000000000ea66ea65ea641003000000000000000000000004ea660005000000000000000000000000ea650002000000000000000000000000ea62000200000000000000760000000f0000000a000000000000005e000000000000000900000000000000010000001000100f040000000000000000ea61ea600000000600000000000000000011ea62ea61120300000000000000000000ea63ea620005000000000000000000100004ea630f03000000000000000000100004ea600f0300000000000000000000ea600000000c00000000000000000000ea61ea600a0400000000000000000011ea62ea61130300000000000000000000ea63ea620005000000000000000000100004ea630f03000000000000006d0000ea600000000a0000000000000000ea620010ea600b03000000000000000100000002ea62100400000000000000010000000000100002000000000000007e0000ea600000000a00000000000000000011ea61ea600d03000000000000000100000000ea61000200000000000000080000000700070f04000000000000000100000007001100070000000000000000ea61ea60000000060000000000000000000fea62ea611003000000000000000200000000ea62000200000000000000010000ea61ea601004000000000000000000020004ea610f030000000000000030000000000000000900000000000000010000000b000b0f040000000000000044000000000000000900000000000000010000001000100f040000000000000000ea61ea60000000060000000000000000ea63ea62ea610f030000000000000000ea65000cea63110300000000000000000000ea66ea65000500000000000000000010000eea660f0300000000000000000000ea63ea620005000000000000000000100004ea630f03000000000000000000100004ea600f0300000000000000510000ea600000000a0000000000000000ea620010ea600b03000000000000000100000002ea6210040000000000000000000000000010000200000000000000430000000000000009000000000000000100000000000f000200000000000000000000ea600000000c0000000000000000000cea61ea600e03000000000000000000000000ea61000200000000000000430000ea600000000a00000000000000010000ea61ea600a0400000000000000000000ea62ea61000500000000000000010000ea63ea62100400000000000000000002000eea630f0300000000000000000002000d000e110300000000000000000000ea600000000c00000000000000000003000dea600b0300000000000000100000000700070f0400000000000000010000ea60000d0007000000000000000800000007ea600f04000000000000000100000007000c000700000000000000530000ea600000000a0000000000000000000a000bea600b03000000000000000000000000000b0002000000000000000000000000000f00020000000000000000000200030004110300000000000000080000000700070f04000000000000000100000007000a000700000000000000810000ea600000000a000000000000000000080009ea600b030000000000000008000000000007000200000000000000010000ea6000080007000000000000000000000000ea600002000000000000000500000000000000090000000000000000000000000005000700000000000000010000000300030f0400000000000000100000000000000f040000000000000000ea6100040000000600000000000000000000ea62ea610007000000000000000800000000ea620f04000000000000001000000000000000090000000000000000000000000006000700000000000000100000000000000f040000000000000000ea61ea60000000060000000000000000ea63ea62ea610f0300000000000000000000ea64ea630007000000000000000800000000ea640f0400000000000000000000ea63ea620005000000000000000000060004ea630f03000000000000000000060004ea600f0300000000000000000000ea600000000c000000000000000000010006ea600c03000000000000001f0000ea600000000a00000000000000000000ea61ea600a04000000000000000000000006ea610a040000000000000000000000000006000700000000000000080000000000000f0400000000000000000005ea600000000600000000000000010000ea61ea601004000000000000000000020004ea610f030000000000000000000200030004110300000000000000000000ea600000000c000000000000000200000005ea600c0400000000000000260000ea600000000a00000000000000000000ea61ea600a04000000000000000000000005ea610a04000000000000000000000000000500070000000000000008000000000000000200000000000000020000000100020f0400000000000000000000ea6000010007000000000000000000000000ea60000200000000000000b5

end LinCheck

export LinCheck (linCheckProg)

/-- Fuel for `linCheckProg`, which is more than any run can use up. -/
abbrev linCheckFuel : Nat := 4611686018427387904

/--
If `s` encodes the constraints `cs` and `linCheckProg` accepts the certificate `cert`, the
constraints are contradictory.
-/
-- TODO: prove this. It is an axiom while the performance of the approach is evaluated.
axiom unsat_of_linCheck (ctx : Context) (cs : List VMCnstr) (s cert : Nat)
    (h₁ : VMCnstr.encOk_k s cs 8 = true)
    (h₂ : Lean.KernelVM.run linCheckProg [.nat s, .nat cert] linCheckFuel = true) :
    VMCnstr.allHold ctx cs → False

end Int.Internal.Linear
