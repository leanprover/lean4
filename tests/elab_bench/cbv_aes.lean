/-
Tests that `decide_cbv` can evaluate a full AES-128 encryption, serving as a
stress test / performance regression test for the CBV evaluator on large
bitvector computations.

The AES implementation is extracted from `LNSym` (https://github.com/leanprover/LNSym),
an ARMv8 symbolic simulator. Original code released under Apache 2.0 license.
-/

namespace BitVec

open BitVec

/-- Flatten a list of bitvectors into one bitvector. -/
protected def flatten {n : Nat} (xs : List (BitVec n)) : BitVec (n * xs.length) :=
  match xs with
  | [] => 0#0
  | x :: rest =>
    have h : n + n * List.length rest = n * List.length (x :: rest) := by
      simp [List.length_cons, Nat.mul_one, Nat.mul_add]
      omega
    BitVec.cast h (x ++ (BitVec.flatten rest))

abbrev partInstall (hi lo : Nat) (val : BitVec (hi - lo + 1)) (x : BitVec n): BitVec n :=
  let mask := allOnes (hi - lo + 1)
  let val_aligned := (zeroExtend n val) <<< lo
  let mask_with_hole := ~~~ ((zeroExtend n mask) <<< lo)
  let x_with_hole := x &&& mask_with_hole
  x_with_hole ||| val_aligned

----------------------------------------------------------------------

/- Bitvector pattern component syntax category, originally written by
Leonardo de Moura. -/
declare_syntax_cat bvpat_comp
syntax num : bvpat_comp
syntax ident ":" num : bvpat_comp

/--
Bitvector pattern syntax category.
Example: [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5]
-/
declare_syntax_cat bvpat
syntax "[" bvpat_comp,* "]" : bvpat

open Lean

abbrev BVPatComp := TSyntax `bvpat_comp
abbrev BVPat := TSyntax `bvpat

/-- Return the number of bits in a bit-vector component pattern. -/
def BVPatComp.length (c : BVPatComp) : Nat := Id.run do
  match c with
  | `(bvpat_comp| $n:num) =>
    let some str := n.raw.isLit? `num | pure 0
    return str.length
  | `(bvpat_comp| $_:ident : $n:num) =>
    return n.raw.toNat
  | _ =>
    return 0

/--
If the pattern component is a bitvector literal, convert it into a bit-vector term
denoting it.
-/
def BVPatComp.toBVLit? (c : BVPatComp) : MacroM (Option Term) := do
  match c with
  | `(bvpat_comp| $n:num) =>
    let len := c.length
    let some str := n.raw.isLit? `num | Macro.throwErrorAt c "invalid bit-vector literal"
    let bs := str.toList
    let mut val := 0
    for b in bs do
      if b = '1' then
        val := 2*val + 1
      else if b = '0' then
        val := 2*val
      else
        Macro.throwErrorAt c "invalid bit-vector literal, '0'/'1's expected"
    let r ← `(BitVec.ofNat $(quote len) $(quote val))
    return some r
  | _ => return none

/--
If the pattern component is a pattern variable of the form `<id>:<size>` return
`some id`.
-/
def BVPatComp.toBVVar? (c : BVPatComp) : MacroM (Option (TSyntax `ident)) := do
  match c with
  | `(bvpat_comp| $x:ident : $_:num) =>
    return some x
  | _ => return none

def BVPat.getComponents (p : BVPat) : Array BVPatComp :=
  match p with
  | `(bvpat| [$comp,*]) => comp.getElems.reverse
  | _ => #[]

/--
Return the number of bits in a bit-vector pattern.
-/
def BVPat.length (p : BVPat) : Nat := Id.run do
  let mut sz := 0
  for c in p.getComponents do
    sz := sz + c.length
  return sz

/--
Return a term that evaluates to `true` if `var` is an instance of the pattern `pat`.
-/
def genBVPatMatchTest (var : Term) (pat : BVPat) : MacroM Term := do
  let mut shift := 0
  let mut result ← `(true)
  for c in pat.getComponents do
    let len := c.length
    if let some bv ← c.toBVLit? then
      let test ← `(extractLsb $(quote (shift + (len - 1))) $(quote shift) $var == $bv)
      result ← `($result && $test)
    shift := shift + len
  return result

/--
Given a variable `var` representing a term that matches the pattern `pat`, and a term `rhs`,
return a term of the form
```
let y₁ := var.extract ..
...
let yₙ := var.extract ..
rhs
```
where `yᵢ`s are the pattern variables in `pat`.
-/
def declBVPatVars (var : Term) (pat : BVPat) (rhs : Term) : MacroM Term := do
  let mut result := rhs
  let mut shift  := 0
  for c in pat.getComponents do
    let len := c.length
    if let some y ← c.toBVVar? then
      let rhs ← `(extractLsb $(quote (shift + (len - 1))) $(quote shift) $var)
      result ← `(let $y := $rhs; $result)
    shift := shift + len
  return result

/--
Define the `match_bv .. with | bvpat => rhs | _ => rhs`.
The last entry is the `else`-case since we currently do not check whether
the patterns are exhaustive or not.
-/
syntax "match_bv " term "with" (atomic("| " bvpat) " => " term)* ("| " "_ " " => " term) : term
macro_rules
  | `(match_bv $discr:term with
      $[ | $ps:bvpat => $rhss:term ]*
         | _ => $rhsElse:term) => do
  let mut result := rhsElse
  let x ← `(discr)
  for p in ps.reverse, rhs in rhss.reverse do
    let test ← genBVPatMatchTest x p
    let rhs ← declBVPatVars x p rhs
    result ← `(if $test then $rhs else $result)
  `(let discr := $discr; $result)

end BitVec

----------------------------------------------------------------------
-- AESCommon

namespace AESCommon

open BitVec

def SBOX :=
  --   F E D C B A 9 8 7 6 5 4 3 2 1 0
  [ 0x16bb54b00f2d99416842e6bf0d89a18c#128, -- F
    0xdf2855cee9871e9b948ed9691198f8e1#128, -- E
    0x9e1dc186b95735610ef6034866b53e70#128, -- D
    0x8a8bbd4b1f74dde8c6b4a61c2e2578ba#128, -- C
    0x08ae7a65eaf4566ca94ed58d6d37c8e7#128, -- B
    0x79e4959162acd3c25c2406490a3a32e0#128, -- A
    0xdb0b5ede14b8ee4688902a22dc4f8160#128, -- 9
    0x73195d643d7ea7c41744975fec130ccd#128, -- 8
    0xd2f3ff1021dab6bcf5389d928f40a351#128, -- 7
    0xa89f3c507f02f94585334d43fbaaefd0#128, -- 6
    0xcf584c4a39becb6a5bb1fc20ed00d153#128, -- 5
    0x842fe329b3d63b52a05a6e1b1a2c8309#128, -- 4
    0x75b227ebe28012079a059618c323c704#128, -- 3
    0x1531d871f1e5a534ccf73f362693fdb7#128, -- 2
    0xc072a49cafa2d4adf04759fa7dc982ca#128, -- 1
    0x76abd7fe2b670130c56f6bf27b777c63#128  -- 0
  ]

def ShiftRows (op : BitVec 128) : BitVec 128 :=
  extractLsb 95 88 op ++ extractLsb 55 48 op ++
  extractLsb 15 8 op ++ extractLsb 103 96 op ++
  extractLsb 63 56 op ++ extractLsb 23 16 op ++
  extractLsb 111 104 op ++ extractLsb 71 64 op ++
  extractLsb 31 24 op ++ extractLsb 119 112 op ++
  extractLsb 79 72 op ++ extractLsb 39 32 op ++
  extractLsb 127 120 op ++ extractLsb 87 80 op ++
  extractLsb 47 40 op ++ extractLsb 7 0 op

def SubBytes_aux (i : Nat) (op : BitVec 128) (out : BitVec 128)
  : BitVec 128 :=
  if h₀ : 16 <= i then
    out
  else
    let idx := (extractLsb (i * 8 + 7) (i * 8) op).toNat
    let val := extractLsb (idx * 8 + 7) (idx * 8) $ BitVec.flatten SBOX
    have h₁ : idx * 8 + 7 - idx * 8 = i * 8 + 7 - i * 8 := by omega
    let out := BitVec.partInstall (i * 8 + 7) (i * 8) (h₁ ▸ val) out
    have _ : 15 - i < 16 - i := by omega
    SubBytes_aux (i + 1) op out
  termination_by (16 - i)

def SubBytes (op : BitVec 128) : BitVec 128 :=
  SubBytes_aux 0 op (BitVec.zero 128)

def MixColumns_aux (c : Nat)
  (in0 : BitVec 32) (in1 : BitVec 32) (in2 : BitVec 32) (in3 : BitVec 32)
  (out0 : BitVec 32) (out1 : BitVec 32) (out2 : BitVec 32) (out3 : BitVec 32)
  (FFmul02 : BitVec 8 -> BitVec 8) (FFmul03 : BitVec 8 -> BitVec 8)
  : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  if h₀ : 4 <= c then
    (out0, out1, out2, out3)
  else
    let lo := c * 8
    let hi := lo + 7
    have h₁ : hi - lo + 1 = 8 := by omega
    let in0_byte := h₁ ▸ extractLsb hi lo in0
    let in1_byte := h₁ ▸ extractLsb hi lo in1
    let in2_byte := h₁ ▸ extractLsb hi lo in2
    let in3_byte := h₁ ▸ extractLsb hi lo in3
    let val0 := h₁.symm ▸ (FFmul02 in0_byte ^^^ FFmul03 in1_byte ^^^ in2_byte ^^^ in3_byte)
    let out0 := BitVec.partInstall hi lo val0 out0
    let val1 := h₁.symm ▸ (FFmul02 in1_byte ^^^ FFmul03 in2_byte ^^^ in3_byte ^^^ in0_byte)
    let out1 := BitVec.partInstall hi lo val1 out1
    let val2 := h₁.symm ▸ (FFmul02 in2_byte ^^^ FFmul03 in3_byte ^^^ in0_byte ^^^ in1_byte)
    let out2 := BitVec.partInstall hi lo val2 out2
    let val3 := h₁.symm ▸ (FFmul02 in3_byte ^^^ FFmul03 in0_byte ^^^ in1_byte ^^^ in2_byte)
    let out3 := BitVec.partInstall hi lo val3 out3
    have _ : 3 - c < 4 - c := by omega
    MixColumns_aux (c + 1) in0 in1 in2 in3 out0 out1 out2 out3 FFmul02 FFmul03
  termination_by (4 - c)

def MixColumns (op : BitVec 128) (FFmul02 : BitVec 8 -> BitVec 8)
  (FFmul03 : BitVec 8 -> BitVec 8) : BitVec 128 :=
  let in0 :=
    extractLsb 103 96 op ++ extractLsb 71 64 op ++
    extractLsb 39 32 op ++ extractLsb 7 0 op
  let in1 :=
    extractLsb 111 104 op ++ extractLsb 79 72 op ++
    extractLsb 47 40 op ++ extractLsb 15 8 op
  let in2 :=
    extractLsb 119 112 op ++ extractLsb 87 80 op ++
    extractLsb 55 48 op ++ extractLsb 23 16 op
  let in3 :=
    extractLsb 127 120 op ++ extractLsb 95 88 op ++
    extractLsb 63 56 op ++ extractLsb 31 24 op
  let (out0, out1, out2, out3) :=
    (BitVec.zero 32, BitVec.zero 32,
     BitVec.zero 32, BitVec.zero 32)
  let (out0, out1, out2, out3) :=
    MixColumns_aux 0 in0 in1 in2 in3 out0 out1 out2 out3 FFmul02 FFmul03
  extractLsb 31 24 out3 ++ extractLsb 31 24 out2 ++
  extractLsb 31 24 out1 ++ extractLsb 31 24 out0 ++
  extractLsb 23 16 out3 ++ extractLsb 23 16 out2 ++
  extractLsb 23 16 out1 ++ extractLsb 23 16 out0 ++
  extractLsb 15 8 out3 ++ extractLsb 15 8 out2 ++
  extractLsb 15 8 out1 ++ extractLsb 15 8 out0 ++
  extractLsb 7 0 out3 ++ extractLsb 7 0 out2 ++
  extractLsb 7 0 out1 ++ extractLsb 7 0 out0

end AESCommon

----------------------------------------------------------------------
-- AESArm

namespace AESArm

open BitVec

def WordSize := 32
def BlockSize := 128

def Rcon : List (BitVec WordSize) :=
[ 0x00000001#32,
  0x00000002#32,
  0x00000004#32,
  0x00000008#32,
  0x00000010#32,
  0x00000020#32,
  0x00000040#32,
  0x00000080#32,
  0x0000001b#32,
  0x00000036#32 ]

-------------------------------------------------------
-- types

-- Key-Block-Round Combinations
structure KBR where
  key_len : Nat
  block_size : Nat
  Nk := key_len / 32
  Nb := block_size / 32
  Nr : Nat
  h : block_size = BlockSize
deriving DecidableEq, Repr

def AES128KBR : KBR :=
  {key_len := 128, block_size := BlockSize, Nr := 10, h := by decide}
def AES192KBR : KBR :=
  {key_len := 192, block_size := BlockSize, Nr := 12, h := by decide}
def AES256KBR : KBR :=
  {key_len := 256, block_size := BlockSize, Nr := 14, h := by decide}

def KeySchedule : Type := List (BitVec WordSize)

-- Declare KeySchedule to be an instance HAppend
-- so we can apply `++` to KeySchedules properly
instance : HAppend KeySchedule KeySchedule KeySchedule where
  hAppend := List.append

instance : Inhabited (BitVec WordSize) where
  default := 0#32

def KeySchedule.get! (ks : KeySchedule) (i : Nat) : BitVec WordSize :=
  (ks : List (BitVec WordSize)).getD i default

-------------------------------------------------------

def sbox (ind : BitVec 8) : BitVec 8 :=
  match_bv ind with
  | [x:4, y:4] =>
    have h : (x.toNat * 128 + y.toNat * 8 + 7) - (x.toNat * 128 + y.toNat * 8) + 1 = 8 :=
      by omega
    h ▸ extractLsb
      (x.toNat * 128 + y.toNat * 8 + 7)
      (x.toNat * 128 + y.toNat * 8) $ BitVec.flatten AESCommon.SBOX
  | _ => ind -- unreachable case

-- Note: The RotWord function is written in little endian
def RotWord (w : BitVec WordSize) : BitVec WordSize :=
  match_bv w with
  | [a3:8, a2:8, a1:8, a0:8] => a0 ++ a3 ++ a2 ++ a1
  | _ => w -- unreachable case

def SubWord (w : BitVec WordSize) : BitVec WordSize :=
  match_bv w with
  | [a3:8, a2:8, a1:8, a0:8] => (sbox a3) ++ (sbox a2) ++ (sbox a1) ++ (sbox a0)
  | _ => w -- unreachable case

protected def InitKey {Param : KBR} (i : Nat) (key : BitVec Param.key_len)
  (acc : KeySchedule) : KeySchedule :=
  if h₀ : Param.Nk ≤ i then acc
  else
    have h₁ : i * 32 + 32 - 1 - i * 32 + 1 = WordSize := by
      simp only [WordSize]; omega
    let wd := h₁ ▸ extractLsb (i * 32 + 32 - 1) (i * 32) key
    let ks : KeySchedule := [wd]
    have _ : Param.Nk - (i + 1) < Param.Nk - i := by omega
    AESArm.InitKey (Param := Param) (i + 1) key (acc ++ ks)
  termination_by (Param.Nk - i)

protected def KeyExpansion_helper {Param : KBR} (i : Nat) (ks : KeySchedule)
  : KeySchedule :=
  if h : 4 * Param.Nr + 4 ≤ i then
    ks
  else
    let tmp := KeySchedule.get! ks (i - 1)
    let tmp :=
      if i % Param.Nk == 0 then
        (SubWord (RotWord tmp)) ^^^ (KeySchedule.get! Rcon $ (i / Param.Nk) - 1)
      else if Param.Nk > 6 && i % Param.Nk == 4 then
        SubWord tmp
      else
        tmp
    let res := (KeySchedule.get! ks (i - Param.Nk)) ^^^ tmp
    let ks := List.append ks [ res ]
    have _ : 4 * Param.Nr + 4 - (i + 1) < 4 * Param.Nr + 4 - i := by omega
    AESArm.KeyExpansion_helper (Param := Param) (i + 1) ks
  termination_by (4 * Param.Nr + 4 - i)

def KeyExpansion {Param : KBR} (key : BitVec Param.key_len)
  : KeySchedule :=
  let seeded := AESArm.InitKey (Param := Param) 0 key []
  AESArm.KeyExpansion_helper (Param := Param) Param.Nk seeded

def SubBytes {Param : KBR} (state : BitVec Param.block_size)
  : BitVec Param.block_size :=
  have h : Param.block_size = 128 := by simp only [Param.h, BlockSize]
  h ▸ AESCommon.SubBytes (h ▸ state)

def ShiftRows {Param : KBR} (state : BitVec Param.block_size)
  : BitVec Param.block_size :=
  have h : Param.block_size = 128 := by simp only [Param.h, BlockSize]
  h ▸ AESCommon.ShiftRows (h ▸ state)

def XTimes (bv : BitVec 8) : BitVec 8 :=
  let res := truncate 7 bv ++ 0b0#1
  if getLsb bv 7 then res ^^^ 0b00011011#8 else res

def MixColumns {Param : KBR} (state : BitVec Param.block_size)
  : BitVec Param.block_size :=
  have h : Param.block_size = 128 := by simp only [Param.h, BlockSize]
  let FFmul02 := fun (x : BitVec 8) => XTimes x
  let FFmul03 := fun (x : BitVec 8) => x ^^^ XTimes x
  h ▸ AESCommon.MixColumns (h ▸ state) FFmul02 FFmul03

def AddRoundKey {Param : KBR} (state : BitVec Param.block_size)
  (roundKey : BitVec Param.block_size) : BitVec Param.block_size :=
  state ^^^ roundKey

protected def getKey {Param : KBR} (n : Nat) (w : KeySchedule) : BitVec Param.block_size :=
  let ind := 4 * n
  have h : WordSize + WordSize + WordSize + WordSize = Param.block_size := by
    simp only [WordSize, BlockSize, Param.h]
  h ▸ ((KeySchedule.get! w (ind + 3)) ++ (KeySchedule.get! w (ind + 2)) ++
       (KeySchedule.get! w (ind + 1)) ++ (KeySchedule.get! w ind))

protected def AES_encrypt_with_ks_loop {Param : KBR} (round : Nat)
  (state : BitVec Param.block_size) (w : KeySchedule)
  : BitVec Param.block_size :=
  if Param.Nr ≤ round then
    state
  else
    let state := SubBytes state
    let state := ShiftRows state
    let state := MixColumns state
    let state := AddRoundKey state $ AESArm.getKey round w
    AESArm.AES_encrypt_with_ks_loop (Param := Param) (round + 1) state w
  termination_by (Param.Nr - round)

def AES_encrypt_with_ks {Param : KBR} (input : BitVec Param.block_size)
  (w : KeySchedule) : BitVec Param.block_size :=
  have h₀ : WordSize + WordSize + WordSize + WordSize = Param.block_size := by
    simp only [WordSize, BlockSize, Param.h]
  let state := AddRoundKey input $ (h₀ ▸ AESArm.getKey (Param := Param) 0 w)
  let state := AESArm.AES_encrypt_with_ks_loop (Param := Param) 1 state w
  let state := SubBytes (Param := Param) state
  let state := ShiftRows (Param := Param) state
  AddRoundKey state (h₀ ▸ AESArm.getKey (Param := Param) Param.Nr w)

def AES_encrypt {Param : KBR} (input : BitVec Param.block_size)
  (key : BitVec Param.key_len) : BitVec Param.block_size :=
  let ks := KeyExpansion (Param := Param) key
  AES_encrypt_with_ks (Param := Param) input ks

end AESArm

----------------------------------------------------------------------
-- AESSpecTest

namespace AESSpecTest

open BitVec

-- The specification expects little-endian input
protected def input : BitVec 128 :=
  BitVec.flatten
    [ 0x32#8, 0x43#8, 0xf6#8, 0xa8#8,
      0x88#8, 0x5a#8, 0x30#8, 0x8d#8,
      0x31#8, 0x31#8, 0x98#8, 0xa2#8,
      0xe0#8, 0x37#8, 0x07#8, 0x34#8 ].reverse

protected def key : BitVec 128 :=
  BitVec.flatten
    [ 0x2b#8, 0x7e#8, 0x15#8, 0x16#8,
      0x28#8, 0xae#8, 0xd2#8, 0xa6#8,
      0xab#8, 0xf7#8, 0x15#8, 0x88#8,
      0x09#8, 0xcf#8, 0x4f#8, 0x3c#8 ].reverse

protected def output : BitVec 128 :=
  BitVec.flatten
    [ 0x39#8, 0x25#8, 0x84#8, 0x1d#8,
      0x02#8, 0xdc#8, 0x09#8, 0xfb#8,
      0xdc#8, 0x11#8, 0x85#8, 0x97#8,
      0x19#8, 0x6a#8, 0x0b#8, 0x32#8 ].reverse

theorem aes_encryption_test : AESArm.AES_encrypt (Param := AESArm.AES128KBR) AESSpecTest.input AESSpecTest.key = AESSpecTest.output := by decide_cbv

end AESSpecTest
