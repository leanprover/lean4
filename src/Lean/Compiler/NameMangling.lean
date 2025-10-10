/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Robin Arnez
-/
module

prelude
public import Init.Prelude
import Init.Data.String.Basic

namespace String

def digitChar (n : UInt32) (h : n < 16) : Char :=
  if h' : n < 10 then ⟨n + 48, ?_⟩
  else ⟨n + 87, ?_⟩
where finally all_goals
  simp_all [UInt32.lt_iff_toNat_lt, UInt32.isValidChar, Nat.isValidChar]; omega

def pushHex (n : Nat) (val : UInt32) (s : String) : String :=
  match n with
  | 0 => s
  | k + 1 =>
    let i := (val >>> (4 * k).toUInt32) &&& 15
    pushHex k val (s.push (digitChar i ?_))
where finally
  have := Nat.and_two_pow_sub_one_eq_mod (n := 4)
  simp only [Nat.reducePow, Nat.add_one_sub_one] at this
  simp [i, UInt32.lt_iff_toNat_lt, this]; omega

def ValidPos.remainingBytes (pos : String.ValidPos s) : Nat :=
  s.utf8ByteSize - pos.offset.byteIdx

theorem ValidPos.remainingBytes_next_lt_of_lt {p p' : String.ValidPos s} (h' : p' < p) :
    p.remainingBytes < p'.remainingBytes := by
  simp only [ValidPos.lt_iff, Pos.Raw.lt_iff] at h' ⊢
  simp only [remainingBytes]
  have : p.offset.byteIdx ≤ s.utf8ByteSize := p.isValid.le_endPos
  omega

theorem ValidPos.lt_next {p : String.ValidPos s} (h) : p < p.next h := by
  simp only [next, lt_iff, Slice.Pos.ofset_ofSlice, Pos.Raw.lt_iff, Slice.Pos.byteIdx_offset_next,
    offset_toSlice, Nat.lt_add_right_iff_pos]
  exact Char.utf8Size_pos _

theorem ValidPos.remainingBytes_next_lt (pos : String.ValidPos s) (h) :
    (pos.next h).remainingBytes < pos.remainingBytes :=
  remainingBytes_next_lt_of_lt (pos.lt_next h)

def mangleAux (s : String) (pos : s.ValidPos) (r : String) : String :=
  if h : pos = s.endValidPos then r else
  let c := pos.get h
  let pos := pos.next h
  if c.isAlpha || c.isDigit then
    mangleAux s pos (r.push c)
  else if c = '_' then
    mangleAux s pos (r ++ "__")
  else if c.toNat < 0x100 then
    mangleAux s pos (pushHex 2 c.val (r ++ "_x"))
  else if c.toNat < 0x10000 then
    mangleAux s pos (pushHex 4 c.val (r ++ "_u"))
  else
    mangleAux s pos (pushHex 8 c.val (r ++ "_U"))
termination_by pos.remainingBytes
decreasing_by all_goals apply ValidPos.remainingBytes_next_lt

public def mangle (s : String) : String :=
  mangleAux s s.startValidPos ""

end String

namespace Lean

def checkLowerHex : Nat → (s : String) → s.ValidPos → Bool
  | 0, _, _ => true
  | k + 1, s, pos =>
    if h : pos = s.endValidPos then
      false
    else
      let ch := pos.get h
      (ch.isDigit || (ch.val >= 97 && ch.val <= 102)) && -- 0-9a-f
        checkLowerHex k s (pos.next h)

theorem valid_of_checkLowerHex (h : checkLowerHex n s p) :
    (String.Pos.Raw.mk (p.offset.byteIdx + n)).IsValid s := by
  fun_induction checkLowerHex
  · rename_i p
    exact p.isValid
  · contradiction
  · rename_i k s p hp ch ih
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    specialize ih h.2
    refine cast ?_ ih
    congr 2
    simp only [String.ValidPos.next, String.Slice.Pos.ofset_ofSlice,
      String.Slice.Pos.byteIdx_offset_next, String.ValidPos.offset_toSlice, Nat.succ_eq_add_one]
    change p.offset.byteIdx + ch.utf8Size + k = _
    rw [Char.utf8Size_eq_one_iff.mpr, Nat.add_assoc, Nat.add_comm 1]
    rcases h.1 with h | h
    · simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
      exact UInt32.le_trans h.2 (by decide)
    · exact UInt32.le_trans h.2 (by decide)

def parseLowerHex : (n : Nat) → (s : String) → (p : s.ValidPos) →
    checkLowerHex n s p → Nat → Nat
  | 0, _, _, _, n => n
  | k + 1, s, pos, h, n =>
    have hpos : pos ≠ s.endValidPos := by
      rw [checkLowerHex] at h
      split at h <;> trivial
    let ch := pos.get hpos
    let pos := pos.next hpos
    have h' : checkLowerHex k s pos := by
      simp only [checkLowerHex, hpos, ↓reduceDIte, ge_iff_le, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, pos] at h ⊢
      exact h.2
    if ch.isDigit then parseLowerHex k s pos h' (n <<< 4 ||| (ch.val - 48).toNat)
    else parseLowerHex k s pos h' (n <<< 4 ||| (ch.val - 87).toNat)

def checkDisambiguation (s : String) (p : s.ValidPos) : Bool :=
  if h : _ then
    let b := p.get h
    if b = '_' then
      checkDisambiguation s (p.next h)
    else if b = 'x' then
      checkLowerHex 2 s (p.next h)
    else if b = 'u' then
      checkLowerHex 4 s (p.next h)
    else if b = 'U' then
      checkLowerHex 8 s (p.next h)
    else if b.val >= 48 && b.val <= 57 then
      true
    else false
  else true
termination_by p.remainingBytes
decreasing_by apply p.remainingBytes_next_lt

def needDisambiguation (prev : String) (next : String) : Bool :=
  prev.endsWith "__" || checkDisambiguation next next.startValidPos

def Name.mangleAux : Name → String
  | Name.anonymous => ""
  | Name.str p s =>
    let m := String.mangle s
    match p with
    | Name.anonymous =>
      if checkDisambiguation m m.startValidPos then "00" ++ m else m
    | p              =>
      let m1 := mangleAux p
      m1 ++ (if needDisambiguation m1 m then "_00" else "_") ++ m
  | Name.num p n =>
    match p with
    | Name.anonymous => n.repr ++ "_"
    | p              =>
      mangleAux p ++ "_" ++ n.repr ++ "_"

@[export lean_name_mangle]
public def Name.mangle (n : Name) (pre : String := "l_") : String :=
  pre ++ Name.mangleAux n

@[export lean_mk_module_initialization_function_name]
public def mkModuleInitializationFunctionName (moduleName : Name) : String :=
  "initialize_" ++ moduleName.mangle ""

-- assumes `s` has been generated `Name.mangle n ""`
def Name.unmangleAux (s : String) (p : s.ValidPos) (res : Name)
    (acc : String) (ucount : Nat) : Name :=
  if h : p = s.endValidPos then res.str (acc.pushn '_' (ucount / 2)) else
  let ch := p.get h
  let p := p.next h
  if ch = '_' then unmangleAux s p res acc (ucount + 1) else
  if ucount % 2 = 0 then
    unmangleAux s p res (acc.pushn '_' (ucount / 2) |>.push ch) 0
  else if ch.isDigit then
    let res := res.str (acc.pushn '_' (ucount / 2))
    if h : ch = '0' ∧ ∃ h : p ≠ s.endValidPos, p.get h = '0' then
      unmangleAux s (p.next h.2.1) res "" 0
    else
      decodeNum s p res (ch.val - 48).toNat
  else if h : ch = 'x' ∧ checkLowerHex 2 s p then
    let acc := acc.pushn '_' (ucount / 2)
    unmangleAux s ⟨_, valid_of_checkLowerHex h.2⟩ res (acc.push (Char.ofNat (parseLowerHex 2 s p h.2 0))) 0
  else if h : ch = 'u' ∧ checkLowerHex 4 s p then
    let acc := acc.pushn '_' (ucount / 2)
    unmangleAux s ⟨_, valid_of_checkLowerHex h.2⟩ res (acc.push (Char.ofNat (parseLowerHex 4 s p h.2 0))) 0
  else if h : ch = 'U' ∧ checkLowerHex 8 s p then
    let acc := acc.pushn '_' (ucount / 2)
    unmangleAux s ⟨_, valid_of_checkLowerHex h.2⟩ res (acc.push (Char.ofNat (parseLowerHex 8 s p h.2 0))) 0
  else
    unmangleAux s p (res.str acc) ("".pushn '_' (ucount / 2) |>.push ch) 0
termination_by p.remainingBytes
decreasing_by
  · apply String.ValidPos.remainingBytes_next_lt
  · apply String.ValidPos.remainingBytes_next_lt
  · apply String.ValidPos.remainingBytes_next_lt_of_lt
        (Nat.lt_trans (String.ValidPos.lt_next _) (String.ValidPos.lt_next _))
  · apply String.ValidPos.remainingBytes_next_lt
  · apply String.ValidPos.remainingBytes_next_lt_of_lt
      (Nat.lt_trans (String.ValidPos.lt_next _) (Nat.lt_add_of_pos_right (by decide)))
  · apply String.ValidPos.remainingBytes_next_lt_of_lt
      (Nat.lt_trans (String.ValidPos.lt_next _) (Nat.lt_add_of_pos_right (by decide)))
  · apply String.ValidPos.remainingBytes_next_lt_of_lt
      (Nat.lt_trans (String.ValidPos.lt_next _) (Nat.lt_add_of_pos_right (by decide)))
  · apply String.ValidPos.remainingBytes_next_lt
where
  decodeNum (s : String) (p : s.ValidPos) (res : Name) (n : Nat) : Name :=
    if h : p = s.endValidPos then res.num n else
    let ch := p.get h
    let p := p.next h
    if ch.isDigit then
      decodeNum s p res (n * 10 + (ch.val - 48).toNat)
    else -- assume ch = '_'
      let res := res.num n
      if h : p = s.endValidPos then res else
      nameStart s (p.next h) res -- assume s.get' p h = '_'
  termination_by p.remainingBytes
  decreasing_by
    · apply String.ValidPos.remainingBytes_next_lt
    · apply String.ValidPos.remainingBytes_next_lt_of_lt
        (Nat.lt_trans (String.ValidPos.lt_next _) (String.ValidPos.lt_next _))
  nameStart (s : String) (p : s.ValidPos) (res : Name) : Name :=
    if h : p = s.endValidPos then res else
    let ch := p.get h
    let p := p.next h
    if ch.isDigit then
      if h : ch = '0' ∧ ∃ h : p ≠ s.endValidPos, p.get h = '0' then
        unmangleAux s (p.next h.2.1) res "" 0
      else
        decodeNum s p res (ch.val - 48).toNat
    else if ch = '_' then
      unmangleAux s p res "" 1
    else
      unmangleAux s p res (String.singleton ch) 0
  termination_by p.remainingBytes
  decreasing_by
    · apply String.ValidPos.remainingBytes_next_lt_of_lt
        (Nat.lt_trans (String.ValidPos.lt_next _) (String.ValidPos.lt_next _))
    all_goals apply String.ValidPos.remainingBytes_next_lt

/-- Assuming `s` has been produced by `Name.mangle _ ""`, return the original name. -/
public def Name.unmangle (s : String) : Name :=
  unmangleAux.nameStart s s.startValidPos .anonymous

/--
Returns the unmangled version of `s`, if it's the result of `Name.mangle _ ""`. Otherwise returns
`none`.
-/
public def Name.unmangle? (s : String) : Option Name :=
  let n := unmangle s
  if mangleAux n = s then some n else none

end Lean
