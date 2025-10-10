/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Robin Arnez
-/
module

prelude
public import Init.Prelude
import Init.Data.String.Basic

public section

namespace String

private def mangleAux : Nat → String.Iterator → String → String
  | 0,   _,  r => r
  | i+1, it, r =>
    let c := it.curr
    if c.isAlpha || c.isDigit then
      mangleAux i it.next (r.push c)
    else if c = '_' then
      mangleAux i it.next (r ++ "__")
    else if c.toNat < 0x100 then
      let n := c.toNat
      let r := r ++ "_x"
      let r := r.push <| Nat.digitChar (n / 0x10)
      let r := r.push <| Nat.digitChar (n % 0x10)
      mangleAux i it.next r
    else if c.toNat < 0x10000 then
      let n := c.toNat
      let r := r ++ "_u"
      let r := r.push <| Nat.digitChar (n / 0x1000)
      let n := n % 0x1000
      let r := r.push <| Nat.digitChar (n / 0x100)
      let n := n % 0x100
      let r := r.push <| Nat.digitChar (n / 0x10)
      let r := r.push <| Nat.digitChar (n % 0x10)
      mangleAux i it.next r
    else
      let n := c.toNat
      let r := r ++ "_U"
      let ds := Nat.toDigits 16 n
      let r := Nat.repeat (·.push '0') (8 - ds.length) r
      let r := ds.foldl (fun r c => r.push c) r
      mangleAux i it.next r

def mangle (s : String) : String :=
  mangleAux s.length s.mkIterator ""

end String

namespace Lean

private def checkLowerHex : Nat → (s : String) → s.ValidPos → Bool
  | 0, _, _ => true
  | k + 1, s, pos =>
    if h : pos = s.endValidPos then
      false
    else
      let ch := pos.get h
      (ch.isDigit || (ch.val >= 97 && ch.val <= 102)) && -- 0-9a-f
        checkLowerHex k s (pos.next h)

private theorem valid_of_checkLowerHex (h : checkLowerHex n s p) :
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

private def parseLowerHex : (n : Nat) → (s : String) → (p : s.ValidPos) →
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

private def checkDisambiguation : Nat → (s : String) → s.ValidPos → Bool
  | 0, _, _ => true
  | k + 1, s, p =>
    if h : _ then
      let b := p.get h
      if b = '_' then
        checkDisambiguation k s (p.next h)
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

private def needDisambiguation (prev : String) (next : String) : Bool :=
  prev.endsWith "__" || checkDisambiguation next.utf8ByteSize next next.startValidPos

private def Name.mangleAux : Name → String
  | Name.anonymous => ""
  | Name.str p s =>
    let m := String.mangle s
    match p with
    | Name.anonymous =>
      if checkDisambiguation m.utf8ByteSize m m.startValidPos then "00" ++ m else m
    | p              =>
      let m1 := mangleAux p
      m1 ++ (if needDisambiguation m1 m then "_00" else "_") ++ m
  | Name.num p n =>
    match p with
    | Name.anonymous => n.repr ++ "_"
    | p              =>
      mangleAux p ++ "_" ++ n.repr ++ "_"

@[export lean_name_mangle]
def Name.mangle (n : Name) (pre : String := "l_") : String :=
  pre ++ Name.mangleAux n

@[export lean_mk_module_initialization_function_name]
def mkModuleInitializationFunctionName (moduleName : Name) : String :=
  "initialize_" ++ moduleName.mangle ""

-- assumes `s` has been generated `Name.mangle n ""`
private def Name.unmangleAux (s : String) (p : s.ValidPos) (res : Name)
    (acc : String) (ucount : Nat) : Nat → Name
  | 0 => res.str (acc.pushn '_' (ucount / 2))
  | k + 1 =>
    if h : p = s.endValidPos then res.str (acc.pushn '_' (ucount / 2)) else
    let ch := p.get h
    let p := p.next h
    if ch = '_' then unmangleAux s p res acc (ucount + 1) k else
    if ucount % 2 = 0 then
      unmangleAux s p res (acc.pushn '_' (ucount / 2) |>.push ch) 0 k
    else if ch.isDigit then
      let res := res.str (acc.pushn '_' (ucount / 2))
      if h : ch = '0' ∧ ∃ h : p ≠ s.endValidPos, p.get h = '0' then
        unmangleAux s (p.next h.2.1) res "" 0 k
      else
        decodeNum s p res (ch.val - 48).toNat k
    else if h : ch = 'x' ∧ checkLowerHex 2 s p then
      let acc := acc.pushn '_' (ucount / 2)
      unmangleAux s ⟨_, valid_of_checkLowerHex h.2⟩ res (acc.push (Char.ofNat (parseLowerHex 2 s p h.2 0))) 0 k
    else if h : ch = 'u' ∧ checkLowerHex 4 s p then
      let acc := acc.pushn '_' (ucount / 2)
      unmangleAux s ⟨_, valid_of_checkLowerHex h.2⟩ res (acc.push (Char.ofNat (parseLowerHex 4 s p h.2 0))) 0 k
    else if h : ch = 'U' ∧ checkLowerHex 8 s p then
      let acc := acc.pushn '_' (ucount / 2)
      unmangleAux s ⟨_, valid_of_checkLowerHex h.2⟩ res (acc.push (Char.ofNat (parseLowerHex 8 s p h.2 0))) 0 k
    else
      unmangleAux s p (res.str acc) ("".pushn '_' (ucount / 2) |>.push ch) 0 k
where
  decodeNum (s : String) (p : s.ValidPos) (res : Name) (n : Nat) : Nat → Name
    | 0 => res.num n
    | k + 1 =>
      if h : p = s.endValidPos then res.num n else
      let ch := p.get h
      let p := p.next h
      if ch.isDigit then
        decodeNum s p res (n * 10 + (ch.val - 48).toNat) k
      else -- assume ch = '_'
        let res := res.num n
        if h : p = s.endValidPos then res else
        nameStart s (p.next h) res k -- assume s.get' p h = '_'
  nameStart (s : String) (p : s.ValidPos) (res : Name) : Nat → Name
    | 0 => res
    | k + 1 =>
      if h : p = s.endValidPos then res else
      let ch := p.get h
      let p := p.next h
      if ch.isDigit then
        if h : ch = '0' ∧ ∃ h : p ≠ s.endValidPos, p.get h = '0' then
          unmangleAux s (p.next h.2.1) res "" 0 k
        else
          decodeNum s p res (ch.val - 48).toNat k
      else if ch = '_' then
        unmangleAux s p res "" 1 k
      else
        unmangleAux s p res (String.singleton ch) 0 k

def Name.unmangle (s : String) : Name :=
  unmangleAux.nameStart s s.startValidPos .anonymous s.length

def Name.unmangle? (s : String) : Option Name :=
  let n := unmangle s
  if mangleAux n = s then some n else none

end Lean
