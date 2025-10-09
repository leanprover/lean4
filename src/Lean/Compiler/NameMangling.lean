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

private def checkLowerHex : Nat → String → String.Pos.Raw → Bool
  | 0, _, _ => true
  | k + 1, s, pos =>
    if h : s.atEnd pos then
      false
    else
      let ch := s.get' pos h
      (ch.isDigit || (ch.val >= 97 && ch.val <= 102)) && -- 0-9a-f
        checkLowerHex k s (s.next' pos h)

private def parseLowerHex : Nat → String → String.Pos.Raw → Nat → Nat
  | 0, _, _, n => n
  | k + 1, s, pos, n =>
    let ch := s.get pos
    let pos := s.next pos
    if ch.isDigit then parseLowerHex k s pos (n <<< 4 ||| (ch.val - 48).toNat)
    else parseLowerHex k s pos (n <<< 4 ||| (ch.val - 87).toNat)

private def checkDisambiguation : Nat → String → String.Pos.Raw → Bool
  | 0, _, _ => true
  | k + 1, s, p =>
    if h : _ then
      let b := s.getUTF8Byte p h
      if b = '_'.toUInt8 then
        checkDisambiguation k s ⟨p.byteIdx + 1⟩
      else if b = 'x'.toUInt8 then
        checkLowerHex 2 s ⟨p.byteIdx + 1⟩
      else if b = 'u'.toUInt8 then
        checkLowerHex 4 s ⟨p.byteIdx + 1⟩
      else if b = 'U'.toUInt8 then
        checkLowerHex 8 s ⟨p.byteIdx + 1⟩
      else if b >= 48 && b <= 57 then
        true
      else false
    else true

private def needDisambiguation (prev : String) (next : String) : Bool :=
  prev.endsWith "__" || checkDisambiguation next.utf8ByteSize next 0

private def Name.mangleAux : Name → String
  | Name.anonymous => ""
  | Name.str p s =>
    let m := String.mangle s
    match p with
    | Name.anonymous =>
      if checkDisambiguation m.utf8ByteSize m 0 then "00" ++ m else m
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
private def Name.unmangleAux (s : String) (p : String.Pos.Raw) (res : Name)
    (acc : String) (ucount : Nat) : Nat → Name
  | 0 => res.str (acc.pushn '_' (ucount / 2))
  | k + 1 =>
    if h : s.atEnd p then res.str (acc.pushn '_' (ucount / 2)) else
    let ch := s.get' p h
    let p := s.next' p h
    if ch = '_' then unmangleAux s p res acc (ucount + 1) k else
    if ucount % 2 = 0 then
      unmangleAux s p res (acc.pushn '_' (ucount / 2) |>.push ch) 0 k
    else if ch.isDigit then
      let res := res.str (acc.pushn '_' (ucount / 2))
      if ch = '0' ∧ s.get p = '0' then
        unmangleAux s (s.next p) res "" 0 k
      else
        decodeNum s p res (ch.val - 48).toNat k
    else if ch = 'x' ∧ checkLowerHex 2 s p then
      let acc := acc.pushn '_' (ucount / 2)
      unmangleAux s ⟨p.byteIdx + 2⟩ res (acc.push (Char.ofNat (parseLowerHex 2 s p 0))) 0 k
    else if ch = 'u' ∧ checkLowerHex 4 s p then
      let acc := acc.pushn '_' (ucount / 2)
      unmangleAux s ⟨p.byteIdx + 4⟩ res (acc.push (Char.ofNat (parseLowerHex 4 s p 0))) 0 k
    else if ch = 'U' ∧ checkLowerHex 8 s p then
      let acc := acc.pushn '_' (ucount / 2)
      unmangleAux s ⟨p.byteIdx + 8⟩ res (acc.push (Char.ofNat (parseLowerHex 8 s p 0))) 0 k
    else
      unmangleAux s p (res.str acc) ("".pushn '_' (ucount / 2) |>.push ch) 0 k
where
  decodeNum (s : String) (p : String.Pos.Raw) (res : Name) (n : Nat) : Nat → Name
    | 0 => res.num n
    | k + 1 =>
      if h : s.atEnd p then res.num n else
      let ch := s.get' p h
      let p := s.next' p h
      if ch.isDigit then
        decodeNum s p res (n * 10 + (ch.val - 48).toNat) k
      else -- assume ch = '_'
        let res := res.num n
        if h : s.atEnd p then res else
        nameStart s (s.next' p h) res k -- assume s.get' p h = '_'
  nameStart (s : String) (p : String.Pos.Raw) (res : Name) : Nat → Name
    | 0 => res
    | k + 1 =>
      if h : s.atEnd p then res else
      let ch := s.get' p h
      let p := s.next' p h
      if ch.isDigit then
        if ch = '0' ∧ s.get p = '0' then
          unmangleAux s (s.next p) res "" 0 k
        else
          decodeNum s p res (ch.val - 48).toNat k
      else if ch = '_' then
        unmangleAux s p res "" 1 k
      else
        unmangleAux s p res (String.singleton ch) 0 k

def Name.unmangle (s : String) : Name :=
  unmangleAux.nameStart s 0 .anonymous s.length

def Name.unmangle? (s : String) : Option Name :=
  let n := unmangle s
  if mangleAux n = s then some n else none

end Lean
