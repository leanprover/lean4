/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Extern
import Init.Data.String.More
import Init.Data.String.Iterator

universe u

namespace Substring

@[inline] def isEmpty (ss : Substring) : Bool :=
  ss.bsize == 0

@[inline] def toString : Substring → String
  | ⟨s, b, e⟩ => s.extract b e

@[inline] def toIterator : Substring → String.Iterator
  | ⟨s, b, _⟩ => ⟨s, b⟩

/-- Return the codepoint at the given offset into the substring. -/
@[inline] def get : Substring → String.Pos → Char
  | ⟨s, b, _⟩, p => s.get (b+p)

/-- Given an offset of a codepoint into the substring,
return the offset there of the next codepoint. -/
@[inline] def next : Substring → String.Pos → String.Pos
  | ⟨s, b, e⟩, p =>
    let absP := b+p
    if absP = e then p else { byteIdx := (s.next absP).byteIdx - b.byteIdx }

theorem lt_next (s : Substring) (i : String.Pos) (h : i.1 < s.bsize) :
    i.1 < (s.next i).1 := by
  simp [next]; rw [if_neg ?a]
  case a =>
    refine mt (congrArg String.Pos.byteIdx) (Nat.ne_of_lt ?_)
    exact (Nat.add_comm .. ▸ Nat.add_lt_of_lt_sub h :)
  apply Nat.lt_sub_of_add_lt
  rw [Nat.add_comm]; apply String.lt_next

/-- Given an offset of a codepoint into the substring,
return the offset there of the previous codepoint. -/
@[inline] def prev : Substring → String.Pos → String.Pos
  | ⟨s, b, _⟩, p =>
    let absP := b+p
    if absP = b then p else { byteIdx := (s.prev absP).byteIdx - b.byteIdx }

def nextn : Substring → Nat → String.Pos → String.Pos
  | _,  0,   p => p
  | ss, i+1, p => ss.nextn i (ss.next p)

def prevn : Substring → Nat → String.Pos → String.Pos
  | _,  0,   p => p
  | ss, i+1, p => ss.prevn i (ss.prev p)

@[inline] def front (s : Substring) : Char :=
  s.get 0

@[inline] def back (s : Substring) : Char :=
  get s (prev s s.stopPos)

/-- Return the offset into `s` of the first occurrence of `c` in `s`,
or `s.bsize` if `c` doesn't occur. -/
@[inline] def posOf (s : Substring) (c : Char) : String.Pos :=
  match s with
  | ⟨s, b, e⟩ => { byteIdx := (String.posOfAux s c e b).byteIdx - b.byteIdx }

@[inline] def drop : Substring → Nat → Substring
  | ss@⟨s, b, e⟩, n => ⟨s, b + ss.nextn n 0, e⟩

@[inline] def dropRight : Substring → Nat → Substring
  | ss@⟨s, b, _⟩, n => ⟨s, b, b + ss.prevn n ⟨ss.bsize⟩⟩

@[inline] def take : Substring → Nat → Substring
  | ss@⟨s, b, _⟩, n => ⟨s, b, b + ss.nextn n 0⟩

@[inline] def takeRight : Substring → Nat → Substring
  | ss@⟨s, b, e⟩, n => ⟨s, b + ss.prevn n ⟨ss.bsize⟩, e⟩

@[inline] def atEnd : Substring → String.Pos → Bool
  | ⟨_, b, e⟩, p => b + p == e

@[inline] def extract : Substring → String.Pos → String.Pos → Substring
  | ⟨s, b, e⟩, b', e' => if b' ≥ e' then ⟨"", 0, 0⟩ else ⟨s, e.min (b+b'), e.min (b+e')⟩

def splitOn (s : Substring) (sep : String := " ") : List Substring :=
  if sep == "" then
    [s]
  else
    let rec loop (b i j : String.Pos) (r : List Substring) : List Substring :=
      if h : i.byteIdx < s.bsize then
        have := Nat.sub_lt_sub_left h (lt_next s i h)
        if s.get i == sep.get j then
          let i := s.next i
          let j := sep.next j
          if sep.atEnd j then
            loop i i 0 (s.extract b (i-j) :: r)
          else
            loop b i j r
        else
          loop b (s.next i) 0 r
      else
        let r := if sep.atEnd j then
          "".toSubstring :: s.extract b (i-j) :: r
        else
          s.extract b i :: r
        r.reverse
      termination_by s.bsize - i.1
    loop 0 0 0 []

@[specialize] def foldlAux {α : Type u} (f : α → Char → α) (s : String) (stopPos : String.Pos) (i : String.Pos) (a : α) : α :=
  if h : i < stopPos then
    have := Nat.sub_lt_sub_left h (String.lt_next s i)
    foldlAux f s stopPos (s.next i) (f a (s.get i))
  else a
termination_by stopPos.1 - i.1

@[inline] def foldl {α : Type u} (f : α → Char → α) (init : α) (s : Substring) : α :=
  match s with
  | ⟨s, b, e⟩ => foldlAux f s e b init

@[specialize] def foldrAux {α : Type u} (f : Char → α → α) (a : α) (s : String) (i begPos : String.Pos) : α :=
  if h : begPos < i then
    have := String.prev_lt_of_pos s i <| mt (congrArg String.Pos.byteIdx) <|
      Ne.symm <| Nat.ne_of_lt <| Nat.lt_of_le_of_lt (Nat.zero_le _) h
    let i := s.prev i
    let a := f (s.get i) a
    foldrAux f a s i begPos
  else a
termination_by i.1

@[inline] def foldr {α : Type u} (f : Char → α → α) (init : α) (s : Substring) : α :=
  match s with
  | ⟨s, b, e⟩ => foldrAux f init s e b

@[specialize] def anyAux (s : String) (stopPos : String.Pos) (p : Char → Bool) (i : String.Pos) : Bool :=
  if h : i < stopPos then
    if p (s.get i) then true
    else
      have := Nat.sub_lt_sub_left h (String.lt_next s i)
      anyAux s stopPos p (s.next i)
  else false
termination_by stopPos.1 - i.1

@[inline] def any (s : Substring) (p : Char → Bool) : Bool :=
  match s with
  | ⟨s, b, e⟩ => anyAux s e p b

@[inline] def all (s : Substring) (p : Char → Bool) : Bool :=
  !s.any (fun c => !p c)

def contains (s : Substring) (c : Char) : Bool :=
  s.any (fun a => a == c)

@[specialize] def takeWhileAux (s : String) (stopPos : String.Pos) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  if h : i < stopPos then
    if p (s.get i) then
      have := Nat.sub_lt_sub_left h (String.lt_next s i)
      takeWhileAux s stopPos p (s.next i)
    else i
  else i
termination_by stopPos.1 - i.1

@[inline] def takeWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let e := takeWhileAux s e p b;
    ⟨s, b, e⟩

@[inline] def dropWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let b := takeWhileAux s e p b;
    ⟨s, b, e⟩

@[specialize] def takeRightWhileAux (s : String) (begPos : String.Pos) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  if h : begPos < i then
    have := String.prev_lt_of_pos s i <| mt (congrArg String.Pos.byteIdx) <|
      Ne.symm <| Nat.ne_of_lt <| Nat.lt_of_le_of_lt (Nat.zero_le _) h
    let i' := s.prev i
    let c  := s.get i'
    if !p c then i
    else takeRightWhileAux s begPos p i'
  else i
termination_by i.1

@[inline] def takeRightWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let b := takeRightWhileAux s b p e
    ⟨s, b, e⟩

@[inline] def dropRightWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let e := takeRightWhileAux s b p e
    ⟨s, b, e⟩

@[inline] def trimLeft (s : Substring) : Substring :=
  s.dropWhile Char.isWhitespace

@[inline] def trimRight (s : Substring) : Substring :=
  s.dropRightWhile Char.isWhitespace

@[inline] def trim : Substring → Substring
  | ⟨s, b, e⟩ =>
    let b := takeWhileAux s e Char.isWhitespace b
    let e := takeRightWhileAux s b Char.isWhitespace e
    ⟨s, b, e⟩

def findAux (s : String) (p : Char → Bool) (stopPos : String.Pos) (pos : String.Pos) : String.Pos :=
  if h : pos < stopPos then
    if p (s.get pos) then pos
    else
      have := Nat.sub_lt_sub_left h (String.lt_next s pos)
      findAux s p stopPos (s.next pos)
  else pos
termination_by stopPos.1 - pos.1

@[inline] def find (s : Substring) (p : Char → Bool) : String.Pos :=
  match s with
  | ⟨s, b, e⟩ => findAux s p e b

def revFindAux (s : String) (p : Char → Bool) (pos : String.Pos) : Option String.Pos :=
  if h : pos = 0 then none
  else
    have := String.prev_lt_of_pos s pos h
    let pos := s.prev pos
    if p (s.get pos) then some pos
    else revFindAux s p pos
termination_by pos.1

def revFind (s : Substring) (p : Char → Bool) : Option String.Pos :=
  match s with
  | ⟨s, _, e⟩ => revFindAux s p e

@[specialize] def splitAux (s : String) (p : Char → Bool) (b : String.Pos) (i : String.Pos) (r : List String) : List String :=
  if h : s.atEnd i then
    let r := (s.extract b i)::r
    r.reverse
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (String.lt_next s _)
    if p (s.get i) then
      let i' := s.next i
      splitAux s p i' i' (s.extract b i :: r)
    else
      splitAux s p b (s.next i) r
termination_by s.endPos.1 - i.1

@[specialize] def split (s : Substring) (p : Char → Bool) : List String :=
  match s with
  | ⟨s, b, _⟩ => splitAux s p b 0 []

def isNat (s : Substring) : Bool :=
  s.all fun c => c.isDigit

def toNat? (s : Substring) : Option Nat :=
  if s.isNat then
    some <| s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0
  else
    none

def beq (ss1 ss2 : Substring) : Bool :=
  ss1.bsize == ss2.bsize && ss1.str.substrEq ss1.startPos ss2.str ss2.startPos ss1.bsize

instance hasBeq : BEq Substring := ⟨beq⟩

/-- Checks whether two substrings have the same position and content. -/
def sameAs (ss1 ss2 : Substring) : Bool :=
  ss1.startPos == ss2.startPos && ss1 == ss2

end Substring
