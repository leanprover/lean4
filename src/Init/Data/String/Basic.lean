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
import Init.Data.String.Substring

universe u

namespace String

@[inline] def find (s : String) (p : Char → Bool) : Pos :=
  s.toSubstring.find p

def revFind (s : String) (p : Char → Bool) : Option Pos :=
  s.toSubstring.revFind p

@[specialize] def split (s : String) (p : Char → Bool) : List String :=
  s.toSubstring.split p

-- find revFind split

def drop (s : String) (n : Nat) : String :=
  (s.toSubstring.drop n).toString

def dropRight (s : String) (n : Nat) : String :=
  (s.toSubstring.dropRight n).toString

def take (s : String) (n : Nat) : String :=
  (s.toSubstring.take n).toString

def takeRight (s : String) (n : Nat) : String :=
  (s.toSubstring.takeRight n).toString

def takeWhile (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.takeWhile p).toString

def dropWhile (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.dropWhile p).toString

def takeRightWhile (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.takeRightWhile p).toString

def dropRightWhile (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.dropRightWhile p).toString

def startsWith (s pre : String) : Bool :=
  s.toSubstring.take pre.length == pre.toSubstring

def endsWith (s post : String) : Bool :=
  s.toSubstring.takeRight post.length == post.toSubstring

def trimRight (s : String) : String :=
  s.toSubstring.trimRight.toString

def trimLeft (s : String) : String :=
  s.toSubstring.trimLeft.toString

def trim (s : String) : String :=
  s.toSubstring.trim.toString

@[inline] def nextWhile (s : String) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  Substring.takeWhileAux s s.endPos p i

@[inline] def nextUntil (s : String) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  nextWhile s (fun c => !p c) i

def toUpper (s : String) : String :=
  s.map Char.toUpper

def toLower (s : String) : String :=
  s.map Char.toLower

def capitalize (s : String) :=
  s.set 0 <| s.get 0 |>.toUpper

def decapitalize (s : String) :=
  s.set 0 <| s.get 0 |>.toLower

end String

namespace Char

protected def toString (c : Char) : String :=
  String.singleton c

end Char

namespace String

/-- Return the beginning of the line that contains character `pos`. -/
def findLineStart (s : String) (pos : String.Pos) : String.Pos :=
  match Substring.revFindAux s (· = '\n') pos with
  | none => 0
  | some n => ⟨n.byteIdx + 1⟩

def findAux (s : String) (p : Char → Bool) (stopPos : String.Pos) (pos : String.Pos) : String.Pos :=
  if h : pos < stopPos then
    if p (s.get pos) then pos
    else
      have := Nat.sub_lt_sub_left h (String.lt_next s pos)
      findAux s p stopPos (s.next pos)
  else pos
termination_by stopPos.1 - pos.1

end String
