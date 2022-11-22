/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
universe u

def List.asString (s : List Char) : String :=
  ⟨s⟩

namespace String

instance : OfNat String.Pos (nat_lit 0) where
  ofNat := {}

instance : LT String :=
  ⟨fun s₁ s₂ => s₁.data < s₂.data⟩

@[extern "lean_string_dec_lt"]
instance decLt (s₁ s₂ : @& String) : Decidable (s₁ < s₂) :=
  List.hasDecidableLt s₁.data s₂.data

@[extern "lean_string_length"]
def length : (@& String) → Nat
  | ⟨s⟩ => s.length

/-- The internal implementation uses dynamic arrays and will perform destructive updates
   if the String is not shared. -/
@[extern "lean_string_push"]
def push : String → Char → String
  | ⟨s⟩, c => ⟨s ++ [c]⟩

/-- The internal implementation uses dynamic arrays and will perform destructive updates
   if the String is not shared. -/
@[extern "lean_string_append"]
def append : String → (@& String) → String
  | ⟨a⟩, ⟨b⟩ => ⟨a ++ b⟩

/-- O(n) in the runtime, where n is the length of the String -/
def toList (s : String) : List Char :=
  s.data

private def utf8GetAux : List Char → Pos → Pos → Char
  | [],    _, _ => default
  | c::cs, i, p => if i = p then c else utf8GetAux cs (i + c) p

/--
  Return character at position `p`. If `p` is not a valid position
  returns `(default : Char)`.
  See `utf8GetAux` for the reference implementation.
-/
@[extern "lean_string_utf8_get"]
def get (s : @& String) (p : @& Pos) : Char :=
  match s with
  | ⟨s⟩ => utf8GetAux s 0 p

private def utf8GetAux? : List Char → Pos → Pos → Option Char
  | [],    _, _ => none
  | c::cs, i, p => if i = p then c else utf8GetAux cs (i + c) p

@[extern "lean_string_utf8_get_opt"]
def get? : (@& String) → (@& Pos) → Option Char
  | ⟨s⟩, p => utf8GetAux? s 0 p

/--
  Similar to `get`, but produces a panic error message if `p` is not a valid `String.Pos`.
-/
@[extern "lean_string_utf8_get_bang"]
def get! (s : @& String) (p : @& Pos) : Char :=
  match s with
  | ⟨s⟩ => utf8GetAux s 0 p

private def utf8SetAux (c' : Char) : List Char → Pos → Pos → List Char
  | [],    _, _ => []
  | c::cs, i, p =>
    if i = p then (c'::cs) else c::(utf8SetAux c' cs (i + c) p)

@[extern "lean_string_utf8_set"]
def set : String → (@& Pos) → Char → String
  | ⟨s⟩, i, c => ⟨utf8SetAux c s 0 i⟩

def modify (s : String) (i : Pos) (f : Char → Char) : String :=
  s.set i <| f <| s.get i

@[extern "lean_string_utf8_next"]
def next (s : @& String) (p : @& Pos) : Pos :=
  let c := get s p
  p + c

private def utf8PrevAux : List Char → Pos → Pos → Pos
  | [],    _, _ => 0
  | c::cs, i, p =>
    let i' := i + c
    if i' = p then i else utf8PrevAux cs i' p

@[extern "lean_string_utf8_prev"]
def prev : (@& String) → (@& Pos) → Pos
  | ⟨s⟩, p => if p = 0 then 0 else utf8PrevAux s 0 p

def front (s : String) : Char :=
  get s 0

def back (s : String) : Char :=
  get s (prev s s.endPos)

@[extern "lean_string_utf8_at_end"]
def atEnd : (@& String) → (@& Pos) → Bool
  | s, p => p.byteIdx ≥ utf8ByteSize s

/--
Similar to `get` but runtime does not perform bounds check.
-/
@[extern "lean_string_utf8_get_fast"]
def get' (s : @& String) (p : @& Pos) (h : ¬ s.atEnd p) : Char :=
  match s with
  | ⟨s⟩ => utf8GetAux s 0 p

@[extern "lean_string_utf8_next_fast"]
def next' (s : @& String) (p : @& Pos) (h : ¬ s.atEnd p) : Pos :=
  let c := get s p
  p + c

/- TODO: remove `partial` keywords after we restore the tactic
  framework and wellfounded recursion support -/

partial def posOfAux (s : String) (c : Char) (stopPos : Pos) (pos : Pos) : Pos :=
  if pos >= stopPos then pos
  else if s.get pos == c then pos
       else posOfAux s c stopPos (s.next pos)

@[inline] def posOf (s : String) (c : Char) : Pos :=
  posOfAux s c s.endPos 0

partial def revPosOfAux (s : String) (c : Char) (pos : Pos) : Option Pos :=
 if s.get pos == c then some pos
 else if pos == 0 then none
 else revPosOfAux s c (s.prev pos)

def revPosOf (s : String) (c : Char) : Option Pos :=
  if s.endPos == 0 then none
  else revPosOfAux s c (s.prev s.endPos)

partial def findAux (s : String) (p : Char → Bool) (stopPos : Pos) (pos : Pos) : Pos :=
  if pos >= stopPos then pos
  else if p (s.get pos) then pos
       else findAux s p stopPos (s.next pos)

@[inline] def find (s : String) (p : Char → Bool) : Pos :=
  findAux s p s.endPos 0

partial def revFindAux (s : String) (p : Char → Bool) (pos : Pos) : Option Pos :=
 if p (s.get pos) then some pos
 else if pos == 0 then none
 else revFindAux s p (s.prev pos)

def revFind (s : String) (p : Char → Bool) : Option Pos :=
  if s.endPos == 0 then none
  else revFindAux s p (s.prev s.endPos)

abbrev Pos.min (p₁ p₂ : Pos) : Pos :=
  { byteIdx := p₁.byteIdx.min p₂.byteIdx }

/-- Returns the first position where the two strings differ. -/
partial def firstDiffPos (a b : String) : Pos :=
  let stopPos := a.endPos.min b.endPos
  let rec loop (i : Pos) : Pos :=
    if i >= stopPos || a.get i != b.get i then i
    else loop (a.next i)
  loop 0

@[extern "lean_string_utf8_extract"]
def extract : (@& String) → (@& Pos) → (@& Pos) → String
  | ⟨s⟩, b, e => if b.byteIdx ≥ e.byteIdx then ⟨[]⟩ else ⟨go₁ s 0 b e⟩
where
  go₁ : List Char → Pos → Pos → Pos → List Char
    | [],        _, _, _ => []
    | s@(c::cs), i, b, e => if i = b then go₂ s i e else go₁ cs (i + c) b e

  go₂ : List Char → Pos → Pos → List Char
    | [],    _, _ => []
    | c::cs, i, e => if i = e then [] else c :: go₂ cs (i + c) e


@[specialize] partial def splitAux (s : String) (p : Char → Bool) (b : Pos) (i : Pos) (r : List String) : List String :=
  if s.atEnd i then
    let r := (s.extract b i)::r
    r.reverse
  else if p (s.get i) then
    let i := s.next i
    splitAux s p i i (s.extract b { byteIdx := i.byteIdx - 1 } :: r)
  else
    splitAux s p b (s.next i) r

@[specialize] def split (s : String) (p : Char → Bool) : List String :=
  splitAux s p 0 0 []

partial def splitOnAux (s sep : String) (b : Pos) (i : Pos) (j : Pos) (r : List String) : List String :=
  if s.atEnd i then
    let r := if sep.atEnd j then ""::(s.extract b (i - j))::r else (s.extract b i)::r
    r.reverse
  else if s.get i == sep.get j then
    let i := s.next i
    let j := sep.next j
    if sep.atEnd j then
      splitOnAux s sep i i 0 (s.extract b (i - j)::r)
    else
      splitOnAux s sep b i j r
  else
    splitOnAux s sep b (s.next i) 0 r

def splitOn (s : String) (sep : String := " ") : List String :=
  if sep == "" then [s] else splitOnAux s sep 0 0 0 []

instance : Inhabited String := ⟨""⟩

instance : Append String := ⟨String.append⟩

def str : String → Char → String := push

def pushn (s : String) (c : Char) (n : Nat) : String :=
  n.repeat (fun s => s.push c) s

def isEmpty (s : String) : Bool :=
  s.endPos == 0

def join (l : List String) : String :=
  l.foldl (fun r s => r ++ s) ""

def singleton (c : Char) : String :=
  "".push c

def intercalate (s : String) : List String → String
  | []      => ""
  | a :: as => go a s as
where go (acc : String) (s : String) : List String → String
  | a :: as => go (acc ++ s ++ a) s as
  | []      => acc

/-- Iterator for `String`. That is, a `String` and a position in that string. -/
structure Iterator where
  s : String
  i : Pos
  deriving DecidableEq

def mkIterator (s : String) : Iterator :=
  ⟨s, 0⟩

abbrev iter := mkIterator

instance : SizeOf String.Iterator where
  sizeOf i := i.1.utf8ByteSize - i.2.byteIdx

theorem Iterator.sizeOf_eq (i : String.Iterator) : sizeOf i = i.1.utf8ByteSize - i.2.byteIdx :=
  rfl

namespace Iterator
def toString : Iterator → String
  | ⟨s, _⟩ => s

def remainingBytes : Iterator → Nat
  | ⟨s, i⟩ => s.endPos.byteIdx - i.byteIdx

def pos : Iterator → Pos
  | ⟨_, i⟩ => i

def curr : Iterator → Char
  | ⟨s, i⟩ => get s i

def next : Iterator → Iterator
  | ⟨s, i⟩ => ⟨s, s.next i⟩

def prev : Iterator → Iterator
  | ⟨s, i⟩ => ⟨s, s.prev i⟩

def atEnd : Iterator → Bool
  | ⟨s, i⟩ => i.byteIdx ≥ s.endPos.byteIdx

def hasNext : Iterator → Bool
  | ⟨s, i⟩ => i.byteIdx < s.endPos.byteIdx

def hasPrev : Iterator → Bool
  | ⟨_, i⟩ => i.byteIdx > 0

def setCurr : Iterator → Char → Iterator
  | ⟨s, i⟩, c => ⟨s.set i c, i⟩

def toEnd : Iterator → Iterator
  | ⟨s, _⟩ => ⟨s, s.endPos⟩

def extract : Iterator → Iterator → String
  | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
    if s₁ ≠ s₂ || b > e then ""
    else s₁.extract b e

def forward : Iterator → Nat → Iterator
  | it, 0   => it
  | it, n+1 => forward it.next n

def remainingToString : Iterator → String
  | ⟨s, i⟩ => s.extract i s.endPos

def nextn : Iterator → Nat → Iterator
  | it, 0   => it
  | it, i+1 => nextn it.next i

def prevn : Iterator → Nat → Iterator
  | it, 0   => it
  | it, i+1 => prevn it.prev i
end Iterator

partial def offsetOfPosAux (s : String) (pos : Pos) (i : Pos) (offset : Nat) : Nat :=
  if i >= pos || s.atEnd i then
    offset
  else
    offsetOfPosAux s pos (s.next i) (offset+1)

def offsetOfPos (s : String) (pos : Pos) : Nat :=
  offsetOfPosAux s pos 0 0

@[specialize] partial def foldlAux {α : Type u} (f : α → Char → α) (s : String) (stopPos : Pos) (i : Pos) (a : α) : α :=
  let rec loop (i : Pos) (a : α) :=
    if i >= stopPos then a
    else loop (s.next i) (f a (s.get i))
  loop i a

@[inline] def foldl {α : Type u} (f : α → Char → α) (init : α) (s : String) : α :=
  foldlAux f s s.endPos 0 init

@[specialize] partial def foldrAux {α : Type u} (f : Char → α → α) (a : α) (s : String) (stopPos : Pos) (i : Pos) : α :=
  let rec loop (i : Pos) :=
    if i >= stopPos then a
    else f (s.get i) (loop (s.next i))
  loop i

@[inline] def foldr {α : Type u} (f : Char → α → α) (init : α) (s : String) : α :=
  foldrAux f init s s.endPos 0

@[specialize] partial def anyAux (s : String) (stopPos : Pos) (p : Char → Bool) (i : Pos) : Bool :=
  let rec loop (i : Pos) :=
    if i >= stopPos then false
    else if p (s.get i) then true
    else loop (s.next i)
  loop i

@[inline] def any (s : String) (p : Char → Bool) : Bool :=
anyAux s s.endPos p 0

@[inline] def all (s : String) (p : Char → Bool) : Bool :=
!s.any (fun c => !p c)

def contains (s : String) (c : Char) : Bool :=
s.any (fun a => a == c)

@[specialize] partial def mapAux (f : Char → Char) (i : Pos) (s : String) : String :=
  if s.atEnd i then s
  else
    let c := f (s.get i)
    let s := s.set i c
    mapAux f (s.next i) s

@[inline] def map (f : Char → Char) (s : String) : String :=
  mapAux f 0 s

def isNat (s : String) : Bool :=
  !s.isEmpty && s.all (·.isDigit)

def toNat? (s : String) : Option Nat :=
  if s.isNat then
    some <| s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0
  else
    none

/--
Return `true` iff the substring of byte size `sz` starting at position `off1` in `s1` is equal to that starting at `off2` in `s2.`.
False if either substring of that byte size does not exist. -/
partial def substrEq (s1 : String) (off1 : String.Pos) (s2 : String) (off2 : String.Pos) (sz : Nat) : Bool :=
  off1.byteIdx + sz ≤ s1.endPos.byteIdx && off2.byteIdx + sz ≤ s2.endPos.byteIdx && loop off1 off2 { byteIdx := off1.byteIdx + sz }
where
  loop (off1 off2 stop1 : Pos) :=
    if off1.byteIdx >= stop1.byteIdx then
      true
    else
      let c₁ := s1.get off1
      let c₂ := s2.get off2
      c₁ == c₂ && loop (off1 + c₁) (off2 + c₂) stop1

/-- Return true iff `p` is a prefix of `s` -/
def isPrefixOf (p : String) (s : String) : Bool :=
  substrEq p 0 s 0 p.endPos.byteIdx

/-- Replace all occurrences of `pattern` in `s` with `replacment`. -/
partial def replace (s pattern replacement : String) : String :=
  loop "" 0 0
where
  loop (acc : String) (accStop pos : String.Pos) :=
    if pos.byteIdx + pattern.endPos.byteIdx > s.endPos.byteIdx then
      acc ++ s.extract accStop s.endPos
    else if s.substrEq pos pattern 0 pattern.endPos.byteIdx then
      loop (acc ++ s.extract accStop pos ++ replacement) (pos + pattern) (pos + pattern)
    else
      loop acc accStop (s.next pos)

end String

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

/-- Return the offset into `s` of the first occurence of `c` in `s`,
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

partial def splitOn (s : Substring) (sep : String := " ") : List Substring :=
  if sep == "" then
    [s]
  else
    let rec loop (b i j : String.Pos) (r : List Substring) : List Substring :=
      if i.byteIdx == s.bsize then
        let r := if sep.atEnd j then
          "".toSubstring :: s.extract b (i-j) :: r
        else
          s.extract b i :: r
        r.reverse
      else if s.get i == sep.get j then
        let i := s.next i
        let j := sep.next j
        if sep.atEnd j then
          loop i i 0 (s.extract b (i-j) :: r)
        else
          loop b i j r
      else
        loop b (s.next i) 0 r
    loop 0 0 0 []

@[inline] def foldl {α : Type u} (f : α → Char → α) (init : α) (s : Substring) : α :=
  match s with
  | ⟨s, b, e⟩ => String.foldlAux f s e b init

@[inline] def foldr {α : Type u} (f : Char → α → α) (init : α) (s : Substring) : α :=
  match s with
  | ⟨s, b, e⟩ => String.foldrAux f init s e b

@[inline] def any (s : Substring) (p : Char → Bool) : Bool :=
  match s with
  | ⟨s, b, e⟩ => String.anyAux s e p b

@[inline] def all (s : Substring) (p : Char → Bool) : Bool :=
  !s.any (fun c => !p c)

def contains (s : Substring) (c : Char) : Bool :=
  s.any (fun a => a == c)

@[specialize] private partial def takeWhileAux (s : String) (stopPos : String.Pos) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  if i >= stopPos then i
  else if p (s.get i) then takeWhileAux s stopPos p (s.next i)
  else i

@[inline] def takeWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let e := takeWhileAux s e p b;
    ⟨s, b, e⟩

@[inline] def dropWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let b := takeWhileAux s e p b;
    ⟨s, b, e⟩

@[specialize] private partial def takeRightWhileAux (s : String) (begPos : String.Pos) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  if i == begPos then i
  else
    let i' := s.prev i
    let c  := s.get i'
    if !p c then i
    else takeRightWhileAux s begPos p i'

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

end Substring

namespace String

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

protected def Char.toString (c : Char) : String :=
  String.singleton c
