/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic init.data.char.basic init.data.option.basic
universes u

structure String :=
(data : List Char)

abbrev String.Pos := Nat

structure Substring :=
(str : String) (startPos : String.Pos) (stopPos : String.Pos)

attribute [extern cpp "lean::string_mk"] String.mk
attribute [extern cpp "lean::string_data"] String.data

@[extern cpp "lean::string_dec_eq"]
def String.decEq (s₁ s₂ : @& String) : Decidable (s₁ = s₂) :=
match s₁, s₂ with
| ⟨s₁⟩, ⟨s₂⟩ =>
 if h : s₁ = s₂ then isTrue (congrArg _ h)
 else isFalse (fun h' => String.noConfusion h' (fun h' => absurd h' h))

instance : DecidableEq String :=
{decEq := String.decEq}

def List.asString (s : List Char) : String :=
⟨s⟩

namespace String
instance : HasLess String :=
⟨fun s₁ s₂ => s₁.data < s₂.data⟩

@[extern cpp "lean::string_dec_lt"]
instance decLt (s₁ s₂ : @& String) : Decidable (s₁ < s₂) :=
List.hasDecidableLt s₁.data s₂.data

@[extern cpp "lean::string_length"]
def length : (@& String) → Nat
| ⟨s⟩  => s.length

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the String is not shared. -/
@[extern cpp "lean::string_push"]
def push : String → Char → String
| ⟨s⟩, c => ⟨s ++ [c]⟩

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the String is not shared. -/
@[extern cpp "lean::string_append"]
def append : String → (@& String) → String
| ⟨a⟩, ⟨b⟩ => ⟨a ++ b⟩

/- O(n) in the runtime, where n is the length of the String -/
def toList (s : String) : List Char :=
s.data

private def csize (c : Char) : Nat :=
c.utf8Size.toNat

private def utf8ByteSizeAux : List Char → Nat → Nat
| [],    r => r
| c::cs, r => utf8ByteSizeAux cs (r + csize c)

@[extern cpp "lean::string_utf8_byte_size"]
def utf8ByteSize : (@& String) → Nat
| ⟨s⟩ => utf8ByteSizeAux s 0

@[inline] def bsize (s : String) : Nat :=
utf8ByteSize s

@[inline] def toSubstring (s : String) : Substring :=
{str := s, startPos := 0, stopPos := s.bsize}

private def utf8GetAux : List Char → Pos → Pos → Char
| [],    i, p => default Char
| c::cs, i, p => if i = p then c else utf8GetAux cs (i + csize c) p

@[extern cpp "lean::string_utf8_get"]
def get : (@& String) → (@& Pos) → Char
| ⟨s⟩, p => utf8GetAux s 0 p

private def utf8SetAux (c' : Char) : List Char → Pos → Pos → List Char
| [],    i, p => []
| c::cs, i, p =>
  if i = p then (c'::cs) else c::(utf8SetAux cs (i + csize c) p)

@[extern cpp "lean::string_utf8_set"]
def set : String → (@& Pos) → Char → String
| ⟨s⟩, i, c => ⟨utf8SetAux c s 0 i⟩

@[extern cpp "lean::string_utf8_next"]
def next (s : @& String) (p : @& Pos) : Pos :=
let c := get s p;
p + csize c

private def utf8PrevAux : List Char → Pos → Pos → Pos
| [],    i, p => 0
| c::cs, i, p =>
  let cz := csize c;
  let i' := i + cz;
  if i' = p then i else utf8PrevAux cs i' p

@[extern cpp "lean::string_utf8_prev"]
def prev : (@& String) → (@& Pos) → Pos
| ⟨s⟩, p => if p = 0 then 0 else utf8PrevAux s 0 p

def front (s : String) : Char :=
get s 0

def back (s : String) : Char :=
get s (prev s (bsize s))

@[extern cpp "lean::string_utf8_at_end"]
def atEnd : (@& String) → (@& Pos) → Bool
| s, p => p ≥ utf8ByteSize s

/- TODO: remove `partial` keywords after we restore the tactic
  framework and wellfounded recursion support -/

partial def posOfAux (s : String) (c : Char) (stopPos : Pos) : Pos → Pos
| pos =>
  if pos == stopPos then pos
  else if s.get pos == c then pos
       else posOfAux (s.next pos)

@[inline] def posOf (s : String) (c : Char) : Pos :=
posOfAux s c s.bsize 0

partial def revPosOfAux (s : String) (c : Char) : Pos → Option Pos
| pos =>
 if s.get pos == c then some pos
 else if pos == 0 then none
 else revPosOfAux (s.prev pos)

def revPosOf (s : String) (c : Char) : Option Pos :=
if s.bsize == 0 then none
else revPosOfAux s c (s.prev s.bsize)

private def utf8ExtractAux₂ : List Char → Pos → Pos → List Char
| [],    _, _ => []
| c::cs, i, e => if i = e then [] else c :: utf8ExtractAux₂ cs (i + csize c) e

private def utf8ExtractAux₁ : List Char → Pos → Pos → Pos → List Char
| [],        _, _, _ => []
| s@(c::cs), i, b, e => if i = b then utf8ExtractAux₂ s i e else utf8ExtractAux₁ cs (i + csize c) b e

@[extern cpp "lean::string_utf8_extract"]
def extract : (@& String) → (@& Pos) → (@& Pos) → String
| ⟨s⟩, b, e => if b ≥ e then ⟨[]⟩ else ⟨utf8ExtractAux₁ s 0 b e⟩

partial def splitAux (s sep : String) : Pos → Pos → Pos → List String → List String
| b, i, j, r =>
  if s.atEnd i then
    let r := if sep.atEnd j then ""::(s.extract b (i-j))::r else (s.extract b i)::r;
    r.reverse
  else if s.get i == sep.get j then
    let i := s.next i;
    let j := sep.next j;
    if sep.atEnd j then splitAux i i 0 (s.extract b (i-j)::r)
    else splitAux b i j r
  else splitAux b (s.next i) 0 r

def split (s : String) (sep : String := " ") : List String :=
if sep == "" then [s] else splitAux s sep 0 0 0 []

instance : Inhabited String :=
⟨""⟩

instance : HasSizeof String :=
⟨String.length⟩

instance : HasAppend String :=
⟨String.append⟩

def str : String → Char → String := push

def pushn (s : String) (c : Char) (n : Nat) : String :=
n.repeat (fun s => s.push c) s

def isEmpty (s : String) : Bool :=
s.bsize == 0

def join (l : List String) : String :=
l.foldl (fun r s => r ++ s) ""

def singleton (c : Char) : String :=
"".push c

def intercalate (s : String) (ss : List String) : String :=
(List.intercalate s.toList (ss.map toList)).asString

structure Iterator :=
(s : String) (i : Pos)

def mkIterator (s : String) : Iterator :=
⟨s, 0⟩

namespace Iterator
def toString : Iterator → String
| ⟨s, _⟩ => s

def remainingBytes : Iterator → Nat
| ⟨s, i⟩ => s.bsize - i

def pos : Iterator → Pos
| ⟨s, i⟩ => i

def curr : Iterator → Char
| ⟨s, i⟩ => get s i

def next : Iterator → Iterator
| ⟨s, i⟩ => ⟨s, s.next i⟩

def prev : Iterator → Iterator
| ⟨s, i⟩ => ⟨s, s.prev i⟩

def hasNext : Iterator → Bool
| ⟨s, i⟩ => i < utf8ByteSize s

def hasPrev : Iterator → Bool
| ⟨s, i⟩ => i > 0

def setCurr : Iterator → Char → Iterator
| ⟨s, i⟩, c => ⟨s.set i c, i⟩

def toEnd : Iterator → Iterator
| ⟨s, _⟩ => ⟨s, s.bsize⟩

def extract : Iterator → Iterator → String
| ⟨s₁, b⟩, ⟨s₂, e⟩ =>
  if s₁ ≠ s₂ || b > e then ""
  else s₁.extract b e

def forward : Iterator → Nat → Iterator
| it, 0     => it
| it, n+1   => forward it.next n

def remainingToString : Iterator → String
| ⟨s, i⟩ => s.extract i s.bsize

/- (isPrefixOfRemaining it₁ it₂) is `true` Iff `it₁.remainingToString` is a prefix
   of `it₂.remainingToString`. -/
def isPrefixOfRemaining : Iterator → Iterator → Bool
| ⟨s₁, i₁⟩, ⟨s₂, i₂⟩ => s₁.extract i₁ s₁.bsize = s₂.extract i₂ (i₂ + (s₁.bsize - i₁))

def nextn : Iterator → Nat → Iterator
| it, 0     => it
| it, i+1   => nextn it.next i

def prevn : Iterator → Nat → Iterator
| it, 0     => it
| it, i+1   => prevn it.prev i
end Iterator

private partial def lineColumnAux (s : String) : Pos → Nat × Nat → Nat × Nat
| i, r@(line, col) =>
  if atEnd s i then r
  else
    let c := s.get i;
    if c = '\n' then lineColumnAux (s.next i) (line+1, 0)
    else lineColumnAux (s.next i) (line, col+1)

def lineColumn (s : String) (pos : Pos) : Nat × Nat :=
lineColumnAux s 0 (1, 0)

partial def offsetOfPosAux (s : String) (pos : Pos) : Pos → Nat → Nat
| i, offset =>
  if i == pos || s.atEnd i then offset
  else offsetOfPosAux (s.next i) (offset+1)

def offsetOfPos (s : String) (pos : Pos) : Nat :=
offsetOfPosAux s pos 0 0

@[specialize] partial def foldlAux {α : Type u} (f : α → Char → α) (s : String) (stopPos : Pos) : Pos → α → α
| i, a =>
  if i == stopPos then a
  else foldlAux (s.next i) (f a (s.get i))

@[inline] def foldl {α : Type u} (f : α → Char → α) (a : α) (s : String) : α :=
foldlAux f s s.bsize 0 a

@[specialize] partial def foldrAux {α : Type u} (f : Char → α → α) (a : α) (s : String) (stopPos : Pos) : Pos → α
| i =>
  if i == stopPos then a
  else f (s.get i) (foldrAux (s.next i))

@[inline] def foldr {α : Type u} (f : Char → α → α) (a : α) (s : String) : α :=
foldrAux f a s s.bsize 0

@[specialize] partial def anyAux (s : String) (stopPos : Pos) (p : Char → Bool) : Pos → Bool
| i =>
  if i == stopPos then false
  else if p (s.get i) then true
  else anyAux (s.next i)

@[inline] def any (s : String) (p : Char → Bool) : Bool :=
anyAux s s.bsize p 0

@[inline] def all (s : String) (p : Char → Bool) : Bool :=
!s.any (fun c => !p c)

def contains (s : String) (c : Char) : Bool :=
s.any (fun a => a == c)

@[specialize] partial def mapAux (f : Char → Char) : Pos → String → String
| i, s =>
  if s.atEnd i then s
  else
    let c := f (s.get i);
    let s := s.set i c;
    mapAux (s.next i) s

@[inline] def map (f : Char → Char) (s : String) : String :=
mapAux f 0 s

def toNat (s : String) : Nat :=
s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0

def isNat (s : String) : Bool :=
s.all $ fun c => c.isDigit

partial def isPrefixOfAux (p s : String) : Pos → Bool
| i =>
  if p.atEnd i then true
  else
    let c₁ := p.get i;
    let c₂ := s.get i;
    c₁ == c₂ && isPrefixOfAux (s.next i)

/- Return true iff `p` is a prefix of `s` -/
def isPrefixOf (p : String) (s : String) : Bool :=
p.length ≤ s.length && isPrefixOfAux p s 0

end String

namespace Substring

@[inline] def toString : Substring → String
| ⟨s, b, e⟩ => s.extract b e

@[inline] def toIterator : Substring → String.Iterator
| ⟨s, b, _⟩ => ⟨s, b⟩

@[inline] def get : Substring → String.Pos → Char
| ⟨s, b, _⟩, p => s.get (b+p)

@[inline] def next : Substring → String.Pos → String.Pos
| ⟨s, b, e⟩, p =>
  let p := s.next (b+p);
  if p > e then e - b else p - b

@[inline] def prev : Substring → String.Pos → String.Pos
| ⟨s, b, _⟩, p =>
  if p = b then p else s.prev (b+p) - b

@[inline] def front (s : Substring) : Char :=
s.get 0

@[inline] def posOf (s : Substring) (c : Char) : String.Pos :=
match s with
| ⟨s, b, e⟩ => (String.posOfAux s c e b) - b

@[inline] def drop : Substring → Nat → Substring
| ⟨s, b, e⟩, n =>
  if b + n ≥ e then "".toSubstring
  else ⟨s, b+n, e⟩

@[inline] def dropRight : Substring → Nat → Substring
| ⟨s, b, e⟩, n =>
  if e - n ≤ e then "".toSubstring
  else ⟨s, b, e - n⟩

@[inline] def take : Substring → Nat → Substring
| ⟨s, b, e⟩, n =>
  let e := if b + n ≥ e then e else b + n;
  ⟨s, b, e⟩

@[inline] def takeRight : Substring → Nat → Substring
| ⟨s, b, e⟩, n =>
  let b := if e - n ≤ b then b else e - n;
  ⟨s, b, e⟩

@[inline] def atEnd : Substring → String.Pos → Bool
| ⟨s, b, e⟩, p => b + p == e

@[inline] def extract : Substring → String.Pos → String.Pos → Substring
| ⟨s, b, _⟩, b', e' => if b' ≥ e' then ⟨"", 0, 1⟩ else ⟨s, b+b', b+e'⟩

partial def splitAux (s sep : String) (stopPos : String.Pos) : String.Pos → String.Pos → String.Pos → List Substring → List Substring
| b, i, j, r =>
  if i == stopPos then
    let r := if sep.atEnd j then "".toSubstring::{str := s, startPos := b, stopPos := i-j}::r else {str := s, startPos := b, stopPos := i}::r;
    r.reverse
  else if s.get i == sep.get j then
    let i := s.next i;
    let j := sep.next j;
    if sep.atEnd j then splitAux i i 0 ({str := s, startPos := b, stopPos := i-j}::r)
    else splitAux b i j r
  else splitAux b (s.next i) 0 r

def split (s : Substring) (sep : String := " ") : List Substring :=
if sep == "" then [s] else splitAux s.str sep s.stopPos s.startPos s.startPos 0 []

@[inline] def foldl {α : Type u} (f : α → Char → α) (a : α) (s : Substring) : α :=
match s with
| ⟨s, b, e⟩ => String.foldlAux f s e b a

@[inline] def foldr {α : Type u} (f : Char → α → α) (a : α) (s : Substring) : α :=
match s with
| ⟨s, b, e⟩ => String.foldrAux f a s e b

@[inline] def any (s : Substring) (p : Char → Bool) : Bool :=
match s with
| ⟨s, b, e⟩ => String.anyAux s e p b

@[inline] def all (s : Substring) (p : Char → Bool) : Bool :=
!s.any (fun c => !p c)

def contains (s : Substring) (c : Char) : Bool :=
s.any (fun a => a == c)

@[specialize] partial def takeWhileAux (s : String) (stopPos : String.Pos) (p : Char → Bool) : String.Pos → String.Pos
| i =>
  if i == stopPos then i
  else if p (s.get i) then takeWhileAux (s.next i)
  else i

@[inline] def takeWhile : Substring → (Char → Bool) → Substring
| ⟨s, b, e⟩, p =>
  let e := takeWhileAux s e p b;
  ⟨s, b, e⟩

@[inline] def dropWhile : Substring → (Char → Bool) → Substring
| ⟨s, b, e⟩, p =>
  let b := takeWhileAux s e p b;
  ⟨s, b, e⟩

@[specialize] partial def takeRightWhileAux (s : String) (begPos : String.Pos) (p : Char → Bool) : String.Pos → String.Pos
| i =>
  if i == begPos then i
  else
    let i' := s.prev i;
    let c  := s.get i';
    if !p c then i
    else takeRightWhileAux i'

@[inline] def takeRightWhile : Substring → (Char → Bool) → Substring
| ⟨s, b, e⟩, p =>
  let b := takeRightWhileAux s b p e;
  ⟨s, b, e⟩

@[inline] def dropRightWhile : Substring → (Char → Bool) → Substring
| ⟨s, b, e⟩, p =>
  let e := takeRightWhileAux s b p e;
  ⟨s, b, e⟩

@[inline] def trimLeft (s : Substring) : Substring :=
s.dropWhile Char.isWhitespace

@[inline] def trimRight (s : Substring) : Substring :=
s.dropRightWhile Char.isWhitespace

@[inline] def trim : Substring → Substring
| ⟨s, b, e⟩ =>
  let b := takeWhileAux s e Char.isWhitespace b;
  let e := takeRightWhileAux s b Char.isWhitespace e;
  ⟨s, b, e⟩

def toNat (s : Substring) : Nat :=
s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0

def isNat (s : Substring) : Bool :=
s.all $ fun c => c.isDigit

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

def trimRight (s : String) : String :=
s.toSubstring.trimRight.toString

def trimLeft (s : String) : String :=
s.toSubstring.trimLeft.toString

def trim (s : String) : String :=
s.toSubstring.trim.toString

end String

protected def Char.toString (c : Char) : String :=
String.singleton c
