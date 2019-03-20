/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic
import init.data.char.basic
import init.data.option.basic

/- In the VM, strings are implemented using a dynamic array and UTF-8 encoding.
   TODO: mark as opaque -/
structure string :=
(data : list char)

attribute [extern cpp "lean::stringMk"] string.mk
attribute [extern cpp "lean::stringData"] string.data

@[extern cpp "lean::stringDecEq"]
def string.decEq (s₁ s₂ : @& string) : decidable (s₁ = s₂) :=
match s₁, s₂ with
| ⟨s₁⟩, ⟨s₂⟩ :=
 if h : s₁ = s₂ then isTrue (congrArg _ h)
 else isFalse (λ h', string.noConfusion h' (λ h', absurd h' h))

instance : decidableEq string :=
{decEq := string.decEq}

def list.asString (s : list char) : string :=
⟨s⟩

namespace string
instance : hasLt string :=
⟨λ s₁ s₂, s₁.data < s₂.data⟩

/- Remark: this function has a VM builtin efficient implementation. -/
@[extern cpp "lean::stringDecLt"]
instance decLt (s₁ s₂ : @& string) : decidable (s₁ < s₂) :=
list.hasDecidableLt s₁.data s₂.data

@[extern cpp "lean::stringLength"]
def length : (@& string) → nat
| ⟨s⟩  := s.length

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/
@[extern cpp "lean::stringPush"]
def push : string → char → string
| ⟨s⟩ c := ⟨s ++ [c]⟩

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/
@[extern cpp "lean::stringAppend"]
def append : string → (@& string) → string
| ⟨a⟩ ⟨b⟩ := ⟨a ++ b⟩

/- O(n) in the runtime, where n is the length of the string -/
def toList (s : string) : list char :=
s.data

private def csize (c : char) : usize :=
usize.ofUint32 c.utf8Size

private def utf8ByteSizeAux : list char → usize → usize
| []      r := r
| (c::cs) r := utf8ByteSizeAux cs (r + csize c)

@[extern cpp "lean::stringUtf8ByteSize"]
def utf8ByteSize : (@& string) → usize
| ⟨s⟩ := utf8ByteSizeAux s 0

@[inline] def bsize (s : string) : usize :=
utf8ByteSize s

abbrev utf8Pos := usize

def utf8Begin : utf8Pos := 0

private def utf8GetAux : list char → usize → usize → char
| []      i p := default char
| (c::cs) i p := if i = p then c else utf8GetAux cs (i + csize c) p

@[extern cpp "lean::stringUtf8Get"]
def utf8Get : (@& string) → utf8Pos → char
| ⟨s⟩ p := utf8GetAux s 0 p

private def utf8SetAux (c' : char) : list char → usize → usize → list char
| []      i p := []
| (c::cs) i p :=
  if i = p then (c'::cs) else c::(utf8SetAux cs (i + csize c) p)

@[extern cpp "lean::stringUtf8Set"]
def utf8Set : string → utf8Pos → char → string
| ⟨s⟩ i c := ⟨utf8SetAux c s 0 i⟩

@[extern cpp "lean::stringUtf8Next"]
def utf8Next (s : @& string) (p : utf8Pos) : utf8Pos :=
let c := utf8Get s p in
p + csize c

private def utf8PrevAux : list char → usize → usize → usize
| []      i p := 0
| (c::cs) i p :=
  let cz := csize c in
  let i' := i + cz in
  if i' = p then i else utf8PrevAux cs i' p

@[extern cpp "lean::stringUtf8Prev"]
def utf8Prev : (@& string) → utf8Pos → utf8Pos
| ⟨s⟩ p := if p = 0 then 0 else utf8PrevAux s 0 p

def front (s : string) : char :=
utf8Get s 0

def back (s : string) : char :=
utf8Get s (utf8Prev s (bsize s))

@[extern cpp "lean::stringUtf8AtEnd"]
def utf8AtEnd : (@& string) → utf8Pos → bool
| s p := p ≥ utf8ByteSize s

private def utf8ExtractAux₂ : list char → usize → usize → list char
| []      _ _ := []
| (c::cs) i e := if i = e then [] else c :: utf8ExtractAux₂ cs (i + csize c) e

private def utf8ExtractAux₁ : list char → usize → usize → usize → list char
| []        _ _ _ := []
| s@(c::cs) i b e := if i = b then utf8ExtractAux₂ s i e else utf8ExtractAux₁ cs (i + csize c) b e

@[extern cpp "lean::stringUtf8Extract"]
def extract : (@& string) → utf8Pos → utf8Pos → string
| ⟨s⟩ b e := if b ≥ e then ⟨[]⟩ else ⟨utf8ExtractAux₁ s 0 b e⟩

def trimLeftAux (s : string) : nat → utf8Pos → utf8Pos
| 0     i := i
| (n+1) i :=
  if i ≥ s.bsize then i
  else let c := s.utf8Get i in
       if !c.isWhitespace then i
       else trimLeftAux n (i + csize c)

def trimLeft (s : string) : string :=
let b := trimLeftAux s s.bsize.toNat 0 in
if b = 0 then s
else s.extract b s.bsize

def trimRightAux (s : string) : nat → utf8Pos → utf8Pos
| 0     i := i
| (n+1) i :=
  if i = 0 then i
  else
    let i' := s.utf8Prev i in
    let c  := s.utf8Get i' in
    if !c.isWhitespace then i
    else trimRightAux n i'

def trimRight (s : string) : string :=
let e := trimRightAux s s.bsize.toNat s.bsize in
if e = s.bsize then s
else s.extract 0 e

def trim (s : string) : string :=
let b := trimLeftAux s s.bsize.toNat 0 in
let e := trimRightAux s s.bsize.toNat s.bsize in
if b = 0 && e = s.bsize then s
else s.extract b e

structure iterator :=
(s : string) (offset : nat) (i : usize)

def mkIterator (s : string) : iterator :=
⟨s, 0, 0⟩

namespace iterator
def remaining : iterator → nat
| ⟨s, o, _⟩ := s.length - o

def toString : iterator → string
| ⟨s, _, _⟩ := s

def remainingBytes : iterator → usize
| ⟨s, _, i⟩ := s.bsize - i

def curr : iterator → char
| ⟨s, _, i⟩ := utf8Get s i

def next : iterator → iterator
| ⟨s, o, i⟩ := ⟨s, o+1, utf8Next s i⟩

def prev : iterator → iterator
| ⟨s, o, i⟩ := ⟨s, o-1, utf8Prev s i⟩

def hasNext : iterator → bool
| ⟨s, _, i⟩ := i < utf8ByteSize s

def hasPrev : iterator → bool
| ⟨s, _, i⟩ := i > 0

def setCurr : iterator → char → iterator
| ⟨s, o, i⟩ c := ⟨utf8Set s i c, o, i⟩

def toEnd : iterator → iterator
| ⟨s, o, _⟩ := ⟨s, s.length, s.bsize⟩

def extract : iterator → iterator → string
| ⟨s₁, _, b⟩ ⟨s₂, _, e⟩ :=
  if s₁ ≠ s₂ || b > e then ""
  else s₁.extract b e

def forward : iterator → nat → iterator
| it 0     := it
| it (n+1) := forward it.next n

def remainingToString : iterator → string
| ⟨s, _, i⟩ := s.extract i s.bsize

/- (isPrefixOfRemaining it₁ it₂) is `tt` iff `it₁.remainingToString` is a prefix
   of `it₂.remainingToString`. -/
def isPrefixOfRemaining : iterator → iterator → bool
| ⟨s₁, _, i₁⟩ ⟨s₂, _, i₂⟩ := s₁.extract i₁ s₁.bsize = s₂.extract i₂ (i₂ + (s₁.bsize - i₁))

end iterator
end string

/- The following definitions do not have builtin support in the VM -/

instance : inhabited string :=
⟨""⟩

instance : hasSizeof string :=
⟨string.length⟩

instance : hasAppend string :=
⟨string.append⟩

namespace string
def str : string → char → string := push

def pushn (s : string) (c : char) (n : nat) : string :=
n.repeat (λ _ s, s.push c) s

def isEmpty (s : string) : bool :=
toBool (s.length = 0)

def join (l : list string) : string :=
l.foldl (λ r s, r ++ s) ""

def singleton (c : char) : string :=
"".push c

def intercalate (s : string) (ss : list string) : string :=
(list.intercalate s.toList (ss.map toList)).asString

namespace iterator
def nextn : iterator → nat → iterator
| it 0     := it
| it (i+1) := nextn it.next i

def prevn : iterator → nat → iterator
| it 0     := it
| it (i+1) := prevn it.prev i
end iterator

private def lineColumnAux : nat → string.iterator → nat × nat → nat × nat
| 0     it r           := r
| (k+1) it r@(line, col) :=
  if it.hasNext = ff then r
  else match it.curr with
       | '\n'  := lineColumnAux k it.next (line+1, 0)
       | other := lineColumnAux k it.next (line, col+1)

def lineColumn (s : string) (offset : nat) : nat × nat :=
lineColumnAux offset s.mkIterator (1, 0)
end string

protected def char.toString (c : char) : string :=
string.singleton c

private def toNatCore : string.iterator → nat → nat → nat
| it      0     r := r
| it      (i+1) r :=
  let c := it.curr in
  let r := r*10 + c.toNat - '0'.toNat in
  toNatCore it.next i r

def string.toNat (s : string) : nat :=
toNatCore s.mkIterator s.length 0
