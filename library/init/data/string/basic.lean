/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic
import init.data.char.basic
import init.data.option.basic

/- In the VM, strings are implemented using a dynamic Array and UTF-8 encoding.
   TODO: mark as opaque -/
structure String :=
(data : List Char)

attribute [extern cpp "lean::string_mk"] String.mk
attribute [extern cpp "lean::string_data"] String.data

@[extern cpp "lean::string_dec_eq"]
def String.decEq (s₁ s₂ : @& String) : Decidable (s₁ = s₂) :=
match s₁, s₂ with
| ⟨s₁⟩, ⟨s₂⟩ :=
 if h : s₁ = s₂ then isTrue (congrArg _ h)
 else isFalse (λ h', String.noConfusion h' (λ h', absurd h' h))

instance : DecidableEq String :=
{decEq := String.decEq}

def List.asString (s : List Char) : String :=
⟨s⟩

namespace String
instance : HasLt String :=
⟨λ s₁ s₂, s₁.data < s₂.data⟩

/- Remark: this Function has a VM builtin efficient implementation. -/
@[extern cpp "lean::string_dec_lt"]
instance decLt (s₁ s₂ : @& String) : Decidable (s₁ < s₂) :=
List.hasDecidableLt s₁.data s₂.data

@[extern cpp "lean::string_length"]
def length : (@& String) → Nat
| ⟨s⟩  := s.length

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the String is not shared. -/
@[extern cpp "lean::string_push"]
def push : String → Char → String
| ⟨s⟩ c := ⟨s ++ [c]⟩

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the String is not shared. -/
@[extern cpp "lean::string_append"]
def append : String → (@& String) → String
| ⟨a⟩ ⟨b⟩ := ⟨a ++ b⟩

/- O(n) in the runtime, where n is the length of the String -/
def toList (s : String) : List Char :=
s.data

private def csize (c : Char) : USize :=
USize.ofUInt32 c.utf8Size

private def utf8ByteSizeAux : List Char → USize → USize
| []      r := r
| (c::cs) r := utf8ByteSizeAux cs (r + csize c)

@[extern cpp "lean::string_utf8_byte_size"]
def utf8ByteSize : (@& String) → USize
| ⟨s⟩ := utf8ByteSizeAux s 0

@[inline] def bsize (s : String) : USize :=
utf8ByteSize s

abbrev utf8Pos := USize

def utf8Begin : utf8Pos := 0

private def utf8GetAux : List Char → USize → USize → Char
| []      i p := default Char
| (c::cs) i p := if i = p then c else utf8GetAux cs (i + csize c) p

@[extern cpp "lean::string_utf8_get"]
def utf8Get : (@& String) → utf8Pos → Char
| ⟨s⟩ p := utf8GetAux s 0 p

private def utf8SetAux (c' : Char) : List Char → USize → USize → List Char
| []      i p := []
| (c::cs) i p :=
  if i = p then (c'::cs) else c::(utf8SetAux cs (i + csize c) p)

@[extern cpp "lean::string_utf8_set"]
def utf8Set : String → utf8Pos → Char → String
| ⟨s⟩ i c := ⟨utf8SetAux c s 0 i⟩

@[extern cpp "lean::string_utf8_next"]
def utf8Next (s : @& String) (p : utf8Pos) : utf8Pos :=
let c := utf8Get s p in
p + csize c

private def utf8PrevAux : List Char → USize → USize → USize
| []      i p := 0
| (c::cs) i p :=
  let cz := csize c in
  let i' := i + cz in
  if i' = p then i else utf8PrevAux cs i' p

@[extern cpp "lean::string_utf8_prev"]
def utf8Prev : (@& String) → utf8Pos → utf8Pos
| ⟨s⟩ p := if p = 0 then 0 else utf8PrevAux s 0 p

def front (s : String) : Char :=
utf8Get s 0

def back (s : String) : Char :=
utf8Get s (utf8Prev s (bsize s))

@[extern cpp "lean::string_utf8_at_end"]
def utf8AtEnd : (@& String) → utf8Pos → Bool
| s p := p ≥ utf8ByteSize s

private def utf8ExtractAux₂ : List Char → USize → USize → List Char
| []      _ _ := []
| (c::cs) i e := if i = e then [] else c :: utf8ExtractAux₂ cs (i + csize c) e

private def utf8ExtractAux₁ : List Char → USize → USize → USize → List Char
| []        _ _ _ := []
| s@(c::cs) i b e := if i = b then utf8ExtractAux₂ s i e else utf8ExtractAux₁ cs (i + csize c) b e

@[extern cpp "lean::string_utf8_extract"]
def extract : (@& String) → utf8Pos → utf8Pos → String
| ⟨s⟩ b e := if b ≥ e then ⟨[]⟩ else ⟨utf8ExtractAux₁ s 0 b e⟩

def trimLeftAux (s : String) : Nat → utf8Pos → utf8Pos
| 0     i := i
| (n+1) i :=
  if i ≥ s.bsize then i
  else let c := s.utf8Get i in
       if !c.isWhitespace then i
       else trimLeftAux n (i + csize c)

def trimLeft (s : String) : String :=
let b := trimLeftAux s s.bsize.toNat 0 in
if b = 0 then s
else s.extract b s.bsize

def trimRightAux (s : String) : Nat → utf8Pos → utf8Pos
| 0     i := i
| (n+1) i :=
  if i = 0 then i
  else
    let i' := s.utf8Prev i in
    let c  := s.utf8Get i' in
    if !c.isWhitespace then i
    else trimRightAux n i'

def trimRight (s : String) : String :=
let e := trimRightAux s s.bsize.toNat s.bsize in
if e = s.bsize then s
else s.extract 0 e

def trim (s : String) : String :=
let b := trimLeftAux s s.bsize.toNat 0 in
let e := trimRightAux s s.bsize.toNat s.bsize in
if b = 0 && e = s.bsize then s
else s.extract b e

structure Iterator :=
(s : String) (offset : Nat) (i : USize)

def mkIterator (s : String) : Iterator :=
⟨s, 0, 0⟩

namespace Iterator
def remaining : Iterator → Nat
| ⟨s, o, _⟩ := s.length - o

def toString : Iterator → String
| ⟨s, _, _⟩ := s

def remainingBytes : Iterator → USize
| ⟨s, _, i⟩ := s.bsize - i

def curr : Iterator → Char
| ⟨s, _, i⟩ := utf8Get s i

def next : Iterator → Iterator
| ⟨s, o, i⟩ := ⟨s, o+1, utf8Next s i⟩

def prev : Iterator → Iterator
| ⟨s, o, i⟩ := ⟨s, o-1, utf8Prev s i⟩

def hasNext : Iterator → Bool
| ⟨s, _, i⟩ := i < utf8ByteSize s

def hasPrev : Iterator → Bool
| ⟨s, _, i⟩ := i > 0

def setCurr : Iterator → Char → Iterator
| ⟨s, o, i⟩ c := ⟨utf8Set s i c, o, i⟩

def toEnd : Iterator → Iterator
| ⟨s, o, _⟩ := ⟨s, s.length, s.bsize⟩

def extract : Iterator → Iterator → String
| ⟨s₁, _, b⟩ ⟨s₂, _, e⟩ :=
  if s₁ ≠ s₂ || b > e then ""
  else s₁.extract b e

def forward : Iterator → Nat → Iterator
| it 0     := it
| it (n+1) := forward it.next n

def remainingToString : Iterator → String
| ⟨s, _, i⟩ := s.extract i s.bsize

/- (isPrefixOfRemaining it₁ it₂) is `true` Iff `it₁.remainingToString` is a prefix
   of `it₂.remainingToString`. -/
def isPrefixOfRemaining : Iterator → Iterator → Bool
| ⟨s₁, _, i₁⟩ ⟨s₂, _, i₂⟩ := s₁.extract i₁ s₁.bsize = s₂.extract i₂ (i₂ + (s₁.bsize - i₁))

end Iterator
end String

/- The following definitions do not have builtin support in the VM -/

instance : Inhabited String :=
⟨""⟩

instance : HasSizeof String :=
⟨String.length⟩

instance : HasAppend String :=
⟨String.append⟩

namespace String
def str : String → Char → String := push

def pushn (s : String) (c : Char) (n : Nat) : String :=
n.repeat (λ _ s, s.push c) s

def isEmpty (s : String) : Bool :=
toBool (s.length = 0)

def join (l : List String) : String :=
l.foldl (λ r s, r ++ s) ""

def singleton (c : Char) : String :=
"".push c

def intercalate (s : String) (ss : List String) : String :=
(List.intercalate s.toList (ss.map toList)).asString

namespace Iterator
def nextn : Iterator → Nat → Iterator
| it 0     := it
| it (i+1) := nextn it.next i

def prevn : Iterator → Nat → Iterator
| it 0     := it
| it (i+1) := prevn it.prev i
end Iterator

private def lineColumnAux : Nat → String.Iterator → Nat × Nat → Nat × Nat
| 0     it r           := r
| (k+1) it r@(line, col) :=
  if it.hasNext = false then r
  else match it.curr with
       | '\n'  := lineColumnAux k it.next (line+1, 0)
       | other := lineColumnAux k it.next (line, col+1)

def lineColumn (s : String) (offset : Nat) : Nat × Nat :=
lineColumnAux offset s.mkIterator (1, 0)
end String

protected def Char.toString (c : Char) : String :=
String.singleton c

private def toNatCore : String.Iterator → Nat → Nat → Nat
| it      0     r := r
| it      (i+1) r :=
  let c := it.curr in
  let r := r*10 + c.toNat - '0'.toNat in
  toNatCore it.next i r

def String.toNat (s : String) : Nat :=
toNatCore s.mkIterator s.length 0
