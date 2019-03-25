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
instance : HasLess String :=
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

abbrev Pos := USize

private def utf8GetAux : List Char → USize → USize → Char
| []      i p := default Char
| (c::cs) i p := if i = p then c else utf8GetAux cs (i + csize c) p

@[extern cpp "lean::string_utf8_get"]
def get : (@& String) → Pos → Char
| ⟨s⟩ p := utf8GetAux s 0 p

private def utf8SetAux (c' : Char) : List Char → USize → USize → List Char
| []      i p := []
| (c::cs) i p :=
  if i = p then (c'::cs) else c::(utf8SetAux cs (i + csize c) p)

@[extern cpp "lean::string_utf8_set"]
def set : String → Pos → Char → String
| ⟨s⟩ i c := ⟨utf8SetAux c s 0 i⟩

@[extern cpp "lean::string_utf8_next"]
def next (s : @& String) (p : Pos) : Pos :=
let c := get s p in
p + csize c

private def utf8PrevAux : List Char → USize → USize → USize
| []      i p := 0
| (c::cs) i p :=
  let cz := csize c in
  let i' := i + cz in
  if i' = p then i else utf8PrevAux cs i' p

@[extern cpp "lean::string_utf8_prev"]
def prev : (@& String) → Pos → Pos
| ⟨s⟩ p := if p = 0 then 0 else utf8PrevAux s 0 p

def front (s : String) : Char :=
get s 0

def back (s : String) : Char :=
get s (prev s (bsize s))

@[extern cpp "lean::string_utf8_at_end"]
def atEnd : (@& String) → Pos → Bool
| s p := p ≥ utf8ByteSize s

private def utf8ExtractAux₂ : List Char → USize → USize → List Char
| []      _ _ := []
| (c::cs) i e := if i = e then [] else c :: utf8ExtractAux₂ cs (i + csize c) e

private def utf8ExtractAux₁ : List Char → USize → USize → USize → List Char
| []        _ _ _ := []
| s@(c::cs) i b e := if i = b then utf8ExtractAux₂ s i e else utf8ExtractAux₁ cs (i + csize c) b e

@[extern cpp "lean::string_utf8_extract"]
def extract : (@& String) → Pos → Pos → String
| ⟨s⟩ b e := if b ≥ e then ⟨[]⟩ else ⟨utf8ExtractAux₁ s 0 b e⟩

def trimLeftAux (s : String) : Nat → Pos → Pos
| 0     i := i
| (n+1) i :=
  if i ≥ s.bsize then i
  else let c := s.get i in
       if !c.isWhitespace then i
       else trimLeftAux n (i + csize c)

def trimLeft (s : String) : String :=
let b := trimLeftAux s s.bsize.toNat 0 in
if b = 0 then s
else s.extract b s.bsize

def trimRightAux (s : String) : Nat → Pos → Pos
| 0     i := i
| (n+1) i :=
  if i = 0 then i
  else
    let i' := s.prev i in
    let c  := s.get i' in
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

def splitAux (s sep : String) : Nat → Pos → Pos → Pos → List String → List String
| 0     b i j r := [] -- unreachable
| (k+1) b i j r :=
  if s.atEnd i then
    let r := if sep.atEnd j then ""::(s.extract b (i-j))::r else (s.extract b i)::r
    in r.reverse
  else if s.get i == sep.get j then
    let i := s.next i in
    let j := sep.next j in
    if sep.atEnd j then splitAux k i i 0 (s.extract b (i-j)::r)
    else splitAux k b i j r
  else splitAux k b (s.next i) 0 r

def split (s : String) (sep : String := " ") : List String :=
if sep == "" then [s] else splitAux s sep (s.length+1) 0 0 0 []

structure Iterator :=
(s : String) (i : USize)

def mkIterator (s : String) : Iterator :=
⟨s, 0⟩

namespace Iterator
def toString : Iterator → String
| ⟨s, _⟩ := s

def remainingBytes : Iterator → Nat
| ⟨s, i⟩ := (s.bsize - i).toNat

def pos : Iterator → Pos
| ⟨s, i⟩ := i

def curr : Iterator → Char
| ⟨s, i⟩ := get s i

def next : Iterator → Iterator
| ⟨s, i⟩ := ⟨s, s.next i⟩

def prev : Iterator → Iterator
| ⟨s, i⟩ := ⟨s, s.prev i⟩

def hasNext : Iterator → Bool
| ⟨s, i⟩ := i < utf8ByteSize s

def hasPrev : Iterator → Bool
| ⟨s, i⟩ := i > 0

def setCurr : Iterator → Char → Iterator
| ⟨s, i⟩ c := ⟨s.set i c, i⟩

def toEnd : Iterator → Iterator
| ⟨s, _⟩ := ⟨s, s.bsize⟩

def extract : Iterator → Iterator → String
| ⟨s₁, b⟩ ⟨s₂, e⟩ :=
  if s₁ ≠ s₂ || b > e then ""
  else s₁.extract b e

def forward : Iterator → Nat → Iterator
| it 0     := it
| it (n+1) := forward it.next n

def remainingToString : Iterator → String
| ⟨s, i⟩ := s.extract i s.bsize

/- (isPrefixOfRemaining it₁ it₂) is `true` Iff `it₁.remainingToString` is a prefix
   of `it₂.remainingToString`. -/
def isPrefixOfRemaining : Iterator → Iterator → Bool
| ⟨s₁, i₁⟩ ⟨s₂, i₂⟩ := s₁.extract i₁ s₁.bsize = s₂.extract i₂ (i₂ + (s₁.bsize - i₁))

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

private def lineColumnAux (s : String) : Nat → Pos → Nat × Nat → Nat × Nat
| 0     i r            := r
| (k+1) i r@(line, col) :=
  if atEnd s i then r
  else let c := s.get i in
       if c = '\n' then lineColumnAux k (s.next i) (line+1, 0)
       else lineColumnAux k (s.next i) (line, col+1)

def lineColumn (s : String) (pos : Pos) : Nat × Nat :=
lineColumnAux s s.length 0 (1, 0)

def offsetOfPosAux (s : String) (pos : Pos) : Nat → Pos → Nat → Nat
| 0     _ offset := offset
| (k+1) i offset :=
  if i == pos || s.atEnd i then offset
  else offsetOfPosAux k (s.next i) (offset+1)

def offsetOfPos (s : String) (pos : Pos) : Nat :=
offsetOfPosAux s pos s.length 0 0

end String

protected def Char.toString (c : Char) : String :=
String.singleton c

namespace String
universes u
@[specialize] def foldlAux {α : Type u} (f : α → Char → α) (s : String) : Nat → Pos → α → α
| 0     _ a := a
| (k+1) i a :=
  if s.atEnd i then a
  else foldlAux k (s.next i) (f a (s.get i))

@[inline] def foldl {α : Type u} (f : α → Char → α) (a : α) (s : String) (start : Pos := 0) : α :=
foldlAux f s s.length 0 a

@[specialize] def foldrAux {α : Type u} (f : Char → α → α) (a : α) (s : String) : Nat → Pos → α
| 0     i := a
| (k+1) i :=
  if s.atEnd i then a
  else f (s.get i) (foldrAux k (s.next i))

@[inline] def foldr {α : Type u} (f : Char → α → α) (a : α) (s : String) (start : Pos := 0) : α :=
foldrAux f a s s.length start

@[inline] def any (s : String) (p : Char → Bool) (start : Pos := 0) : Bool :=
s.foldr (λ a r, p a || r) false start

@[inline] def all (s : String) (p : Char → Bool) (start : Pos := 0) : Bool :=
s.foldr (λ a r, p a && r) true start

def toNat (s : String) : Nat :=
s.foldl (λ n c, n*10 + (c.toNat - '0'.toNat)) 0

def isNat (s : String) : Bool :=
s.all $ λ c, c.isDigit

end String
