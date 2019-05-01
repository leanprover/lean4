/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic init.data.fin.basic init.data.uint
import init.data.repr init.data.tostring init.control.id
universes u v w

/-
The Compiler has special support for arrays.
They are implemented using dynamic arrays: https://en.wikipedia.org/wiki/Dynamic_array
-/
structure Array (α : Type u) :=
(sz   : Nat)
(data : Fin sz → α)

attribute [extern cpp inline "lean::array_sz(#2)"] Array.sz

@[reducible, extern cpp inline "lean::array_get_size(#2)"]
def Array.size {α : Type u} (a : @& Array α) : Nat :=
a.sz

namespace Array
variables {α : Type u} {β : Type v}

/- The parameter `c` is the initial capacity -/
@[extern cpp inline "lean::mk_empty_array(#2)"]
def mkEmpty (c : @& Nat) : Array α :=
{ sz := 0,
  data := λ ⟨x, h⟩, absurd h (Nat.notLtZero x) }

@[extern cpp inline "lean::array_push(#2, #3)"]
def push (a : Array α) (v : α) : Array α :=
{ sz   := Nat.succ a.sz,
  data := λ ⟨j, h₁⟩,
    if h₂ : j = a.sz then v
    else a.data ⟨j, Nat.ltOfLeOfNe (Nat.leOfLtSucc h₁) h₂⟩ }

@[extern cpp inline "lean::mk_array(#2, #3)"]
def mkArray {α : Type u} (n : Nat) (v : α) : Array α :=
{ sz   := n,
  data := λ _, v}

theorem szMkArrayEq {α : Type u} (n : Nat) (v : α) : (mkArray n v).sz = n :=
rfl

def empty : Array α :=
mkEmpty 0

instance : HasEmptyc (Array α) :=
⟨Array.empty⟩

instance : Inhabited (Array α) :=
⟨Array.empty⟩

def isEmpty (a : Array α) : Bool :=
a.size = 0

def singleton (v : α) : Array α :=
mkArray 1 v

@[extern cpp inline "lean::array_index(#2, #3)"]
def index (a : @& Array α) (i : @& Fin a.size) : α :=
a.data i

/- Low-level version of `index` which is as fast as a C array read.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `index` may be slightly slower than `idx`. -/
@[extern cpp inline "lean::array_idx(#2, #3)"]
def idx (a : @& Array α) (i : USize) (h : i.toNat < a.size) : α :=
a.index ⟨i.toNat, h⟩

/- "Comfortable" version of `index`. It performs a bound check at runtime. -/
@[extern cpp inline "lean::array_get(#2, #3, #4)"]
def get [Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
if h : i < a.size then a.index ⟨i, h⟩ else default α

def back [Inhabited α] (a : Array α) : α :=
a.get (a.size - 1)

def getOpt (a : Array α) (i : Nat) : Option α :=
if h : i < a.size then some (a.index ⟨i, h⟩) else none

@[extern cpp inline "lean::array_update(#2, #3, #4)"]
def update (a : Array α) (i : @& Fin a.size) (v : α) : Array α :=
{ sz   := a.sz,
  data := λ j, if h : i = j then v else a.data j }

/- Low-level version of `update` which is as fast as a C array update.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `update` may be slightly slower than `updt`. -/
@[extern cpp inline "lean::array_updt(#2, #3, #4)"]
def updt (a : Array α) (i : USize) (v : α) (h : i.toNat < a.size) : Array α :=
a.update ⟨i.toNat, h⟩ v

/- "Comfortable" version of `update`. It performs a bound check at runtime. -/
@[extern cpp inline "lean::array_set(#2, #3, #4)"]
def set (a : Array α) (i : @& Nat) (v : α) : Array α :=
if h : i < a.size then a.update ⟨i, h⟩ v else a

@[extern cpp inline "lean::array_fswap(#2, #3, #4)"]
def fswap (a : Array α) (i j : @& Fin a.size) : Array α :=
let v₁ := a.index i in
let v₂ := a.index j in
let a  := a.update i v₂ in
a.update j v₁

@[extern cpp inline "lean::array_swap(#2, #3, #4)"]
def swap (a : Array α) (i j : @& Nat) : Array α :=
if h₁ : i < a.size then
if h₂ : j < a.size then fswap a ⟨i, h₁⟩ ⟨j, h₂⟩
else a
else a

theorem szUpdateEq (a : Array α) (i : Fin a.size) (v : α) : (update a i v).size = a.size :=
rfl

@[extern cpp inline "lean::array_pop(#2)"]
def pop (a : Array α) : Array α :=
{ sz   := Nat.pred a.size,
  data := λ ⟨j, h⟩, a.index ⟨j, Nat.ltOfLtOfLe h (Nat.predLe _)⟩ }

-- TODO(Leo): justify termination using wf-rec
partial def shrink : Array α → Nat → Array α
| a n := if n ≥ a.size then a else shrink a.pop n

section
variables {m : Type v → Type v} [Monad m]
local attribute [instance] monadInhabited'

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def miterateAux (a : Array α) (f : Π i : Fin a.size, α → β → m β) : Nat → β → m β
| i b :=
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩ in
     f idx (a.index idx) b >>= miterateAux (i+1)
  else pure b

@[inline] def miterate (a : Array α) (b : β) (f : Π i : Fin a.size, α → β → m β) : m β :=
miterateAux a f 0 b

@[inline] def mfoldl (a : Array α) (b : β) (f : β → α → m β) : m β :=
miterate a b (λ _ b a, f a b)

@[inline] def mfoldlFrom (a : Array α) (b : β) (f : β → α → m β) (ini : Nat := 0) : m β :=
miterateAux a (λ _ b a, f a b) ini b

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def miterate₂Aux (a₁ a₂ : Array α) (f : Π i : Fin a₁.size, α → α → β → m β) : Nat → β → m β
| i b :=
  if h₁ : i < a₁.size then
     let idx₁ : Fin a₁.size := ⟨i, h₁⟩ in
     if h₂ : i < a₂.size then
       let idx₂ : Fin a₂.size := ⟨i, h₂⟩ in
       f idx₁ (a₁.index idx₁) (a₂.index idx₂) b >>= miterate₂Aux (i+1)
     else pure b
  else pure b

@[inline] def miterate₂ (a₁ a₂ : Array α) (b : β) (f : Π i : Fin a₁.size, α → α → β → m β) : m β :=
miterate₂Aux a₁ a₂ f 0 b

@[inline] def mfoldl₂ (a₁ a₂ : Array α) (b : β) (f : β → α → α → m β) : m β :=
miterate₂ a₁ a₂ b (λ _ a₁ a₂ b, f b a₁ a₂)

local attribute [instance] monadInhabited

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def mfindAux (a : Array α) (f : α → m (Option β)) : Nat → m (Option β)
| i :=
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩ in
     do r ← f (a.index idx),
        (match r with
         | some v := pure r
         | none   := mfindAux (i+1))
  else pure none

@[inline] def mfind (a : Array α) (f : α → m (Option β)) : m (Option β) :=
mfindAux a f 0

end

@[inline] def iterate (a : Array α) (b : β) (f : Π i : Fin a.size, α → β → β) : β :=
Id.run $ miterateAux a f 0 b

@[inline] def foldl (a : Array α) (f : β → α → β) (b : β) : β :=
iterate a b (λ _ a b, f b a)

@[inline] def foldlFrom (a : Array α) (f : β → α → β) (b : β) (ini : Nat := 0) : β :=
Id.run $ mfoldlFrom a b f ini

@[inline] def iterate₂ (a₁ a₂ : Array α) (b : β) (f : Π i : Fin a₁.size, α → α → β → β) : β :=
Id.run $ miterate₂Aux a₁ a₂ f 0 b

@[inline] def foldl₂ (a₁ a₂ : Array α) (f : β → α → α → β) (b : β) : β :=
iterate₂ a₁ a₂ b (λ _ a₁ a₂ b, f b a₁ a₂)

@[inline] def find (a : Array α) (f : α → Option β) : Option β :=
Id.run $ mfindAux a f 0

@[specialize] partial def anyAux (a : Array α) (p : α → Bool) : Nat → Bool
| i :=
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩ in
     match p (a.index idx) with
     | true  := true
     | false := anyAux (i+1)
  else false

@[inline] def any (a : Array α) (p : α → Bool) : Bool :=
anyAux a p 0

@[inline] def all (a : Array α) (p : α → Bool) : Bool :=
!any a (λ v, !p v)

@[specialize] private def revIterateAux (a : Array α) (f : Π i : Fin a.size, α → β → β) : Π (i : Nat), i ≤ a.size → β → β
| 0     h b := b
| (j+1) h b :=
  let i : Fin a.size := ⟨j, h⟩ in
  revIterateAux j (Nat.leOfLt h) (f i (a.index i) b)

@[inline] def revIterate (a : Array α) (b : β) (f : Π i : Fin a.size, α → β → β) : β :=
revIterateAux a f a.size (Nat.leRefl _) b

@[inline] def revFoldl (a : Array α) (b : β) (f : α → β → β) : β :=
revIterate a b (λ _, f)

def toList (a : Array α) : List α :=
a.revFoldl [] (::)

instance [HasRepr α] : HasRepr (Array α) :=
⟨repr ∘ toList⟩

instance [HasToString α] : HasToString (Array α) :=
⟨toString ∘ toList⟩

section
variables {m : Type u → Type u} [Monad m]

@[inline] def mmap {β : Type u} (f : α → m β) (as : Array α) : m (Array β) :=
as.mfoldl (mkEmpty as.size) (λ bs a, do b ← f a, pure (bs.push b))
end

@[inline] def modify [Inhabited α] (a : Array α) (i : Nat) (f : α → α) : Array α :=
if h : i < a.size then
  let idx : Fin a.size := ⟨i, h⟩ in
  let v                := a.index idx in
  let a                := a.update idx (default α) in
  let v                := f v in
  a.update idx v
else
  a

section
variables {m : Type u → Type v} [Monad m] [Inhabited α]
local attribute [instance] monadInhabited'

@[specialize] partial def hmmapAux (f : α → m α) : Nat → Array α → m (Array α)
| i a :=
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩ in
     let v   : α          := a.index idx in
     let a                := a.update idx (default α) in
     do v ← f v, hmmapAux (i+1) (a.update idx v)
  else
     pure a

/- Homogeneous `mmap` -/
@[inline] def hmmap (f : α → m α) (a : Array α) : m (Array α) :=
hmmapAux f 0 a
end

/- Homogeneous map -/
@[inline] def hmap [Inhabited α] (f : α → α) (a : Array α) : Array α :=
Id.run $ hmmap f a

@[inline] def map (f : α → β) (as : Array α) : Array β :=
as.foldl (λ bs a, bs.push (f a)) (mkEmpty as.size)

-- TODO(Leo): justify termination using wf-rec
partial def extractAux (a : Array α) : Nat → Π (e : Nat), e ≤ a.size → Array α → Array α
| i e hle r :=
  if hlt : i < e then
    let idx : Fin a.size := ⟨i, Nat.ltOfLtOfLe hlt hle⟩ in
    extractAux (i+1) e hle (r.push (a.index idx))
 else r

def extract (a : Array α) (b e : Nat) : Array α :=
let r : Array α := mkEmpty (e - b) in
if h : e ≤ a.size then extractAux a b e h r
else r

@[inline] protected def append (a : Array α) (b : Array α) : Array α :=
b.foldl (λ a v, a.push v) a

instance : HasAppend (Array α) := ⟨Array.append⟩

-- TODO(Leo): justify termination using wf-rec
partial def isEqvAux (a b : Array α) (hsz : a.size = b.size) (p : α → α → Bool) : Nat → Bool
| i :=
  if h : i < a.size then
     let aidx : Fin a.size := ⟨i, h⟩ in
     let bidx : Fin b.size := ⟨i, hsz ▸ h⟩ in
     match p (a.index aidx) (b.index bidx) with
     | true  := isEqvAux (i+1)
     | false := false
  else
    true

@[specialize] def isEqv (a b : Array α) (p : α → α → Bool) : Bool :=
if h : a.size = b.size then
  isEqvAux a b h p 0
else
  false

instance [HasBeq α] : HasBeq (Array α) :=
⟨λ a b, isEqv a b (==)⟩
end Array

export Array (mkArray)

@[inlineIfReduce] def List.toArrayAux {α : Type u} : List α → Array α → Array α
| []      r := r
| (a::as) r := List.toArrayAux as (r.push a)

@[inlineIfReduce] def List.redLength {α : Type u} : List α → Nat
| []      := 0
| (_::as) := as.redLength + 1

@[inline] def List.toArray {α : Type u} (as : List α) : Array α :=
as.toArrayAux (Array.mkEmpty as.redLength)
