/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic init.data.fin.basic init.data.uint
import init.data.repr init.data.tostring init.control.id
import init.util
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
variables {α : Type u}

/- The parameter `c` is the initial capacity -/
@[extern cpp inline "lean::mk_empty_array(#2)"]
def mkEmpty (c : @& Nat) : Array α :=
{ sz := 0,
  data := fun ⟨x, h⟩ => absurd h (Nat.notLtZero x) }

@[extern cpp inline "lean::array_push(#2, #3)"]
def push (a : Array α) (v : α) : Array α :=
{ sz   := Nat.succ a.sz,
  data := fun ⟨j, h₁⟩ =>
    if h₂ : j = a.sz then v
    else a.data ⟨j, Nat.ltOfLeOfNe (Nat.leOfLtSucc h₁) h₂⟩ }

@[extern cpp inline "lean::mk_array(#2, #3)"]
def mkArray {α : Type u} (n : Nat) (v : α) : Array α :=
{ sz   := n,
  data := fun _ => v}

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

@[extern cpp inline "lean::array_fget(#2, #3)"]
def fget (a : @& Array α) (i : @& Fin a.size) : α :=
a.data i

/- Low-level version of `fget` which is as fast as a C array read.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `fget` may be slightly slower than `uget`. -/
@[extern cpp inline "lean::array_uget(#2, #3)"]
def uget (a : @& Array α) (i : USize) (h : i.toNat < a.size) : α :=
a.fget ⟨i.toNat, h⟩

/- "Comfortable" version of `fget`. It performs a bound check at runtime. -/
@[extern cpp inline "lean::array_get(#2, #3, #4)"]
def get [Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
if h : i < a.size then a.fget ⟨i, h⟩ else default α

def back [Inhabited α] (a : Array α) : α :=
a.get (a.size - 1)

def getOpt (a : Array α) (i : Nat) : Option α :=
if h : i < a.size then some (a.fget ⟨i, h⟩) else none

@[extern cpp inline "lean::array_fset(#2, #3, #4)"]
def fset (a : Array α) (i : @& Fin a.size) (v : α) : Array α :=
{ sz   := a.sz,
  data := fun j => if h : i = j then v else a.data j }

theorem szFSetEq (a : Array α) (i : Fin a.size) (v : α) : (fset a i v).size = a.size :=
rfl

theorem szPushEq (a : Array α) (v : α) : (push a v).size = a.size + 1 :=
rfl

/- Low-level version of `fset` which is as fast as a C array fset.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `fset` may be slightly slower than `uset`. -/
@[extern cpp inline "lean::array_uset(#2, #3, #4)"]
def uset (a : Array α) (i : USize) (v : α) (h : i.toNat < a.size) : Array α :=
a.fset ⟨i.toNat, h⟩ v

/- "Comfortable" version of `fset`. It performs a bound check at runtime. -/
@[extern cpp inline "lean::array_set(#2, #3, #4)"]
def set (a : Array α) (i : @& Nat) (v : α) : Array α :=
if h : i < a.size then a.fset ⟨i, h⟩ v else a

@[extern cpp inline "lean::array_fswap(#2, #3, #4)"]
def fswap (a : Array α) (i j : @& Fin a.size) : Array α :=
let v₁ := a.fget i;
let v₂ := a.fget j;
let a  := a.fset i v₂;
a.fset j v₁

@[extern cpp inline "lean::array_swap(#2, #3, #4)"]
def swap (a : Array α) (i j : @& Nat) : Array α :=
if h₁ : i < a.size then
if h₂ : j < a.size then fswap a ⟨i, h₁⟩ ⟨j, h₂⟩
else a
else a

@[inline] def fswapAt {α : Type} (a : Array α) (i : Fin a.size) (v : α) : α × Array α :=
let e := a.fget i;
let a := a.fset i v;
(e, a)

@[inline] def swapAt {α : Type} (a : Array α) (i : Nat) (v : α) : α × Array α :=
if h : i < a.size then fswapAt a ⟨i, h⟩ v else (v, a)

@[extern cpp inline "lean::array_pop(#2)"]
def pop (a : Array α) : Array α :=
{ sz   := Nat.pred a.size,
  data := fun ⟨j, h⟩ => a.fget ⟨j, Nat.ltOfLtOfLe h (Nat.predLe _)⟩ }

-- TODO(Leo): justify termination using wf-rec
partial def shrink : Array α → Nat → Array α
| a n := if n ≥ a.size then a else shrink a.pop n

section
variables {m : Type v → Type w} [Monad m]
variables {β : Type v} {σ : Type u}

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def miterateAux (a : Array α) (f : ∀ (i : Fin a.size), α → β → m β) : Nat → β → m β
| i b :=
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     f idx (a.fget idx) b >>= miterateAux (i+1)
  else pure b

@[inline] def miterate (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → m β) : m β :=
miterateAux a f 0 b

@[inline] def mfoldl (f : β → α → m β) (b : β) (a : Array α) : m β :=
miterate a b (fun _ b a => f a b)

@[inline] def mfoldlFrom (f : β → α → m β) (b : β) (a : Array α) (ini : Nat := 0) : m β :=
miterateAux a (fun _ b a => f a b) ini b

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def miterate₂Aux (a₁ : Array α) (a₂ : Array σ) (f : ∀ (i : Fin a₁.size), α → σ → β → m β) : Nat → β → m β
| i b :=
  if h₁ : i < a₁.size then
     let idx₁ : Fin a₁.size := ⟨i, h₁⟩;
     if h₂ : i < a₂.size then
       let idx₂ : Fin a₂.size := ⟨i, h₂⟩;
       f idx₁ (a₁.fget idx₁) (a₂.fget idx₂) b >>= miterate₂Aux (i+1)
     else pure b
  else pure b

@[inline] def miterate₂ (a₁ : Array α) (a₂ : Array σ) (b : β) (f : ∀ (i : Fin a₁.size), α → σ → β → m β) : m β :=
miterate₂Aux a₁ a₂ f 0 b

@[inline] def mfoldl₂ (f : β → α → σ → m β) (b : β) (a₁ : Array α) (a₂ : Array σ): m β :=
miterate₂ a₁ a₂ b (fun _ a₁ a₂ b => f b a₁ a₂)


-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def mfindAux (a : Array α) (f : α → m (Option β)) : Nat → m (Option β)
| i :=
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     do r ← f (a.fget idx);
        match r with
        | some v => pure r
        | none   => mfindAux (i+1)
  else pure none

@[inline] def mfind (a : Array α) (f : α → m (Option β)) : m (Option β) :=
mfindAux a f 0

@[specialize] partial def mfindRevAux (a : Array α) (f : α → m (Option β)) : ∀ (idx : Nat), idx ≤ a.size → m (Option β)
| i h :=
  if hLt : 0 < i then
    have i - 1 < i from Nat.subLt hLt (Nat.zeroLtSucc 0);
    have i - 1 < a.size from Nat.ltOfLtOfLe this h;
    let idx : Fin a.size := ⟨i - 1, this⟩;
    do
      r ← f (a.fget idx);
      match r with
      | some v => pure r
      | none   =>
        have i - 1 ≤ a.size from Nat.leOfLt this;
        mfindRevAux (i-1) this
  else pure none

@[inline] def mfindRev (a : Array α) (f : α → m (Option β)) : m (Option β) :=
mfindRevAux a f a.size (Nat.leRefl _)

end

section
variables {β:Type w} {σ:Type u}

@[inline] def iterate (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → β) : β :=
Id.run $ miterateAux a f 0 b

@[inline] def iterateFrom (a : Array α) (b : β) (i : Nat) (f : ∀ (i : Fin a.size), α → β → β) : β :=
Id.run $ miterateAux a f i b

@[inline] def foldl (f : β → α → β) (b : β) (a : Array α) : β :=
iterate a b (fun _ a b => f b a)

@[inline] def foldlFrom (f : β → α → β) (b : β) (a : Array α) (ini : Nat := 0) : β :=
Id.run $ mfoldlFrom f b a ini

@[inline] def iterate₂ (a₁ : Array α) (a₂ : Array σ) (b : β) (f : ∀ (i : Fin a₁.size), α → σ → β → β) : β :=
Id.run $ miterate₂Aux a₁ a₂ f 0 b

@[inline] def foldl₂ (f : β → α → σ → β) (b : β) (a₁ : Array α) (a₂ : Array σ) : β :=
iterate₂ a₁ a₂ b (fun _ a₁ a₂ b => f b a₁ a₂)

@[inline] def find (a : Array α) (f : α → Option β) : Option β :=
Id.run $ mfindAux a f 0

@[inline] def findRev (a : Array α) (f : α → Option β) : Option β :=
Id.run $ mfindRevAux a f a.size (Nat.leRefl _)
end

section
variables {m : Type → Type w} [Monad m]

@[specialize] partial def anyMAux (a : Array α) (p : α → m Bool) : Nat → m Bool
| i :=
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     do b ← p (a.fget idx);
     match b with
     | true  => pure true
     | false => anyMAux (i+1)
  else pure false

@[inline] def anyM (a : Array α) (p : α → m Bool) : m Bool :=
anyMAux a p 0

@[inline] def allM (a : Array α) (p : α → m Bool) : m Bool :=
not <$> anyM a (fun v => not <$> p v)
end

@[inline] def any (a : Array α) (p : α → Bool) : Bool :=
Id.run $ anyM a p

@[inline] def all (a : Array α) (p : α → Bool) : Bool :=
!any a (fun v => !p v)

section
variable {β:Type w}

@[specialize] private def revIterateAux (a : Array α) (f : ∀ (i : Fin a.size), α → β → β) : ∀ (i : Nat), i ≤ a.size → β → β
| 0     h b := b
| (j+1) h b :=
  let i : Fin a.size := ⟨j, h⟩;
  revIterateAux j (Nat.leOfLt h) (f i (a.fget i) b)

@[inline] def revIterate (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → β) : β :=
revIterateAux a f a.size (Nat.leRefl _) b

@[inline] def revFoldl (a : Array α) (b : β) (f : α → β → β) : β :=
revIterate a b (fun _ => f)

def toList (a : Array α) : List α :=
a.revFoldl [] List.cons

instance [HasRepr α] : HasRepr (Array α) :=
⟨repr ∘ toList⟩

instance [HasToString α] : HasToString (Array α) :=
⟨toString ∘ toList⟩
end

section
variables {m : Type u → Type w} [Monad m]
variable {β:Type u}

@[specialize] unsafe partial def ummapAux (f : Nat → α → m β) : Nat → Array α → m (Array β)
| i a :=
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     let v   : α          := a.fget idx;
     let a                := a.fset idx (@unsafeCast _ _ ⟨v⟩ ());
     do newV ← f i v; ummapAux (i+1) (a.fset idx (@unsafeCast _ _ ⟨v⟩ newV))
  else
     pure (unsafeCast a)

@[inline] unsafe partial def ummap (f : α → m β) (as : Array α) : m (Array β) :=
ummapAux (fun i a => f a) 0 as

@[inline] unsafe partial def ummapIdx (f : Nat → α → m β) (as : Array α) : m (Array β) :=
ummapAux f 0 as

@[implementedBy Array.ummap] def mmap (f : α → m β) (as : Array α) : m (Array β) :=
as.mfoldl (fun bs a => do b ← f a; pure (bs.push b)) (mkEmpty as.size)

@[implementedBy Array.ummapIdx] def mmapIdx (f : Nat → α → m β) (as : Array α) : m (Array β) :=
as.miterate (mkEmpty as.size) (fun i a bs => do b ← f i.val a; pure (bs.push b))
end

section
variable {β:Type u}

@[inline] def modify [Inhabited α] (a : Array α) (i : Nat) (f : α → α) : Array α :=
if h : i < a.size then
  let idx : Fin a.size := ⟨i, h⟩;
  let v                := a.fget idx;
  let a                := a.fset idx (default α);
  let v                := f v;
  a.fset idx v
else
  a

@[inline] def mapIdx (f : Nat → α → β) (a : Array α) : Array β :=
Id.run $ mmapIdx f a

@[inline] def map (f : α → β) (as : Array α) : Array β :=
Id.run $ mmap f as
end

section
variables {m : Type u → Type u} [Monad m]
variable {β:Type u}

@[specialize]
partial def mforAux {α : Type w} {β : Type u} (f : α → m β) (a : Array α) : Nat → m PUnit
| i :=
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     let v   : α          := a.fget idx;
     f v *> mforAux (i+1)
  else
     pure ⟨⟩

def mfor {α : Type w} {β : Type u} (f : α → m β) (a : Array α) : m PUnit :=
a.mforAux f 0

end

-- TODO(Leo): justify termination using wf-rec
partial def extractAux (a : Array α) : Nat → ∀ (e : Nat), e ≤ a.size → Array α → Array α
| i e hle r :=
  if hlt : i < e then
    let idx : Fin a.size := ⟨i, Nat.ltOfLtOfLe hlt hle⟩;
    extractAux (i+1) e hle (r.push (a.fget idx))
 else r

def extract (a : Array α) (b e : Nat) : Array α :=
let r : Array α := mkEmpty (e - b);
if h : e ≤ a.size then extractAux a b e h r
else r

protected def append (a : Array α) (b : Array α) : Array α :=
b.foldl (fun a v => a.push v) a

instance : HasAppend (Array α) := ⟨Array.append⟩

-- TODO(Leo): justify termination using wf-rec
partial def isEqvAux (a b : Array α) (hsz : a.size = b.size) (p : α → α → Bool) : Nat → Bool
| i :=
  if h : i < a.size then
     let aidx : Fin a.size := ⟨i, h⟩;
     let bidx : Fin b.size := ⟨i, hsz ▸ h⟩;
     match p (a.fget aidx) (b.fget bidx) with
     | true  => isEqvAux (i+1)
     | false => false
  else
    true

@[specialize] def isEqv (a b : Array α) (p : α → α → Bool) : Bool :=
if h : a.size = b.size then
  isEqvAux a b h p 0
else
  false

instance [HasBeq α] : HasBeq (Array α) :=
⟨fun a b => isEqv a b HasBeq.beq⟩

-- TODO(Leo): justify termination using wf-rec, and use `fswap`
partial def reverseAux : Array α → Nat → Array α
| a i :=
  let n := a.size;
  if i < n / 2 then
    reverseAux (a.swap i (n - i - 1)) (i+1)
  else
    a

def reverse (a : Array α) : Array α :=
reverseAux a 0

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def filterAux (p : α → Bool) : Array α → Nat → Nat → Array α
| a i j :=
  if h₁ : i < a.size then
    if p (a.fget ⟨i, h₁⟩) then
       if h₂ : j < i then
         filterAux (a.fswap ⟨i, h₁⟩ ⟨j, Nat.ltTrans h₂ h₁⟩) (i+1) (j+1)
       else
         filterAux a (i+1) (j+1)
    else
       filterAux a (i+1) j
  else
    a.shrink j

@[inline] def filter (p : α → Bool) (as : Array α) : Array α :=
filterAux p as 0 0

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
