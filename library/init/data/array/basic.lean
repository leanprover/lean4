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

-- TODO(Leo): mark as opaque
structure Array (α : Type u) :=
(sz   : Nat)
(data : Fin sz → α)

attribute [extern cpp inline "lean::array_sz(#2)"] Array.sz

@[extern cpp inline "lean::array_get_size(#2)"]
def Array.size {α : Type u} (a : @& Array α) : Nat :=
a.sz

namespace Array
variables {α : Type u} {β : Type v}

/- The parameter `c` is the initial capacity -/
@[extern cpp inline "lean::mk_empty_array(#1)"]
def mkEmpty (c : @& Nat) : Array α :=
{ sz   := 0,
  data := λ ⟨x, h⟩, absurd h (Nat.notLtZero x) }

@[extern cpp inline "lean::array_push(#2, #3)"]
def push (a : Array α) (v : α) : Array α :=
{ sz   := Nat.succ a.sz,
  data := λ ⟨j, h₁⟩,
    if h₂ : j = a.sz then v
    else a.data ⟨j, Nat.ltOfLeOfNe (Nat.leOfLtSucc h₁) h₂⟩ }

def mkArray {α : Type u} (n : Nat) (v : α) : Array α :=
let a : Array α := mkEmpty n in
n.repeat (λ a, a.push v) a

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
def index (a : @& Array α) (i : @& Fin a.sz) : α :=
a.data i

/- Low-level version of `index` which is as fast as a C array read.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `index` may be slightly slower than `idx`. -/
@[extern cpp inline "lean::array_idx(#2, #3)"]
def idx (a : @& Array α) (i : USize) (h : i.toNat < a.sz) : α :=
a.index ⟨i.toNat, h⟩

/- "Comfortable" version of `index`. It performs a bound check at runtime. -/
@[extern cpp inline "lean::array_get(#2, #3, #4)"]
def get [Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
if h : i < a.sz then a.index ⟨i, h⟩ else default α

def getOpt (a : Array α) (i : Nat) : Option α :=
if h : i < a.size then some (a.index ⟨i, h⟩) else none

@[extern cpp inline "lean::array_update(#2, #3, #4)"]
def update (a : Array α) (i : @& Fin a.sz) (v : α) : Array α :=
{ sz   := a.sz,
  data := λ j, if h : i = j then v else a.data j }

/- Low-level version of `update` which is as fast as a C array update.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `update` may be slightly slower than `updt`. -/
@[extern cpp inline "lean::array_updt(#2, #3, #4)"]
def updt (a : @& Array α) (i : USize) (v : @& α) (h : i.toNat < a.sz) : Array α :=
a.update ⟨i.toNat, h⟩ v

/- "Comfortable" version of `update`. It performs a bound check at runtime. -/
@[extern cpp inline "lean::array_set(#2, #3, #4)"]
def set (a : Array α) (i : @& Nat) (v : α) : Array α :=
if h : i < a.sz then a.update ⟨i, h⟩ v else a

theorem szUpdateEq (a : Array α) (i : Fin a.sz) (v : α) : (update a i v).sz = a.sz :=
rfl

@[extern cpp inline "lean::array_pop(#2)"]
def pop (a : Array α) : Array α :=
{ sz   := Nat.pred a.sz,
  data := λ ⟨j, h⟩, a.index ⟨j, Nat.ltOfLtOfLe h (Nat.predLe _)⟩ }

section
variables {m : Type v → Type v} [Monad m]
local attribute [instance] monadInhabited'

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def miterateAux (a : Array α) (f : Π i : Fin a.sz, α → β → m β) : Nat → β → m β
| i b :=
  if h : i < a.sz then
     let idx : Fin a.sz := ⟨i, h⟩ in
     f idx (a.index idx) b >>= miterateAux (i+1)
  else pure b

@[inline] def miterate (a : Array α) (b : β) (f : Π i : Fin a.sz, α → β → m β) : m β :=
miterateAux a f 0 b

@[inline] def mfoldl (a : Array α) (b : β) (f : α → β → m β) : m β :=
miterate a b (λ _, f)
end

@[inline] def iterate (a : Array α) (b : β) (f : Π i : Fin a.sz, α → β → β) : β :=
id.run $ miterateAux a f 0 b

@[inline] def foldl (a : Array α) (f : α → β → β) (b : β) : β :=
iterate a b (λ _, f)

@[specialize] private def revIterateAux (a : Array α) (f : Π i : Fin a.sz, α → β → β) : Π (i : Nat), i ≤ a.sz → β → β
| 0     h b := b
| (j+1) h b :=
  let i : Fin a.sz := ⟨j, h⟩ in
  revIterateAux j (Nat.leOfLt h) (f i (a.index i) b)

@[inline] def revIterate (a : Array α) (b : β) (f : Π i : Fin a.sz, α → β → β) : β :=
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

@[inline] private def mforeachAux (a : Array α) (f : Π i : Fin a.sz, α → m α) : m { a' : Array α // a'.sz = a.sz } :=
miterate a ⟨a, rfl⟩ $ λ i v ⟨a', h⟩, do
  let i' : Fin a'.sz := Eq.recOn h.symm i,
  x ← f i v,
  pure $ ⟨a'.update i' x, (szUpdateEq a' i' x) ▸ h⟩

@[inline] def mforeach (a : Array α) (f : Π i : Fin a.sz, α → m α) : m (Array α) :=
Subtype.val <$> mforeachAux a f

@[inline] def mmap (f : α → m α) (a : Array α) : m (Array α) :=
mforeach a (λ _, f)
end

@[inline] def foreach (a : Array α) (f : Π i : Fin a.sz, α → α) : Array α :=
id.run $ mforeach a f

theorem szForeachEq (a : Array α) (f : Π i : Fin a.sz, α → α) : (foreach a f).sz = a.sz :=
(id.run $ mforeachAux a f).property

@[inline] def map (f : α → α) (a : Array α) : Array α :=
foreach a (λ _, f)

@[inline] def map₂ (f : α → α → α) (a b : Array α) : Array α :=
if h : a.size ≤ b.size
then foreach a (λ ⟨i, h'⟩, f (b.index ⟨i, Nat.ltOfLtOfLe h' h⟩))
else foreach b (λ ⟨i, h'⟩, f (a.index ⟨i, Nat.ltTrans h' (Nat.gtOfNotLe h)⟩))

end Array

export Array (mkArray)

private theorem repeatCorePushSz {α : Type u} : ∀ (n : Nat) (v : α) (a : Array α),
   (Nat.repeatCore (λ (a : Array α), a.push v) n (a.push v)).sz =
   (Nat.repeatCore (λ (a : Array α), a.push v) n a).sz.succ
| 0            _ _ := rfl
| (Nat.succ n) v a :=
  show (Nat.repeatCore (λ (a : Array α), a.push v) n ((a.push v).push v)).sz =
       (Nat.repeatCore (λ (a : Array α), a.push v) n (a.push v)).sz.succ, from
  repeatCorePushSz n v (a.push v)

theorem szMkArrayEq {α : Type u} (n : Nat) (v : α) : (mkArray n v).sz = n :=
Nat.recOn n rfl $ λ n ih,
  have aux₁ : (Nat.repeatCore (λ (a : Array α), a.push v) n (Array.mkEmpty n)).sz = n, from ih,
  have aux₂ : (Nat.repeatCore (λ (a : Array α), a.push v) n ((Array.mkEmpty n).push v)).sz =
              (Nat.repeatCore (λ (a : Array α), a.push v) n (Array.mkEmpty n)).sz.succ, from
    repeatCorePushSz _ _ _,
  have aux₃ : (Nat.repeatCore (λ (a : Array α), a.push v) n (Array.mkEmpty n)).sz.succ = n.succ, from
    congrArg _ aux₁,
  Eq.trans aux₂ aux₃

@[inlineIfReduce] def List.toArrayAux {α : Type u} : List α → Array α → Array α
| []      r := r
| (a::as) r := List.toArrayAux as (r.push a)

@[inline] def List.toArray {α : Type u} (as : List α) : Array α :=
as.toArrayAux (Array.mkEmpty as.length)
