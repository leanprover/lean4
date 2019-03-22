/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic init.data.fin.basic init.data.uint
import init.data.repr init.data.tostring
universes u v w

/-
The Compiler has special support for arrays.
They are implemented as a dynamic Array.
-/

-- TODO(Leo): mark as opaque
structure Array (α : Type u) :=
(sz   : Nat)
(data : Fin sz → α)

attribute [extern cpp inline "lean::array_sz(#2)"] Array.sz

@[extern cpp inline "lean::array_get_size(#2)"]
def Array.size {α : Type u} (a : @& Array α) : Nat :=
a.sz

@[extern cpp inline "lean::mk_array(#2, #3)"]
def mkArray {α : Type u} (n : Nat) (v : α) : Array α :=
{ sz   := n,
  data := λ _, v}

theorem szMkArrayEq {α : Type u} (n : Nat) (v : α) : (mkArray n v).sz = n :=
rfl

namespace Array
variables {α : Type u} {β : Type v}

@[extern cpp inline "lean::mk_empty_array()"]
def mkEmpty (_ : Unit) : Array α :=
{ sz   := 0,
  data := λ ⟨x, h⟩, absurd h (Nat.notLtZero x) }

def empty : Array α :=
mkEmpty ()

instance : HasEmptyc (Array α) :=
⟨Array.empty⟩

def isEmpty (a : Array α) : Bool :=
a.size = 0

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

@[extern cpp inline "lean::array_push(#2, #3)"]
def push (a : Array α) (v : α) : Array α :=
{ sz   := Nat.succ a.sz,
  data := λ ⟨j, h₁⟩,
    if h₂ : j = a.sz then v
    else a.data ⟨j, Nat.ltOfLeOfNe (Nat.leOfLtSucc h₁) h₂⟩ }

@[extern cpp inline "lean::array_pop(#2)"]
def pop (a : Array α) : Array α :=
{ sz   := Nat.pred a.sz,
  data := λ ⟨j, h⟩, a.index ⟨j, Nat.ltOfLtOfLe h (Nat.predLe _)⟩ }

-- TODO(Leo): justify termination using wf-rec
@[specialize] private def iterateAux (a : Array α) (f : Π i : Fin a.sz, α → β → β) : Nat → β → β
| i b :=
  if h : i < a.sz then
     let idx : Fin a.sz := ⟨i, h⟩ in
     iterateAux (i+1) (f idx (a.index idx) b)
  else b

@[inline] def iterate (a : Array α) (b : β) (f : Π i : Fin a.sz, α → β → β) : β :=
iterateAux a f 0 b

@[inline] def foldl (a : Array α) (b : β) (f : α → β → β) : β :=
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

@[inline] private def foreachAux (a : Array α) (f : Π i : Fin a.sz, α → α) : { a' : Array α // a'.sz = a.sz } :=
iterate a ⟨a, rfl⟩ $ λ i v ⟨a', h⟩,
  let i' : Fin a'.sz := Eq.recOn h.symm i in
  ⟨a'.update i' (f i v), (szUpdateEq a' i' (f i v)) ▸ h⟩

@[inline] def foreach (a : Array α) (f : Π i : Fin a.sz, α → α) : Array α :=
(foreachAux a f).val

theorem szForeachEq (a : Array α) (f : Π i : Fin a.sz, α → α) : (foreach a f).sz = a.sz :=
(foreachAux a f).property

@[inline] def map (f : α → α) (a : Array α) : Array α :=
foreach a (λ _, f)

@[inline] def map₂ (f : α → α → α) (a b : Array α) : Array α :=
if h : a.size ≤ b.size
then foreach a (λ ⟨i, h'⟩, f (b.index ⟨i, Nat.ltOfLtOfLe h' h⟩))
else foreach b (λ ⟨i, h'⟩, f (a.index ⟨i, Nat.ltTrans h' (Nat.gtOfNotLe h)⟩))

end Array

def List.toArrayAux {α : Type u} : List α → Array α → Array α
| []      r := r
| (a::as) r := List.toArrayAux as (r.push a)

def List.toArray {α : Type u} (l : List α) : Array α :=
l.toArrayAux ∅
