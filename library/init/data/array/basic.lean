/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic init.data.fin.basic init.data.uint init.data.repr init.function
import init.data.toString
universes u v w

/-
The compiler has special support for arrays.
They are implemented as a dynamic array.
-/

-- TODO(Leo): mark as opaque
structure array (α : Type u) :=
(sz   : nat)
(data : fin sz → α)

attribute [extern cpp inline "lean::arraySz(#2)"] array.sz

@[extern cpp inline "lean::arrayGetSize(#2)"]
def array.size {α : Type u} (a : @& array α) : nat :=
a.sz

@[extern cpp inline "lean::mkArray(#2, #3)"]
def mkArray {α : Type u} (n : nat) (v : α) : array α :=
{ sz   := n,
  data := λ _, v}

theorem szMkArrayEq {α : Type u} (n : nat) (v : α) : (mkArray n v).sz = n :=
rfl

namespace array
variables {α : Type u} {β : Type v}

@[extern cpp inline "lean::mkNilArray()"]
def mkNil (_ : unit) : array α :=
{ sz   := 0,
  data := λ ⟨x, h⟩, absurd h (nat.notLtZero x) }

def nil : array α :=
mkNil ()

def empty (a : array α) : bool :=
a.size = 0

@[extern cpp inline "lean::arrayRead(#2, #3)"]
def read (a : @& array α) (i : @& fin a.sz) : α :=
a.data i

@[extern cpp inline "lean::arrayWrite(#2, #3, #4)"]
def write (a : array α) (i : @& fin a.sz) (v : α) : array α :=
{ sz   := a.sz,
  data := λ j, if h : i = j then v else a.data j }

theorem szWriteEq (a : array α) (i : fin a.sz) (v : α) : (write a i v).sz = a.sz :=
rfl

@[extern cpp inline "lean::arraySafeRead(#2, #3, #4)"]
def read' [inhabited α] (a : @& array α) (i : @& nat) : α :=
if h : i < a.sz then a.read ⟨i, h⟩ else default α

@[extern cpp inline "lean::arraySafeWrite(#2, #3, #4)"]
def write' (a : array α) (i : @& nat) (v : α) : array α :=
if h : i < a.sz then a.write ⟨i, h⟩ v else a

@[extern cpp inline "lean::arrayUread(#2, #3)"]
def uread (a : @& array α) (i : usize) (h : i.toNat < a.sz) : α :=
a.read ⟨i.toNat, h⟩

@[extern cpp inline "lean::arrayUwrite(#2, #3, #4)"]
def uwrite (a : @& array α) (i : usize) (v : @& α) (h : i.toNat < a.sz) : array α :=
a.write ⟨i.toNat, h⟩ v

@[extern cpp inline "lean::arraySafeUread(#2, #3, #4)"]
def uread' [inhabited α] (a : array α) (i : usize) : α :=
if h : i.toNat < a.sz then a.read ⟨i.toNat, h⟩ else default α

@[extern cpp inline "lean::arraySafeUwrite(#2, #3, #4)"]
def uwrite' (a : array α) (i : usize) (v : α) : array α :=
if h : i.toNat < a.sz then a.write ⟨i.toNat, h⟩ v else a

@[extern cpp inline "lean::arrayPush(#2, #3)"]
def push (a : array α) (v : α) : array α :=
{ sz   := nat.succ a.sz,
  data := λ ⟨j, h₁⟩,
    if h₂ : j = a.sz then v
    else a.data ⟨j, nat.ltOfLeOfNe (nat.leOfLtSucc h₁) h₂⟩ }

@[extern cpp inline "lean::arrayPop(#2)"]
def pop (a : array α) : array α :=
{ sz   := nat.pred a.sz,
  data := λ ⟨j, h⟩, a.read ⟨j, nat.ltOfLtOfLe h (nat.predLe _)⟩ }

-- TODO(Leo): justify termination using wf-rec
@[specialize] private def iterateAux (a : array α) (f : Π i : fin a.sz, α → β → β) : nat → β → β
| i b :=
  if h : i < a.sz then
     let idx : fin a.sz := ⟨i, h⟩ in
     iterateAux (i+1) (f idx (a.read idx) b)
  else b

@[inline] def iterate (a : array α) (b : β) (f : Π i : fin a.sz, α → β → β) : β :=
iterateAux a f 0 b

@[inline] def foldl (a : array α) (b : β) (f : α → β → β) : β :=
iterate a b (λ _, f)

@[specialize] private def revIterateAux (a : array α) (f : Π i : fin a.sz, α → β → β) : Π (i : nat), i ≤ a.sz → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin a.sz := ⟨j, h⟩ in
  revIterateAux j (nat.leOfLt h) (f i (a.read i) b)

@[inline] def revIterate (a : array α) (b : β) (f : Π i : fin a.sz, α → β → β) : β :=
revIterateAux a f a.size (nat.leRefl _) b

@[inline] def revFoldl (a : array α) (b : β) (f : α → β → β) : β :=
revIterate a b (λ _, f)

def toList (a : array α) : list α :=
a.revFoldl [] (::)

instance [hasRepr α] : hasRepr (array α) :=
⟨repr ∘ toList⟩

instance [hasToString α] : hasToString (array α) :=
⟨toString ∘ toList⟩

@[inline] private def foreachAux (a : array α) (f : Π i : fin a.sz, α → α) : { a' : array α // a'.sz = a.sz } :=
iterate a ⟨a, rfl⟩ $ λ i v ⟨a', h⟩,
  let i' : fin a'.sz := eq.recOn h.symm i in
  ⟨a'.write i' (f i v), (szWriteEq a' i' (f i v)) ▸ h⟩

@[inline] def foreach (a : array α) (f : Π i : fin a.sz, α → α) : array α :=
(foreachAux a f).val

theorem szForeachEq (a : array α) (f : Π i : fin a.sz, α → α) : (foreach a f).sz = a.sz :=
(foreachAux a f).property

@[inline] def map (f : α → α) (a : array α) : array α :=
foreach a (λ _, f)

@[inline] def map₂ (f : α → α → α) (a b : array α) : array α :=
if h : a.size ≤ b.size
then foreach a (λ ⟨i, h'⟩, f (b.read ⟨i, nat.ltOfLtOfLe h' h⟩))
else foreach b (λ ⟨i, h'⟩, f (a.read ⟨i, nat.ltTrans h' (nat.gtOfNotLe h)⟩))

end array

def list.toArrayAux {α : Type u} : list α → array α → array α
| []      r := r
| (a::as) r := list.toArrayAux as (r.push a)

def list.toArray {α : Type u} (l : list α) : array α :=
l.toArrayAux array.nil
