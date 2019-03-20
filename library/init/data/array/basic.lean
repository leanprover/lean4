/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic init.data.fin.basic init.data.uint init.data.repr init.function
import init.data.tostring
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

@[extern cpp inline "lean::mk_nil_array()"]
def mkNil (_ : unit) : Array α :=
{ sz   := 0,
  data := λ ⟨x, h⟩, absurd h (Nat.notLtZero x) }

def nil : Array α :=
mkNil ()

def Empty (a : Array α) : Bool :=
a.size = 0

@[extern cpp inline "lean::array_read(#2, #3)"]
def read (a : @& Array α) (i : @& Fin a.sz) : α :=
a.data i

@[extern cpp inline "lean::array_write(#2, #3, #4)"]
def write (a : Array α) (i : @& Fin a.sz) (v : α) : Array α :=
{ sz   := a.sz,
  data := λ j, if h : i = j then v else a.data j }

theorem szWriteEq (a : Array α) (i : Fin a.sz) (v : α) : (write a i v).sz = a.sz :=
rfl

@[extern cpp inline "lean::array_safe_read(#2, #3, #4)"]
def read' [Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
if h : i < a.sz then a.read ⟨i, h⟩ else default α

@[extern cpp inline "lean::array_safe_write(#2, #3, #4)"]
def write' (a : Array α) (i : @& Nat) (v : α) : Array α :=
if h : i < a.sz then a.write ⟨i, h⟩ v else a

@[extern cpp inline "lean::array_uread(#2, #3)"]
def uread (a : @& Array α) (i : Usize) (h : i.toNat < a.sz) : α :=
a.read ⟨i.toNat, h⟩

@[extern cpp inline "lean::array_uwrite(#2, #3, #4)"]
def uwrite (a : @& Array α) (i : Usize) (v : @& α) (h : i.toNat < a.sz) : Array α :=
a.write ⟨i.toNat, h⟩ v

@[extern cpp inline "lean::array_safe_uread(#2, #3, #4)"]
def uread' [Inhabited α] (a : Array α) (i : Usize) : α :=
if h : i.toNat < a.sz then a.read ⟨i.toNat, h⟩ else default α

@[extern cpp inline "lean::array_safe_uwrite(#2, #3, #4)"]
def uwrite' (a : Array α) (i : Usize) (v : α) : Array α :=
if h : i.toNat < a.sz then a.write ⟨i.toNat, h⟩ v else a

@[extern cpp inline "lean::array_push(#2, #3)"]
def push (a : Array α) (v : α) : Array α :=
{ sz   := Nat.succ a.sz,
  data := λ ⟨j, h₁⟩,
    if h₂ : j = a.sz then v
    else a.data ⟨j, Nat.ltOfLeOfNe (Nat.leOfLtSucc h₁) h₂⟩ }

@[extern cpp inline "lean::array_pop(#2)"]
def pop (a : Array α) : Array α :=
{ sz   := Nat.pred a.sz,
  data := λ ⟨j, h⟩, a.read ⟨j, Nat.ltOfLtOfLe h (Nat.predLe _)⟩ }

-- TODO(Leo): justify termination using wf-rec
@[specialize] private def iterateAux (a : Array α) (f : Π i : Fin a.sz, α → β → β) : Nat → β → β
| i b :=
  if h : i < a.sz then
     let idx : Fin a.sz := ⟨i, h⟩ in
     iterateAux (i+1) (f idx (a.read idx) b)
  else b

@[inline] def iterate (a : Array α) (b : β) (f : Π i : Fin a.sz, α → β → β) : β :=
iterateAux a f 0 b

@[inline] def foldl (a : Array α) (b : β) (f : α → β → β) : β :=
iterate a b (λ _, f)

@[specialize] private def revIterateAux (a : Array α) (f : Π i : Fin a.sz, α → β → β) : Π (i : Nat), i ≤ a.sz → β → β
| 0     h b := b
| (j+1) h b :=
  let i : Fin a.sz := ⟨j, h⟩ in
  revIterateAux j (Nat.leOfLt h) (f i (a.read i) b)

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
  ⟨a'.write i' (f i v), (szWriteEq a' i' (f i v)) ▸ h⟩

@[inline] def foreach (a : Array α) (f : Π i : Fin a.sz, α → α) : Array α :=
(foreachAux a f).val

theorem szForeachEq (a : Array α) (f : Π i : Fin a.sz, α → α) : (foreach a f).sz = a.sz :=
(foreachAux a f).property

@[inline] def map (f : α → α) (a : Array α) : Array α :=
foreach a (λ _, f)

@[inline] def map₂ (f : α → α → α) (a b : Array α) : Array α :=
if h : a.size ≤ b.size
then foreach a (λ ⟨i, h'⟩, f (b.read ⟨i, Nat.ltOfLtOfLe h' h⟩))
else foreach b (λ ⟨i, h'⟩, f (a.read ⟨i, Nat.ltTrans h' (Nat.gtOfNotLe h)⟩))

end Array

def List.toArrayAux {α : Type u} : List α → Array α → Array α
| []      r := r
| (a::as) r := List.toArrayAux as (r.push a)

def List.toArray {α : Type u} (l : List α) : Array α :=
l.toArrayAux Array.nil
