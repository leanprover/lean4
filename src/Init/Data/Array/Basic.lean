/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Basic
import Init.Data.Fin.Basic
import Init.Data.UInt
import Init.Data.Repr
import Init.Data.ToString.Basic
import Init.Control.Id
import Init.Util
universes u v w

-- TODO: CLEANUP

/-
The Compiler has special support for arrays.
They are implemented using dynamic arrays: https://en.wikipedia.org/wiki/Dynamic_array
-/
structure Array (α : Type u) :=
  (sz   : Nat)
  (data : Fin sz → α)

attribute [extern "lean_array_mk"] Array.mk
attribute [extern "lean_array_data"] Array.data
attribute [extern "lean_array_sz"] Array.sz

@[reducible, extern "lean_array_get_size"]
def Array.size {α : Type u} (a : @& Array α) : Nat :=
  a.sz

namespace Array
variables {α : Type u}

/- The parameter `c` is the initial capacity -/
@[extern "lean_mk_empty_array_with_capacity"]
def mkEmpty (c : @& Nat) : Array α := {
  sz   := 0,
  data := fun ⟨x, h⟩ => absurd h (Nat.notLtZero x)
}

@[extern "lean_array_push"]
def push (a : Array α) (v : α) : Array α := {
  sz   := Nat.succ a.sz,
  data := fun ⟨j, h₁⟩ =>
    if h₂ : j = a.sz then v
    else a.data ⟨j, Nat.ltOfLeOfNe (Nat.leOfLtSucc h₁) h₂⟩ }

@[extern "lean_mk_array"]
def mkArray {α : Type u} (n : Nat) (v : α) : Array α := {
  sz   := n,
  data := fun _ => v}

theorem szMkArrayEq (n : Nat) (v : α) : (mkArray n v).sz = n :=
  rfl

def empty : Array α :=
  mkEmpty 0

instance : HasEmptyc (Array α) := ⟨Array.empty⟩
instance : Inhabited (Array α) := ⟨Array.empty⟩

def isEmpty (a : Array α) : Bool :=
  a.size = 0

def singleton (v : α) : Array α :=
  mkArray 1 v

@[extern "lean_array_fget"]
def get (a : @& Array α) (i : @& Fin a.size) : α :=
  a.data i

/- Low-level version of `fget` which is as fast as a C array read.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `fget` may be slightly slower than `uget`. -/
@[extern "lean_array_uget"]
def uget (a : @& Array α) (i : USize) (h : i.toNat < a.size) : α :=
  a.get ⟨i.toNat, h⟩

/- "Comfortable" version of `fget`. It performs a bound check at runtime. -/
@[extern "lean_array_get"]
def get! [Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
  if h : i < a.size then a.get ⟨i, h⟩ else arbitrary α

def back [Inhabited α] (a : Array α) : α :=
  a.get! (a.size - 1)

def get? (a : Array α) (i : Nat) : Option α :=
  if h : i < a.size then some (a.get ⟨i, h⟩) else none

def getD (a : Array α) (i : Nat) (v₀ : α) : α :=
  if h : i < a.size then a.get ⟨i, h⟩ else v₀

def getOp [Inhabited α] (self : Array α) (idx : Nat) : α :=
  self.get! idx

-- auxiliary declaration used in the equation compiler when pattern matching array literals.
abbrev getLit {α : Type u} {n : Nat} (a : Array α) (i : Nat) (h₁ : a.size = n) (h₂ : i < n) : α :=
  a.get ⟨i, h₁.symm ▸ h₂⟩

@[extern "lean_array_fset"]
def set (a : Array α) (i : @& Fin a.size) (v : α) : Array α := {
  sz   := a.sz,
  data := fun j => if h : i = j then v else a.data j
}

theorem szFSetEq (a : Array α) (i : Fin a.size) (v : α) : (set a i v).size = a.size :=
  rfl

theorem szPushEq (a : Array α) (v : α) : (push a v).size = a.size + 1 :=
  rfl

/- Low-level version of `fset` which is as fast as a C array fset.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `fset` may be slightly slower than `uset`. -/
@[extern "lean_array_uset"]
def uset (a : Array α) (i : USize) (v : α) (h : i.toNat < a.size) : Array α :=
  a.set ⟨i.toNat, h⟩ v

/- "Comfortable" version of `fset`. It performs a bound check at runtime. -/
@[extern "lean_array_set"]
def set! (a : Array α) (i : @& Nat) (v : α) : Array α :=
  if h : i < a.size then a.set ⟨i, h⟩ v else panic! "index out of bounds"

@[extern "lean_array_fswap"]
def swap (a : Array α) (i j : @& Fin a.size) : Array α :=
  let v₁ := a.get i;
  let v₂ := a.get j;
  let a  := a.set i v₂;
  a.set j v₁

@[extern "lean_array_swap"]
def swap! (a : Array α) (i j : @& Nat) : Array α :=
  if h₁ : i < a.size then
  if h₂ : j < a.size then swap a ⟨i, h₁⟩ ⟨j, h₂⟩
  else panic! "index out of bounds"
  else panic! "index out of bounds"

@[inline] def swapAt {α : Type} (a : Array α) (i : Fin a.size) (v : α) : α × Array α :=
  let e := a.get i;
  let a := a.set i v;
  (e, a)

-- TODO: delete as soon as we can define local instances
@[neverExtract] private def swapAtPanic! [Inhabited α] (i : Nat) : α × Array α :=
  panic! ("index " ++ toString i ++ " out of bounds")

@[inline] def swapAt! {α : Type} (a : Array α) (i : Nat) (v : α) : α × Array α :=
  if h : i < a.size then swapAt a ⟨i, h⟩ v else @swapAtPanic! _ ⟨v⟩ i

@[extern "lean_array_pop"]
def pop (a : Array α) : Array α := {
  sz   := Nat.pred a.size,
  data := fun ⟨j, h⟩ => a.get ⟨j, Nat.ltOfLtOfLe h (Nat.predLe _)⟩
}

-- TODO(Leo): justify termination using wf-rec
partial def shrink : Array α → Nat → Array α
  | a, n => if n ≥ a.size then a else shrink a.pop n

section
variables {m : Type v → Type w} [Monad m]
variables {β : Type v} {σ : Type u}

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def iterateMAux (a : Array α) (f : ∀ (i : Fin a.size), α → β → m β) : Nat → β → m β
  | i, b =>
    if h : i < a.size then
       let idx : Fin a.size := ⟨i, h⟩;
       f idx (a.get idx) b >>= iterateMAux a f (i+1)
    else pure b

@[inline] def iterateM (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → m β) : m β :=
  iterateMAux a f 0 b

@[inline] def foldlM (f : β → α → m β) (init : β) (a : Array α) : m β :=
  iterateM a init (fun _ b a => f a b)

@[inline] def foldlFromM (f : β → α → m β) (init : β) (beginIdx : Nat) (a : Array α) : m β :=
  iterateMAux a (fun _ b a => f a b) beginIdx init

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def iterateM₂Aux (a₁ : Array α) (a₂ : Array σ) (f : ∀ (i : Fin a₁.size), α → σ → β → m β) : Nat → β → m β
  | i, b =>
    if h₁ : i < a₁.size then
       let idx₁ : Fin a₁.size := ⟨i, h₁⟩;
       if h₂ : i < a₂.size then
         let idx₂ : Fin a₂.size := ⟨i, h₂⟩;
         f idx₁ (a₁.get idx₁) (a₂.get idx₂) b >>= iterateM₂Aux a₁ a₂ f (i+1)
       else pure b
    else pure b

@[inline] def iterateM₂ (a₁ : Array α) (a₂ : Array σ) (b : β) (f : ∀ (i : Fin a₁.size), α → σ → β → m β) : m β :=
  iterateM₂Aux a₁ a₂ f 0 b

@[inline] def foldlM₂ (f : β → α → σ → m β) (b : β) (a₁ : Array α) (a₂ : Array σ): m β :=
  iterateM₂ a₁ a₂ b (fun _ a₁ a₂ b => f b a₁ a₂)

@[specialize] partial def findSomeMAux (a : Array α) (f : α → m (Option β)) : Nat → m (Option β)
  | i =>
    if h : i < a.size then
       let idx : Fin a.size := ⟨i, h⟩;
       do let r ← f (a.get idx);
          match r with
          | some v => pure r
          | none   => findSomeMAux a f (i+1)
    else pure none

@[inline] def findSomeM? (a : Array α) (f : α → m (Option β)) : m (Option β) :=
  findSomeMAux a f 0

@[specialize] partial def findSomeRevMAux (a : Array α) (f : α → m (Option β)) : ∀ (idx : Nat), idx ≤ a.size → m (Option β)
  | 0,   h => pure none
  | i+1, h => do
      have i < a.size from sorry
      let idx : Fin a.size := ⟨i, this⟩;
      do
        let r ← f (a.get idx);
        match r with
        | some v => pure r
        | none   =>
          have i ≤ a.size from Nat.leOfLt this;
          findSomeRevMAux a f i this


@[inline] def findSomeRevM? (a : Array α) (f : α → m (Option β)) : m (Option β) :=
  findSomeRevMAux a f a.size (Nat.leRefl _)
end

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def findMAux {α : Type} {m : Type → Type} [Monad m] (a : Array α) (p : α → m Bool) : Nat → m (Option α)
| i =>
  if h : i < a.size then do
    let v := a.get ⟨i, h⟩;
    condM (p v) (pure (some v)) (findMAux a p (i+1))
  else pure none

@[inline] def findM? {α : Type} {m : Type → Type} [Monad m] (a : Array α) (p : α → m Bool) : m (Option α) :=
findMAux a p 0

@[inline] def find? {α : Type} (a : Array α) (p : α → Bool) : Option α :=
Id.run $ a.findM? p

@[specialize] partial def findRevMAux {α : Type} {m : Type → Type} [Monad m] (a : Array α) (p : α → m Bool) : ∀ (idx : Nat), idx ≤ a.size → m (Option α)
| i, h =>
  if hLt : 0 < i then
    have i - 1 < i from sorry -- Nat.subLt hLt (Nat.zeroLtSucc 0);
    have i - 1 < a.size from Nat.ltOfLtOfLe this h;
    let v := a.get ⟨i - 1, this⟩;
    do {
      condM (p v) (pure (some v)) $
        have i - 1 ≤ a.size from Nat.leOfLt this;
        findRevMAux a p (i-1) this
    }
  else pure none

@[inline] def findRevM? {α : Type} {m : Type → Type} [Monad m] (a : Array α) (p : α → m Bool) : m (Option α) :=
findRevMAux a p a.size (Nat.leRefl _)

@[inline] def findRev? {α : Type} (a : Array α) (p : α → Bool) : Option α :=
Id.run $ a.findRevM? p

section
variables {β : Type w} {σ : Type u}

@[inline] def iterate (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → β) : β :=
Id.run $ iterateMAux a f 0 b

@[inline] def iterateFrom (a : Array α) (b : β) (i : Nat) (f : ∀ (i : Fin a.size), α → β → β) : β :=
Id.run $ iterateMAux a f i b

@[inline] def foldl (f : β → α → β) (init : β) (a : Array α) : β :=
iterate a init (fun _ a b => f b a)

@[inline] def foldlFrom (f : β → α → β) (init : β) (beginIdx : Nat) (a : Array α) : β :=
Id.run $ foldlFromM f init beginIdx a

@[inline] def iterate₂ (a₁ : Array α) (a₂ : Array σ) (b : β) (f : ∀ (i : Fin a₁.size), α → σ → β → β) : β :=
Id.run $ iterateM₂Aux a₁ a₂ f 0 b

@[inline] def foldl₂ (f : β → α → σ → β) (b : β) (a₁ : Array α) (a₂ : Array σ) : β :=
iterate₂ a₁ a₂ b (fun _ a₁ a₂ b => f b a₁ a₂)

@[inline] def findSome? (a : Array α) (f : α → Option β) : Option β :=
Id.run $ findSomeMAux a f 0

@[inline] def findSome! [Inhabited β] (a : Array α) (f : α → Option β) : β :=
match findSome? a f with
| some b => b
| none   => panic! "failed to find element"

@[inline] def findSomeRev? (a : Array α) (f : α → Option β) : Option β :=
Id.run $ findSomeRevMAux a f a.size (Nat.leRefl _)

@[inline] def findSomeRev! [Inhabited β] (a : Array α) (f : α → Option β) : β :=
match findSomeRev? a f with
| some b => b
| none   => panic! "failed to find element"

@[specialize] partial def findIdxMAux {m : Type → Type u} [Monad m] (a : Array α) (p : α → m Bool) : Nat → m (Option Nat)
| i =>
  if h : i < a.size then
    condM (p (a.get ⟨i, h⟩)) (pure (some i)) (findIdxMAux a p (i+1))
  else
    pure none

@[inline] def findIdxM? {m : Type → Type u} [Monad m] (a : Array α) (p : α → m Bool) : m (Option Nat) :=
findIdxMAux a p 0

@[specialize] partial def findIdxAux (a : Array α) (p : α → Bool) : Nat → Option Nat
| i =>
  if h : i < a.size then
    if p (a.get ⟨i, h⟩) then some i else findIdxAux a p (i+1)
  else
    none

@[inline] def findIdx? (a : Array α) (p : α → Bool) : Option Nat :=
findIdxAux a p 0

@[inline] def findIdx! (a : Array α) (p : α → Bool) : Nat :=
match findIdxAux a p 0 with
| some i => i
| none   => panic! "failed to find element"

def getIdx? [HasBeq α] (a : Array α) (v : α) : Option Nat :=
a.findIdx? $ fun a => a == v

end

section
variables {m : Type → Type w} [Monad m]

@[specialize] partial def anyRangeMAux (a : Array α) (endIdx : Nat) (hlt : endIdx ≤ a.size) (p : α → m Bool) : Nat → m Bool
| i =>
  if h : i < endIdx then
     let idx : Fin a.size := ⟨i, Nat.ltOfLtOfLe h hlt⟩;
     do
     let b ← p (a.get idx);
     match b with
     | true  => pure true
     | false => anyRangeMAux a endIdx hlt p (i+1)
  else pure false

@[inline] def anyM (a : Array α) (p : α → m Bool) : m Bool :=
anyRangeMAux a a.size (Nat.leRefl _) p 0

@[inline] def allM (a : Array α) (p : α → m Bool) : m Bool := do
let b ← anyM a (fun v => do let b ← p v; pure (!b)); pure (!b)

@[inline] def anyRangeM (a : Array α) (beginIdx endIdx : Nat) (p : α → m Bool) : m Bool :=
if h : endIdx ≤ a.size then
  anyRangeMAux a endIdx h p beginIdx
else
  anyRangeMAux a a.size (Nat.leRefl _) p beginIdx

@[inline] def allRangeM (a : Array α) (beginIdx endIdx : Nat) (p : α → m Bool) : m Bool := do
let b ← anyRangeM a beginIdx endIdx (fun v => do let b ← p v; pure b); pure (!b)

end

@[inline] def any (a : Array α) (p : α → Bool) : Bool :=
Id.run $ anyM a p

@[inline] def anyRange (a : Array α) (beginIdx endIdx : Nat) (p : α → Bool) : Bool :=
Id.run $ anyRangeM a beginIdx endIdx p

@[inline] def anyFrom (a : Array α) (beginIdx : Nat) (p : α → Bool) : Bool :=
Id.run $ anyRangeM a beginIdx a.size p

@[inline] def all (a : Array α) (p : α → Bool) : Bool :=
!any a (fun v => !p v)

@[inline] def allRange (a : Array α) (beginIdx endIdx : Nat) (p : α → Bool) : Bool :=
!anyRange a beginIdx endIdx (fun v => !p v)

section
variables {m : Type v → Type w} [Monad m]
variable {β : Type v}

@[specialize] private def iterateRevMAux (a : Array α) (f : ∀ (i : Fin a.size), α → β → m β) : ∀ (i : Nat), i ≤ a.size → β → m β
| 0,   h, b => pure b
| j+1, h, b => do
  let i : Fin a.size := ⟨j, h⟩;
  b ← f i (a.get i) b;
  iterateRevMAux a f j (Nat.leOfLt h) b

@[inline] def iterateRevM (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → m β) : m β :=
iterateRevMAux a f a.size (Nat.leRefl _) b

@[inline] def foldrM (f : α → β → m β) (init : β) (a : Array α) : m β :=
iterateRevM a init (fun _ => f)

@[specialize] private def foldrRangeMAux (a : Array α) (f : α → β → m β) (beginIdx : Nat) : ∀ (i : Nat), i ≤ a.size → β → m β
| 0,   h, b => pure b
| j+1, h, b => do
  let i : Fin a.size := ⟨j, h⟩;
  let b ← f (a.get i) b;
  if j == beginIdx then pure b else foldrRangeMAux a f beginIdx j (Nat.leOfLt h) b

@[inline] def foldrRangeM (beginIdx endIdx : Nat) (f : α → β → m β) (ini : β) (a : Array α) : m β :=
if h : endIdx ≤ a.size then
  foldrRangeMAux a f beginIdx endIdx h ini
else
  foldrRangeMAux a f beginIdx a.size (Nat.leRefl _) ini

@[specialize] partial def foldlStepMAux (step : Nat) (a : Array α) (f : β → α → m β) : Nat → β → m β
| i, b =>
  if h : i < a.size then do
    let curr := a.get ⟨i, h⟩;
    b ← f b curr;
    foldlStepMAux step a f (i+step) b
  else
    pure b

@[inline] def foldlStepM (f : β → α → m β) (init : β) (step : Nat) (a : Array α) : m β :=
foldlStepMAux step a f 0 init

end

@[inline] def iterateRev {β} (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → β) : β :=
Id.run $ iterateRevM a b f

@[inline] def foldr {β} (f : α → β → β) (init : β) (a : Array α) : β :=
Id.run $ foldrM f init a

@[inline] def foldrRange {β} (beginIdx endIdx : Nat) (f : α → β → β) (init : β) (a : Array α) : β :=
Id.run $ foldrRangeM beginIdx endIdx f init a

@[inline] def foldlStep {β} (f : β → α → β) (init : β) (step : Nat) (a : Array α) : β :=
Id.run $ foldlStepM f init step a

@[inline] def getEvenElems (a : Array α) : Array α :=
a.foldlStep (fun r a => Array.push r a) empty 2

def toList (a : Array α) : List α :=
a.foldr List.cons []

instance [Repr α] : Repr (Array α) :=
⟨fun a => "#" ++ repr a.toList⟩

instance [ToString α] : ToString (Array α) :=
⟨fun a => "#" ++ toString a.toList⟩

section
variables {m : Type v → Type w} [Monad m]
variable {β : Type v}

@[specialize] unsafe def umapMAux (f : Nat → α → m β) : Nat → Array NonScalar → m (Array PNonScalar.{v})
| i, a =>
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     let v   : NonScalar  := a.get idx;
     let a                := a.set idx (arbitrary _);
     do let newV ← f i (unsafeCast v); umapMAux f (i+1) (a.set idx (unsafeCast newV))
  else
     pure (unsafeCast a)

@[inline] unsafe def umapM (f : α → m β) (as : Array α) : m (Array β) :=
@unsafeCast (m (Array PNonScalar.{v})) (m (Array β)) $ umapMAux (fun i a => f a) 0 (unsafeCast as)

@[inline] unsafe def umapIdxM (f : Nat → α → m β) (as : Array α) : m (Array β) :=
@unsafeCast (m (Array PNonScalar.{v})) (m (Array β)) $ umapMAux f 0 (unsafeCast as)

@[implementedBy Array.umapM] def mapM (f : α → m β) (as : Array α) : m (Array β) :=
as.foldlM (fun bs a => do let b ← f a; pure (bs.push b)) (mkEmpty as.size)

@[implementedBy Array.umapIdxM] def mapIdxM (f : Nat → α → m β) (as : Array α) : m (Array β) :=
as.iterateM (mkEmpty as.size) (fun i a bs => do let b ← f i.val a; pure (bs.push b))
end

section
variables {m : Type u → Type v} [Monad m]

@[inline] def modifyM [Inhabited α] (a : Array α) (i : Nat) (f : α → m α) : m (Array α) :=
if h : i < a.size then do
  let idx : Fin a.size := ⟨i, h⟩;
  let v                := a.get idx;
  let a                := a.set idx (arbitrary α);
  v ← f v;
  pure $ (a.set idx v)
else
  pure a

end

section
variable {β : Type v}

@[inline] def modify [Inhabited α] (a : Array α) (i : Nat) (f : α → α) : Array α :=
Id.run $ a.modifyM i f

@[inline] def modifyOp [Inhabited α] (self : Array α) (idx : Nat) (f : α → α) : Array α :=
self.modify idx f

@[inline] def mapIdx (f : Nat → α → β) (a : Array α) : Array β :=
Id.run $ mapIdxM f a

@[inline] def map (f : α → β) (as : Array α) : Array β :=
Id.run $ mapM f as
end

section
variables {m : Type v → Type w} [Monad m]
variable {β : Type v}

@[specialize]
partial def forMAux (f : α → m PUnit) (a : Array α) : Nat → m PUnit
| i =>
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     let v   : α          := a.get idx;
     do f v; forMAux f a (i+1)
  else
     pure ⟨⟩

@[inline] def forM (f : α → m PUnit) (a : Array α) : m PUnit :=
a.forMAux f 0

@[inline] def forFromM (f : α → m PUnit) (beginIdx : Nat) (a : Array α) : m PUnit :=
a.forMAux f beginIdx

@[specialize]
partial def forRevMAux (f : α → m PUnit) (a : Array α) : forall (i : Nat), i ≤ a.size → m PUnit
| i, h =>
  if hLt : 0 < i then
    have i - 1 < i from sorry -- Nat.subLt hLt (Nat.zeroLtSucc 0);
    have i - 1 < a.size from Nat.ltOfLtOfLe this h;
    let v : α := a.get ⟨i-1, this⟩;
    have i - 1 ≤ a.size from Nat.leOfLt this;
    do f v; forRevMAux f a (i-1) this
  else
     pure ⟨⟩

@[inline] def forRevM (f : α → m PUnit) (a : Array α) : m PUnit :=
a.forRevMAux f a.size (Nat.leRefl _)

end

protected def append (a : Array α) (b : Array α) : Array α :=
b.foldl (fun a v => a.push v) a

instance : HasAppend (Array α) := ⟨Array.append⟩

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def isEqvAux (a b : Array α) (hsz : a.size = b.size) (p : α → α → Bool) : Nat → Bool
| i =>
  if h : i < a.size then
     let aidx : Fin a.size := ⟨i, h⟩;
     let bidx : Fin b.size := ⟨i, hsz ▸ h⟩;
     match p (a.get aidx) (b.get bidx) with
     | true  => isEqvAux a b hsz p (i+1)
     | false => false
  else
    true

@[inline] def isEqv (a b : Array α) (p : α → α → Bool) : Bool :=
if h : a.size = b.size then
  isEqvAux a b h p 0
else
  false

instance [HasBeq α] : HasBeq (Array α) :=
⟨fun a b => isEqv a b HasBeq.beq⟩

-- TODO(Leo): justify termination using wf-rec, and use `swap`
partial def reverseAux : Array α → Nat → Array α
| a, i =>
  let n := a.size;
  if i < n / 2 then
    reverseAux (a.swap! i (n - i - 1)) (i+1)
  else
    a

def reverse (a : Array α) : Array α :=
reverseAux a 0

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def filterAux (p : α → Bool) : Array α → Nat → Nat → Array α
| a, i, j =>
  if h₁ : i < a.size then
    if p (a.get ⟨i, h₁⟩) then
       if h₂ : j < i then
         filterAux p (a.swap ⟨i, h₁⟩ ⟨j, Nat.ltTrans h₂ h₁⟩) (i+1) (j+1)
       else
         filterAux p a (i+1) (j+1)
    else
       filterAux p a (i+1) j
  else
    a.shrink j

@[inline] def filter (p : α → Bool) (as : Array α) : Array α :=
filterAux p as 0 0

@[specialize] partial def filterMAux {m : Type → Type} [Monad m] {α : Type} (p : α → m Bool) : Array α → Nat → Nat → m (Array α)
| a, i, j =>
  if h₁ : i < a.size then
    condM (p (a.get ⟨i, h₁⟩))
     (if h₂ : j < i then
        filterMAux p (a.swap ⟨i, h₁⟩ ⟨j, Nat.ltTrans h₂ h₁⟩) (i+1) (j+1)
      else
        filterMAux p a (i+1) (j+1))
     (filterMAux p a (i+1) j)
  else
    pure $ a.shrink j

@[inline] def filterM {m : Type → Type} [Monad m] {α : Type}  (p : α → m Bool) (as : Array α) : m (Array α) :=
filterMAux p as 0 0

@[inline] def filterFromM {m : Type → Type} [Monad m] {α : Type}  (p : α → m Bool) (beginIdx : Nat) (as : Array α) : m (Array α) :=
filterMAux p as beginIdx beginIdx

@[specialize] partial def filterMapMAux {m : Type u → Type v} [Monad m] {α β : Type u} (f : α → m (Option β)) (as : Array α) : Nat → Array β → m (Array β)
| i, bs =>
  if h : i < as.size then do
    let a := as.get ⟨i, h⟩;
    let b? ← f a;
    match b? with
    | none   => filterMapMAux f as (i+1) bs
    | some b => filterMapMAux f as (i+1) (bs.push b)
  else
    pure bs

@[inline] def filterMapM {m : Type u → Type v} [Monad m] {α β : Type u} (f : α → m (Option β)) (as : Array α) : m (Array β) :=
filterMapMAux f as 0 Array.empty

@[inline] def filterMap {α β : Type u} (f : α → Option β) (as : Array α) : Array β :=
Id.run $ filterMapM f as

partial def indexOfAux {α} [HasBeq α] (a : Array α) (v : α) : Nat → Option (Fin a.size)
| i =>
  if h : i < a.size then
    let idx : Fin a.size := ⟨i, h⟩;
    if a.get idx == v then some idx
    else indexOfAux a v (i+1)
  else none

def indexOf? {α} [HasBeq α] (a : Array α) (v : α) : Option (Fin a.size) :=
indexOfAux a v 0

partial def eraseIdxAux {α} : Nat → Array α → Array α
| i, a =>
  if h : i < a.size then
    let idx  : Fin a.size := ⟨i, h⟩;
    let idx1 : Fin a.size := ⟨i - 1, Nat.ltOfLeOfLt (Nat.predLe i) h⟩;
    eraseIdxAux (i+1) (a.swap idx idx1)
  else
    a.pop

def feraseIdx {α} (a : Array α) (i : Fin a.size) : Array α :=
eraseIdxAux (i.val + 1) a

def eraseIdx {α} (a : Array α) (i : Nat) : Array α :=
if i < a.size then eraseIdxAux (i+1) a else a

theorem szFSwapEq (a : Array α) (i j : Fin a.size) : (a.swap i j).size = a.size :=
rfl

theorem szPopEq (a : Array α) : a.pop.size = a.size - 1 :=
rfl

section
/- Instance for justifying `partial` declaration.
   We should be able to delete it as soon as we restore support for well-founded recursion. -/
instance eraseIdxSzAuxInstance (a : Array α) : Inhabited { r : Array α // r.size = a.size - 1 } :=
⟨⟨a.pop, szPopEq a⟩⟩

partial def eraseIdxSzAux {α} (a : Array α) : ∀ (i : Nat) (r : Array α), r.size = a.size → { r : Array α // r.size = a.size - 1 }
| i, r, heq =>
  if h : i < r.size then
    let idx  : Fin r.size := ⟨i, h⟩;
    let idx1 : Fin r.size := ⟨i - 1, Nat.ltOfLeOfLt (Nat.predLe i) h⟩;
    eraseIdxSzAux a (i+1) (r.swap idx idx1) ((szFSwapEq r idx idx1).trans heq)
  else
    ⟨r.pop, (szPopEq r).trans (heq ▸ rfl)⟩
end

def eraseIdx' {α} (a : Array α) (i : Fin a.size) : { r : Array α // r.size = a.size - 1 } :=
eraseIdxSzAux a (i.val + 1) a rfl

def contains [HasBeq α] (as : Array α) (a : α) : Bool :=
as.any $ fun b => a == b

def elem [HasBeq α] (a : α) (as : Array α) : Bool :=
as.contains a

def erase [HasBeq α] (as : Array α) (a : α) : Array α :=
match as.indexOf? a with
| none   => as
| some i => as.feraseIdx i

partial def insertAtAux {α} (i : Nat) : Array α → Nat → Array α
| as, j =>
  if i == j then as
  else
    let as := as.swap! (j-1) j;
    insertAtAux i as (j-1)

/--
  Insert element `a` at position `i`.
  Pre: `i < as.size` -/
def insertAt {α} (as : Array α) (i : Nat) (a : α) : Array α :=
if i > as.size then panic! "invalid index"
else
  let as := as.push a;
  as.insertAtAux i as.size

theorem ext (a b : Array α) : a.size = b.size → (∀ (i : Nat) (hi₁ : i < a.size) (hi₂ : i < b.size) , a.get ⟨i, hi₁⟩ = b.get ⟨i, hi₂⟩) → a = b :=
match a, b with
| ⟨sz₁, f₁⟩, ⟨sz₂, f₂⟩ => by
  show sz₁ = sz₂ → (∀ (i : Nat) (hi₁ : i < sz₁) (hi₂ : i < sz₂) , f₁ ⟨i, hi₁⟩ = f₂ ⟨i, hi₂⟩) → Array.mk sz₁ f₁ = Array.mk sz₂ f₂
  intro h₁ h₂
  subst h₁
  have f₁ = f₂ from funext $ fun ⟨i, hi₁⟩ => h₂ i hi₁ hi₁
  subst this
  exact rfl

theorem extLit {α : Type u} {n : Nat}
    (a b : Array α)
    (hsz₁ : a.size = n) (hsz₂ : b.size = n)
    (h : ∀ (i : Nat) (hi : i < n), a.getLit i hsz₁ hi = b.getLit i hsz₂ hi) : a = b :=
Array.ext a b (hsz₁.trans hsz₂.symm) $ fun i hi₁ hi₂ => h i (hsz₁ ▸ hi₁)

end Array

export Array (mkArray)

@[inlineIfReduce] def List.toArrayAux {α : Type u} : List α → Array α → Array α
| [],    r => r
| a::as, r => toArrayAux as (r.push a)

@[inlineIfReduce] def List.redLength {α : Type u} : List α → Nat
| []    => 0
| _::as => as.redLength + 1

@[inline, matchPattern] def List.toArray {α : Type u} (as : List α) : Array α :=
as.toArrayAux (Array.mkEmpty as.redLength)

namespace Array

def toListLitAux {α : Type u} (a : Array α) (n : Nat) (hsz : a.size = n) : ∀ (i : Nat), i ≤ a.size → List α → List α
| 0,     hi, acc => acc
| (i+1), hi, acc => toListLitAux a n hsz i (Nat.leOfSuccLe hi) (a.getLit i hsz (Nat.ltOfLtOfEq (Nat.ltOfLtOfLe (Nat.ltSuccSelf i) hi) hsz) :: acc)

def toArrayLit {α : Type u} (a : Array α) (n : Nat) (hsz : a.size = n) : Array α :=
List.toArray $ toListLitAux a n hsz n (hsz ▸ Nat.leRefl _) []

theorem toArrayLitEq {α : Type u} (a : Array α) (n : Nat) (hsz : a.size = n) : a = toArrayLit a n hsz :=
-- TODO: this is painful to prove without proper automation
sorry
/-
First, we need to prove
∀ i j acc, i ≤ a.size → (toListLitAux a n hsz (i+1) hi acc).index j = if j < i then a.getLit j hsz _ else acc.index (j - i)
by induction

Base case is trivial
(j : Nat) (acc : List α) (hi : 0 ≤ a.size)
     |- (toListLitAux a n hsz 0 hi acc).index j = if j < 0 then a.getLit j hsz _ else acc.index (j - 0)
...  |- acc.index j = acc.index j

Induction

(j : Nat) (acc : List α) (hi : i+1 ≤ a.size)
      |- (toListLitAux a n hsz (i+1) hi acc).index j = if j < i + 1 then a.getLit j hsz _ else acc.index (j - (i + 1))
  ... |- (toListLitAux a n hsz i hi' (a.getLit i hsz _ :: acc)).index j = if j < i + 1 then a.getLit j hsz _ else acc.index (j - (i + 1))  * by def
  ... |- if j < i     then a.getLit j hsz _ else (a.getLit i hsz _ :: acc).index (j-i)    * by induction hypothesis
         =
         if j < i + 1 then a.getLit j hsz _ else acc.index (j - (i + 1))
If j < i, then both are a.getLit j hsz _
If j = i, then lhs reduces else-branch to (a.getLit i hsz _) and rhs is then-brachn (a.getLit i hsz _)
If j >= i + 1, we use
   - j - i >= 1 > 0
   - (a::as).index k = as.index (k-1) If k > 0
   - j - (i + 1) = (j - i) - 1
   Then lhs = (a.getLit i hsz _ :: acc).index (j-i) = acc.index (j-i-1) = acc.index (j-(i+1)) = rhs

With this proof, we have

∀ j, j < n → (toListLitAux a n hsz n _ []).index j = a.getLit j hsz _

We also need

- (toListLitAux a n hsz n _ []).length = n
- j < n -> (List.toArray as).getLit j _ _ = as.index j

Then using Array.extLit, we have that a = List.toArray $ toListLitAux a n hsz n _ []
-/

@[specialize] def getMax? {α : Type u} (as : Array α) (lt : α → α → Bool) : Option α :=
if h : 0 < as.size then
  let a0 := as.get ⟨0, h⟩;
  some $ as.foldlFrom (fun best a => if lt best a then a else best) a0 1
else
  none

@[specialize] partial def partitionAux {α : Type u} (p : α → Bool) (as : Array α) : Nat → Array α → Array α → Array α × Array α
| i, bs, cs =>
  if h : i < as.size then
    let a := as.get ⟨i, h⟩;
    match p a with
    | true  => partitionAux p as (i+1) (bs.push a) cs
    | false => partitionAux p as (i+1) bs (cs.push a)
  else
    (bs, cs)

@[inline] def partition {α : Type u} (p : α → Bool) (as : Array α) : Array α × Array α :=
partitionAux p as 0 #[] #[]

partial def isPrefixOfAux {α : Type u} [HasBeq α] (as bs : Array α) (hle : as.size ≤ bs.size) : Nat → Bool
| i =>
  if h : i < as.size then
    let a := as.get ⟨i, h⟩;
    let b := bs.get ⟨i, Nat.ltOfLtOfLe h hle⟩;
    if a == b then
      isPrefixOfAux as bs hle (i+1)
    else
      false
  else
    true

/- Return true iff `as` is a prefix of `bs` -/
def isPrefixOf  {α : Type u} [HasBeq α] (as bs : Array α) : Bool :=
if h : as.size ≤ bs.size then
  isPrefixOfAux as bs h 0
else
  false

private def allDiffAuxAux {α} [HasBeq α] (as : Array α) (a : α) : forall (i : Nat), i < as.size → Bool
| 0,   h => true
| i+1, h =>
  have i < as.size from Nat.ltTrans (Nat.ltSuccSelf _) h;
  a != as.get ⟨i, this⟩ && allDiffAuxAux as a i this

private partial def allDiffAux {α} [HasBeq α] (as : Array α) : Nat → Bool
| i =>
  if h : i < as.size then
    allDiffAuxAux as (as.get ⟨i, h⟩) i h && allDiffAux as (i+1)
  else
    true

def allDiff {α} [HasBeq α] (as : Array α) : Bool :=
allDiffAux as 0

@[specialize] partial def zipWithAux {α β γ} (f : α → β → γ) (as : Array α) (bs : Array β) : Nat → Array γ → Array γ
| i, cs =>
  if h : i < as.size then
    let a := as.get ⟨i, h⟩;
    if h : i < bs.size then
      let b := bs.get ⟨i, h⟩;
      zipWithAux f as bs (i+1) (cs.push $ f a b)
    else
      cs
  else
    cs

@[inline] def zipWith {α β γ} (as : Array α) (bs : Array β) (f : α → β → γ) : Array γ :=
zipWithAux f as bs 0 #[]

def zip {α β} (as : Array α) (bs : Array β) : Array (α × β) :=
zipWith as bs Prod.mk

end Array
