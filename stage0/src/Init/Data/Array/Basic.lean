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
import Init.Data.ToString
import Init.Control.Id
import Init.Util
universes u v w

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
def mkEmpty (c : @& Nat) : Array α :=
{ sz := 0,
  data := fun ⟨x, h⟩ => absurd h (Nat.notLtZero x) }

@[extern "lean_array_push"]
def push (a : Array α) (v : α) : Array α :=
{ sz   := Nat.succ a.sz,
  data := fun ⟨j, h₁⟩ =>
    if h₂ : j = a.sz then v
    else a.data ⟨j, Nat.ltOfLeOfNe (Nat.leOfLtSucc h₁) h₂⟩ }

@[extern "lean_mk_array"]
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

@[extern "lean_array_fset"]
def set (a : Array α) (i : @& Fin a.size) (v : α) : Array α :=
{ sz   := a.sz,
  data := fun j => if h : i = j then v else a.data j }

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
def pop (a : Array α) : Array α :=
{ sz   := Nat.pred a.size,
  data := fun ⟨j, h⟩ => a.get ⟨j, Nat.ltOfLtOfLe h (Nat.predLe _)⟩ }

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
     f idx (a.get idx) b >>= iterateMAux (i+1)
  else pure b

@[inline] def iterateM (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → m β) : m β :=
iterateMAux a f 0 b

@[inline] def foldlM (f : β → α → m β) (init : β) (a : Array α) : m β :=
iterateM a init (fun _ b a => f a b)

@[inline] def foldlFromM (f : β → α → m β) (init : β) (a : Array α) (beginIdx : Nat := 0) : m β :=
iterateMAux a (fun _ b a => f a b) beginIdx init

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def iterateM₂Aux (a₁ : Array α) (a₂ : Array σ) (f : ∀ (i : Fin a₁.size), α → σ → β → m β) : Nat → β → m β
| i, b =>
  if h₁ : i < a₁.size then
     let idx₁ : Fin a₁.size := ⟨i, h₁⟩;
     if h₂ : i < a₂.size then
       let idx₂ : Fin a₂.size := ⟨i, h₂⟩;
       f idx₁ (a₁.get idx₁) (a₂.get idx₂) b >>= iterateM₂Aux (i+1)
     else pure b
  else pure b

@[inline] def iterateM₂ (a₁ : Array α) (a₂ : Array σ) (b : β) (f : ∀ (i : Fin a₁.size), α → σ → β → m β) : m β :=
iterateM₂Aux a₁ a₂ f 0 b

@[inline] def foldlM₂ (f : β → α → σ → m β) (b : β) (a₁ : Array α) (a₂ : Array σ): m β :=
iterateM₂ a₁ a₂ b (fun _ a₁ a₂ b => f b a₁ a₂)

-- TODO(Leo): justify termination using wf-rec
@[specialize] partial def findMAux (a : Array α) (f : α → m (Option β)) : Nat → m (Option β)
| i =>
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     do r ← f (a.get idx);
        match r with
        | some v => pure r
        | none   => findMAux (i+1)
  else pure none

@[inline] def findM? (a : Array α) (f : α → m (Option β)) : m (Option β) :=
findMAux a f 0

@[specialize] partial def findRevMAux (a : Array α) (f : α → m (Option β)) : ∀ (idx : Nat), idx ≤ a.size → m (Option β)
| i, h =>
  if hLt : 0 < i then
    have i - 1 < i from Nat.subLt hLt (Nat.zeroLtSucc 0);
    have i - 1 < a.size from Nat.ltOfLtOfLe this h;
    let idx : Fin a.size := ⟨i - 1, this⟩;
    do
      r ← f (a.get idx);
      match r with
      | some v => pure r
      | none   =>
        have i - 1 ≤ a.size from Nat.leOfLt this;
        findRevMAux (i-1) this
  else pure none

@[inline] def findRevM? (a : Array α) (f : α → m (Option β)) : m (Option β) :=
findRevMAux a f a.size (Nat.leRefl _)

end

section
variables {β : Type w} {σ : Type u}

@[inline] def iterate (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → β) : β :=
Id.run $ iterateMAux a f 0 b

@[inline] def iterateFrom (a : Array α) (b : β) (i : Nat) (f : ∀ (i : Fin a.size), α → β → β) : β :=
Id.run $ iterateMAux a f i b

@[inline] def foldl (f : β → α → β) (init : β) (a : Array α) : β :=
iterate a init (fun _ a b => f b a)

@[inline] def foldlFrom (f : β → α → β) (init : β) (a : Array α) (beginIdx : Nat := 0) : β :=
Id.run $ foldlFromM f init a beginIdx

@[inline] def iterate₂ (a₁ : Array α) (a₂ : Array σ) (b : β) (f : ∀ (i : Fin a₁.size), α → σ → β → β) : β :=
Id.run $ iterateM₂Aux a₁ a₂ f 0 b

@[inline] def foldl₂ (f : β → α → σ → β) (b : β) (a₁ : Array α) (a₂ : Array σ) : β :=
iterate₂ a₁ a₂ b (fun _ a₁ a₂ b => f b a₁ a₂)

@[inline] def find? (a : Array α) (f : α → Option β) : Option β :=
Id.run $ findMAux a f 0

@[inline] def find! [Inhabited β] (a : Array α) (f : α → Option β) : β :=
match find? a f with
| some b => b
| none   => panic! "failed to find element"

@[inline] def findRev? (a : Array α) (f : α → Option β) : Option β :=
Id.run $ findRevMAux a f a.size (Nat.leRefl _)

@[inline] def findRev! [Inhabited β] (a : Array α) (f : α → Option β) : β :=
match findRev? a f with
| some b => b
| none   => panic! "failed to find element"

@[specialize] partial def findIdxAux (a : Array α) (p : α → Bool) : Nat → Option Nat
| i =>
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     if p (a.get idx) then some i
     else findIdxAux (i+1)
  else none

@[inline] def findIdx? (a : Array α) (p : α → Bool) : Option Nat :=
findIdxAux a p 0

@[inline] def findIdx! (a : Array α) (p : α → Bool) : Nat :=
match findIdxAux a p 0 with
| some i => i
| none   => panic! "failed to find element"

end

section
variables {m : Type → Type w} [Monad m]

@[specialize] partial def anyRangeMAux (a : Array α) (endIdx : Nat) (hlt : endIdx ≤ a.size) (p : α → m Bool) : Nat → m Bool
| i =>
  if h : i < endIdx then
     let idx : Fin a.size := ⟨i, Nat.ltOfLtOfLe h hlt⟩;
     do b ← p (a.get idx);
     match b with
     | true  => pure true
     | false => anyRangeMAux (i+1)
  else pure false

@[inline] def anyM (a : Array α) (p : α → m Bool) : m Bool :=
anyRangeMAux a a.size (Nat.leRefl _) p 0

@[inline] def allM (a : Array α) (p : α → m Bool) : m Bool := do
b ← anyM a (fun v => do b ← p v; pure (!b)); pure (!b)

@[inline] def anyRangeM (a : Array α) (beginIdx endIdx : Nat) (p : α → m Bool) : m Bool :=
if h : endIdx ≤ a.size then
  anyRangeMAux a endIdx h p beginIdx
else
  anyRangeMAux a a.size (Nat.leRefl _) p beginIdx

@[inline] def allRangeM (a : Array α) (beginIdx endIdx : Nat) (p : α → m Bool) : m Bool := do
b ← anyRangeM a beginIdx endIdx (fun v => do b ← p v; pure b); pure (!b)

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
  iterateRevMAux j (Nat.leOfLt h) b

@[inline] def iterateRevM (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → m β) : m β :=
iterateRevMAux a f a.size (Nat.leRefl _) b

@[inline] def foldrM (f : α → β → m β) (init : β) (a : Array α) : m β :=
iterateRevM a init (fun _ => f)

end

@[inline] def iterateRev {β} (a : Array α) (b : β) (f : ∀ (i : Fin a.size), α → β → β) : β :=
Id.run $ iterateRevM a b f

@[inline] def foldr {β} (f : α → β → β) (init : β) (a : Array α) : β :=
Id.run $ foldrM f init a

def toList (a : Array α) : List α :=
a.foldr List.cons []

instance [HasRepr α] : HasRepr (Array α) :=
⟨fun a => "#" ++ repr a.toList⟩

instance [HasToString α] : HasToString (Array α) :=
⟨fun a => "#" ++ toString a.toList⟩

section
variables {m : Type u → Type w} [Monad m]
variable {β : Type u}

@[specialize] unsafe partial def umapMAux (f : Nat → α → m β) : Nat → Array α → m (Array β)
| i, a =>
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     let v   : α          := a.get idx;
     let a                := a.set idx (@unsafeCast _ _ ⟨v⟩ ());
     do newV ← f i v; umapMAux (i+1) (a.set idx (@unsafeCast _ _ ⟨v⟩ newV))
  else
     pure (unsafeCast a)

@[inline] unsafe partial def umapM (f : α → m β) (as : Array α) : m (Array β) :=
umapMAux (fun i a => f a) 0 as

@[inline] unsafe partial def umapIdxM (f : Nat → α → m β) (as : Array α) : m (Array β) :=
umapMAux f 0 as

@[implementedBy Array.umapM] def mapM (f : α → m β) (as : Array α) : m (Array β) :=
as.foldlM (fun bs a => do b ← f a; pure (bs.push b)) (mkEmpty as.size)

@[implementedBy Array.umapIdxM] def mapIdxM (f : Nat → α → m β) (as : Array α) : m (Array β) :=
as.iterateM (mkEmpty as.size) (fun i a bs => do b ← f i.val a; pure (bs.push b))
end

section
variables {m : Type u → Type v} [Monad m]
variable {β : Type u}

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
variable {β : Type u}

@[inline] def modify [Inhabited α] (a : Array α) (i : Nat) (f : α → α) : Array α :=
Id.run $ a.modifyM i f

@[inline] def mapIdx (f : Nat → α → β) (a : Array α) : Array β :=
Id.run $ mapIdxM f a

@[inline] def map (f : α → β) (as : Array α) : Array β :=
Id.run $ mapM f as
end

section
variables {m : Type u → Type v} [Monad m]
variable {β : Type u}

@[specialize]
partial def forMAux {α : Type w} {β : Type u} (f : α → m β) (a : Array α) : Nat → m PUnit
| i =>
  if h : i < a.size then
     let idx : Fin a.size := ⟨i, h⟩;
     let v   : α          := a.get idx;
     do f v; forMAux (i+1)
  else
     pure ⟨⟩

@[inline] def forM {α : Type w} {β : Type u} (f : α → m β) (a : Array α) : m PUnit :=
a.forMAux f 0

@[specialize]
partial def forRevMAux {α : Type w} {β : Type u} (f : α → m β) (a : Array α) : forall (i : Nat), i ≤ a.size → m PUnit
| i, h =>
  if hLt : 0 < i then
    have i - 1 < i from Nat.subLt hLt (Nat.zeroLtSucc 0);
    have i - 1 < a.size from Nat.ltOfLtOfLe this h;
    let v : α := a.get ⟨i-1, this⟩;
    have i - 1 ≤ a.size from Nat.leOfLt this;
    do f v; forRevMAux (i-1) this
  else
     pure ⟨⟩

@[inline] def forRevM {α : Type w} {β : Type u} (f : α → m β) (a : Array α) : m PUnit :=
a.forRevMAux f a.size (Nat.leRefl _)

end

-- TODO(Leo): justify termination using wf-rec
partial def extractAux (a : Array α) : Nat → ∀ (e : Nat), e ≤ a.size → Array α → Array α
| i, e, hle, r =>
  if hlt : i < e then
    let idx : Fin a.size := ⟨i, Nat.ltOfLtOfLe hlt hle⟩;
    extractAux (i+1) e hle (r.push (a.get idx))
 else r

def extract (a : Array α) (b e : Nat) : Array α :=
let r : Array α := mkEmpty (e - b);
if h : e ≤ a.size then extractAux a b e h r
else r

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
     | true  => isEqvAux (i+1)
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
         filterAux (a.swap ⟨i, h₁⟩ ⟨j, Nat.ltTrans h₂ h₁⟩) (i+1) (j+1)
       else
         filterAux a (i+1) (j+1)
    else
       filterAux a (i+1) j
  else
    a.shrink j

@[inline] def filter (p : α → Bool) (as : Array α) : Array α :=
filterAux p as 0 0

partial def indexOfAux {α} [HasBeq α] (a : Array α) (v : α) : Nat → Option (Fin a.size)
| i =>
  if h : i < a.size then
    let idx : Fin a.size := ⟨i, h⟩;
    if a.get idx == v then some idx
    else indexOfAux (i+1)
  else none

def indexOf {α} [HasBeq α] (a : Array α) (v : α) : Option (Fin a.size) :=
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
    eraseIdxSzAux (i+1) (r.swap idx idx1) ((szFSwapEq r idx idx1).trans heq)
  else
    ⟨r.pop, (szPopEq r).trans (heq ▸ rfl)⟩
end

def eraseIdx' {α} (a : Array α) (i : Fin a.size) : { r : Array α // r.size = a.size - 1 } :=
eraseIdxSzAux a (i.val + 1) a rfl

def contains [HasBeq α] (as : Array α) (a : α) : Bool :=
as.any $ fun b => a == b

partial def insertAtAux {α} (i : Nat) : Array α → Nat → Array α
| as, j =>
  if i == j then as
  else
    let as := as.swap! (j-1) j;
    insertAtAux as (j-1)

/--
  Insert element `a` at position `i`.
  Pre: `i < as.size` -/
def insertAt {α} (as : Array α) (i : Nat) (a : α) : Array α :=
if i > as.size then panic! "invalid index"
else
  let as := as.push a;
  as.insertAtAux i as.size

end Array

export Array (mkArray)

@[inlineIfReduce] def List.toArrayAux {α : Type u} : List α → Array α → Array α
| [],    r => r
| a::as, r => List.toArrayAux as (r.push a)

@[inlineIfReduce] def List.redLength {α : Type u} : List α → Nat
| []    => 0
| _::as => as.redLength + 1

@[inline] def List.toArray {α : Type u} (as : List α) : Array α :=
as.toArrayAux (Array.mkEmpty as.redLength)
