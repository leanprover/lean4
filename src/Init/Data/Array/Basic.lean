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
import Init.Util
universe u v w

namespace Array
variable {α : Type u}

@[extern "lean_mk_array"]
def mkArray {α : Type u} (n : Nat) (v : α) : Array α := {
  data := List.replicate n v
}

@[simp] theorem size_mkArray (n : Nat) (v : α) : (mkArray n v).size = n :=
  List.length_replicate ..

instance : EmptyCollection (Array α) := ⟨Array.empty⟩
instance : Inhabited (Array α) where
  default := Array.empty

def isEmpty (a : Array α) : Bool :=
  a.size = 0

def singleton (v : α) : Array α :=
  mkArray 1 v

/- Low-level version of `fget` which is as fast as a C array read.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `fget` may be slightly slower than `uget`. -/
@[extern "lean_array_uget"]
def uget (a : @& Array α) (i : USize) (h : i.toNat < a.size) : α :=
  a.get ⟨i.toNat, h⟩

def back [Inhabited α] (a : Array α) : α :=
  a.get! (a.size - 1)

def get? (a : Array α) (i : Nat) : Option α :=
  if h : i < a.size then some (a.get ⟨i, h⟩) else none

def back? (a : Array α) : Option α :=
  a.get? (a.size - 1)

-- auxiliary declaration used in the equation compiler when pattern matching array literals.
abbrev getLit {α : Type u} {n : Nat} (a : Array α) (i : Nat) (h₁ : a.size = n) (h₂ : i < n) : α :=
  a.get ⟨i, h₁.symm ▸ h₂⟩

@[simp] theorem size_set (a : Array α) (i : Fin a.size) (v : α) : (set a i v).size = a.size :=
  List.length_set ..

@[simp] theorem size_push (a : Array α) (v : α) : (push a v).size = a.size + 1 :=
  List.length_concat ..

/- Low-level version of `fset` which is as fast as a C array fset.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `fset` may be slightly slower than `uset`. -/
@[extern "lean_array_uset"]
def uset (a : Array α) (i : USize) (v : α) (h : i.toNat < a.size) : Array α :=
  a.set ⟨i.toNat, h⟩ v

@[extern "lean_array_fswap"]
def swap (a : Array α) (i j : @& Fin a.size) : Array α :=
  let v₁ := a.get i
  let v₂ := a.get j
  let a'  := a.set i v₂
  a'.set (size_set a i v₂ ▸ j) v₁

@[extern "lean_array_swap"]
def swap! (a : Array α) (i j : @& Nat) : Array α :=
  if h₁ : i < a.size then
  if h₂ : j < a.size then swap a ⟨i, h₁⟩ ⟨j, h₂⟩
  else panic! "index out of bounds"
  else panic! "index out of bounds"

@[inline] def swapAt (a : Array α) (i : Fin a.size) (v : α) : α × Array α :=
  let e := a.get i
  let a := a.set i v
  (e, a)

@[inline]
def swapAt! (a : Array α) (i : Nat) (v : α) : α × Array α :=
  if h : i < a.size then
    swapAt a ⟨i, h⟩ v
  else
    have : Inhabited α := ⟨v⟩
    panic! ("index " ++ toString i ++ " out of bounds")

@[extern "lean_array_pop"]
def pop (a : Array α) : Array α := {
  data := a.data.dropLast
}

def shrink (a : Array α) (n : Nat) : Array α :=
  let rec loop
    | 0,   a => a
    | n+1, a => loop n a.pop
  loop (a.size - n) a

@[inline]
def modifyM [Monad m] [Inhabited α] (a : Array α) (i : Nat) (f : α → m α) : m (Array α) := do
  if h : i < a.size then
    let idx : Fin a.size := ⟨i, h⟩
    let v                := a.get idx
    let a'               := a.set idx arbitrary
    let v ← f v
    pure <| a'.set (size_set a .. ▸ idx) v
  else
    pure a

@[inline]
def modify [Inhabited α] (a : Array α) (i : Nat) (f : α → α) : Array α :=
  Id.run <| a.modifyM i f

@[inline]
def modifyOp [Inhabited α] (self : Array α) (idx : Nat) (f : α → α) : Array α :=
  self.modify idx f

/-
  We claim this unsafe implementation is correct because an array cannot have more than `usizeSz` elements in our runtime.

  This kind of low level trick can be removed with a little bit of compiler support. For example, if the compiler simplifies `as.size < usizeSz` to true. -/
@[inline] unsafe def forInUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  let sz := USize.ofNat as.size
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := as.uget i lcProof
      match (← f a b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop 0 b

-- Move?
private theorem zero_lt_of_lt : {a b : Nat} → a < b → 0 < b
  | 0,   _, h => h
  | a+1, b, h =>
    have : a < b := Nat.lt_trans (Nat.lt_succ_self _) h
    zero_lt_of_lt this

/- Reference implementation for `forIn` -/
@[implementedBy Array.forInUnsafe]
protected def forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : as.size - 1 < as.size     := Nat.sub_lt (zero_lt_of_lt h') (by decide)
      have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
      match (← f (as.get ⟨as.size - 1 - i, this⟩) b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

instance : ForIn m (Array α) α where
  forIn := Array.forIn

/- See comment at forInUnsafe -/
@[inline]
unsafe def foldlMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (as : Array α) (start := 0) (stop := as.size) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i+1) stop (← f b (as.uget i lcProof))
  if start < stop then
    if stop ≤ as.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else
    pure init

/- Reference implementation for `foldlM` -/
@[implementedBy foldlMUnsafe]
def foldlM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (as : Array α) (start := 0) (stop := as.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => pure b
        | i'+1 =>
          loop i' (j+1) (← f b (as.get ⟨j, Nat.lt_of_lt_of_le hlt h⟩))
      else
        pure b
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.le_refl _)

/- See comment at forInUnsafe -/
@[inline]
unsafe def foldrMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) (init : β) (as : Array α) (start := as.size) (stop := 0) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i-1) stop (← f (as.uget (i-1) lcProof) b)
  if start ≤ as.size then
    if stop < start then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else if stop < as.size then
    fold (USize.ofNat as.size) (USize.ofNat stop) init
  else
    pure init

/- Reference implementation for `foldrM` -/
@[implementedBy foldrMUnsafe]
def foldrM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) (init : β) (as : Array α) (start := as.size) (stop := 0) : m β :=
  let rec fold (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    if i == stop then
      pure b
    else match i, h with
      | 0, _   => pure b
      | i+1, h =>
        have : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
        fold i (Nat.le_of_lt this) (← f (as.get ⟨i, this⟩) b)
  if h : start ≤ as.size then
    if stop < start then
      fold start h init
    else
      pure init
  else if stop < as.size then
    fold as.size (Nat.le_refl _) init
  else
    pure init

/- See comment at forInUnsafe -/
@[inline]
unsafe def mapMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m β) (as : Array α) : m (Array β) :=
  let sz := USize.ofNat as.size
  let rec @[specialize] map (i : USize) (r : Array NonScalar) : m (Array PNonScalar.{v}) := do
    if i < sz then
     let v    := r.uget i lcProof
     let r    := r.uset i arbitrary lcProof
     let vNew ← f (unsafeCast v)
     map (i+1) (r.uset i (unsafeCast vNew) lcProof)
    else
     pure (unsafeCast r)
  unsafeCast <| map 0 (unsafeCast as)

/- Reference implementation for `mapM` -/
@[implementedBy mapMUnsafe]
def mapM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m β) (as : Array α) : m (Array β) :=
  as.foldlM (fun bs a => do let b ← f a; pure (bs.push b)) (mkEmpty as.size)

@[inline]
def mapIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (f : Fin as.size → α → m β) : m (Array β) :=
  let rec @[specialize] map (i : Nat) (j : Nat) (inv : i + j = as.size) (bs : Array β) : m (Array β) := do
    match i, inv with
    | 0,    _  => pure bs
    | i+1, inv =>
      have : j < as.size := by
        rw [← inv, Nat.add_assoc, Nat.add_comm 1 j, Nat.add_comm]
        apply Nat.le_add_right
      let idx : Fin as.size := ⟨j, this⟩
      have : i + (j + 1) = as.size := by rw [← inv, Nat.add_comm j 1, Nat.add_assoc]
      map i (j+1) this (bs.push (← f idx (as.get idx)))
  map as.size 0 rfl (mkEmpty as.size)

@[inline]
def findSomeM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (f : α → m (Option β)) : m (Option β) := do
  for a in as do
    match (← f a) with
    | some b => return b
    | _      => pure ⟨⟩
  return none

@[inline]
def findM? {α : Type} {m : Type → Type} [Monad m] (as : Array α) (p : α → m Bool) : m (Option α) := do
  for a in as do
    if (← p a) then
      return a
  return none

@[inline]
def findIdxM? [Monad m] (as : Array α) (p : α → m Bool) : m (Option Nat) := do
  let mut i := 0
  for a in as do
    if (← p a) then
      return some i
    i := i + 1
  return none

@[inline]
unsafe def anyMUnsafe {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  let rec @[specialize] any (i : USize) (stop : USize) : m Bool := do
    if i == stop then
      pure false
    else
      if (← p (as.uget i lcProof)) then
        pure true
      else
        any (i+1) stop
  if start < stop then
    if stop ≤ as.size then
      any (USize.ofNat start) (USize.ofNat stop)
    else
      pure false
  else
    pure false

@[implementedBy anyMUnsafe]
def anyM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  let any (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) : m Bool := do
      if hlt : j < stop then
        match i with
        | 0    => pure false
        | i'+1 =>
          if (← p (as.get ⟨j, Nat.lt_of_lt_of_le hlt h⟩)) then
            pure true
          else
            loop i' (j+1)
      else
        pure false
    loop (stop - start) start
  if h : stop ≤ as.size then
    any stop h
  else
    any as.size (Nat.le_refl _)

@[inline]
def allM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  return !(← as.anyM fun v => return !(← p v))

@[inline]
def findSomeRevM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (f : α → m (Option β)) : m (Option β) :=
  let rec @[specialize] find : (i : Nat) → i ≤ as.size → m (Option β)
    | 0,   h => pure none
    | i+1, h => do
      have : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
      let r ← f (as.get ⟨i, this⟩)
      match r with
      | some v => pure r
      | none   =>
        have : i ≤ as.size := Nat.le_of_lt this
        find i this
  find as.size (Nat.le_refl _)

@[inline]
def findRevM? {α : Type} {m : Type → Type w} [Monad m] (as : Array α) (p : α → m Bool) : m (Option α) :=
  as.findSomeRevM? fun a => return if (← p a) then some a else none

@[inline]
def forM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Array α) (start := 0) (stop := as.size) : m PUnit :=
  as.foldlM (fun _ => f) ⟨⟩ start stop

@[inline]
def forRevM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Array α) (start := as.size) (stop := 0) : m PUnit :=
  as.foldrM (fun a _ => f a) ⟨⟩ start stop

@[inline]
def foldl {α : Type u} {β : Type v} (f : β → α → β) (init : β) (as : Array α) (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlM f init start stop

@[inline]
def foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β) (as : Array α) (start := as.size) (stop := 0) : β :=
  Id.run <| as.foldrM f init start stop

@[inline]
def map {α : Type u} {β : Type v} (f : α → β) (as : Array α) : Array β :=
  Id.run <| as.mapM f

@[inline]
def mapIdx {α : Type u} {β : Type v} (as : Array α) (f : Fin as.size → α → β) : Array β :=
  Id.run <| as.mapIdxM f

@[inline]
def find? {α : Type} (as : Array α) (p : α → Bool) : Option α :=
  Id.run <| as.findM? p

@[inline]
def findSome? {α : Type u} {β : Type v} (as : Array α) (f : α → Option β) : Option β :=
  Id.run <| as.findSomeM? f

@[inline]
def findSome! {α : Type u} {β : Type v} [Inhabited β] (a : Array α) (f : α → Option β) : β :=
  match findSome? a f with
  | some b => b
  | none   => panic! "failed to find element"

@[inline]
def findSomeRev? {α : Type u} {β : Type v} (as : Array α) (f : α → Option β) : Option β :=
  Id.run <| as.findSomeRevM? f

@[inline]
def findRev? {α : Type} (as : Array α) (p : α → Bool) : Option α :=
  Id.run <| as.findRevM? p

@[inline]
def findIdx? {α : Type u} (as : Array α) (p : α → Bool) : Option Nat :=
  let rec loop (i : Nat) (j : Nat) (inv : i + j = as.size) : Option Nat :=
    if hlt : j < as.size then
      match i, inv with
      | 0, inv => by
        apply False.elim
        rw [Nat.zero_add] at inv
        rw [inv] at hlt
        exact absurd hlt (Nat.lt_irrefl _)
      | i+1, inv =>
        if p (as.get ⟨j, hlt⟩) then
          some j
        else
          have : i + (j+1) = as.size := by
            rw [← inv, Nat.add_comm j 1, Nat.add_assoc]
          loop i (j+1) this
    else
      none
  loop as.size 0 rfl

def getIdx? [BEq α] (a : Array α) (v : α) : Option Nat :=
a.findIdx? fun a => a == v

@[inline]
def any (as : Array α) (p : α → Bool) (start := 0) (stop := as.size) : Bool :=
  Id.run <| as.anyM p start stop

@[inline]
def all (as : Array α) (p : α → Bool) (start := 0) (stop := as.size) : Bool :=
  Id.run <| as.allM p start stop

def contains [BEq α] (as : Array α) (a : α) : Bool :=
  as.any fun b => a == b

def elem [BEq α] (a : α) (as : Array α) : Bool :=
  as.contains a

-- TODO(Leo): justify termination using wf-rec, and use `swap`
partial def reverse (as : Array α) : Array α :=
  let n   := as.size
  let mid := n / 2
  let rec rev (as : Array α) (i : Nat) :=
    if i < mid then
      rev (as.swap! i (n - i - 1)) (i+1)
    else
      as
  rev as 0

@[inline] def getEvenElems (as : Array α) : Array α :=
  (·.2) <| as.foldl (init := (true, Array.empty)) fun (even, r) a =>
    if even then
      (false, r.push a)
    else
      (true, r)

@[export lean_array_to_list]
def toList (as : Array α) : List α :=
  as.foldr List.cons []

instance {α : Type u} [Repr α] : Repr (Array α) where
  reprPrec a n :=
    let _ : Std.ToFormat α := ⟨repr⟩
    if a.size == 0 then
      "#[]"
    else
      Std.Format.bracketFill "#[" (Std.Format.joinSep (toList a) ("," ++ Std.Format.line)) "]"

instance [ToString α] : ToString (Array α) where
  toString a := "#" ++ toString a.toList

protected def append (as : Array α) (bs : Array α) : Array α :=
  bs.foldl (init := as) fun r v => r.push v

instance : Append (Array α) := ⟨Array.append⟩

protected def appendList (as : Array α) (bs : List α) : Array α :=
  bs.foldl (init := as) fun r v => r.push v

instance : HAppend (Array α) (List α) (Array α) := ⟨Array.appendList⟩

@[inline]
def concatMapM [Monad m] (f : α → m (Array β)) (as : Array α) : m (Array β) :=
  as.foldlM (init := empty) fun bs a => do return bs ++ (← f a)

@[inline]
def concatMap (f : α → Array β) (as : Array α) : Array β :=
  as.foldl (init := empty) fun bs a => bs ++ f a

end Array

export Array (mkArray)

syntax "#[" sepBy(term, ", ") "]" : term

macro_rules
  | `(#[ $elems,* ]) => `(List.toArray [ $elems,* ])

namespace Array

-- TODO(Leo): cleanup
@[specialize]
partial def isEqvAux (a b : Array α) (hsz : a.size = b.size) (p : α → α → Bool) (i : Nat) : Bool :=
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

instance [BEq α] : BEq (Array α) :=
  ⟨fun a b => isEqv a b BEq.beq⟩

@[inline]
def filter (p : α → Bool) (as : Array α) (start := 0) (stop := as.size) : Array α :=
  as.foldl (init := #[]) (start := start) (stop := stop) fun r a =>
    if p a then r.push a else r

@[inline]
def filterM [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m (Array α) :=
  as.foldlM (init := #[]) (start := start) (stop := stop) fun r a => do
    if (← p a) then r.push a else r

@[specialize]
def filterMapM [Monad m] (f : α → m (Option β)) (as : Array α) (start := 0) (stop := as.size) : m (Array β) :=
  as.foldlM (init := #[]) (start := start) (stop := stop) fun bs a => do
    match (← f a) with
    | some b => pure (bs.push b)
    | none   => pure bs

@[inline]
def filterMap (f : α → Option β) (as : Array α) (start := 0) (stop := as.size) : Array β :=
  Id.run <| as.filterMapM f (start := start) (stop := stop)

@[specialize]
def getMax? (as : Array α) (lt : α → α → Bool) : Option α :=
  if h : 0 < as.size then
    let a0 := as.get ⟨0, h⟩
    some <| as.foldl (init := a0) (start := 1) fun best a =>
      if lt best a then a else best
  else
    none

@[inline]
def partition (p : α → Bool) (as : Array α) : Array α × Array α := do
  let mut bs := #[]
  let mut cs := #[]
  for a in as do
    if p a then
      bs := bs.push a
    else
      cs := cs.push a
  return (bs, cs)

theorem ext (a b : Array α)
    (h₁ : a.size = b.size)
    (h₂ : (i : Nat) → (hi₁ : i < a.size) → (hi₂ : i < b.size) → a.get ⟨i, hi₁⟩ = b.get ⟨i, hi₂⟩)
    : a = b := by
  let rec extAux (a b : List α)
      (h₁ : a.length = b.length)
      (h₂ : (i : Nat) → (hi₁ : i < a.length) → (hi₂ : i < b.length) → a.get i hi₁ = b.get i hi₂)
      : a = b := by
    induction a generalizing b with
    | nil =>
      cases b with
      | nil       => rfl
      | cons b bs => rw [List.length_cons] at h₁; injection h₁
    | cons a as ih =>
      cases b with
      | nil => rw [List.length_cons] at h₁; injection h₁
      | cons b bs =>
        have hz₁ : 0 < (a::as).length := by rw [List.length_cons]; apply Nat.zero_lt_succ
        have hz₂ : 0 < (b::bs).length := by rw [List.length_cons]; apply Nat.zero_lt_succ
        have headEq : a = b := h₂ 0 hz₁ hz₂
        have h₁' : as.length = bs.length := by rw [List.length_cons, List.length_cons] at h₁; injection h₁; assumption
        have h₂' : (i : Nat) → (hi₁ : i < as.length) → (hi₂ : i < bs.length) → as.get i hi₁ = bs.get i hi₂ := by
          intro i hi₁ hi₂
          have hi₁' : i+1 < (a::as).length := by rw [List.length_cons]; apply Nat.succ_lt_succ; assumption
          have hi₂' : i+1 < (b::bs).length := by rw [List.length_cons]; apply Nat.succ_lt_succ; assumption
          have : (a::as).get (i+1) hi₁' = (b::bs).get (i+1) hi₂' := h₂ (i+1) hi₁' hi₂'
          apply this
        have tailEq : as = bs := ih bs h₁' h₂'
        rw [headEq, tailEq]
  cases a; cases b
  apply congrArg
  apply extAux
  assumption
  assumption

theorem extLit {n : Nat}
    (a b : Array α)
    (hsz₁ : a.size = n) (hsz₂ : b.size = n)
    (h : (i : Nat) → (hi : i < n) → a.getLit i hsz₁ hi = b.getLit i hsz₂ hi) : a = b :=
  Array.ext a b (hsz₁.trans hsz₂.symm) fun i hi₁ hi₂ => h i (hsz₁ ▸ hi₁)

end Array

-- CLEANUP the following code
namespace Array

partial def indexOfAux [BEq α] (a : Array α) (v : α) : Nat → Option (Fin a.size)
  | i =>
    if h : i < a.size then
      let idx : Fin a.size := ⟨i, h⟩;
      if a.get idx == v then some idx
      else indexOfAux a v (i+1)
    else none

def indexOf? [BEq α] (a : Array α) (v : α) : Option (Fin a.size) :=
  indexOfAux a v 0

partial def eraseIdxAux : Nat → Array α → Array α
  | i, a =>
    if h : i < a.size then
      let idx  : Fin a.size := ⟨i, h⟩;
      let idx1 : Fin a.size := ⟨i - 1, by exact Nat.lt_of_le_of_lt (Nat.pred_le i) h⟩;
      eraseIdxAux (i+1) (a.swap idx idx1)
    else
      a.pop

def feraseIdx (a : Array α) (i : Fin a.size) : Array α :=
  eraseIdxAux (i.val + 1) a

def eraseIdx (a : Array α) (i : Nat) : Array α :=
  if i < a.size then eraseIdxAux (i+1) a else a

@[simp] theorem size_swap (a : Array α) (i j : Fin a.size) : (a.swap i j).size = a.size := by
  show ((a.set i (a.get j)).set (size_set a i _ ▸ j) (a.get i)).size = a.size
  rw [size_set, size_set]

@[simp] theorem size_pop (a : Array α) : a.pop.size = a.size - 1 :=
  List.length_dropLast ..

section
/- Instance for justifying `partial` declaration.
   We should be able to delete it as soon as we restore support for well-founded recursion. -/
instance eraseIdxSzAuxInstance (a : Array α) : Inhabited { r : Array α // r.size = a.size - 1 } where
  default := ⟨a.pop, size_pop a⟩

partial def eraseIdxSzAux (a : Array α) : ∀ (i : Nat) (r : Array α), r.size = a.size → { r : Array α // r.size = a.size - 1 }
  | i, r, heq =>
    if h : i < r.size then
      let idx  : Fin r.size := ⟨i, h⟩;
      let idx1 : Fin r.size := ⟨i - 1, by exact Nat.lt_of_le_of_lt (Nat.pred_le i) h⟩;
      eraseIdxSzAux a (i+1) (r.swap idx idx1) ((size_swap r idx idx1).trans heq)
    else
      ⟨r.pop, (size_pop r).trans (heq ▸ rfl)⟩
end

def eraseIdx' (a : Array α) (i : Fin a.size) : { r : Array α // r.size = a.size - 1 } :=
  eraseIdxSzAux a (i.val + 1) a rfl

def erase [BEq α] (as : Array α) (a : α) : Array α :=
  match as.indexOf? a with
  | none   => as
  | some i => as.feraseIdx i

partial def insertAtAux (i : Nat) : Array α → Nat → Array α
  | as, j =>
    if i == j then as
    else
      let as := as.swap! (j-1) j;
      insertAtAux i as (j-1)

/--
  Insert element `a` at position `i`.
  Pre: `i < as.size` -/
def insertAt (as : Array α) (i : Nat) (a : α) : Array α :=
  if i > as.size then panic! "invalid index"
  else
    let as := as.push a;
    as.insertAtAux i as.size

def toListLitAux (a : Array α) (n : Nat) (hsz : a.size = n) : ∀ (i : Nat), i ≤ a.size → List α → List α
  | 0,     hi, acc => acc
  | (i+1), hi, acc => toListLitAux a n hsz i (Nat.le_of_succ_le hi) (a.getLit i hsz (Nat.lt_of_lt_of_eq (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi) hsz) :: acc)

def toArrayLit (a : Array α) (n : Nat) (hsz : a.size = n) : Array α :=
  List.toArray <| toListLitAux a n hsz n (hsz ▸ Nat.le_refl _) []

theorem toArrayLit_eq (a : Array α) (n : Nat) (hsz : a.size = n) : a = toArrayLit a n hsz :=
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

  Then using Array.extLit, we have that a = List.toArray <| toListLitAux a n hsz n _ []
  -/

partial def isPrefixOfAux [BEq α] (as bs : Array α) (hle : as.size ≤ bs.size) : Nat → Bool
  | i =>
    if h : i < as.size then
      let a := as.get ⟨i, h⟩;
      let b := bs.get ⟨i, Nat.lt_of_lt_of_le h hle⟩;
      if a == b then
        isPrefixOfAux as bs hle (i+1)
      else
        false
    else
      true

/- Return true iff `as` is a prefix of `bs` -/
def isPrefixOf [BEq α] (as bs : Array α) : Bool :=
  if h : as.size ≤ bs.size then
    isPrefixOfAux as bs h 0
  else
    false

private def allDiffAuxAux [BEq α] (as : Array α) (a : α) : forall (i : Nat), i < as.size → Bool
  | 0,   h => true
  | i+1, h =>
    have : i < as.size := Nat.lt_trans (Nat.lt_succ_self _) h;
    a != as.get ⟨i, this⟩ && allDiffAuxAux as a i this

private partial def allDiffAux [BEq α] (as : Array α) : Nat → Bool
  | i =>
    if h : i < as.size then
      allDiffAuxAux as (as.get ⟨i, h⟩) i h && allDiffAux as (i+1)
    else
      true

def allDiff [BEq α] (as : Array α) : Bool :=
  allDiffAux as 0

@[specialize] partial def zipWithAux (f : α → β → γ) (as : Array α) (bs : Array β) : Nat → Array γ → Array γ
  | i, cs =>
    if h : i < as.size then
      let a := as.get ⟨i, h⟩;
      if h : i < bs.size then
        let b := bs.get ⟨i, h⟩;
        zipWithAux f as bs (i+1) <| cs.push <| f a b
      else
        cs
    else
      cs

@[inline] def zipWith (as : Array α) (bs : Array β) (f : α → β → γ) : Array γ :=
  zipWithAux f as bs 0 #[]

def zip (as : Array α) (bs : Array β) : Array (α × β) :=
  zipWith as bs Prod.mk

def unzip (as : Array (α × β)) : Array α × Array β :=
  as.foldl (init := (#[], #[])) fun (as, bs) (a, b) => (as.push a, bs.push b)

def split (as : Array α) (p : α → Bool) : Array α × Array α :=
  as.foldl (init := (#[], #[])) fun (as, bs) a =>
    if p a then (as.push a, bs) else (as, bs.push a)

end Array
