/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Init
public import Lean.Expr
/- `withPtrEq`/`withPtrAddr`/`withPtrEqDecEq` are public but not exposed;
`Expr.beq_eq_beqMemo` needs their bodies (`k ()`, `k 0`), as con-leche's
`ConLeche/Kernel/Expr.lean` does. -/
import all Init.Util

/-!
# InLean: decidable equality of `Lean.Expr`, executed pointer-first

InLean is to be provable by a simulation onto con-leche's cached checker, so
it does not use core's opaque externs.
Core's `BEq Expr` is `Expr.eqv`, an `@[extern] opaque` (alpha-equivalence
in C++).  InLean's executed equality is con-leche's design
(`ConLeche/Kernel/Expr.lean`, `Expr.beq`/`beqMemo`): **the specification
is decidable equality**, `Expr.beqI a b = decide (a = b)`, so `LawfulBEq`
holds by construction, and the executed function is the memoised,
pointer-first descent `Expr.beqMemo`, proved equal to it
(`beq_eq_beqMemo`) and substituted by `@[csimp]` — no `implemented_by`,
nothing `unsafe`; the runtime facts enter only through `Init.Util`'s
`withPtrEq`/`withPtrAddr`.

Decidable equality of `Lean.Expr` needs it for every component; core
provides it for `Name` only.  The rest is derived here (`Level`,
`Literal`, `BinderInfo`, the ids, `SourceInfo`, `DataValue`, `KVMap`,
`Expr`); `Syntax` (an `mdata` payload can hold one) is a nested
inductive the deriving handler refuses, and gets a structural equality
with its two lemmas.

**Deviation from con-leche.**  con-leche probes and records only pairs
whose two nodes are shared (`withExclusive`, its one `unsafe`-implemented
primitive, `ConLeche/Kernel/Exclusive.lean`); InLean may add no
`unsafe` code, so every recursive pair is probed and recorded.

The instance is `scoped` in `InLean`: every InLean module (all inside the
namespace) and every memo map's key type there compares expressions by
it; code outside keeps core's.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

deriving instance DecidableEq for LevelMVarId
deriving instance DecidableEq for FVarId
deriving instance DecidableEq for MVarId
deriving instance DecidableEq for BinderInfo
deriving instance DecidableEq for Literal
deriving instance DecidableEq for Level
deriving instance DecidableEq for Substring.Raw
deriving instance DecidableEq for SourceInfo
deriving instance DecidableEq for Syntax.Preresolved

mutual
/-- Structural equality of `Syntax` (the deriving handler refuses nested
inductives). -/
def synEq : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node i k ⟨as⟩, .node i' k' ⟨bs⟩ => decide (i = i') && decide (k = k') && synListEq as bs
  | .atom i v, .atom i' v' => decide (i = i') && decide (v = v')
  | .ident i r v p, .ident i' r' v' p' =>
    decide (i = i') && decide (r = r') && decide (v = v') && decide (p = p')
  | _, _ => false
def synListEq : List Syntax → List Syntax → Bool
  | [], [] => true
  | a :: as, b :: bs => synEq a b && synListEq as bs
  | _, _ => false
end

mutual
theorem synEq_sound : ∀ a b, synEq a b = true → a = b
  | .missing, .missing, _ => rfl
  | .node i k ⟨as⟩, .node i' k' ⟨bs⟩, h => by
    simp only [synEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rw [synListEq_sound as bs h]
  | .atom i v, .atom i' v', h => by
    simp only [synEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | .ident i r v p, .ident i' r' v' p', h => by
    simp only [synEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h; rfl
  | .missing, .node .., h | .missing, .atom .., h | .missing, .ident .., h
  | .node .., .missing, h | .node .., .atom .., h | .node .., .ident .., h
  | .atom .., .missing, h | .atom .., .node .., h | .atom .., .ident .., h
  | .ident .., .missing, h | .ident .., .node .., h | .ident .., .atom .., h => by simp [synEq] at h
theorem synListEq_sound : ∀ as bs, synListEq as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [synListEq, Bool.and_eq_true] at h
    rw [synEq_sound a b h.1, synListEq_sound as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [synListEq] at h
end

mutual
theorem synEq_refl : ∀ a, synEq a a = true
  | .missing => rfl
  | .node _ _ ⟨as⟩ => by simp [synEq, synListEq_refl as]
  | .atom _ _ => by simp [synEq]
  | .ident _ _ _ _ => by simp [synEq]
theorem synListEq_refl : ∀ as, synListEq as as = true
  | [] => rfl
  | a :: as => by simp [synListEq, synEq_refl a, synListEq_refl as]
end

instance instDecidableEqSyntaxI : DecidableEq Syntax := fun a b =>
  if h : synEq a b then isTrue (synEq_sound a b h)
  else isFalse (fun e => by subst e; exact h (synEq_refl a))

deriving instance DecidableEq for DataValue
deriving instance DecidableEq for KVMap
deriving instance DecidableEq for Expr

/-! ## The memoised pointer-first descent (twin of `Expr.beqMemo`) -/

/-- The nodes whose comparison recurses (twin of `beqRecursive`). -/
@[inline] def beqRecursive : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. | .mdata .. => true
  | _ => false

/-- A memo entry: a pair a completed descent proved equal, the addresses
it was seen at, the proof (twin of `EqPair`). -/
structure EqPair where
  fst : Expr
  snd : Expr
  pa : USize
  pb : USize
  eq : fst = snd

def EqPair.dflt : EqPair := ⟨.bvar 0, .bvar 0, 0, 0, rfl⟩

abbrev BeqMap := Std.HashMap Nat EqPair

/-- Twin of `beqKey`. -/
@[inline] def beqKey (pa pb : USize) : Nat :=
  ((pa ^^^ (pb * 0x9E3779B97F4A7C15)) &&& 0x3FFFFFFFFFFFFFFF).toNat

/-- Twin of `withAddr`. -/
@[inline] def withAddr {α : Type u} {β : Type v} [Subsingleton β] (a : α) (k : USize → β) : β :=
  withPtrAddr a k (fun _ _ => Subsingleton.elim _ _)

/-- Twin of `ptrDec`. -/
@[inline] def ptrDec (a b : Expr) : Decidable (a = b) :=
  withPtrEqDecEq a b (fun _ => (inferInstance : DecidableEq Expr) a b)

/-- Twin of `probeHit`. -/
@[inline] def probeHit (m : BeqMap) (key : Nat) (pa pb : USize) (a b : Expr) :
    { h : Bool // h = true → a = b } :=
  let p := m.getD key EqPair.dflt
  if p.pa == pa && p.pb == pb then
    match ptrDec p.fst a, ptrDec p.snd b with
    | isTrue h1, isTrue h2 => ⟨true, fun _ => h1 ▸ h2 ▸ p.eq⟩
    | _, _ => ⟨false, fun h => Bool.noConfusion h⟩
  else ⟨false, fun h => Bool.noConfusion h⟩

structure BeqResX (a b : Expr) where
  dec : Decidable (a = b)
  map : Option BeqMap

abbrev BeqOutX (a b : Expr) := Squash (BeqResX a b)

@[inline] def BeqOutX.mk {a b : Expr} (d : Decidable (a = b)) (map : Option BeqMap) : BeqOutX a b :=
  Quot.mk _ ⟨d, map⟩

@[inline] def BeqMap.record (mp : Option BeqMap) (key : Nat) (p : EqPair) : Option BeqMap :=
  match mp with
  | none => some (({} : BeqMap).insert key p)
  | some m => some (m.insert key p)

/-- Twin of `enterBeq`, every recursive pair probed (no `withExclusive`). -/
@[inline] def enterBeq (map : Option BeqMap) (a b : @& Expr) (rec : Option BeqMap → BeqOutX a b) :
    BeqOutX a b :=
  withAddr a fun pa => withAddr b fun pb =>
  if pa == pb then .mk (ptrDec a b) map
  else if !beqRecursive a then rec map
  else
    let hit : { h : Bool // h = true → a = b } :=
      match map with
      | some m => probeHit m (beqKey pa pb) pa pb a b
      | none => ⟨false, fun h => Bool.noConfusion h⟩
    if hh : hit.1 then .mk (isTrue (hit.2 hh)) map
    else Squash.lift (rec map) fun r =>
      match r.dec with
      | isTrue h => .mk (isTrue h) (BeqMap.record r.map (beqKey pa pb) ⟨a, b, pa, pb, h⟩)
      | d => .mk d r.map

/-- Twin of `beqGoX` over `Lean.Expr`: the constructor cases, each child
through `enterBeq`; leaves decided by their components' equality. -/
def beqGoX (map : Option BeqMap) (a b : @& Expr) : BeqOutX a b :=
  match a, b with
  | .app f x, .app g y =>
    Squash.lift (enterBeq map f g fun m => beqGoX m f g) fun r₁ =>
      match r₁.dec with
      | isFalse h => .mk (isFalse (fun e => h (Expr.app.inj e).1)) r₁.map
      | isTrue h => Squash.lift (enterBeq r₁.map x y fun m => beqGoX m x y) fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h' => isTrue (by subst h; subst h'; rfl)
          | isFalse h' => isFalse (fun e => h' (Expr.app.inj e).2))
          r₂.map
  | .lam n t b bi, .lam n' t' b' bi' =>
    if hn : n = n' ∧ bi = bi' then
      Squash.lift (enterBeq map t t' fun mp => beqGoX mp t t') fun r₁ =>
        match r₁.dec with
        | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.lam.inj e).2.1)) r₁.map
        | isTrue h₁ => Squash.lift (enterBeq r₁.map b b' fun mp => beqGoX mp b b') fun r₂ =>
          .mk (match r₂.dec with
            | isTrue h₂ => isTrue (by obtain ⟨rfl, rfl⟩ := hn; subst h₁; subst h₂; rfl)
            | isFalse h₂ => isFalse (fun e => h₂ (Expr.lam.inj e).2.2.1))
            r₂.map
    else .mk (isFalse (fun e => hn ⟨(Expr.lam.inj e).1, (Expr.lam.inj e).2.2.2⟩)) map
  | .forallE n t b bi, .forallE n' t' b' bi' =>
    if hn : n = n' ∧ bi = bi' then
      Squash.lift (enterBeq map t t' fun mp => beqGoX mp t t') fun r₁ =>
        match r₁.dec with
        | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.forallE.inj e).2.1)) r₁.map
        | isTrue h₁ => Squash.lift (enterBeq r₁.map b b' fun mp => beqGoX mp b b') fun r₂ =>
          .mk (match r₂.dec with
            | isTrue h₂ => isTrue (by obtain ⟨rfl, rfl⟩ := hn; subst h₁; subst h₂; rfl)
            | isFalse h₂ => isFalse (fun e => h₂ (Expr.forallE.inj e).2.2.1))
            r₂.map
    else .mk (isFalse (fun e => hn ⟨(Expr.forallE.inj e).1, (Expr.forallE.inj e).2.2.2⟩)) map
  | .letE n t v b nd, .letE n' t' v' b' nd' =>
    if hn : n = n' ∧ nd = nd' then
      Squash.lift (enterBeq map t t' fun mp => beqGoX mp t t') fun r₁ =>
        match r₁.dec with
        | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.letE.inj e).2.1)) r₁.map
        | isTrue h₁ => Squash.lift (enterBeq r₁.map v v' fun mp => beqGoX mp v v') fun r₂ =>
          match r₂.dec with
          | isFalse h₂ => .mk (isFalse (fun e => h₂ (Expr.letE.inj e).2.2.1)) r₂.map
          | isTrue h₂ => Squash.lift (enterBeq r₂.map b b' fun mp => beqGoX mp b b') fun r₃ =>
            .mk (match r₃.dec with
              | isTrue h₃ => isTrue (by obtain ⟨rfl, rfl⟩ := hn; subst h₁; subst h₂; subst h₃; rfl)
              | isFalse h₃ => isFalse (fun e => h₃ (Expr.letE.inj e).2.2.2.1))
              r₃.map
    else .mk (isFalse (fun e => hn ⟨(Expr.letE.inj e).1, (Expr.letE.inj e).2.2.2.2⟩)) map
  | .proj s i x, .proj s' i' x' =>
    if hs : s = s' ∧ i = i' then
      Squash.lift (enterBeq map x x' fun mp => beqGoX mp x x') fun r =>
        .mk (match r.dec with
          | isTrue h => isTrue (by obtain ⟨rfl, rfl⟩ := hs; subst h; rfl)
          | isFalse h => isFalse (fun e => h (Expr.proj.inj e).2.2))
          r.map
    else .mk (isFalse (fun e => hs ⟨(Expr.proj.inj e).1, (Expr.proj.inj e).2.1⟩)) map
  | .mdata d x, .mdata d' x' =>
    if hd : d = d' then
      Squash.lift (enterBeq map x x' fun mp => beqGoX mp x x') fun r =>
        .mk (match r.dec with
          | isTrue h => isTrue (by subst hd; subst h; rfl)
          | isFalse h => isFalse (fun e => h (Expr.mdata.inj e).2))
          r.map
    else .mk (isFalse (fun e => hd (Expr.mdata.inj e).1)) map
  | a, b => .mk ((inferInstance : DecidableEq Expr) a b) map

/-- Twin of `Expr.beqMemo`: the pointer test, then the memoised descent. -/
def Expr.beqMemo (a b : Expr) : Bool :=
  withPtrEq a b (fun _ => @decide (a = b) (Squash.lift (beqGoX none a b) (fun r => r.dec)))
    (fun h => by subst h; simp)

/-- **InLean's executed expression equality**: decidable equality,
substituted by the memoised descent. -/
def Expr.beqI (a b : Expr) : Bool := decide (a = b)

/-- Twin of `Expr.beq_eq_beqMemo`. -/
@[csimp] theorem Expr.beqI_eq_beqMemo : @Expr.beqI = @Expr.beqMemo := by
  funext a b
  unfold Expr.beqI Expr.beqMemo withPtrEq
  congr 1

/-- The scoped equality of expressions in InLean (memo keys included). -/
scoped instance instBEqExprI : BEq Expr := ⟨Expr.beqI⟩

scoped instance : LawfulBEq Expr where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Expr.beqI]

/-- Hashing is core's cached word (a read of the computed field: equal
expressions have equal words, so `LawfulHashable` holds for the lawful
equality). -/
instance : LawfulHashable Expr where
  hash_eq a b h := by rw [eq_of_beq h]

end Lean.Kernel.InLean
