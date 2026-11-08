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
`ConLeche.Kernel.Expr` does. -/
import all Init.Util

/-!
# InLean: decidable equality of `Lean.Expr`, executed pointer-first

InLean is to be provable by a simulation onto con-leche's cached checker, so it
does not use core's opaque externs.
Core's `BEq Expr` is `Expr.eqv`, an `@[extern] opaque` (alpha-equivalence
in C++).  InLean's executed equality is con-leche's design
(`ConLeche.Kernel.Expr`, `Expr.beq`/`beqMemo`): **the specification
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
primitive, `ConLeche.Kernel.Exclusive`); InLean may add no
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

/-- **Exact equality** as an instance, for the walks' memos and the
generator (`Lean.Kernel.InLean.ExprOps`, `Lean.Kernel.InLean.IndGen`), whose results
keep binder names. -/
@[reducible] def instBEqExprExact : BEq Expr := ⟨Expr.beqI⟩

theorem instBEqExprExact_lawful : @LawfulBEq Expr instBEqExprExact := by
  letI := instBEqExprExact
  exact { eq_of_beq := fun h => of_decide_eq_true h, rfl := by simp [BEq.beq, Expr.beqI] }

/-! ## Equality up to what con-leche's terms do not have

con-leche's expressions carry no binder names, no binder infos, no `let`'s
`nonDep` flag and no `mdata`; its checker compares them by decidable
equality.  InLean has two equalities:

* **`Expr.clEq`, the checker's comparison** (the scoped `==`): equal after
  erasing all four (`erase`), so two of its terms compare equal exactly when
  the con-leche terms they stand for do.
* **`Expr.keyEq`, the memo maps' key equality** (`EKey`): equal after
  erasing binder names, infos and `nonDep` but not `mdata` (`eraseK`), none
  of which Lean's cached hash reads, so the maps are lawful.  Two keys that
  differ only in `mdata` are two entries: InLean may miss where con-leche
  hits, never the converse.
-/

/-- Binder names, binder infos, `nonDep` and `mdata` erased, hereditarily:
what `toCL` keeps. -/
def erase : Expr → Expr
  | .app f a => .app (erase f) (erase a)
  | .lam _ t b _ => .lam .anonymous (erase t) (erase b) .default
  | .forallE _ t b _ => .forallE .anonymous (erase t) (erase b) .default
  | .letE _ t v b _ => .letE .anonymous (erase t) (erase v) (erase b) false
  | .mdata _ e => erase e
  | .proj s i e => .proj s i (erase e)
  | e => e

/-- Binder names, binder infos and `nonDep` erased, `mdata` kept. -/
def eraseK : Expr → Expr
  | .app f a => .app (eraseK f) (eraseK a)
  | .lam _ t b _ => .lam .anonymous (eraseK t) (eraseK b) .default
  | .forallE _ t b _ => .forallE .anonymous (eraseK t) (eraseK b) .default
  | .letE _ t v b _ => .letE .anonymous (eraseK t) (eraseK v) (eraseK b) false
  | .mdata m e => .mdata m (eraseK e)
  | .proj s i e => .proj s i (eraseK e)
  | e => e

/-- `e` with its top-level `mdata` wrappers peeled (O(wrappers)): how the
checker reads a node, as the official kernel's `whnf_core`/`infer` do,
never rebuilding a term. -/
def EO.stripTop : Expr → Expr
  | .mdata _ x => EO.stripTop x
  | e => e

theorem erase_stripTop (e : Expr) : erase (EO.stripTop e) = erase e := by
  induction e <;> simp_all [EO.stripTop, erase]

/-- The constructor of a node. -/
def ctorTag : Expr → Nat
  | .bvar .. => 0 | .fvar .. => 1 | .mvar .. => 2 | .sort .. => 3 | .const .. => 4
  | .app .. => 5 | .lam .. => 6 | .forallE .. => 7 | .letE .. => 8 | .lit .. => 9
  | .mdata .. => 10 | .proj .. => 11

theorem ctorTag_eraseK (e : Expr) : ctorTag (eraseK e) = ctorTag e := by
  cases e <;> rfl

/-- A memo entry of an erased comparison: a pair a completed descent proved
equal after `er`, the addresses it was seen at, the proof. -/
structure ClPair (er : Expr → Expr) where
  fst : Expr
  snd : Expr
  pa : USize
  pb : USize
  eq : er fst = er snd

abbrev ClMap (er : Expr → Expr) := Std.HashMap Nat (ClPair er)

@[inline] def clProbeHit {er : Expr → Expr} (m : ClMap er) (key : Nat) (pa pb : USize)
    (a b : Expr) : { h : Bool // h = true → er a = er b } :=
  match m.get? key with
  | some p =>
    if p.pa == pa && p.pb == pb then
      match ptrDec p.fst a, ptrDec p.snd b with
      | isTrue h1, isTrue h2 => ⟨true, fun _ => h1 ▸ h2 ▸ p.eq⟩
      | _, _ => ⟨false, fun h => Bool.noConfusion h⟩
    else ⟨false, fun h => Bool.noConfusion h⟩
  | none => ⟨false, fun h => Bool.noConfusion h⟩

structure ClResX (er : Expr → Expr) (a b : Expr) where
  dec : Decidable (er a = er b)
  map : Option (ClMap er)

abbrev ClOutX (er : Expr → Expr) (a b : Expr) := Squash (ClResX er a b)

@[inline] def ClOutX.mk {er : Expr → Expr} {a b : Expr} (d : Decidable (er a = er b))
    (map : Option (ClMap er)) : ClOutX er a b :=
  Quot.mk _ ⟨d, map⟩

@[inline] def ClMap.record {er : Expr → Expr} (mp : Option (ClMap er)) (key : Nat)
    (p : ClPair er) : Option (ClMap er) :=
  match mp with
  | none => some ((Std.HashMap.emptyWithCapacity (key % 8 + 8) : ClMap er).insert key p)
  | some m => some (m.insert key p)

/-- Twin of `enterBeq` for an erased comparison. -/
@[inline] def enterCl {er : Expr → Expr} (map : Option (ClMap er)) (a b : @& Expr)
    (rec : Option (ClMap er) → ClOutX er a b) : ClOutX er a b :=
  withAddr a fun pa => withAddr b fun pb =>
  if pa == pb then
    .mk (match ptrDec a b with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse _ => (inferInstance : DecidableEq Expr) (er a) (er b)) map
  else if !beqRecursive a then rec map
  else
    let hit : { h : Bool // h = true → er a = er b } :=
      match map with
      | some m => clProbeHit m (beqKey pa pb) pa pb a b
      | none => ⟨false, fun h => Bool.noConfusion h⟩
    if hh : hit.1 then .mk (isTrue (hit.2 hh)) map
    else Squash.lift (rec map) fun r =>
      match r.dec with
      | isTrue h => .mk (isTrue h) (ClMap.record r.map (beqKey pa pb) ⟨a, b, pa, pb, h⟩)
      | d => .mk d r.map

/-- The key comparison's descent (`eraseK`): names, infos and `nonDep` not
compared, `mdata` compared; a pair of different constructors is unequal, a
pair of leaves decided by their equality. -/
def keyGoX (map : Option (ClMap eraseK)) (a b : @& Expr) : ClOutX eraseK a b :=
  match a, b with
  | .app f x, .app g y =>
    Squash.lift (enterCl map f g fun m => keyGoX m f g) fun r₁ =>
      match r₁.dec with
      | isFalse h => .mk (isFalse (fun e => h (Expr.app.inj e).1)) r₁.map
      | isTrue h => Squash.lift (enterCl r₁.map x y fun m => keyGoX m x y) fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h' => isTrue (by simp only [eraseK, h, h'])
          | isFalse h' => isFalse (fun e => h' (Expr.app.inj e).2))
          r₂.map
  | .lam _ t b _, .lam _ t' b' _ =>
    Squash.lift (enterCl map t t' fun mp => keyGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.lam.inj e).2.1)) r₁.map
      | isTrue h₁ => Squash.lift (enterCl r₁.map b b' fun mp => keyGoX mp b b') fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h₂ => isTrue (by simp only [eraseK, h₁, h₂])
          | isFalse h₂ => isFalse (fun e => h₂ (Expr.lam.inj e).2.2.1))
          r₂.map
  | .forallE _ t b _, .forallE _ t' b' _ =>
    Squash.lift (enterCl map t t' fun mp => keyGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.forallE.inj e).2.1)) r₁.map
      | isTrue h₁ => Squash.lift (enterCl r₁.map b b' fun mp => keyGoX mp b b') fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h₂ => isTrue (by simp only [eraseK, h₁, h₂])
          | isFalse h₂ => isFalse (fun e => h₂ (Expr.forallE.inj e).2.2.1))
          r₂.map
  | .letE _ t v b _, .letE _ t' v' b' _ =>
    Squash.lift (enterCl map t t' fun mp => keyGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.letE.inj e).2.1)) r₁.map
      | isTrue h₁ => Squash.lift (enterCl r₁.map v v' fun mp => keyGoX mp v v') fun r₂ =>
        match r₂.dec with
        | isFalse h₂ => .mk (isFalse (fun e => h₂ (Expr.letE.inj e).2.2.1)) r₂.map
        | isTrue h₂ => Squash.lift (enterCl r₂.map b b' fun mp => keyGoX mp b b') fun r₃ =>
          .mk (match r₃.dec with
            | isTrue h₃ => isTrue (by simp only [eraseK, h₁, h₂, h₃])
            | isFalse h₃ => isFalse (fun e => h₃ (Expr.letE.inj e).2.2.2.1))
            r₃.map
  | .proj s i x, .proj s' i' x' =>
    if hs : s = s' ∧ i = i' then
      Squash.lift (enterCl map x x' fun mp => keyGoX mp x x') fun r =>
        .mk (match r.dec with
          | isTrue h => isTrue (by obtain ⟨rfl, rfl⟩ := hs; simp only [eraseK, h])
          | isFalse h => isFalse (fun e => h (Expr.proj.inj e).2.2))
          r.map
    else .mk (isFalse (fun e => hs ⟨(Expr.proj.inj e).1, (Expr.proj.inj e).2.1⟩)) map
  | .mdata d x, .mdata d' x' =>
    if hd : d = d' then
      Squash.lift (enterCl map x x' fun mp => keyGoX mp x x') fun r =>
        .mk (match r.dec with
          | isTrue h => isTrue (by subst hd; simp only [eraseK, h])
          | isFalse h => isFalse (fun e => h (Expr.mdata.inj e).2))
          r.map
    else .mk (isFalse (fun e => hd (Expr.mdata.inj e).1)) map
  | a, b =>
    if hc : ctorTag a = ctorTag b then
      -- same constructor, not one the arms above take: two leaves (O(1) `eraseK`)
      .mk ((inferInstance : DecidableEq Expr) (eraseK a) (eraseK b)) map
    else .mk (isFalse (fun e => hc (by rw [← ctorTag_eraseK a, ← ctorTag_eraseK b, e]))) map

theorem erase_mdata (m : MData) (x : Expr) : erase (.mdata m x) = erase x := rfl

theorem ctorTag_erase_of_ne (e : Expr) (h : ctorTag e ≠ 10) : ctorTag (erase e) = ctorTag e := by
  cases e <;> first | rfl | exact absurd rfl h

/-- The checker comparison's descent (`erase`): a `mdata` node is read
through (no rebuilt term), then the constructor cases as `keyGoX`'s. -/
def clGoX (map : Option (ClMap erase)) (a b : @& Expr) : ClOutX erase a b :=
  match a, b with
  | .mdata m x, b =>
    Squash.lift (clGoX map x b) fun r => .mk (erase_mdata m x ▸ r.dec) r.map
  | a, .mdata m y =>
    Squash.lift (clGoX map a y) fun r => .mk (erase_mdata m y ▸ r.dec) r.map
  | .app f x, .app g y =>
    Squash.lift (enterCl map f g fun m => clGoX m f g) fun r₁ =>
      match r₁.dec with
      | isFalse h => .mk (isFalse (fun e => h (Expr.app.inj e).1)) r₁.map
      | isTrue h => Squash.lift (enterCl r₁.map x y fun m => clGoX m x y) fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h' => isTrue (by simp only [erase, h, h'])
          | isFalse h' => isFalse (fun e => h' (Expr.app.inj e).2))
          r₂.map
  | .lam _ t b _, .lam _ t' b' _ =>
    Squash.lift (enterCl map t t' fun mp => clGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.lam.inj e).2.1)) r₁.map
      | isTrue h₁ => Squash.lift (enterCl r₁.map b b' fun mp => clGoX mp b b') fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h₂ => isTrue (by simp only [erase, h₁, h₂])
          | isFalse h₂ => isFalse (fun e => h₂ (Expr.lam.inj e).2.2.1))
          r₂.map
  | .forallE _ t b _, .forallE _ t' b' _ =>
    Squash.lift (enterCl map t t' fun mp => clGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.forallE.inj e).2.1)) r₁.map
      | isTrue h₁ => Squash.lift (enterCl r₁.map b b' fun mp => clGoX mp b b') fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h₂ => isTrue (by simp only [erase, h₁, h₂])
          | isFalse h₂ => isFalse (fun e => h₂ (Expr.forallE.inj e).2.2.1))
          r₂.map
  | .letE _ t v b _, .letE _ t' v' b' _ =>
    Squash.lift (enterCl map t t' fun mp => clGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.letE.inj e).2.1)) r₁.map
      | isTrue h₁ => Squash.lift (enterCl r₁.map v v' fun mp => clGoX mp v v') fun r₂ =>
        match r₂.dec with
        | isFalse h₂ => .mk (isFalse (fun e => h₂ (Expr.letE.inj e).2.2.1)) r₂.map
        | isTrue h₂ => Squash.lift (enterCl r₂.map b b' fun mp => clGoX mp b b') fun r₃ =>
          .mk (match r₃.dec with
            | isTrue h₃ => isTrue (by simp only [erase, h₁, h₂, h₃])
            | isFalse h₃ => isFalse (fun e => h₃ (Expr.letE.inj e).2.2.2.1))
            r₃.map
  | .proj s i x, .proj s' i' x' =>
    if hs : s = s' ∧ i = i' then
      Squash.lift (enterCl map x x' fun mp => clGoX mp x x') fun r =>
        .mk (match r.dec with
          | isTrue h => isTrue (by obtain ⟨rfl, rfl⟩ := hs; simp only [erase, h])
          | isFalse h => isFalse (fun e => h (Expr.proj.inj e).2.2))
          r.map
    else .mk (isFalse (fun e => hs ⟨(Expr.proj.inj e).1, (Expr.proj.inj e).2.1⟩)) map
  | a, b =>
    if hc : ctorTag a ≠ ctorTag b ∧ ctorTag a ≠ 10 ∧ ctorTag b ≠ 10 then
      -- different constructors, neither `mdata` (the arms above took those),
      -- which `erase` keeps
      .mk (isFalse (fun e => hc.1 (by
        rw [← ctorTag_erase_of_ne a hc.2.1, ← ctorTag_erase_of_ne b hc.2.2, e]))) map
    else
      -- two leaves of one constructor: `erase` is O(1) on them
      .mk ((inferInstance : DecidableEq Expr) (erase a) (erase b)) map
termination_by (sizeOf a + sizeOf b)

/-- **The memo maps' key equality**: equal after `eraseK`. -/
def Expr.keyEq (a b : Expr) : Bool := decide (eraseK a = eraseK b)

def Expr.keyEqMemo (a b : Expr) : Bool :=
  withPtrEq a b
    (fun _ => @decide (eraseK a = eraseK b) (Squash.lift (keyGoX none a b) (fun r => r.dec)))
    (fun h => by subst h; simp)

@[csimp] theorem Expr.keyEq_eq_keyEqMemo : @Expr.keyEq = @Expr.keyEqMemo := by
  funext a b
  unfold Expr.keyEq Expr.keyEqMemo withPtrEq
  congr 1

/-- **InLean's checker equality**: equal after `erase` (the specification),
executed by `Expr.clEqMemo`. -/
def Expr.clEq (a b : Expr) : Bool := decide (erase a = erase b)

def Expr.clEqMemo (a b : Expr) : Bool :=
  withPtrEq a b
    (fun _ => @decide (erase a = erase b) (Squash.lift (clGoX none a b) (fun r => r.dec)))
    (fun h => by subst h; simp)

@[csimp] theorem Expr.clEq_eq_clEqMemo : @Expr.clEq = @Expr.clEqMemo := by
  funext a b
  unfold Expr.clEq Expr.clEqMemo withPtrEq
  congr 1

/-- **The scoped equality of expressions in InLean's checker**: `Expr.clEq`. -/
scoped instance instBEqExprI : BEq Expr := ⟨Expr.clEq⟩

theorem Expr.clEq_iff (a b : Expr) : Expr.clEq a b = true ↔ erase a = erase b := by
  simp [Expr.clEq]

scoped instance : EquivBEq Expr where
  rfl := by simp [BEq.beq, Expr.clEq]
  symm h := by simp only [BEq.beq, Expr.clEq, decide_eq_true_eq] at *; exact h.symm
  trans h₁ h₂ := by
    simp only [BEq.beq, Expr.clEq, decide_eq_true_eq] at *; exact h₁.trans h₂

/-- **A memo key**: an expression compared by `Expr.keyEq`, hashed by Lean's
cached hash (which reads no binder name, info or `nonDep`). -/
structure EKey where
  e : Expr

instance : BEq EKey := ⟨fun a b => Expr.keyEq a.e b.e⟩
instance : Hashable EKey := ⟨fun a => hash a.e⟩

instance : EquivBEq EKey where
  rfl := by simp [BEq.beq, Expr.keyEq]
  symm h := by simp only [BEq.beq, Expr.keyEq, decide_eq_true_eq] at *; exact h.symm
  trans h₁ h₂ := by
    simp only [BEq.beq, Expr.keyEq, decide_eq_true_eq] at *; exact h₁.trans h₂

/-- The bulk-instantiation memo's key: a term and the values, each by
`keyEq`. -/
structure InstKey where
  e : Expr
  vs : List Expr

def keyEqList : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => Expr.keyEq a b && keyEqList as bs
  | _, _ => false

instance : BEq InstKey := ⟨fun a b => Expr.keyEq a.e b.e && keyEqList a.vs b.vs⟩
instance : Hashable InstKey := ⟨fun a => mixHash (hash a.e) (hash a.vs)⟩

end Lean.Kernel.InLean
