/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Init

public import Lean.Expr
public import Lean.Kernel.InLean.Exclusive
/- `withPtrEq`/`withPtrAddr`/`withPtrEqDecEq` are public but not exposed;
`Expr.beq_eq_beqMemo` needs their bodies (`k ()`, `k 0`), as con-leche's
`ConLeche.Kernel.Expr` does. -/
import all Init.Util
/- The computed field `Expr.data`'s equations are not exposed by `Lean.Expr`;
`data_eraseK` (the key equality's data-word test) reads them. -/
import all Lean.Expr

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

**The memo discipline** is con-leche's: only a pair whose two nodes are
both shared (`withExclusive`, `Lean.Kernel.InLean.Exclusive`) is probed and recorded —
a pair with an exclusive side cannot be queried again within the
comparison.  The official kernel's `expr_eq_fn::check_cache` guards its
cache the same way.

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

/-- The cached data word, as the `UInt64` it is. -/
@[inline] def dataWord (e : Expr) : UInt64 := e.data

/-- The cached data words differ (Lean's computed field: hash, depth, flags,
range): then the terms do. -/
@[inline] def dataNe (a b : Expr) : Bool := dataWord a != dataWord b

theorem dataNe_self (a : Expr) : dataNe a a = false := by simp [dataNe]

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

/-- Twin of `enterBeq`: pointer identity, the cached data word, the leaf
test, then the exclusivity of each side — an exclusive side means the pair
cannot recur and the descent runs with the memo untouched; a shared/shared
pair is probed, and recorded on a completed `true`. -/
@[inline] def enterBeq (map : Option BeqMap) (a b : @& Expr) (rec : Option BeqMap → BeqOutX a b) :
    BeqOutX a b :=
  withAddr a fun pa => withAddr b fun pb =>
  if pa == pb then .mk (ptrDec a b) map
  else if h : dataNe a b then
    .mk (isFalse (fun e => by subst e; simp [dataNe_self] at h)) map
  else if !beqRecursive a then rec map
  else withExcl a fun ea =>
    if ea then rec map
    else withExcl b fun eb =>
    if eb then rec map
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

/-- Twin of `Expr.beqMemo`: the pointer test, the cached data word, then the
memoised descent. -/
def Expr.beqMemo (a b : Expr) : Bool :=
  withPtrEq a b (fun _ => if !dataNe a b then
      @decide (a = b) (Squash.lift (beqGoX none a b) (fun r => r.dec))
    else false)
    (fun h => by subst h; simp [dataNe_self])

/-- **InLean's executed expression equality**: decidable equality,
substituted by the memoised descent. -/
def Expr.beqI (a b : Expr) : Bool := decide (a = b)

/-- Twin of `Expr.beq_eq_beqMemo`. -/
@[csimp] theorem Expr.beqI_eq_beqMemo : @Expr.beqI = @Expr.beqMemo := by
  funext a b
  unfold Expr.beqI Expr.beqMemo withPtrEq
  split
  · congr 1
  · rename_i h
    exact decide_eq_false (fun e => by subst e; simp [dataNe_self] at h)

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
  erasing all four (`erase`), each pair of nodes it meets first tested on
  the part of the cached data word `mdata` keeps (flags and loose-variable
  range).  It answers `true` only on `erase`-equal terms; on terms C can
  build, `erase`-equal terms have those parts equal, so two of its terms
  compare equal exactly when the con-leche terms they stand for do.
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

/-- A memo entry of a comparison `R`: a pair a completed descent proved
related, the addresses it was seen at, the proof. -/
structure ClPair (R : Expr → Expr → Prop) where
  fst : Expr
  snd : Expr
  pa : USize
  pb : USize
  rel : R fst snd

abbrev ClMap (R : Expr → Expr → Prop) := Std.HashMap Nat (ClPair R)

@[inline] def clProbeHit {R : Expr → Expr → Prop} (m : ClMap R) (key : Nat) (pa pb : USize)
    (a b : Expr) : { h : Bool // h = true → R a b } :=
  match m.get? key with
  | some p =>
    if p.pa == pa && p.pb == pb then
      match ptrDec p.fst a, ptrDec p.snd b with
      | isTrue h1, isTrue h2 => ⟨true, fun _ => h1 ▸ h2 ▸ p.rel⟩
      | _, _ => ⟨false, fun h => Bool.noConfusion h⟩
    else ⟨false, fun h => Bool.noConfusion h⟩
  | none => ⟨false, fun h => Bool.noConfusion h⟩

/-- A descent's answer for `P`, with the memo of `R`-related pairs. -/
structure ClResX (R : Expr → Expr → Prop) (P : Prop) where
  dec : Decidable P
  map : Option (ClMap R)

abbrev ClOutX (R : Expr → Expr → Prop) (P : Prop) := Squash (ClResX R P)

@[inline] def ClOutX.mk {R : Expr → Expr → Prop} {P : Prop} (d : Decidable P)
    (map : Option (ClMap R)) : ClOutX R P :=
  Quot.mk _ ⟨d, map⟩

@[inline] def ClMap.record {R : Expr → Expr → Prop} (mp : Option (ClMap R)) (key : Nat)
    (p : ClPair R) : Option (ClMap R) :=
  match mp with
  | none => some ((Std.HashMap.emptyWithCapacity (key % 8 + 8) : ClMap R).insert key p)
  | some m => some (m.insert key p)

/-- Twin of `enterBeq` for a reflexive comparison `R`: `rej` is the O(1)
test that rejects a pair (the data word, or the part of it `R` keeps), and
the descent `rec` runs on a pair `rej` let through. -/
@[inline] def enterCl {R : Expr → Expr → Prop} (hrefl : ∀ a, R a a) (rej : Expr → Expr → Bool)
    (hrej : ∀ a b, rej a b = true → ¬ R a b) (map : Option (ClMap R)) (a b : @& Expr)
    (rec : rej a b = false → Option (ClMap R) → ClOutX R (R a b)) : ClOutX R (R a b) :=
  withAddr a fun pa => withAddr b fun pb =>
  if pa == pb then
    match ptrDec a b with
    | isTrue h => .mk (isTrue (h ▸ hrefl a)) map
    | isFalse _ =>
      if h : rej a b then .mk (isFalse (hrej a b h)) map
      else rec (Bool.of_not_eq_true h) map
  else if h : rej a b then .mk (isFalse (hrej a b h)) map
  else
  have h := Bool.of_not_eq_true h
  if !beqRecursive a then rec h map
  else withExcl a fun ea =>
    if ea then rec h map
    else withExcl b fun eb =>
    if eb then rec h map
    else
    let hit : { h : Bool // h = true → R a b } :=
      match map with
      | some m => clProbeHit m (beqKey pa pb) pa pb a b
      | none => ⟨false, fun h => Bool.noConfusion h⟩
    if hh : hit.1 then .mk (isTrue (hit.2 hh)) map
    else Squash.lift (rec h map) fun r =>
      match r.dec with
      | isTrue hr => .mk (isTrue hr) (ClMap.record r.map (beqKey pa pb) ⟨a, b, pa, pb, hr⟩)
      | d => .mk d r.map

/-- Lean's cached data reads no binder name, binder info or `nonDep`. -/
theorem data_eraseK : ∀ e : Expr, (eraseK e).data = e.data := by
  intro e
  induction e <;> simp_all [eraseK, Expr.data]

theorem dataNe_eraseK (a b : Expr) (h : dataNe a b = true) : eraseK a ≠ eraseK b := by
  intro e
  have : dataWord a = dataWord b := by
    simp only [dataWord]; rw [← data_eraseK a, e, data_eraseK]
  simp [dataNe, this] at h

/-- The key comparison's relation. -/
abbrev KeyR (a b : Expr) : Prop := eraseK a = eraseK b

/-- A child pair of the key comparison: the pointers, the data word, the
memo, the descent `go`. -/
@[inline] def keyChild (map : Option (ClMap KeyR)) (a b : @& Expr)
    (go : Option (ClMap KeyR) → ClOutX KeyR (KeyR a b)) : ClOutX KeyR (KeyR a b) :=
  enterCl (R := KeyR) (fun _ => rfl) dataNe dataNe_eraseK map a b fun _ => go

/-- The key comparison's descent (`eraseK`): names, infos and `nonDep` not
compared, `mdata` compared; a pair of different constructors is unequal, a
pair of leaves decided by their equality. -/
def keyGoX (map : Option (ClMap KeyR)) (a b : @& Expr) : ClOutX KeyR (KeyR a b) :=
  match a, b with
  | .app f x, .app g y =>
    Squash.lift (keyChild map f g fun m => keyGoX m f g) fun r₁ =>
      match r₁.dec with
      | isFalse h => .mk (isFalse (fun e => h (Expr.app.inj e).1)) r₁.map
      | isTrue h => Squash.lift (keyChild r₁.map x y fun m => keyGoX m x y) fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h' => isTrue (by simp only [KeyR, eraseK] at *; simp only [h, h'])
          | isFalse h' => isFalse (fun e => h' (Expr.app.inj e).2))
          r₂.map
  | .lam _ t b _, .lam _ t' b' _ =>
    Squash.lift (keyChild map t t' fun mp => keyGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.lam.inj e).2.1)) r₁.map
      | isTrue h₁ => Squash.lift (keyChild r₁.map b b' fun mp => keyGoX mp b b') fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h₂ => isTrue (by simp only [KeyR, eraseK] at *; simp only [h₁, h₂])
          | isFalse h₂ => isFalse (fun e => h₂ (Expr.lam.inj e).2.2.1))
          r₂.map
  | .forallE _ t b _, .forallE _ t' b' _ =>
    Squash.lift (keyChild map t t' fun mp => keyGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.forallE.inj e).2.1)) r₁.map
      | isTrue h₁ => Squash.lift (keyChild r₁.map b b' fun mp => keyGoX mp b b') fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h₂ => isTrue (by simp only [KeyR, eraseK] at *; simp only [h₁, h₂])
          | isFalse h₂ => isFalse (fun e => h₂ (Expr.forallE.inj e).2.2.1))
          r₂.map
  | .letE _ t v b _, .letE _ t' v' b' _ =>
    Squash.lift (keyChild map t t' fun mp => keyGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (fun e => h₁ (Expr.letE.inj e).2.1)) r₁.map
      | isTrue h₁ => Squash.lift (keyChild r₁.map v v' fun mp => keyGoX mp v v') fun r₂ =>
        match r₂.dec with
        | isFalse h₂ => .mk (isFalse (fun e => h₂ (Expr.letE.inj e).2.2.1)) r₂.map
        | isTrue h₂ => Squash.lift (keyChild r₂.map b b' fun mp => keyGoX mp b b') fun r₃ =>
          .mk (match r₃.dec with
            | isTrue h₃ => isTrue (by simp only [KeyR, eraseK] at *; simp only [h₁, h₂, h₃])
            | isFalse h₃ => isFalse (fun e => h₃ (Expr.letE.inj e).2.2.2.1))
            r₃.map
  | .proj s i x, .proj s' i' x' =>
    if hs : s = s' ∧ i = i' then
      Squash.lift (keyChild map x x' fun mp => keyGoX mp x x') fun r =>
        .mk (match r.dec with
          | isTrue h => isTrue (by
              obtain ⟨rfl, rfl⟩ := hs; simp only [KeyR, eraseK] at *; simp only [h])
          | isFalse h => isFalse (fun e => h (Expr.proj.inj e).2.2))
          r.map
    else .mk (isFalse (fun e => hs ⟨(Expr.proj.inj e).1, (Expr.proj.inj e).2.1⟩)) map
  | .mdata d x, .mdata d' x' =>
    if hd : d = d' then
      Squash.lift (keyChild map x x' fun mp => keyGoX mp x x') fun r =>
        .mk (match r.dec with
          | isTrue h => isTrue (by subst hd; simp only [KeyR, eraseK] at *; simp only [h])
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

/-- The part of the cached data word that `mdata` copies from its body: the
four flags and the loose-variable range (bits 40 to 63), not the hash or
the depth. -/
@[inline] def dataInv (e : Expr) : UInt64 := dataWord e >>> 40

/-- The words' `mdata`-invariant parts differ. -/
@[inline] def clDataNe (a b : Expr) : Bool := dataInv a != dataInv b

theorem clDataNe_self (a : Expr) : clDataNe a a = false := by simp [clDataNe]

/-- **The checker's comparison, as a plain descent**: `mdata` read through,
each pair of children first by `clDataNe`, then the constructor cases as
`keyGoX`'s; two leaves by their equality after `erase`.  `Expr.clEq` is its
memoised execution. -/
def clB : Expr → Expr → Bool
  | .mdata _ x, b => clB x b
  | a, .mdata _ y => clB a y
  | .app f x, .app g y => (!clDataNe f g && clB f g) && (!clDataNe x y && clB x y)
  | .lam _ t b _, .lam _ t' b' _ => (!clDataNe t t' && clB t t') && (!clDataNe b b' && clB b b')
  | .forallE _ t b _, .forallE _ t' b' _ =>
    (!clDataNe t t' && clB t t') && (!clDataNe b b' && clB b b')
  | .letE _ t v b _, .letE _ t' v' b' _ =>
    (!clDataNe t t' && clB t t') && (!clDataNe v v' && clB v v') && (!clDataNe b b' && clB b b')
  | .proj s i x, .proj s' i' x' => decide (s = s' ∧ i = i') && (!clDataNe x x' && clB x x')
  | a, b =>
    if ctorTag a ≠ ctorTag b ∧ ctorTag a ≠ 10 ∧ ctorTag b ≠ 10 then false
    else decide (erase a = erase b)
termination_by a b => sizeOf a + sizeOf b

/-- A child pair: the data word's invariant part, then the descent. -/
def clStep (a b : Expr) : Bool := !clDataNe a b && clB a b

theorem clStep_of {a b : Expr} (h : clDataNe a b = false) : clStep a b = clB a b := by
  simp [clStep, h]

theorem clB_app (f x g y : Expr) : clB (.app f x) (.app g y) = (clStep f g && clStep x y) := by
  rw [clB]; rfl
theorem clB_lam (n n' : Name) (t b t' b' : Expr) (bi bi' : BinderInfo) :
    clB (.lam n t b bi) (.lam n' t' b' bi') = (clStep t t' && clStep b b') := by
  rw [clB]; rfl
theorem clB_forallE (n n' : Name) (t b t' b' : Expr) (bi bi' : BinderInfo) :
    clB (.forallE n t b bi) (.forallE n' t' b' bi') = (clStep t t' && clStep b b') := by
  rw [clB]; rfl
theorem clB_letE (n n' : Name) (t v b t' v' b' : Expr) (nd nd' : Bool) :
    clB (.letE n t v b nd) (.letE n' t' v' b' nd') =
      (clStep t t' && clStep v v' && clStep b b') := by
  rw [clB]; rfl
theorem clB_proj (s s' : Name) (i i' : Nat) (x x' : Expr) :
    clB (.proj s i x) (.proj s' i' x') = (decide (s = s' ∧ i = i') && clStep x x') := by
  rw [clB]; rfl
theorem clB_mdata_l (m : MData) (x b : Expr) : clB (.mdata m x) b = clB x b := by
  rw [clB]

theorem clB_mdata_r (m : MData) (y : Expr) : ∀ a, clB a (.mdata m y) = clB a y
  | .mdata m' x => by rw [clB_mdata_l, clB_mdata_l, clB_mdata_r m y x]
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .app .. | .lam .. | .forallE ..
  | .letE .. | .lit .. | .proj .. => by rw [clB]; intro _ _ h; nomatch h

theorem clB_refl : ∀ a, clB a a = true
  | .mdata m x => by rw [clB_mdata_l, clB_mdata_r, clB_refl x]
  | .app f x => by simp [clB_app, clStep, clDataNe_self, clB_refl f, clB_refl x]
  | .lam _ t b _ => by simp [clB_lam, clStep, clDataNe_self, clB_refl t, clB_refl b]
  | .forallE _ t b _ => by simp [clB_forallE, clStep, clDataNe_self, clB_refl t, clB_refl b]
  | .letE _ t v b _ => by
    simp [clB_letE, clStep, clDataNe_self, clB_refl t, clB_refl v, clB_refl b]
  | .proj _ _ x => by simp [clB_proj, clStep, clDataNe_self, clB_refl x]
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => by simp [clB, ctorTag]

/-- `clB` on a pair neither of which is `mdata` and which is not one
compound constructor twice: the constructors, then `erase` (O(1) there). -/
theorem clB_other (a b : Expr) (ha : ctorTag a ≠ 10) (hb : ctorTag b ≠ 10)
    (hs : ctorTag a = ctorTag b → beqRecursive a = false) :
    clB a b = (ctorTag a == ctorTag b && decide (erase a = erase b)) := by
  cases a <;> cases b <;> simp_all [clB, ctorTag, beqRecursive]

theorem clStep_refl (a : Expr) : clStep a a = true := by
  simp [clStep, clDataNe_self, clB_refl]

/-- `clB` answers `true` only on terms equal after `erase`. -/
theorem clB_sound : ∀ a b, clB a b = true → erase a = erase b := by
  intro a b
  fun_induction clB a b <;> simp_all [erase]

theorem clStep_sound {a b : Expr} (h : clStep a b = true) : erase a = erase b := by
  simp only [clStep, Bool.and_eq_true] at h; exact clB_sound a b h.2

/-- The comparison's relation on a pair of children. -/
abbrev ClR (a b : Expr) : Prop := clStep a b = true

theorem clDataNe_rej (a b : Expr) (h : clDataNe a b = true) : ¬ ClR a b := by
  simp [ClR, clStep, h]

/-- A child pair of the checker's comparison: the pointers, the invariant
part of the data word, the memo, the descent `go`. -/
@[inline] def clChild (map : Option (ClMap ClR)) (a b : @& Expr)
    (go : Option (ClMap ClR) → ClOutX ClR (clB a b = true)) : ClOutX ClR (ClR a b) :=
  enterCl clStep_refl clDataNe clDataNe_rej map a b fun h m =>
    Squash.lift (go m) fun r =>
      .mk (@decidable_of_iff _ _ (by simp only [ClR, clStep_of h]) r.dec) r.map

/-- The checker comparison's descent (`clB`): a `mdata` node is read
through (no rebuilt term), then the constructor cases, each child through
`clChild`. -/
def clGoX (map : Option (ClMap ClR)) (a b : @& Expr) : ClOutX ClR (clB a b = true) :=
  match a, b with
  | .mdata m x, b =>
    Squash.lift (clGoX map x b) fun r => .mk (clB_mdata_l m x b ▸ r.dec) r.map
  | a, .mdata m y =>
    Squash.lift (clGoX map a y) fun r => .mk (clB_mdata_r m y a ▸ r.dec) r.map
  | .app f x, .app g y =>
    Squash.lift (clChild map f g fun m => clGoX m f g) fun r₁ =>
      match r₁.dec with
      | isFalse h => .mk (isFalse (by simp_all [clB_app])) r₁.map
      | isTrue h => Squash.lift (clChild r₁.map x y fun m => clGoX m x y) fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h' => isTrue (by simp_all [clB_app])
          | isFalse h' => isFalse (by simp_all [clB_app]))
          r₂.map
  | .lam _ t b _, .lam _ t' b' _ =>
    Squash.lift (clChild map t t' fun mp => clGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (by simp_all [clB_lam])) r₁.map
      | isTrue h₁ => Squash.lift (clChild r₁.map b b' fun mp => clGoX mp b b') fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h₂ => isTrue (by simp_all [clB_lam])
          | isFalse h₂ => isFalse (by simp_all [clB_lam]))
          r₂.map
  | .forallE _ t b _, .forallE _ t' b' _ =>
    Squash.lift (clChild map t t' fun mp => clGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (by simp_all [clB_forallE])) r₁.map
      | isTrue h₁ => Squash.lift (clChild r₁.map b b' fun mp => clGoX mp b b') fun r₂ =>
        .mk (match r₂.dec with
          | isTrue h₂ => isTrue (by simp_all [clB_forallE])
          | isFalse h₂ => isFalse (by simp_all [clB_forallE]))
          r₂.map
  | .letE _ t v b _, .letE _ t' v' b' _ =>
    Squash.lift (clChild map t t' fun mp => clGoX mp t t') fun r₁ =>
      match r₁.dec with
      | isFalse h₁ => .mk (isFalse (by simp_all [clB_letE])) r₁.map
      | isTrue h₁ => Squash.lift (clChild r₁.map v v' fun mp => clGoX mp v v') fun r₂ =>
        match r₂.dec with
        | isFalse h₂ => .mk (isFalse (by simp_all [clB_letE])) r₂.map
        | isTrue h₂ => Squash.lift (clChild r₂.map b b' fun mp => clGoX mp b b') fun r₃ =>
          .mk (match r₃.dec with
            | isTrue h₃ => isTrue (by simp_all [clB_letE])
            | isFalse h₃ => isFalse (by simp_all [clB_letE]))
            r₃.map
  | .proj s i x, .proj s' i' x' =>
    if hs : s = s' ∧ i = i' then
      Squash.lift (clChild map x x' fun mp => clGoX mp x x') fun r =>
        .mk (match r.dec with
          | isTrue h => isTrue (by simp_all [clB_proj])
          | isFalse h => isFalse (by simp_all [clB_proj]))
          r.map
    else .mk (isFalse (by simp_all [clB_proj])) map
  | a, b =>
    if h : ctorTag a ≠ 10 ∧ ctorTag b ≠ 10 ∧ (ctorTag a = ctorTag b → beqRecursive a = false) then
      -- two leaves of one constructor, or different constructors
      if hc : ctorTag a = ctorTag b then
        .mk (decidable_of_iff (erase a = erase b)
          (by rw [clB_other a b h.1 h.2.1 h.2.2]; simp [hc])) map
      else .mk (isFalse (by rw [clB_other a b h.1 h.2.1 h.2.2]; simp [hc])) map
    else .mk (instDecidableEqBool (clB a b) true) map
termination_by (sizeOf a + sizeOf b)

/-- **The memo maps' key equality**: equal after `eraseK`. -/
def Expr.keyEq (a b : Expr) : Bool := decide (eraseK a = eraseK b)

/-- The pointer test, the cached data word, then the memoised descent. -/
def Expr.keyEqMemo (a b : Expr) : Bool :=
  withPtrEq a b
    (fun _ => if !dataNe a b then
        @decide (eraseK a = eraseK b) (Squash.lift (keyGoX none a b) (fun r => r.dec))
      else false)
    (fun h => by subst h; simp [dataNe_self])

@[csimp] theorem Expr.keyEq_eq_keyEqMemo : @Expr.keyEq = @Expr.keyEqMemo := by
  funext a b
  unfold Expr.keyEq Expr.keyEqMemo withPtrEq
  split
  · congr 1
  · rename_i h
    exact decide_eq_false (dataNe_eraseK a b (by simpa using h))

/-- **InLean's checker equality**: the pointer test, the invariant part of
the cached data word, then the memoised descent (`clB`, executed by
`clGoX`).  It answers `true` only on terms equal after `erase`
(`Expr.clEq_sound`). -/
def Expr.clEq (a b : Expr) : Bool :=
  withPtrEq a b
    (fun _ => !clDataNe a b &&
      @decide (clB a b = true) (Squash.lift (clGoX none a b) (fun r => r.dec)))
    (fun h => by subst h; simp [clDataNe_self, clB_refl])

/-- `Expr.clEq` is the plain descent's answer on the pair. -/
theorem Expr.clEq_eq (a b : Expr) : Expr.clEq a b = clStep a b := by
  unfold Expr.clEq withPtrEq clStep
  cases clDataNe a b <;> simp

theorem Expr.clEq_sound {a b : Expr} (h : Expr.clEq a b = true) : erase a = erase b :=
  clStep_sound (by rwa [Expr.clEq_eq] at h)

/-- **The scoped equality of expressions in InLean's checker**: `Expr.clEq`. -/
scoped instance instBEqExprI : BEq Expr := ⟨Expr.clEq⟩

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
