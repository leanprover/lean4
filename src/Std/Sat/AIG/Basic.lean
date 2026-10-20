/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Data.HashSet
public import Init.Data.Vector.Basic
public import Init.Data.Hashable
public import Init.Data.String.Defs
public import Init.Data.ToString.Macro
import Init.Omega

@[expose] public section

namespace Std
namespace Sat

/-!
This module contains the basic definitions for an AIG (And Inverter Graph) in the style of AIGNET,
as described in https://arxiv.org/pdf/1304.7861.pdf section 3. It consists of an AIG definition,
a description of its semantics and basic operations to construct nodes in the AIG.
-/

variable {α : Type} [Hashable α] [DecidableEq α]

namespace AIG

/--
This datatype is isomorphic to a pair of a `Nat` and a `Bool`, however the `Bool` is stored in the
lowest bit of the `Nat` in order to save memory. It is used to describe an input to an `AIG` circuit
node which consists of a `Nat` describing the input node and a `Bool` saying whether there is an inverter
on the input.
-/
structure Fanin where
  ofRaw ::
    val : Nat
  deriving Hashable, Repr, DecidableEq, Inhabited

namespace Fanin

/--
The public constructor of `Fanin`.
-/
@[inline]
def mk (gate : Nat) (invert : Bool) : Fanin :=
  ⟨gate * 2 ||| invert.toNat⟩

/--
Get the gate.
-/
@[inline]
def gate (f : Fanin) : Nat := f.val / 2

/--
Get the inverter bit.
-/
@[inline]
def invert (f : Fanin) : Bool :=
  1 &&& f.val != 0

/--
Flip the inverter bit according to `val`.
-/
@[inline]
def flip (f : Fanin) (val : Bool) : Fanin := ⟨f.val ^^^ val.toNat⟩

@[simp]
theorem gate_mk : (Fanin.mk g i).gate = g := by
  cases i <;>
    simp [mk, gate, ← Nat.shiftLeft_eq _ 1, ← Nat.shiftRight_eq_div_pow _ 1,
      Nat.shiftRight_or_distrib]

@[simp]
theorem invert_mk : (Fanin.mk g i).invert = i := by
  cases i <;> simp [mk, invert]

@[simp]
theorem gate_flip (f : Fanin) : (f.flip v).gate = f.gate := by
  cases v <;> simp [flip, gate, ← Nat.shiftRight_eq_div_pow _ 1, Nat.shiftRight_xor_distrib]

private theorem invert_eq_testBit (f : Fanin) : f.invert = f.val.testBit 0 := by
  simp [invert, Nat.testBit]

@[simp]
theorem invert_flip (f : Fanin) : (f.flip v).invert = (f.invert ^^ v) := by
  cases v <;> simp [flip, invert_eq_testBit, -Nat.mod_two_not_eq_one]

end Fanin

/--
A circuit node. These are not recursive but instead contain indices into an `AIG`, with inputs indexed by `α`.
-/
inductive Decl (α : Type) where
  /--
  A node with the constant value false. The constant true can be represented
  with a `Ref` to `false` with `invert` set true
  -/
  | false
  /--
  An input node to the circuit.
  -/
  | atom (idx : α)
  /--
  An AIG gate with configurable input nodes and polarity. `l` and `r` are the
  input nodes together with their inverter bit.
  -/
  | gate (l r : Fanin)
  deriving Hashable, Repr, DecidableEq, Inhabited


structure Cache.WF (decls : Array (Decl α)) (cache : HashMap (Decl α) Nat) : Prop where
  /--
  Whenever `cache[decl]?` returns an index into `decls`, `decls[index] = decl`. Note that this
  does not force the cache to be complete for gates, if there is no entry in the cache for some
  gate, it can still exist in `decls`.
  -/
  sound : ∀ (decl : Decl α) (idx : Nat), cache[decl]? = some idx →
    ∃ h : idx < decls.size, decls[idx] = decl
  /--
  The cache knows about every `atom` in `decls`. This is crucial to enforce that all atoms occur
  at most once in the AIG.
  -/
  atoms : ∀ (i : Nat) (h : i < decls.size) (a : α), decls[i] = .atom a → cache[Decl.atom a]? = some i

/--
An empty `Cache` is valid for any `Array Decl` without atoms as it never has a hit.
-/
theorem Cache.WF.empty {decls : Array (Decl α)}
    (hatoms : ∀ (i : Nat) (h : i < decls.size) (a : α), decls[i] ≠ .atom a) : WF decls {} where
  sound := by
    intro decl idx h
    simp at h
  atoms := by
    intro i h a hatom
    exact absurd hatom (hatoms i h a)

/--
Given a `cache`, valid with respect to some `decls`, we can extend the `decls` and the `cache` at
the same time with a `decl` that is not yet in the cache and remain valid.
-/
theorem Cache.WF.push_cache {decls : Array (Decl α)} {cache : HashMap (Decl α) Nat} {decl : Decl α}
    (h : WF decls cache) (hmiss : cache[decl]? = none) :
    WF (decls.push decl) (cache.insert decl decls.size) where
  sound := by
    intro decl' idx hfound
    rw [HashMap.getElem?_insert] at hfound
    split at hfound
    · next heq =>
      simp only [beq_iff_eq] at heq
      simp only [Option.some.injEq] at hfound
      subst heq hfound
      constructor <;> simp
    · rcases h.sound decl' idx hfound with ⟨hlt, heq⟩
      exact ⟨by simp; omega, by simp [Array.getElem_push, hlt, heq]⟩
  atoms := by
    intro i hi a hatom
    rw [HashMap.getElem?_insert]
    rw [Array.getElem_push] at hatom
    split at hatom
    · next hlt =>
      have := h.atoms i hlt a hatom
      split
      · simp_all
      · assumption
    · next hge =>
      have : i = decls.size := by
        simp only [Array.size_push] at hi
        omega
      simp [this, hatom]

/--
A cache for reusing elements from `decls` if they are available.
-/
def Cache (α : Type) [DecidableEq α] [Hashable α] (decls : Array (Decl α)) :=
  { map : HashMap (Decl α) Nat // Cache.WF decls map }

/--
Create an empty `Cache`, valid with respect to any `Array Decl` without atoms.
-/
@[irreducible, inline]
def Cache.empty {decls : Array (Decl α)}
    (hatoms : ∀ (i : Nat) (h : i < decls.size) (a : α), decls[i] ≠ .atom a := by simp) :
    Cache α decls :=
  ⟨{}, WF.empty hatoms⟩

/-
We require the `decls` as an explicit argument because we use `decls.size` so accidentally mutating
`decls` before calling `Cache.insert` will destroy `decl` linearity.
-/
@[inherit_doc Cache.WF.push_cache, irreducible, inline]
def Cache.insert (decls : Array (Decl α)) (cache : Cache α decls) (decl : Decl α)
    (hmiss : cache.val[decl]? = none) : Cache α (decls.push decl) :=
  ⟨cache.val.insert decl decls.size, Cache.WF.push_cache cache.property hmiss⟩

/--
Contains the index of `decl` in `decls` along with a proof that the index is indeed correct.
-/
structure CacheHit (decls : Array (Decl α)) (decl : Decl α) where
  idx : Nat
  hbound : idx < decls.size
  hvalid : decls[idx]'hbound = decl

/--
For a `c : Cache α decls`, any index `idx` that is a cache hit for some `decl` is within bounds of `decls` (i.e. `idx < decls.size`).
-/
theorem Cache.get?_bounds {decls : Array (Decl α)} {idx : Nat} (c : Cache α decls) (decl : Decl α)
    (hfound : c.val[decl]? = some idx) :
    idx < decls.size :=
  (c.property.sound decl idx hfound).1

/--
If `Cache.get? decl` returns `some i` then `decls[i] = decl` holds.
-/
theorem Cache.get?_property {decls : Array (Decl α)} {idx : Nat} (c : Cache α decls) (decl : Decl α)
    (hfound : c.val[decl]? = some idx) :
    decls[idx]'(Cache.get?_bounds c decl hfound) = decl :=
  (c.property.sound decl idx hfound).2

/--
Lookup a `Decl` in a `Cache`.
-/
@[inline]
def Cache.get? (cache : Cache α decls) (decl : Decl α) : Option (CacheHit decls decl) :=
  match hfound : cache.val[decl]? with
  | some hit =>
    some ⟨hit, Cache.get?_bounds _ _ hfound, Cache.get?_property _ _ hfound⟩
  | none => none

theorem Cache.get?_eq_none_iff {decls : Array (Decl α)} {cache : Cache α decls} {decl : Decl α} :
    cache.get? decl = none ↔ cache.val[decl]? = none := by
  simp only [Cache.get?]
  split <;> simp_all

theorem Cache.get?_eq_some_iff {decls : Array (Decl α)} {cache : Cache α decls} {decl : Decl α}
    {hit : CacheHit decls decl} :
    cache.get? decl = some hit ↔ cache.val[decl]? = some hit.idx := by
  simp only [Cache.get?]
  split
  next idx hfound =>
    constructor
    · intro h
      cases h
      exact hfound
    · intro h
      rw [hfound] at h
      cases hit
      simp_all
  next hfound => simp [hfound]

theorem Cache.get?_atom {decls : Array (Decl α)} (cache : Cache α decls) {i : Nat}
    {hi : i < decls.size} {a : α} (h : decls[i] = .atom a) :
    cache.get? (.atom a) = some ⟨i, hi, h⟩ :=
  Cache.get?_eq_some_iff.mpr (cache.property.atoms i hi a h)

theorem Cache.ofAtoms.complete_succ {decls : Array (Decl α)} {map : HashMap (Decl α) Nat} {idx : Nat}
    (hcomp : ∀ (i : Nat) (h : i < decls.size), i < idx → ∀ (a : α),
      decls[i] = .atom a → map[Decl.atom a]? = some i)
    (hnot : ∀ (h : idx < decls.size) (a : α), decls[idx] ≠ .atom a) :
    ∀ (i : Nat) (h : i < decls.size), i < idx + 1 → ∀ (a : α),
      decls[i] = .atom a → map[Decl.atom a]? = some i := by
  intro i h hlt a hatom
  cases Nat.lt_or_ge i idx with
  | inl hlt' => exact hcomp i h hlt' a hatom
  | inr hge =>
    have heq : i = idx := by omega
    subst heq
    exact absurd hatom (hnot h a)

/--
Build a cache for `decls` that contains exactly the atoms of `decls`. This requires that every
atom occurs at most once in `decls`.
-/
def Cache.ofAtoms (decls : Array (Decl α))
    (huniq : ∀ (i j : Nat) (hi : i < decls.size) (hj : j < decls.size) (a : α),
      decls[i] = .atom a → decls[j] = .atom a → i = j) :
    Cache α decls :=
  go 0 {} (by simp) (by omega)
where
  go (idx : Nat) (map : HashMap (Decl α) Nat)
      (hsound : ∀ (decl : Decl α) (i : Nat), map[decl]? = some i →
        ∃ h : i < decls.size, decls[i] = decl)
      (hcomp : ∀ (i : Nat) (h : i < decls.size), i < idx → ∀ (a : α),
        decls[i] = .atom a → map[Decl.atom a]? = some i) :
      Cache α decls :=
    if hidx : idx < decls.size then
      match hdecl : decls[idx] with
      | .atom a =>
        have hsound' : ∀ (decl : Decl α) (i : Nat), (map.insert (.atom a) idx)[decl]? = some i →
            ∃ h : i < decls.size, decls[i] = decl := by
          intro decl i hfound
          rw [HashMap.getElem?_insert] at hfound
          split at hfound
          next heq =>
            simp only [beq_iff_eq] at heq
            simp only [Option.some.injEq] at hfound
            subst heq hfound
            exact ⟨hidx, hdecl⟩
          next => exact hsound decl i hfound
        have hcomp' : ∀ (i : Nat) (h : i < decls.size), i < idx + 1 → ∀ (b : α),
            decls[i] = .atom b → (map.insert (.atom a) idx)[Decl.atom b]? = some i := by
          intro i h hlt b hatom
          rw [HashMap.getElem?_insert]
          split
          next heq =>
            simp only [beq_iff_eq, Decl.atom.injEq] at heq
            subst heq
            have := huniq idx i hidx h a hdecl hatom
            rw [this]
          next heq =>
            have hne : i ≠ idx := by
              intro hcontra
              simp_all
            exact hcomp i h (by omega) b hatom
        go (idx + 1) (map.insert (.atom a) idx) hsound' hcomp'
      | .false => go (idx + 1) map hsound (ofAtoms.complete_succ hcomp (by simp [hdecl]))
      | .gate _ _ => go (idx + 1) map hsound (ofAtoms.complete_succ hcomp (by simp [hdecl]))
    else
      ⟨map, ⟨hsound, fun i h a hatom => hcomp i h (by omega) a hatom⟩⟩
  termination_by decls.size - idx

/--
An `Array Decl` is a Direct Acyclic Graph (DAG) if a gate at index `i` only points to nodes with index lower than `i`.
-/
def IsDAG (α : Type) (decls : Array (Decl α)) : Prop :=
  ∀ ⦃i lhs rhs⦄ (h : i < decls.size),
      decls[i] = .gate lhs rhs → lhs.gate < i ∧ rhs.gate < i

/--
The empty AIG is a DAG.
-/
theorem IsDAG.empty {α : Type} : IsDAG α #[.false] := by
  intro i lhs rhs h
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.lt_one_iff] at h
  simp [h]

end AIG

/--
An And Inverter Graph together with a cache for subterm sharing.
-/
structure AIG (α : Type) [DecidableEq α] [Hashable α] where
  /--
  The circuit itself as an `Array Decl` whose members have indices into said array.
  -/
  decls : Array (AIG.Decl α)
  /--
  The `Decl` cache, valid with respect to `decls`.
  -/
  cache : AIG.Cache α decls
  /--
  In order to be a valid AIG, `decls` must form a DAG.
  -/
  hdag : AIG.IsDAG α decls
  /--
  The `decls` `Array` can never be empty, see `hconst`.
  -/
  hzero : 0 < decls.size
  /--
  We always store `.false` at the first position. This allows us to avoid cache lookups
  -/
  hconst : decls[0]'hzero = .false

namespace AIG

/--
An `AIG` with an empty AIG and cache.
-/
def empty : AIG α :=
  {
    decls := #[.false],
    cache := Cache.empty,
    hdag := IsDAG.empty,
    hzero := by simp
    hconst := by simp
  }

/--
Every atom occurs at most once in an `AIG`.
-/
theorem atom_unique (aig : AIG α) {i j : Nat} {hi : i < aig.decls.size} {hj : j < aig.decls.size}
    {a : α} (h1 : aig.decls[i] = .atom a) (h2 : aig.decls[j] = .atom a) : i = j := by
  have h := aig.cache.get?_atom h1
  rw [aig.cache.get?_atom h2] at h
  cases h
  rfl

/--
The atom `a` occurs in `aig`.
-/
def Mem (aig : AIG α) (a : α) : Prop := (.atom a) ∈ aig.decls

instance : Membership α (AIG α) where
  mem := Mem

/--
A reference to a node within an AIG.
-/
structure Ref (aig : AIG α) where
  gate : Nat
  invert : Bool
  hgate : gate < aig.decls.size

/--
A `Ref` into `aig1` is also valid for `aig2` if `aig1` is smaller than `aig2`.
-/
@[inline, implicit_reducible]
def Ref.cast {aig1 aig2 : AIG α} (ref : Ref aig1) (h : aig1.decls.size ≤ aig2.decls.size) :
    Ref aig2 :=
  { ref with hgate := by have := ref.hgate; omega }


/--
Flip the polarity of `Ref` if `inv` is set.
-/
@[inline]
def Ref.flip {aig : AIG α} (ref : Ref aig) (inv : Bool) : Ref aig :=
  { ref with invert := inv ^^ ref.invert }

/--
Flip the polarity of `Ref`.
-/
@[inline]
def Ref.not {aig : AIG α} (ref : Ref aig) : Ref aig :=
  ref.flip true

/--
A pair of `Ref`s, useful for `LawfulOperator`s that act on two `Ref`s at a time.
-/
structure BinaryInput (aig : AIG α) where
  lhs : Ref aig
  rhs : Ref aig

/--
The `Ref.cast` equivalent for `BinaryInput`.
-/
@[inline]
def BinaryInput.cast {aig1 aig2 : AIG α} (input : BinaryInput aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    BinaryInput aig2 :=
  { input with lhs := input.lhs.cast h, rhs := input.rhs.cast h }

/--
Flip the current inverter settings of the `BinaryInput` if `linv` or `rinv` is set respectively.
-/
@[inline]
def BinaryInput.invert {aig : AIG α} (input : BinaryInput aig) (linv rinv : Bool) :
    BinaryInput aig :=
  { input with lhs := input.lhs.flip linv, rhs := input.rhs.flip rinv }

/--
A collection of 3 of `Ref`s, useful for `LawfulOperator`s that act on three `Ref`s at a time,
in particular multiplexer style functions.
-/
structure TernaryInput (aig : AIG α) where
  discr : Ref aig
  lhs : Ref aig
  rhs : Ref aig

/--
The `Ref.cast` equivalent for `TernaryInput`.
-/
@[inline]
def TernaryInput.cast {aig1 aig2 : AIG α} (input : TernaryInput aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) :
    TernaryInput aig2 :=
  { input with discr := input.discr.cast h, lhs := input.lhs.cast h, rhs := input.rhs.cast h }

/--
An entrypoint into an `AIG`. This can be used to evaluate a circuit, starting at a certain node,
with `AIG.denote` or to construct bigger circuits on top of this specific node.
-/
structure Entrypoint (α : Type) [DecidableEq α] [Hashable α] where
  /--
  The AIG that we are in.
  -/
  aig : AIG α
  /--
  The reference to the node in `aig` that this `Entrypoint` targets.
  -/
  ref : Ref aig

/--
Transform an `Entrypoint` into a graphviz string. Useful for debugging purposes.
-/
def toGraphviz {α : Type} [DecidableEq α] [ToString α] [Hashable α] (entry : Entrypoint α) :
    String :=
  let ⟨⟨decls, _, hinv, _, _⟩, ⟨idx, invert, h⟩⟩ := entry
  let (dag, s) := go "" decls hinv idx h |>.run ∅
  let nodes := s.fold (fun x y ↦ x ++ toGraphvizString decls y) ""
  "Digraph AIG {" ++ nodes ++ dag ++ "}"
where
  go {α : Type} [DecidableEq α] [ToString α] [Hashable α] (acc : String) (decls : Array (Decl α))
      (hinv : IsDAG α decls) (idx : Nat) (hidx : idx < decls.size) :
      StateM (HashSet (Fin decls.size)) String := do
    let fidx : Fin decls.size := Fin.mk idx hidx
    if (← get).contains fidx then
      return acc
    modify (fun s ↦ s.insert fidx)
    match elem : decls[idx] with
    | Decl.false => return acc
    | Decl.atom _ => return acc
    | Decl.gate lhs rhs =>
      let lidx := lhs.gate
      let linv := lhs.invert
      let ridx := rhs.gate
      let rinv := rhs.invert
      let curr := s!"{idx} -> {lidx}{invEdgeStyle linv}; {idx} -> {ridx}{invEdgeStyle rinv};"
      let hlr := hinv hidx elem
      let laig ← go (acc ++ curr) decls hinv lidx (by omega)
      go laig decls hinv ridx (by omega)
  invEdgeStyle (isInv : Bool) : String :=
    if isInv then " [color=red]" else " [color=blue]"
  toGraphvizString {α : Type} [DecidableEq α] [ToString α] [Hashable α] (decls : Array (Decl α))
      (idx : Fin decls.size) : String :=
    match decls[idx] with
    | Decl.false => s!"{idx} [label=\"{false}\", shape=box];"
    | Decl.atom i => s!"{idx} [label=\"{i}\", shape=doublecircle];"
    | Decl.gate .. => s!"{idx} [label=\"{idx} ∧\",shape=trapezium];"

/--
A vector of references into `aig`. This is the `AIG` analog of `BitVec`.
-/
structure RefVec (aig : AIG α) (w : Nat) where
  refs : Vector Fanin w
  hrefs : ∀ (h : i < w), refs[i].gate < aig.decls.size

/--
A sequence of references bundled with their AIG.
-/
structure RefVecEntry (α : Type) [DecidableEq α] [Hashable α] [DecidableEq α] (w : Nat) where
  aig : AIG α
  vec : RefVec aig w

/--
A `RefVec` bundled with constant distance to be shifted by.
-/
structure ShiftTarget (aig : AIG α) (w : Nat) where
  vec : AIG.RefVec aig w
  distance : Nat

/--
A `RefVec` bundled with a `RefVec` as distance to be shifted by.
-/
structure ArbitraryShiftTarget (aig : AIG α) (m : Nat) where
  n : Nat
  target : AIG.RefVec aig m
  distance : AIG.RefVec aig n

/--
A `RefVec` to be extended to `newWidth`.
-/
structure ExtendTarget (aig : AIG α) (newWidth : Nat) where
  w : Nat
  vec : AIG.RefVec aig w

/--
Evaluate an `AIG.Entrypoint` using some assignment for atoms.
-/
def denote (assign : α → Bool) (entry : Entrypoint α) : Bool :=
  go entry.ref.gate entry.aig.decls assign entry.ref.hgate entry.aig.hdag ^^ entry.ref.invert
where
  go (x : Nat) (decls : Array (Decl α)) (assign : α → Bool) (h1 : x < decls.size)
      (h2 : IsDAG α decls) :
      Bool :=
    match h3 : decls[x] with
    | .false => false
    | .atom v => assign v
    | .gate lhs rhs =>
      have := h2 h1 h3
      let lval := go lhs.gate decls assign (by omega) h2
      let rval := go rhs.gate decls assign (by omega) h2
      xor lval lhs.invert && xor rval rhs.invert
  termination_by (x, 0) -- Don't allow reduction, we have large concrete gate entries

/--
Denotation of an `AIG` at a specific `Entrypoint`.
-/
scoped syntax "⟦" term ", " term "⟧" : term

/--
Denotation of an `AIG` at a specific `Entrypoint` with the `Entrypoint` being constructed on the fly.
-/
scoped syntax "⟦" term ", " term ", " term "⟧" : term

macro_rules
| `(⟦$entry, $assign⟧) => `(denote $assign $entry)
| `(⟦$aig, $ref, $assign⟧) => `(denote $assign (Entrypoint.mk $aig $ref))

@[app_unexpander AIG.denote]
meta def unexpandDenote : Lean.PrettyPrinter.Unexpander
  | `($(_) {aig := $aig, start := $start, inv := $hbound} $assign) =>
    `(⟦$aig, ⟨$start, $hbound⟩, $assign⟧)
  | `($(_) $entry $assign) => `(⟦$entry, $assign⟧)
  | _ => throw ()

/--
The denotation of the sub-DAG in the `aig` at node `start` is false for all assignments.
-/
def UnsatAt (aig : AIG α) (start : Nat) (invert : Bool) (h : start < aig.decls.size) : Prop :=
  ∀ assign, ⟦aig, ⟨start, invert, h⟩, assign⟧ = false

/--
The denotation of the `Entrypoint` is false for all assignments.
-/
def Entrypoint.Unsat (entry : Entrypoint α) : Prop :=
  entry.aig.UnsatAt entry.ref.gate entry.ref.invert entry.ref.hgate

/--
Determine whether `ref` is a `Decl.const` with value `b`.
-/
def isConstant (aig : AIG α) (ref : Ref aig) (b : Bool) : Bool :=
  let ⟨gate, invert, hgate⟩ := ref
  let decl := aig.decls[gate]'hgate
  match decl with
  | .false => invert = b
  | _ => false

/--
Get the value of `ref` if it is constant.
-/
def getConstant (aig : AIG α) (ref : Ref aig) : Option Bool :=
  let ⟨gate, invert, hgate⟩ := ref
  let decl := aig.decls[gate]'hgate
  match decl with
  | .false => some invert
  | _ => none

end AIG

end Sat
end Std
