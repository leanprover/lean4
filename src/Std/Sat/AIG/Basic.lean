/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Data.HashSet
import Init.Data.Vector.Basic

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
  private of ::
    private val : Nat
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
theorem invert_flip (f : Fanin) : (f.flip v).invert = f.invert ^^ v := by
  cases v <;> simp [flip, invert_eq_testBit]

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


/--
`Cache.WF xs` is a predicate asserting that a `cache : HashMap (Decl α) Nat` is a valid lookup
cache for `xs : Array (Decl α)`, that is, whenever `cache.find? decl` returns an index into
`xs : Array Decl`, `xs[index] = decl`. Note that this predicate does not force the cache to be
complete, if there is no entry in the cache for some node, it can still exist in the AIG.
-/
inductive Cache.WF : Array (Decl α) → HashMap (Decl α) Nat → Prop where
  /--
  An empty `Cache` is valid for any `Array Decl` as it never has a hit.
  -/
  | empty : WF decls {}
  /--
  Given a `cache`, valid with respect to some `decls`, we can extend the `decls` without
  extending the cache and remain valid.
  -/
  | push_id (h : WF decls cache) : WF (decls.push decl) cache
  /--
  Given a `cache`, valid with respect to some `decls`, we can extend the `decls`
  and the `cache` at the same time with the same values and remain valid.
  -/
  | push_cache (h : WF decls cache) : WF (decls.push decl) (cache.insert decl decls.size)

/--
A cache for reusing elements from `decls` if they are available.
-/
def Cache (α : Type) [DecidableEq α] [Hashable α] (decls : Array (Decl α)) :=
  { map : HashMap (Decl α) Nat // Cache.WF decls map }

/--
Create an empty `Cache`, valid with respect to any `Array Decl`.
-/
@[irreducible, inline]
def Cache.empty {decls : Array (Decl α)} : Cache α decls := ⟨{}, WF.empty⟩

@[inherit_doc Cache.WF.push_id, irreducible, inline]
def Cache.noUpdate (cache : Cache α decls) : Cache α (decls.push decl) :=
  ⟨cache.val, Cache.WF.push_id cache.property⟩

/-
We require the `decls` as an explicit argument because we use `decls.size` so accidentally mutating
`decls` before calling `Cache.insert` will destroy `decl` linearity.
-/
@[inherit_doc Cache.WF.push_cache, irreducible, inline]
def Cache.insert (decls : Array (Decl α)) (cache : Cache α decls) (decl : Decl α) :
    Cache α (decls.push decl) :=
  ⟨cache.val.insert decl decls.size, Cache.WF.push_cache cache.property⟩

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
    idx < decls.size := by
  rcases c with ⟨cache, hcache⟩
  induction hcache with
  | empty => simp at hfound
  | push_id wf ih =>
    specialize ih hfound
    simp
    omega
  | @push_cache _ _ decl' wf ih =>
    simp only [HashMap.getElem?_insert, beq_iff_eq] at hfound
    split at hfound <;> rename_i h
    · subst h
      simp_all
    · specialize ih hfound
      simp
      omega

/--
If `Cache.get? decl` returns `some i` then `decls[i] = decl` holds.
-/
theorem Cache.get?_property {decls : Array (Decl α)} {idx : Nat} (c : Cache α decls) (decl : Decl α)
    (hfound : c.val[decl]? = some idx) :
    decls[idx]'(Cache.get?_bounds c decl hfound) = decl := by
  rcases c with ⟨cache, hcache⟩
  induction hcache generalizing decl with
  | empty => simp at hfound
  | push_id wf ih =>
    rw [Array.getElem_push]
    split
    · apply ih
      simp [hfound]
    · next hbounds =>
      exfalso
      apply hbounds
      specialize ih _ hfound
      apply Array.lt_of_getElem
      assumption
  | push_cache wf ih =>
    rename_i decl'
    rw [Array.getElem_push]
    split
    · simp only [HashMap.getElem?_insert] at hfound
      match heq : decl == decl' with
      | true =>
        simp only [beq_iff_eq] at heq
        simp [heq] at hfound
        omega
      | false =>
        apply ih
        simpa [BEq.symm_false heq] using hfound
    · next hbounds =>
      simp only [HashMap.getElem?_insert] at hfound
      match heq : decl == decl' with
      | true =>
        apply Eq.symm
        simpa using heq
      | false =>
        exfalso
        apply hbounds
        simp only [BEq.symm_false heq, cond_false] at hfound
        specialize ih _ hfound
        apply Array.lt_of_getElem
        assumption

/--
Lookup a `Decl` in a `Cache`.
-/
@[irreducible, inline]
def Cache.get? (cache : Cache α decls) (decl : Decl α) : Option (CacheHit decls decl) :=
  match hfound : cache.val[decl]? with
  | some hit =>
    some ⟨hit, Cache.get?_bounds _ _ hfound, Cache.get?_property _ _ hfound⟩
  | none => none

/--
An `Array Decl` is a Direct Acyclic Graph (DAG) if a gate at index `i` only points to nodes with index lower than `i`.
-/
def IsDAG (α : Type) (decls : Array (Decl α)) : Prop :=
  ∀ {i lhs rhs} (h : i < decls.size),
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
@[inline]
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
def unexpandDenote : Lean.PrettyPrinter.Unexpander
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
Add a new and inverter gate to the AIG in `aig`. Note that this version is only meant for proving,
for production purposes use `AIG.mkGateCached` and equality theorems to this one.
-/
def mkGate (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  let g := aig.decls.size
  let decls :=
    aig.decls.push <| .gate (.mk input.lhs.gate input.lhs.invert) (.mk input.rhs.gate input.rhs.invert)
  let cache := aig.cache.noUpdate
  have hdag := by
    intro i lhs' rhs' h1 h2
    simp only [Array.getElem_push] at h2
    split at h2
    · apply aig.hdag <;> assumption
    · injection h2 with hl hr
      have := input.lhs.hgate
      have := input.rhs.hgate
      simp [← hl, ← hr]
      omega
  have hzero := by simp [decls]
  have hconst := by simp [decls, Array.getElem_push, aig.hzero, aig.hconst]
  ⟨⟨decls, cache, hdag, hzero, hconst⟩, ⟨g, false, by simp [g, decls]⟩⟩

/--
Add a new input node to the AIG in `aig`. Note that this version is only meant for proving,
for production purposes use `AIG.mkAtomCached` and equality theorems to this one.
-/
def mkAtom (aig : AIG α) (n : α) : Entrypoint α :=
  let g := aig.decls.size
  let decls := aig.decls.push (.atom n)
  let cache := aig.cache.noUpdate
  have hdag := by
    intro i lhs rhs h1 h2
    simp only [Array.getElem_push] at h2
    split at h2
    · apply aig.hdag <;> assumption
    · contradiction
  have hzero := by simp [decls]
  have hconst := by simp [decls, Array.getElem_push, aig.hzero, aig.hconst]
  ⟨⟨decls, cache, hdag, hzero, hconst⟩, ⟨g, false, by simp [g, decls]⟩⟩

/--
Add a new constant node to `aig`. Note that this version is only meant for proving,
for production purposes use `AIG.mkConstCached` and equality theorems to this one.
-/
def mkConst (aig : AIG α) (val : Bool) : Entrypoint α :=
  let g := aig.decls.size
  let decls := aig.decls.push .false
  let cache := aig.cache.noUpdate
  have hdag := by
    intro i lhs rhs h1 h2
    simp only [Array.getElem_push] at h2
    split at h2
    · apply aig.hdag <;> assumption
    · contradiction
  have hzero := by simp [decls]
  have hconst := by simp [decls, Array.getElem_push, aig.hzero, aig.hconst]
  ⟨⟨decls, cache, hdag, hzero, hconst⟩, ⟨g, val, by simp [g, decls]⟩⟩

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
