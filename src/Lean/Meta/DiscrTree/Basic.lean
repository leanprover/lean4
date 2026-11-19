/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.DiscrTree.Types
public import Lean.CoreM
import Init.Data.Range.Polymorphic.Iterators
import Init.Omega
import Std.Data.HashMap.Basic
public section
namespace Lean.Meta.DiscrTree

def mkNoindexAnnotation (e : Expr) : Expr :=
  mkAnnotation `noindex e

def hasNoindexAnnotation (e : Expr) : Bool :=
  annotation? `noindex e |>.isSome

instance : Inhabited (Trie α) where
  default := .node #[] #[]

instance : Inhabited (DiscrTree α) where
  default := {}

def empty : DiscrTree α := { root := {} }

/-- Whether `t` is a `chain` or `node`. -/
@[expose, inline] def Trie.isForced : Trie α → Bool
  | .chain .. | .node .. => true
  | .lazy _ | .suffix .. => false

/-- A `chain` or `node`, as returned by `Trie.force`. -/
abbrev Trie.Forced (α : Type) := { t : Trie α // t.isForced }

instance : Inhabited (Trie.Forced α) := ⟨⟨.node #[] #[], rfl⟩⟩

/-- The first key of the suffix `.suffix ks i v` as a `chain`, or its value as a `node`. -/
private def Trie.unfoldSuffix (ks : Array Key) (i : Nat) (v : α) : Trie.Forced α :=
  if h : i < ks.size then ⟨.chain ks[i] (.suffix ks (i + 1) v), rfl⟩ else ⟨.node #[v] #[], rfl⟩

-- out of line, as traversals that need to be fast handle suffixes before forcing
@[noinline] private def Trie.forceSlow : Trie α → Trie.Forced α
  | .lazy t =>
    let t := t.get
    if h : t.isForced then ⟨t, h⟩ else
    match t with
    | .suffix ks i v => unfoldSuffix ks i v
    | _ => panic! "merged discrimination tree node is lazy"
  | .suffix ks i v => unfoldSuffix ks i v
  | t => if h : t.isForced then ⟨t, h⟩ else default  -- unreachable

/--
The node `t` stands for as a `chain` or `node`: merges a `lazy` node and unfolds the first key of a
`suffix`.
-/
@[inline] def Trie.force (t : Trie α) : Trie.Forced α :=
  if h : t.isForced then ⟨t, h⟩ else t.forceSlow

instance : ToExpr Key where
  toTypeExpr := mkConst ``Key
  toExpr k   := match k with
   | .const n a => mkApp2 (mkConst ``Key.const) (toExpr n) (toExpr a)
   | .fvar id a => mkApp2 (mkConst ``Key.fvar) (toExpr id) (toExpr a)
   | .lit l => mkApp (mkConst ``Key.lit) (toExpr l)
   | .star => mkConst ``Key.star
   | .other => mkConst ``Key.other
   | .arrow => mkConst ``Key.arrow
   | .proj n i a => mkApp3 (mkConst ``Key.proj) (toExpr n) (toExpr i) (toExpr a)

def Key.lt : Key → Key → Bool
  | .lit v₁,        .lit v₂        => v₁ < v₂
  | .fvar n₁ a₁,    .fvar n₂ a₂    => Name.quickLt n₁.name n₂.name || (n₁ == n₂ && a₁ < a₂)
  | .const n₁ a₁,   .const n₂ a₂   => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | .proj s₁ i₁ a₁, .proj s₂ i₂ a₂ => Name.quickLt s₁ s₂ || (s₁ == s₂ && i₁ < i₂) || (s₁ == s₂ && i₁ == i₂ && a₁ < a₂)
  | k₁,             k₂             => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

def Key.format : Key → Format
  | .star            => "*"
  | .other           => "◾"
  | .lit (.natVal v) => Std.format v
  | .lit (.strVal v) => repr v
  | .const k _       => Std.format k
  | .proj s i _      => Std.format s ++ "." ++ Std.format i
  | .fvar k _        => Std.format k.name
  | .arrow           => "∀"

instance : ToFormat Key := ⟨Key.format⟩

partial def Trie.format [ToFormat α] : Trie α → Format
  | .chain k c => Format.group $ Format.paren $
    "chain " ++ Std.format k ++ " => " ++ format c
  | .node vs cs => Format.group $ Format.paren $
    "node" ++ (if vs.isEmpty then Format.nil else " " ++ Std.format vs)
    ++ Format.join (cs.toList.map fun ⟨k, c⟩ => Format.line ++ Format.paren (Std.format k ++ " => " ++ format c))
  | .lazy t => format t.get
  | t@(.suffix ..) => format t.force.1

instance [ToFormat α] : ToFormat (Trie α) := ⟨Trie.format⟩

partial def format [ToFormat α] (d : DiscrTree α) : Format :=
  let (_, r) := d.root.foldl
    (fun (p : Bool × Format) k c =>
      (false, p.2 ++ (if p.1 then Format.nil else Format.line) ++ Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r

instance [ToFormat α] : ToFormat (DiscrTree α) := ⟨format⟩

/--
Helper function for converting an entry (i.e., `Array Key`) to the discrimination tree into
`MessageData` that is more user-friendly. We use this function to implement diagnostic information.
-/
partial def keysAsPattern (keys : Array Key) : CoreM MessageData := do
  go (parenIfNonAtomic := false) |>.run' keys.toList
where
  next? : StateRefT (List Key) CoreM (Option Key) := do
    let key :: keys ← get | return none
    set keys
    return some key

  mkApp (f : MessageData) (args : Array MessageData) (parenIfNonAtomic : Bool) : CoreM MessageData := do
    if args.isEmpty then
      return f
    else
      let mut r := m!""
      for arg in args do
        r := r ++ Format.line ++ arg
      r := f ++ .nest 2 r
      if parenIfNonAtomic then
        return .paren r
      else
        return .group r

  go (parenIfNonAtomic := true) : StateRefT (List Key) CoreM MessageData := do
    let some key ← next? | return .nil
    match key with
    | .const declName nargs =>
      mkApp m!"{← mkConstWithLevelParams declName}" (← goN nargs) parenIfNonAtomic
    | .fvar fvarId nargs =>
      mkApp m!"{mkFVar fvarId}" (← goN nargs) parenIfNonAtomic
    | .proj _ i nargs =>
      mkApp m!"{← go}.{i+1}" (← goN nargs) parenIfNonAtomic
    | .arrow =>
      mkApp m!"∀ " (← goN 1) parenIfNonAtomic
    | .star => return "_"
    | .other => return "<other>"
    | .lit (.natVal v) => return m!"{v}"
    | .lit (.strVal v) => return m!"{v}"

  goN (num : Nat) : StateRefT (List Key) CoreM (Array MessageData) := do
    let mut r := #[]
    for _ in *...num do
      r := r.push (← go)
    return r

private def createNodes (keys : Array Key) (v : α) (i : Nat) : Trie α :=
  .suffix keys i v

/--
If `vs` contains an element `v'` such that `v == v'`, then replace `v'` with `v`.
Otherwise, push `v`.
See issue #2155
Recall that `BEq α` may not be Lawful.
-/
private def insertVal [BEq α] (vs : Array α) (v : α) : Array α :=
  loop 0
where
  loop (i : Nat) : Array α :=
    if h : i < vs.size then
      if v == vs[i] then
        vs.set i v
      else
        loop (i+1)
    else
      vs.push v
  termination_by vs.size - i

private def insertAux [BEq α] (keys : Array Key) (v : α) (i : Nat) (t : Trie α) : Trie α :=
  match t.force with
  | ⟨.chain k c, _⟩ =>
    if h : i < keys.size then
      if keys[i] == k then
        .chain k (insertAux keys v (i+1) c)
      else
        .node #[] <|
          #[(k, c)].binInsert (fun a b => a.1 < b.1) (keys[i], createNodes keys v (i+1))
    else
      .node #[v] #[(k, c)]
  | ⟨.node vs cs, _⟩ =>
    if h : i < keys.size then
      let k := keys[i]
      let c := Id.run $ cs.binInsertM
          (fun a b => a.1 < b.1)
          (fun ⟨_, s⟩ => let c := insertAux keys v (i+1) s; (k, c)) -- merge with existing
          (fun _ => let c := createNodes keys v (i+1); (k, c))
          (k, default)
      .node vs c
    else
      .node (insertVal vs v) cs
termination_by keys.size - i

def insertKeyValue [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]!
    { d with root :=
        d.root.alter k fun
          | none => some <| createNodes keys v 1
          | some c => insertAux keys v 1 c
    }

/--
Termination measure of `mergeTries`: the number of nodes of a trie, counting each remaining key of a
`suffix` as a node.
-/
private noncomputable def Trie.weight : Trie α → Nat
  | .chain _ c => weight c + 1
  | .node _ ⟨cs⟩ => weights cs + 1
  | .lazy _ => 0
  | .suffix ks i _ => ks.size - i + 1
where
  weights : List (Key × Trie α) → Nat
    | [] => 0
    | (_, c) :: cs => weight c + weights cs

/-- The values and children of `t`, unfolding the first key of a `suffix`. -/
private def Trie.unfold : Trie α → Array α × Array (Key × Trie α)
  | .chain k c => (#[], #[(k, c)])
  | .node vs cs => (vs, cs)
  | .suffix ks i v =>
    if h : i < ks.size then (#[], #[(ks[i], .suffix ks (i + 1) v)]) else (#[v], #[])
  | .lazy _ => unreachable!

private theorem Trie.weight_lt_of_mem_unfold {t : Trie α} (h : p ∈ t.unfold.2) :
    p.2.weight < t.weight := by
  match t with
  | .chain k c => simp_all [unfold, weight]
  | .node vs ⟨cs⟩ =>
    simp only [unfold, List.mem_toArray] at h
    simp only [weight]
    suffices p.2.weight ≤ weight.weights cs by omega
    induction cs with
    | nil => simp at h
    | cons q cs ih => cases List.mem_cons.1 h <;> simp_all [weight.weights] <;> omega
  | .suffix ks i v => simp only [unfold] at h; split at h <;> simp_all [weight]; omega
  | .lazy _ => simp [unfold, panicWithPosWithDecl, panic, panicCore, default, Array.empty] at h

/-- Termination measure of `mergeTries`: the maximal weight of the given tries. -/
private noncomputable def maxWeight (ts : Array (Trie α)) : Nat :=
  ts.toList.foldr (fun t m => max t.weight m) 0

private theorem weight_le_maxWeight {ts : Array (Trie α)} (h : t ∈ ts) :
    t.weight ≤ maxWeight ts := by
  rcases ts with ⟨ts⟩
  simp only [maxWeight, List.mem_toArray] at *
  induction ts with
  | nil => simp at h
  | cons t ts ih => cases List.mem_cons.1 h <;> simp_all <;> omega

private theorem maxWeight_lt {g : Array (Trie α)} (hne : 0 < g.size) (h : ∀ c ∈ g, c.weight < n) :
    maxWeight g < n := by
  rcases g with ⟨g⟩
  simp only [maxWeight, List.mem_toArray, List.size_toArray] at *
  induction g with
  | nil => simp at hne
  | cons c g ih =>
    cases g with
    | nil => simp_all
    | cons => simp_all; omega

/--
Groups the given tries by key, keeping each group in the given order. Groups appear in the order in
which their keys are last encountered. Each group records that it is nonempty and that its tries
satisfy `P`, for the termination of `mergeTries`.
-/
private def groupByKey (ts : Array (Array (Key × Trie α))) (P : Trie α → Prop)
    (hP : ∀ cs ∈ ts, ∀ p ∈ cs, P p.2) :
    Array (Key × {g : Array (Trie α) // 0 < g.size ∧ ∀ c ∈ g, P c}) := Id.run do
  let mut idx : Std.HashMap Key Nat := {}
  let mut groups : Array (Key × {g : Array (Trie α) // 0 < g.size ∧ ∀ c ∈ g, P c} × Nat) := #[]
  let mut pos := 0
  for hcs : cs in ts do
    for hp : p in cs do
      have hc : P p.2 := hP cs hcs p hp
      match idx[p.1]? with
      | some i =>
        groups := groups.modify i fun (k, ⟨g, hg⟩, _) =>
          (k, ⟨g.push p.2, by simp, by simpa [or_imp, forall_and, hc] using hg.2⟩, pos)
      | none =>
        idx := idx.insert p.1 groups.size
        groups := groups.push (p.1, ⟨#[p.2], by simp, by simpa⟩, pos)
      pos := pos + 1
  return groups.qsort (·.2.2 < ·.2.2) |>.map fun (k, g, _) => (k, g)

mutual
/--
Merges tries of several modules, given in module order, as if their entries had been inserted in
this order. Only the root node is merged eagerly; see `mergeGroup`. The given tries must not contain
`lazy` nodes.
-/
private def mergeTries [BEq α] (ts : Array (Trie α)) : Trie α :=
  let nodes := ts.map Trie.unfold
  -- `insertVal` replaces equal values in place, so the values of a single trie need no re-insertion
  let vs := nodes.foldl (init := #[]) fun vs (tvs, _) =>
    if vs.isEmpty then tvs else tvs.foldl insertVal vs
  let cs := groupByKey (nodes.map (·.2)) (·.weight < maxWeight ts) (by
      simp only [nodes, Array.map_map, Array.mem_map, Function.comp_apply]
      rintro _ ⟨t, ht, rfl⟩ p hp
      exact Nat.lt_of_lt_of_le (Trie.weight_lt_of_mem_unfold hp) (weight_le_maxWeight ht))
    |>.qsort (·.1 < ·.1) |>.map fun kg => (kg.1, mergeGroup kg.2.1)
  if h : vs.isEmpty ∧ cs.size = 1 then .chain cs[0].1 cs[0].2 else .node vs cs
termination_by (maxWeight ts, 0)
decreasing_by exact Prod.Lex.left _ _ (maxWeight_lt kg.2.2.1 kg.2.2.2)

/-- Merges the tries of a group on first access, sharing a trie that is alone in its group. -/
private def mergeGroup [BEq α] (g : Array (Trie α)) : Trie α :=
  if h : g.size = 1 then g[0] else .lazy (Thunk.mk fun _ => mergeTries g)
termination_by (maxWeight g, 1)
decreasing_by exact Prod.Lex.right _ (by decide)
end

/--
Inserts the given entries in order and returns the root of the resulting tree in the form expected
by `ofModuleRoots`, e.g. for storing the tree of a single module in its olean. Root keys are listed
in the order of their last insertion.
-/
def moduleRootsOf [BEq α] (entries : Array (Array Key × α)) : Array (Key × Trie α) := Id.run do
  let mut d : DiscrTree α := {}
  let mut last : Std.HashMap Key Nat := {}
  let mut i := 0
  for (ks, v) in entries do
    if h : 0 < ks.size then
      last := last.insert ks[0] i
    d := d.insertKeyValue ks v
    i := i + 1
  let keys := last.toArray.qsort (·.2 < ·.2)
  return keys.map fun (k, _) => (k, d.root.find? k |>.getD default)

/--
Merges per-module trees, given as `moduleRootsOf` in module order, into a tree equal to the one
obtained by inserting the entries of all modules in this order, down to the iteration order of its
root. Only the root is built eagerly: subtrees occurring in a single module are shared with the given
tries, and nodes occurring in several modules are merged on first access.
-/
def ofModuleRoots [BEq α] (mods : Array (Array (Key × Trie α))) : DiscrTree α :=
  -- `PersistentHashMap.alter` moves updated keys to the end of their collision node, so inserting
  -- root keys in order of last insertion reproduces the iteration order of `root`
  { root := groupByKey mods (fun _ => True) (by simp) |>.foldl (init := {}) fun root (k, g) =>
      root.insert k (mergeGroup g.1) }

@[deprecated insertKeyValue (since := "2026-01-02")]
def insertCore [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  insertKeyValue d keys v

private def getEntriesWithKeysAux (keys : Array Key) (i : Nat) (t : Trie α) : Array α :=
  match t.force with
  | ⟨.chain k c, _⟩ =>
    if h : i < keys.size then
      if keys[i] == k then
        getEntriesWithKeysAux keys (i + 1) c
      else
        #[]
    else
      #[]
  | ⟨.node vs cs, _⟩ =>
    if h : i < keys.size then
      let k := keys[i]
      match cs.binSearch (k, default) (fun a b => a.1 < b.1) with
      | none => #[]
      | some (_, t) => getEntriesWithKeysAux keys (i + 1) t
    else
      vs
termination_by keys.size - i

/--
Returns all entries that have exactly the provided key sequence.
-/
def getEntriesWithKeys (d : DiscrTree α) (keys : Array Key) : Array α :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]!
    match d.root.find? k with
    | none => #[]
    | some t => getEntriesWithKeysAux keys 1 t

end Lean.Meta.DiscrTree
