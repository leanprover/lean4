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

/--
The node `t` stands for as a `chain` or `node`: merges a `lazy` node and unfolds the first key of a
`suffix`.
-/
@[inline] def Trie.force : Trie α → Trie α
  | .lazy t => t.get
  | .suffix ks i v => if h : i < ks.size then .chain ks[i] (.suffix ks (i + 1) v) else .node #[v] #[]
  | t => t

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
  | t@(.suffix ..) => format t.force

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
  match i, t.force with
  | i, .chain k c =>
    if h : i < keys.size then
      if keys[i] == k then
        .chain k (insertAux keys v (i+1) c)
      else
        .node #[] <|
          #[(k, c)].binInsert (fun a b => a.1 < b.1) (keys[i], createNodes keys v (i+1))
    else
      .node #[v] #[(k, c)]
  | i, .node vs cs =>
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
  | _, .lazy _ | _, .suffix .. => unreachable!
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
Groups the given tries by key, keeping each group in the given order. Groups appear in the order in
which their keys are last encountered.
-/
private def groupByKey (ts : Array (Array (Key × Trie α))) : Array (Key × Array (Trie α)) := Id.run do
  let mut idx : Std.HashMap Key Nat := {}
  let mut groups : Array (Key × Array (Trie α) × Nat) := #[]
  let mut pos := 0
  for cs in ts do
    for (k, c) in cs do
      match idx[k]? with
      | some i => groups := groups.modify i fun (k, g, _) => (k, g.push c, pos)
      | none =>
        idx := idx.insert k groups.size
        groups := groups.push (k, #[c], pos)
      pos := pos + 1
  return groups.qsort (·.2.2 < ·.2.2) |>.map fun (k, g, _) => (k, g)

mutual
/--
Merges tries of several modules, given in module order, as if their entries had been inserted in
this order. Only the root node is merged eagerly; see `mergeGroup`.
-/
private partial def mergeTries [BEq α] (ts : Array (Trie α)) : Trie α :=
  let nodes := ts.map fun t => match t.force with
    | .chain k c => (#[], #[(k, c)])
    | .node vs cs => (vs, cs)
    | .lazy _ | .suffix .. => unreachable!
  -- `insertVal` replaces equal values in place, so the values of a single trie need no re-insertion
  let vs := nodes.foldl (init := #[]) fun vs (tvs, _) =>
    if vs.isEmpty then tvs else tvs.foldl insertVal vs
  let cs := groupByKey (nodes.map (·.2)) |>.qsort (·.1 < ·.1) |>.map fun (k, g) => (k, mergeGroup g)
  if h : vs.isEmpty ∧ cs.size = 1 then .chain cs[0].1 cs[0].2 else .node vs cs

/-- Merges the tries of a group on first access, sharing a trie that is alone in its group. -/
private partial def mergeGroup [BEq α] (g : Array (Trie α)) : Trie α :=
  if h : g.size = 1 then g[0] else .lazy (Thunk.mk fun _ => mergeTries g)
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
  { root := groupByKey mods |>.foldl (init := {}) fun root (k, g) => root.insert k (mergeGroup g) }

@[deprecated insertKeyValue (since := "2026-01-02")]
def insertCore [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  insertKeyValue d keys v

private def getEntriesWithKeysAux (keys : Array Key) (i : Nat) (t : Trie α) : Array α :=
  match i, t.force with
  | i, .chain k c =>
    if h : i < keys.size then
      if keys[i] == k then
        getEntriesWithKeysAux keys (i + 1) c
      else
        #[]
    else
      #[]
  | i, .node vs cs =>
    if h : i < keys.size then
      let k := keys[i]
      match cs.binSearch (k, default) (fun a b => a.1 < b.1) with
      | none => #[]
      | some (_, t) => getEntriesWithKeysAux keys (i + 1) t
    else
      vs
  | _, .lazy _ | _, .suffix .. => unreachable!
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
