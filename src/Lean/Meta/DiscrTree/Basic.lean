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
public section
namespace Lean.Meta.DiscrTree

def mkNoindexAnnotation (e : Expr) : Expr :=
  mkAnnotation `noindex e

def hasNoindexAnnotation (e : Expr) : Bool :=
  annotation? `noindex e |>.isSome

instance : Inhabited (Trie α) where
  default := .empty

instance : Inhabited (DiscrTree α) where
  default := {}

def empty : DiscrTree α := { root := {} }

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
  | .empty => "empty"
  | .values vs t => Format.group $ Format.paren $
    "values" ++ (if vs.isEmpty then Format.nil else " " ++ Std.format vs)
    ++ Format.line ++ format t
  | .path ks t => Format.group $ Format.paren $
    "path" ++ (if ks.isEmpty then Format.nil else " " ++ Std.format ks)
    ++ Format.line ++ format t
  | .branch cs => Format.group $ Format.paren $
    "node"
    ++ Format.join (cs.toList.map fun ⟨k, c⟩ =>
      Format.line ++ Format.paren (Std.format k ++ " => " ++ format c))

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

/-- Creates a trie with the keys `keys` starting at `i`, and the value `v` as the leaf -/
private partial def createNodes (keys : Array Key) (v : α) (i : Nat) : Trie α :=
  let t := .values #[v] .empty
  if i < keys.size then
    .path (keys.extract i keys.size) t
  else
    t

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

/--
Calculate the length of the common prefix of two arrays of keys.
The parameter `i` marks the starting position in the second array.
-/
def commonPrefix (ks1 : Array Key) (ks2 : Array Key) (i : Nat) : Nat :=
  go 0
where
  go (j : Nat) : Nat :=
    if h1 : j < ks1.size then
      if h2 : j + i < ks2.size then
        if ks1[j] == ks2[j + i] then
          go (j + 1)
        else
          j
      else
        j
    else
      j
  termination_by ks1.size - j

/-- Smart constructor around branch that ensures the ordering -/
private def branch2 (k1 : Key) (t1 : Trie α) (k2 : Key) (t2 : Trie α) : Trie α :=
  if k1 < k2 then
    .branch #[(k1, t1), (k2, t2)]
  else
    .branch #[(k2, t2), (k1, t1)]

/-- Smart constructor ensuring that `.values` constructors are not nested -/
private partial def insertHere [BEq α] (v : α) : Trie α → Trie α
  | .values vs t => .values (insertVal vs v) t
  | t => .values #[v] t

private partial def insertAux [BEq α] (keys : Array Key) (v : α) (i : Nat) (t : Trie α) :
    Trie α :=
  if h : i < keys.size then
    -- we have to walk down the tree some more
    match t with
    | .empty => createNodes keys v i
    | .values _ t => insertAux keys v i t
    | .path ks t =>
      let j := commonPrefix ks keys i
      let t' := -- the new tree after the common prefix
        if h1 : j < ks.size then
          if h2 : i + j < keys.size then
            -- we must branch at offset j
            let k1 := ks[j]
            let t1 := if j + 1 < ks.size then .path (ks.extract (j + 1) ks.size) t else t
            let k2 := keys[i + j]
            let t2 := createNodes keys v (i + j + 1)
            branch2 k1 t1 k2 t2
          else
            -- the entry keys are a prefix of the path in the node: split the path, insert the value
            .values #[v] (.path (ks.extract j ks.size) t)
        else
          -- the node path is a prefix of the new entry
          insertAux keys v (i + j) t
      if 0 < j then
        -- add a .path for the common prefix, if present
        .path (ks.extract 0 j) t'
      else
        t'
    | .branch cs =>
      let k := keys[i]
      let c := Id.run $ cs.binInsertM
          (fun a b => a.1 < b.1)
          (fun ⟨_, s⟩ => let c := insertAux keys v (i+1) s; (k, c)) -- merge with existing
          (fun _ => let c := createNodes keys v (i+1); (k, c))
          (k, default)
      .branch c
  else
    -- this is where we need to insert the value
    insertHere v t

def insertKeyValue [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]!
    match d.root.find? k with
    | none =>
      let c := createNodes keys v 1
      { root := d.root.insert k c }
    | some c =>
      let c := insertAux keys v 1 c
      { root := d.root.insert k c }

def getValues : Trie α → Array α
  | .values vs _ => vs
  | _ => #[]

@[deprecated insertKeyValue (since := "2026-01-02")]
def insertCore [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  insertKeyValue d keys v

end Lean.Meta.DiscrTree
