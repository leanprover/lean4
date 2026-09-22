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
  default := .node #[] #[]

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
  | .chain k c => Format.group $ Format.paren $
    "chain " ++ Std.format k ++ " => " ++ format c
  | .node vs cs => Format.group $ Format.paren $
    "node" ++ (if vs.isEmpty then Format.nil else " " ++ Std.format vs)
    ++ Format.join (cs.toList.map fun ⟨k, c⟩ => Format.line ++ Format.paren (Std.format k ++ " => " ++ format c))

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

namespace Trie

/--
Constructs a trie node from values and an array of children, using the compact `chain`
representation when possible.
-/
@[inline]
def mkNode (vs : Array α) (cs : Array (Key × Trie α)) : Trie α :=
  if h : vs.isEmpty ∧ cs.size = 1 then
    .chain cs[0].1 cs[0].2
  else
    .node vs cs

/--
Inspect a trie node as an array of values and an array of children.
-/
@[inline]
def asNode : Trie α → Array α × Array (Key × Trie α)
  | .chain k v => ⟨#[], #[(k, v)]⟩
  | .node vs cs => ⟨vs, cs⟩

/--
Returns the values stored at the current trie node.
Equivalent to `t.asNode.1`.
-/
@[inline]
def nodeValues : Trie α → Array α
  | .chain _ _ => #[]
  | .node vs _ => vs

/--
Returns the child nodes of the current trie node.
Equivalent to `t.asNode.2`.
-/
@[inline]
def nodeChildren : Trie α → Array (Key × Trie α)
  | .chain k v => #[(k, v)]
  | .node _ cs => cs

/--
Checks whether a trie node is empty (no values and no children).

This is only a check for actual trie emptiness (`t.size = 0`) if all operations maintain the
invariant that no trie node has an empty child node.
-/
@[inline]
def isEmptyNode : Trie α → Bool
  | .chain _ _ => false
  | .node vs children => vs.isEmpty && children.isEmpty

/--
Checks whether a trie node has any children.
-/
@[inline]
def hasChildren : Trie α → Bool
  | .chain .. => true
  | .node _ cs => !cs.isEmpty

/--
Returns the child for `Key.star`, if any.
`Key.star` is the minimal key, so it is always the first child of a `node`.
-/
@[inline]
def starChild? : Trie α → Option (Trie α)
  | .chain key child => if key == .star then some child else none
  | .node _ cs =>
    if h : 0 < cs.size then
      if cs[0].1 == .star then some cs[0].2 else none
    else
      none

/--
Returns the child for key `k`, if any.
-/
@[inline]
def findChild? (t : Trie α) (k : Key) : Option (Trie α) :=
  match t with
  | .chain key child => if key == k then some child else none
  | .node _ cs => (cs.binSearch (k, default) (fun a b => a.1 < b.1)).map (·.2)

/--
Monadically folds over the children of a trie node together with their keys.
-/
@[inline]
def foldChildrenM [Monad m] (f : σ → Key → Trie α → m σ) (init : σ) : Trie α → m σ
  | .chain key child => f init key child
  | .node _ cs => cs.foldlM (init := init) fun s (k, c) => f s k c

end Trie

private partial def createNodes (keys : Array Key) (v : α) (i : Nat) : Trie α :=
  if h : i < keys.size then
    let k := keys[i]
    let c := createNodes keys v (i+1)
    .chain k c
  else
    .node #[v] #[]

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

private partial def insertAux [BEq α] (keys : Array Key) (v : α) : Nat → Trie α → Trie α
  | i, .chain k c =>
    if h : i < keys.size then
      if keys[i] == k then
        .chain k (insertAux keys v (i+1) c)
      else
        insertAux keys v i (.node #[] #[(k, c)])
    else
      insertAux keys v i (.node #[] #[(k, c)])
  | i, .node vs cs =>
    if h : i < keys.size then
      let k := keys[i]
      let c := Id.run $ cs.binInsertM
          (fun a b => a.1 < b.1)
          (fun ⟨_, s⟩ => let c := insertAux keys v (i+1) s; (k, c)) -- merge with existing
          (fun _ => let c := createNodes keys v (i+1); (k, c))
          (k, default)
      .mkNode vs c
    else
      .node (insertVal vs v) cs

def insertKeyValue [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]!
    { d with root :=
        d.root.alter k fun
          | none => some <| createNodes keys v 1
          | some c => insertAux keys v 1 c
    }

@[deprecated insertKeyValue (since := "2026-01-02")]
def insertCore [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  insertKeyValue d keys v

end Lean.Meta.DiscrTree
