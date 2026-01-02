/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.DiscrTree.Types
public import Lean.ToExpr
public import Lean.CoreM
public section
namespace Lean.Meta.DiscrTree

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

end Lean.Meta.DiscrTree
