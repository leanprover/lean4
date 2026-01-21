/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Pattern
public import Lean.Meta.DiscrTree.Basic
import Lean.Meta.Sym.Offset
namespace Lean.Meta.Sym
open DiscrTree

/-!
# Discrimination Tree for the Symbolic Simulation Framework

This module provides pattern insertion into discrimination trees for the symbolic simulation
framework. Unlike the standard `DiscrTree` insertion which works with arbitrary expressions,
this module converts `Pattern` values (see `Sym/Pattern.lean`) into discrimination tree keys.
`Pattern` values have been preprocessed and use de Bruijn variables for wildcards instead of
metavariables.

## Key Design Decisions

The conversion from `Pattern` to `Array Key` respects the structural matching semantics of `Sym`:

1. **Proof and instance arguments are wildcards.** When building keys for a function application,
   arguments marked as proofs or instances in `ProofInstInfo` are replaced with `Key.star`.
   This ensures that during retrieval, terms differing only in proof/instance arguments will
   match the same entries.

2. **Bound variables are wildcards.** Pattern variables (represented as de Bruijn indices in
   `Pattern.pattern`) become `Key.star`, allowing them to match any subterm during retrieval.

3. **`noindex` annotations are respected.** Subterms annotated with `noindex` become `Key.star`.

## Usage

Use `insertPattern` to add a pattern to a discrimination tree:
```
let tree := insertPattern tree pattern value
```

Retrieval should use the standard `DiscrTree.getMatch` or similar, which will find all patterns
whose key sequence is compatible with the query term.
-/

/-- Returns `true` if argument at position `i` should be ignored (is a proof or instance). -/
def ignoreArg (infos : Array ProofInstArgInfo) (i : Nat) : Bool :=
  if h : i < infos.size then
    let info := infos[i]
    info.isInstance || info.isProof
  else
    false

/-- Pushes all arguments of an application onto the todo stack in reverse order. -/
def pushAllArgs (e : Expr) (todo : Array Expr) : Array Expr :=
  match e with
  | .app f a => pushAllArgs f (todo.push a)
  | _ => todo

/--
Pushes arguments of an application onto the todo stack, replacing proof/instance arguments
with dummy bound variables (which become `Key.star` wildcards).
-/
def pushArgsUsingInfo (infos : Array ProofInstArgInfo) (i : Nat) (e : Expr) (todo : Array Expr) : Array Expr :=
  match e with
  | .app f a =>
    if ignoreArg infos i then
      -- **Note**: We use a dummy bvar, it will be transformed into a `Key.star` later.
      let dummyBVar := .bvar 1000000
      pushArgsUsingInfo infos (i-1) f (todo.push dummyBVar)
    else
      pushArgsUsingInfo infos (i-1) f (todo.push a)
  | _ => todo

/--
Computes the discrimination tree key for an expression and pushes its subterms onto the todo stack.
Returns `Key.star` for bound variables and `noindex`-annotated terms.
-/
def pushArgs (root : Bool) (fnInfos : AssocList Name ProofInstInfo) (todo : Array Expr) (e : Expr) : Key × Array Expr :=
  if hasNoindexAnnotation e then
    (.star, todo)
  else
    let fn := e.getAppFn
    match fn with
    | .lit v => (.lit v, todo)
    | .bvar _ => (.star, todo)
    | .forallE _ d b _ => (.arrow, todo.push b |>.push d)
    | .const declName _ =>
      if !root && isOffset' declName e then
        (.star, todo)
      else
        let numArgs := e.getAppNumArgs
        let todo := if let some info := fnInfos.find? declName then
          pushArgsUsingInfo info.argsInfo (numArgs - 1) e todo
        else
          pushAllArgs e todo
        (.const declName numArgs, todo)
    | .fvar fvarId   =>
      let numArgs := e.getAppNumArgs
      let todo := pushAllArgs e todo
      (.fvar fvarId numArgs, todo)
    | _ => (.other, todo)

/-- Work-list based traversal that builds the key sequence for a pattern. -/
partial def mkPathAux (root : Bool) (fnInfos : AssocList Name ProofInstInfo) (todo : Array Expr) (keys : Array Key) : Array Key :=
  if todo.isEmpty then
    keys
  else
    let e    := todo.back!
    let todo := todo.pop
    let (k, todo) := pushArgs root fnInfos todo e
    mkPathAux false fnInfos todo (keys.push k)

def initCapacity := 8

/-- Converts a `Pattern` into a discrimination tree key sequence. -/
public def Pattern.mkDiscrTreeKeys (p : Pattern) : Array Key :=
  let todo : Array Expr := .mkEmpty initCapacity
  let keys : Array Key := .mkEmpty initCapacity
  mkPathAux true p.fnInfos (todo.push p.pattern) keys

/-- Inserts a pattern into a discrimination tree, associating it with value `v`. -/
public def insertPattern [BEq α] (d : DiscrTree α) (p : Pattern) (v : α) : DiscrTree α :=
  let keys := p.mkDiscrTreeKeys
  d.insertKeyValue keys v

abbrev findKey? (cs : Array (Key × Trie α)) (k : Key) : Option (Key × Trie α) :=
  cs.binSearch (k, default) (fun a b => a.1 < b.1)

def getKey (e : Expr) : Key :=
  match e.getAppFn with
  | .lit v            => .lit v
  | .const declName _ => .const declName e.getAppNumArgs
  | .fvar fvarId      => .fvar fvarId e.getAppNumArgs
  | .forallE ..       => .arrow
  | _ => .other

/-- Push `e` arguments/children into the `todo` stack.  -/
def pushArgsTodo (todo : Array Expr) (e : Expr) : Array Expr :=
  match e with
  | .app f a => pushArgsTodo (todo.push a) f
  | .forallE _ d b _ => todo.push b |>.push d
  | _ => todo

partial def getMatchLoop (todo : Array Expr) (c : Trie α) (result : Array α) : Array α :=
  match c with
  | .node vs cs =>
    let csize := cs.size
    if todo.isEmpty then
      result ++ vs
    else if h : csize = 0 then
      result
    else
      let e     := todo.back!
      let todo  := todo.pop
      let first := cs[0] /- Recall that `Key.star` is the minimal key -/
      if csize = 1 then
        /- Special case: only one child node -/
        if first.1 == .star then
          getMatchLoop todo first.2 result
        else if first.1 == getKey e then
          getMatchLoop (pushArgsTodo todo e) first.2 result
        else
          result
      else
        /- We must always visit `Key.star` edges since they are wildcards.
          Thus, `todo` is not used linearly when there is `Key.star` edge
          and there is an edge for `k` and `k != Key.star`. -/
        let result := if first.1 == .star then
          getMatchLoop todo first.2 result
        else
          result
        match findKey? cs (getKey e) with
        | none   => result
        | some c => getMatchLoop (pushArgsTodo todo e) c.2 result

/--
Retrieves all values whose patterns match the expression `e`.
-/
public def getMatch (d : DiscrTree α) (e : Expr) : Array α :=
  let result := match d.root.find? .star with
  | none              => .mkEmpty initCapacity
  | some (.node vs _) => vs
  match d.root.find? (getKey e) with
  | none   => result
  | some c => getMatchLoop (pushArgsTodo #[] e) c result

/--
Retrieves all values whose patterns match a prefix of `e`, along with the number of
extra (ignored) arguments.

This is useful for rewriting: if a pattern matches `f x` but `e` is `f x y z`, we can
still apply the rewrite and return `(value, 2)` indicating 2 extra arguments.
-/
public partial def getMatchWithExtra (d : DiscrTree α) (e : Expr) : Array (α × Nat) :=
  let result := getMatch d e
  let result := result.map (·, 0)
  if !e.isApp then
    result
  else if !mayMatchPrefix (getKey e) then
    result
  else
    go e.appFn! 1 result
where
  mayMatchPrefix (k : Key) : Bool :=
    let cont (k : Key) : Bool :=
      if d.root.find? k |>.isSome then
        true
      else
        mayMatchPrefix k
    match k with
    | .const f (n+1)  => cont (.const f n)
    | .fvar f (n+1)   => cont (.fvar f n)
    | _               => false

  go (e : Expr) (numExtra : Nat) (result : Array (α × Nat)) : Array (α × Nat) :=
    let result := result ++ (getMatch d e).map (., numExtra)
    if e.isApp then
      go e.appFn! (numExtra + 1) result
    else
      result

end Lean.Meta.Sym
