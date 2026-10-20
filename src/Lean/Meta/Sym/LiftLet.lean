/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.ReplaceS
namespace Lean.Meta.Sym
open Lean.Meta.Sym.Internal

/-!
# `let`-lifting for `SymM`

`Sym.liftLets` moves `let`/`have` declarations toward the root of a term, as far out as
their dependencies allow. The result is definitionally equal to the input (lifting is a
zeta-permutation), so no proof term is produced.

The implementation avoids the performance pitfalls of the standard
`Lean.Meta.liftLets`:

- **No per-binder instantiate/abstract round-trips.** The traversal carries an
  environment `xs : PArray Expr` mapping de Bruijn indices of the `let`s being lifted to
  scratch free variables. Each subterm is processed once; all de Bruijn arithmetic for the
  result is performed by a single closing pass (`mkLets`).
- **Pointer-keyed memoization.** Results are cached per `(environment, expression)`
  pointer pair. For subterms without loose bound variables the result does not depend on
  the environment, so they are cached by expression pointer alone; this also makes the
  `let`-block of a shared closed subterm lifted once and shared by all occurrences.
- **O(1) merging.** In the maximally shared world, syntactically equal types/values are
  pointer-equal, so deduplicating `let`s with equal definitions is a pointer-map lookup
  (cf. the `merge := true` option of `extract_lets`). If occurrences disagree on
  `let` vs `have`, the merged declaration is a `let`, since tactics may zeta-delta reduce
  `let`s but not `have`s.

Scope:
- `let`s under `fun`/`∀` binders are **not** lifted, even when they do not depend on the
  binder. Binder nodes are treated as opaque: their bound occurrences of lifted `let`s
  are substituted (they must be, since inserting foreign binders shifts indices), but no
  `let` is collected from inside them.
- Both dependent `let`s and `have`s (nondependent `let`s) are lifted, and the
  `nondep` flag is preserved.
- `let`s occurring in the *types* of lifted `let`s are lifted as well.
-/

namespace LiftLet

/-- A `let`-declaration collected by `Sym.liftLets`, in dependency order. -/
structure Decl where
  /-- Hash-consed `.fvar` node standing for this declaration in intermediate terms. -/
  fvar     : Expr
  userName : Name
  /-- Type after processing: maximally shared, referencing earlier declarations via their scratch fvars. -/
  type     : Expr
  /-- Value after processing. -/
  value    : Expr
  /-- `true` if this is a `have` (nondependent `let`). -/
  nondep   : Bool
  deriving Inhabited

/--
Pointer-equality key for the traversal environment.
`PArray.push` returns a new object, so pointer equality identifies the exact environment.
-/
structure EnvPtr where
  env : PArray Expr

abbrev hashPtrEnv (xs : PArray Expr) : UInt64 :=
  unsafe (ptrAddrUnsafe xs >>> 3).toUInt64

abbrev isSameEnv (xs ys : PArray Expr) : Bool :=
  unsafe ptrEq xs ys

instance : Hashable EnvPtr where
  hash k := hashPtrEnv k.env

instance : BEq EnvPtr where
  beq k₁ k₂ := isSameEnv k₁.env k₂.env

structure State where
  /--
  Cache for subterms with loose bound variables, keyed by `(environment, expression)`
  pointer pair. The same expression under different environments denotes different terms
  (alpha-sharing makes distinct-meaning terms pointer-equal), so the environment must be
  part of the key.
  -/
  cache : Std.HashMap (EnvPtr × ExprPtr) Expr := {}
  /--
  Cache for subterms without loose bound variables. Their result does not depend on the
  environment: every bound variable inside resolves to a declaration pushed during their
  own processing. Keying them by expression pointer alone recovers sharing across branches
  whose environments differ.
  -/
  cacheClosed : Std.HashMap ExprPtr Expr := {}
  /-- Pointer-cached result of `hasLiftableLet`. -/
  hasLetCache : Std.HashMap ExprPtr Bool := {}
  /-- Collected declarations. Dependencies always precede dependents. -/
  decls : Array Decl := #[]
  /--
  Maps `(type, value)` pointer pairs to an index into `decls`.
  Implements `let`-merging: pointer equality is alpha-equality in the maximally
  shared world.
  -/
  valueMap : Std.HashMap (ExprPtr × ExprPtr) Nat := {}

abbrev M := StateRefT State SymM

/--
Returns `true` if `e` contains a `let`-expression that `liftLets` would lift.
`let`s under `fun`/`∀` binders are not lifted, so binder nodes are not descended into.
The result is pointer-cached; each shared node is visited at most once per session.
-/
partial def hasLiftableLet (e : Expr) : M Bool := do
  let withLetCache (e : Expr) (k : M Bool) : M Bool := do
    if let some r := (← get).hasLetCache[{ expr := e : ExprPtr }]? then
      return r
    else
      let r ← k
      modify fun s => { s with hasLetCache := s.hasLetCache.insert { expr := e } r }
      return r
  match e with
  | .letE .. => return true
  | .app f a => withLetCache e (hasLiftableLet f <||> hasLiftableLet a)
  | .mdata _ b => withLetCache e (hasLiftableLet b)
  | .proj _ _ b => withLetCache e (hasLiftableLet b)
  | _ => return false

/--
Creates (or reuses) the declaration for a `let` with the given (already processed) type
and value, and returns its scratch fvar. See `State.valueMap` for the merge semantics.
-/
def mkDecl (userName : Name) (type value : Expr) (nondep : Bool) : M Expr := do
  let key := ({ expr := type : ExprPtr }, { expr := value : ExprPtr })
  if let some idx := (← get).valueMap[key]? then
    -- Merge. A `let` occurrence upgrades a merged `have`: tactics may
    -- zeta-delta reduce `let`s, so the merged declaration must be a `let` if any
    -- occurrence was.
    unless nondep do
      modify fun s => { s with decls := s.decls.modify idx fun d => { d with nondep := false } }
    return (← get).decls[idx]!.fvar
  let fvar ← mkFVarS (← mkFreshFVarId)
  let idx := (← get).decls.size
  modify fun s => { s with
    decls    := s.decls.push { fvar, userName, type, value, nondep }
    valueMap := s.valueMap.insert key idx
  }
  return fvar

/--
Substitutes the loose bound variables of `e` (all of which refer to `let`s being lifted)
with the corresponding scratch fvars from `xs`. Used for `fun`/`∀` nodes: they are not
descended into for `let`-collection, but their bound occurrences must still be
substituted, since the lifted `let`s end up at new positions.

The scratch fvars are closed terms, so no index adjustment is needed.
-/
def substEnv (xs : PArray Expr) (e : Expr) : M Expr := do
  let n := xs.size
  replaceS e fun sub offset => do
    match sub with
    | .bvar idx =>
      if idx ≥ offset then
        pure (some xs[n - (idx - offset) - 1]!)
      else
        pure (some sub)
    | .lit _ | .mvar _ | .fvar _ | .const _ _ | .sort _ => pure (some sub)
    | _ => if offset ≥ sub.looseBVarRange then pure (some sub) else pure none

/--
Main traversal. `xs` maps the de Bruijn indices of the enclosing (lifted) `let` binders
to their scratch fvars: index `i` maps to `xs[xs.size - i - 1]`.
-/
partial def go (xs : PArray Expr) (e : Expr) : M Expr := do
  match e with
  | .bvar idx =>
    let n := xs.size
    if _ : idx < n then
      return xs[n - idx - 1]
    else
      throwError "`Sym.liftLets` internal error, input term is not closed"
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => return e
  | _ =>
    if !e.hasLooseBVars then
      -- The result does not depend on `xs`; see `State.cacheClosed`.
      if !(← hasLiftableLet e) then
        return e
      if let some r := (← get).cacheClosed[{ expr := e : ExprPtr }]? then
        return r
      let r ← visit {} e
      modify fun s => { s with cacheClosed := s.cacheClosed.insert { expr := e } r }
      return r
    else
      let key := ({ env := xs : EnvPtr }, { expr := e : ExprPtr })
      if let some r := (← get).cache[key]? then
        return r
      let r ← visit xs e
      modify fun s => { s with cache := s.cache.insert key r }
      return r
where
  visit (xs : PArray Expr) (e : Expr) : M Expr := do
    match e with
    | .letE n t v b nondep =>
      let t ← go xs t
      let v ← go xs v
      let x ← mkDecl n t v nondep
      go (xs.push x) b
    | .app f a    => e.updateAppS! (← go xs f) (← go xs a)
    | .mdata _ b  => e.updateMDataS! (← go xs b)
    | .proj _ _ b => e.updateProjS! (← go xs b)
    | .forallE .. | .lam .. => substEnv xs e
    | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => unreachable!

/--
Closing pass: wraps `e` with the collected declarations, converting the scratch fvars
back to de Bruijn indices. Declaration `i` ends up under `i` binders (declarations
`0, ..., i-1`), so an occurrence of declaration `p` in a piece placed under `i` binders
at binder offset `offset` becomes `#(offset + i - p - 1)`. Each piece (every declaration
type/value and the body) is traversed exactly once.
-/
def mkLets (e : Expr) : M Expr := do
  let decls := (← get).decls
  if decls.isEmpty then
    return e
  let mut posMap : Std.HashMap FVarId Nat := {}
  let mut i := 0
  for d in decls do
    posMap := posMap.insert d.fvar.fvarId! i
    i := i + 1
  let abst (piece : Expr) (i : Nat) : M Expr :=
    replaceS piece fun sub offset => do
      match sub with
      | .fvar fvarId =>
        if let some p := posMap[fvarId]? then
          assert! p < i
          some <$> mkBVarS (offset + i - p - 1)
        else
          pure (some sub)
      | .lit _ | .mvar _ | .bvar _ | .const _ _ | .sort _ => pure (some sub)
      | _ => if !sub.hasFVar then pure (some sub) else pure none
  let mut r ← abst e decls.size
  let mut j := decls.size
  for d in decls.reverse do
    j := j - 1
    let t ← abst d.type j
    let v ← abst d.value j
    r ← mkLetS d.userName t v r d.nondep
  return r

end LiftLet

/--
Moves the `let`/`have` declarations of `e` toward the root, as far out as their
dependencies allow. Nested declarations are flattened, and declarations with pointer-equal
types and values are merged. The result is definitionally equal to `e`.

`let`s under `fun`/`∀` binders are not lifted; see the module docstring for the
precise scope.

Assumptions:
- `e` is maximally shared and has no loose bound variables.
- Metavariables in `e` have been instantiated; they are treated as opaque atoms.

If nothing is lifted, the result is pointer-equal to `e` (check with `isSameExpr`).
-/
public def liftLets (e : Expr) : SymM Expr := do
  if e.hasLooseBVars then
    throwError "`Sym.liftLets` internal error, input term has loose bound variables"
  let x : LiftLet.M Expr := do LiftLet.mkLets (← LiftLet.go {} e)
  x.run' {}

end Lean.Meta.Sym
