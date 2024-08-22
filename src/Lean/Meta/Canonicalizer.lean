/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.HashMap
import Lean.Util.ShareCommon
import Lean.Meta.Basic
import Lean.Meta.FunInfo
import Std.Data.HashMap.Raw

namespace Lean.Meta
namespace Canonicalizer

/-!
Applications have implicit arguments. Thus, two terms that may look identical when pretty-printed can be structurally different.
For example, `@id (Id Nat) x` and `@id Nat x` are structurally different but are both pretty-printed as `id x`.
Moreover, these two terms are definitionally equal since `Id Nat` reduces to `Nat`. This may create situations
that are counterintuitive to our users. Furthermore, several tactics (e.g., `omega`) need to collect unique atoms in a goal.
One simple approach is to maintain a list of atoms found so far, and whenever a new atom is discovered, perform a
linear scan to test whether it is definitionally equal to a previously found one. However, this method is too costly,
even if the definitional equality test were inexpensive.

This module aims to efficiently identify terms that are structurally different, definitionally equal, and structurally equal
when we disregard implicit arguments like `@id (Id Nat) x` and `@id Nat x`. The procedure is straightforward. For each atom,
we create a hash that ignores all implicit information. Thus the hash for terms are equal `@id (Id Nat) x` and `@id Nat x`.
To preserve any pre-existing directed acyclic graph (DAG) structure and prevent exponential blowups while computing the hash code,
we employ unsafe techniques, such as pointer equality. Additionally, we maintain a mapping from hash to lists of terms, where each
list contains terms sharing the same hash but not definitionally equal. We posit that these lists will be small in practice.
-/

/--
Auxiliary structure for creating a pointer-equality.
-/
structure ExprVisited where
  e : Expr
  deriving Inhabited

unsafe instance : BEq ExprVisited where
  beq a b := ptrAddrUnsafe a == ptrAddrUnsafe b

unsafe instance : Hashable ExprVisited where
  hash a := USize.toUInt64 (ptrAddrUnsafe a)

/--
State for the `CanonM` monad.
-/
structure State where
  /-- Mapping from `Expr` to hash. -/
  -- We use `HashMap.Raw` to ensure we don't have to tag `State` as `unsafe`.
  cache      : Std.HashMap.Raw ExprVisited UInt64 := Std.HashMap.Raw.empty
  /--
  Given a hashcode `k` and `keyToExprs.find? h = some es`, we have that all `es` have hashcode `k`, and
  are not definitionally equal modulo the transparency setting used. -/
  keyToExprs : Std.HashMap UInt64 (List Expr) := ∅

instance : Inhabited State where
  default := {}

abbrev CanonM := ReaderT TransparencyMode $ StateRefT State MetaM

/--
The definitionally equality tests are performed using the given transparency mode.
We claim `TransparencyMode.instances` is a good setting for most applications.
-/
def CanonM.run' (x : CanonM α) (transparency := TransparencyMode.instances) (s : State := {}) : MetaM α :=
  StateRefT'.run' (x transparency) s

def CanonM.run (x : CanonM α) (transparency := TransparencyMode.instances) (s : State := {}) : MetaM (α × State) :=
  StateRefT'.run (x transparency) s

private partial def mkKey (e : Expr) : CanonM UInt64 := do
  if let some hash := unsafe (← get).cache.get? { e } then
    return hash
  else
    let key ← match e with
      | .sort .. | .fvar .. | .bvar .. | .lit .. =>
        return hash e
      | .const n _ =>
        return n.hash
      | .mvar .. =>
        -- We instantiate assigned metavariables because the
        -- pretty-printer also instantiates them.
        let eNew ← instantiateMVars e
        if eNew == e then return hash e else mkKey eNew
      | .mdata _ a => mkKey a
      | .app .. =>
        let f := e.getAppFn
        if f.isMVar then
          let eNew ← instantiateMVars e
          unless eNew == e do
            return (← mkKey eNew)
        let info ← getFunInfo f
        let mut k ← mkKey f
        for i in [:e.getAppNumArgs] do
          if h : i < info.paramInfo.size then
            let info := info.paramInfo[i]
            if info.isExplicit && !info.isProp then
              k := mixHash k (← mkKey (e.getArg! i))
          else
              k := mixHash k (← mkKey (e.getArg! i))
        return k
      | .lam _ t b _
      | .forallE _ t b _ =>
        return mixHash (← mkKey t) (← mkKey b)
      | .letE _ _ v b _ =>
        return mixHash (← mkKey v) (← mkKey b)
      | .proj _ i s =>
        return mixHash i.toUInt64 (← mkKey s)
    unsafe modify fun { cache, keyToExprs} => { keyToExprs, cache := cache.insert { e } key }
    return key

/--
"Canonicalize" the given expression.
-/
def canon (e : Expr) : CanonM Expr := do
  let k ← mkKey e
  -- Find all expressions canonicalized before that have the same key.
  if let some es' := unsafe (← get).keyToExprs[k]? then
    withTransparency (← read) do
      for e' in es' do
        -- Found an expression `e'` that is definitionally equal to `e` and share the same key.
        if (← isDefEq e e') then
          return e'
      -- `e` is not definitionally equal to any expression in `es'`. We claim this should be rare.
      unsafe modify fun { cache, keyToExprs } => { cache, keyToExprs := keyToExprs.insert k (e :: es') }
      return e
  else
    -- `e` is the first expression we found with key `k`.
    unsafe modify fun { cache, keyToExprs } => { cache, keyToExprs := keyToExprs.insert k [e] }
    return e

end Canonicalizer

export Canonicalizer (CanonM canon)

end Lean.Meta
