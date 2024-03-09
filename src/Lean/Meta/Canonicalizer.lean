/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.ShareCommon
import Lean.Data.HashMap
import Lean.Meta.Basic
import Lean.Meta.FunInfo

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
we create a new abstracted atom by erasing all implicit information. We refer to this abstracted atom as a 'key.' For the two
terms mentioned, the key would be `@id _ x`, where `_` denotes a placeholder for a dummy term. To preserve any
pre-existing directed acyclic graph (DAG) structure and prevent exponential blowups while constructing the key, we employ
unsafe techniques, such as pointer equality. Additionally, we maintain a mapping from keys to lists of terms, where each
list contains terms sharing the same key but not definitionally equal. We posit that these lists will be small in practice.
-/

/--
Auxiliary structure for creating a pointer-equality mapping from `Expr` to `Key`.
We use this mapping to ensure we preserve the dag-structure of input expressions.
-/
structure ExprVisited where
  e : Expr
  deriving Inhabited

unsafe instance : BEq ExprVisited where
  beq a b := ptrAddrUnsafe a == ptrAddrUnsafe b

unsafe instance : Hashable ExprVisited where
  hash a := USize.toUInt64 (ptrAddrUnsafe a)

abbrev Key := ExprVisited

/--
State for the `CanonM` monad.
-/
structure State where
  /-- "Set" of all keys created so far. This is a hash-consing helper structure available in Lean. -/
  keys       : ShareCommon.State.{0} Lean.ShareCommon.objectFactory := ShareCommon.State.mk Lean.ShareCommon.objectFactory
  /-- Mapping from `Expr` to `Key`. See comment at `ExprVisited`. -/
  -- We use `HashMapImp` to ensure we don't have to tag `State` as `unsafe`.
  cache      : HashMapImp ExprVisited Key := mkHashMapImp
  /--
  Given a key `k` and `keyToExprs.find? k = some es`, we have that all `es` share key `k`, and
  are not definitionally equal modulo the transparency setting used. -/
  keyToExprs : HashMapImp Key (List Expr) := mkHashMapImp

instance : Inhabited State where
  default := {}

abbrev CanonM := ReaderT TransparencyMode $ StateRefT State MetaM

/--
The definitionally equality tests are performed using the given transparency mode.
We claim `TransparencyMode.instances` is a good setting for most applications.
-/
def CanonM.run (x : CanonM α) (transparency := TransparencyMode.instances) : MetaM α :=
  StateRefT'.run' (x transparency) {}

private def shareCommon (a : α) : CanonM α :=
  modifyGet fun { keys, cache, keyToExprs } =>
    let (a, keys) := ShareCommon.State.shareCommon keys a
    (a, { keys, cache, keyToExprs })

private partial def mkKey (e : Expr) : CanonM Key := do
  if let some key := unsafe (← get).cache.find? { e } then
    return key
  else
    let key ← match e with
      | .sort .. | .fvar .. | .bvar .. | .const .. | .lit .. =>
        pure { e := (← shareCommon e) }
      | .mvar .. =>
        -- We instantiate assigned metavariables because the
        -- pretty-printer also instantiates them.
        let eNew ← instantiateMVars e
        if eNew == e then pure { e := (← shareCommon e) }
        else mkKey eNew
      | .mdata _ a => mkKey a
      | .app .. =>
        let f := (← mkKey e.getAppFn).e
        if f.isMVar then
          let eNew ← instantiateMVars e
          unless eNew == e do
            return (← mkKey eNew)
        let info ← getFunInfo f
        let args ← e.getAppArgs.mapIdxM fun i arg => do
          if h : i < info.paramInfo.size then
            let info := info.paramInfo[i]
            if info.isExplicit then
              pure (← mkKey arg).e
            else
              pure (mkSort 0) -- some dummy value for erasing implicit
          else
            pure (← mkKey arg).e
        pure { e := (← shareCommon (mkAppN f args)) }
      | .lam n t b i =>
        pure { e := (← shareCommon (.lam n (← mkKey t).e (← mkKey b).e i)) }
      | .forallE n t b i =>
        pure { e := (← shareCommon (.forallE n (← mkKey t).e (← mkKey b).e i)) }
      | .letE n t v b d =>
        pure { e := (← shareCommon (.letE n (← mkKey t).e (← mkKey v).e (← mkKey b).e d)) }
      | .proj t i s =>
        pure { e := (← shareCommon (.proj t i (← mkKey s).e)) }
    unsafe modify fun { keys, cache, keyToExprs} => { keys, keyToExprs, cache := cache.insert { e } key |>.1 }
    return key

/--
"Canonicalize" the given expression.
-/
def canon (e : Expr) : CanonM Expr := do
  let k ← mkKey e
  -- Find all expressions canonicalized before that have the same key.
  if let some es' := unsafe (← get).keyToExprs.find? k then
    withTransparency (← read) do
      for e' in es' do
        -- Found an expression `e'` that is definitionally equal to `e` and share the same key.
        if (← isDefEq e e') then
          return e'
      -- `e` is not definitionally equal to any expression in `es'`. We claim this should be rare.
      unsafe modify fun { keys, cache, keyToExprs } => { keys, cache, keyToExprs := keyToExprs.insert k (e :: es') |>.1 }
      return e
  else
    -- `e` is the first expression we found with key `k`.
    unsafe modify fun { keys, cache, keyToExprs } => { keys, cache, keyToExprs := keyToExprs.insert k [e] |>.1 }
    return e

end Canonicalizer

export Canonicalizer (CanonM canon)

end Lean.Meta
