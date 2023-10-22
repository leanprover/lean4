/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.FunInfo
import Lean.Meta.DiscrTree

namespace Lean

def Expr.ctorWeight : Expr → UInt8
  | bvar ..    => 0
  | fvar ..    => 1
  | mvar ..    => 2
  | sort ..    => 3
  | const ..   => 4
  | lit ..     => 5
  | mdata ..   => 6
  | proj ..    => 7
  | app ..     => 8
  | lam ..     => 9
  | forallE .. => 10
  | letE ..    => 11

namespace Meta
namespace ACLt

inductive ReduceMode where
  | reduce
  | reduceSimpleOnly
  | none

mutual

/--
  An AC-compatible ordering.

  Recall that an AC-compatible ordering if it is monotonic, well-founded, and total.
  Both KBO and LPO are AC-compatible. KBO is faster, but we do not cache the weight of
  each expression in Lean 4. Even if we did, we would need to have a weight where implicit instance arguments are ignored.
  So, we use a LPO-like term ordering.

  Remark: this method is used to implement ordered rewriting. We ignore implicit instance
  arguments to address an issue reported at issue #972.

  Remark: the order is not really total on terms since
   - We instance implicit arguments.
   - We ignore metadata.
   - We ignore universe parameterst at constants.
-/
unsafe def main (a b : Expr) (mode : ReduceMode := .none) : MetaM Bool :=
  lt a b
where
  reduce (e : Expr) : MetaM Expr := do
    if e.hasLooseBVars then
      -- We don't reduce terms occurring inside binders.
      -- See issue #1841.
      -- TODO: investigate whether we have to create temporary fresh free variables in practice.
      -- Drawback: cost.
      return e
    else match mode with
      | .reduce => DiscrTree.reduce e {}
      | .reduceSimpleOnly => DiscrTree.reduce e { iota := false, proj := .no }
      | .none => return e

  lt (a b : Expr) : MetaM Bool := do
    if ptrAddrUnsafe a == ptrAddrUnsafe b then
      return false
    -- We ignore metadata
    else if a.isMData then
      lt a.mdataExpr! b
    else if b.isMData then
      lt a b.mdataExpr!
    else
      lpo (← reduce a) (← reduce b)

  ltPair (a₁ a₂ b₁ b₂ : Expr) : MetaM Bool := do
    if (← lt a₁ b₁) then
      return true
    else if (← lt b₁ a₁) then
      return false
    else
      lt a₂ b₂

  ltApp (a b : Expr) : MetaM Bool := do
    let aFn := a.getAppFn
    let bFn := b.getAppFn
    if (← lt aFn bFn) then
      return true
    else if (← lt bFn aFn) then
      return false
    else
      let aArgs := a.getAppArgs
      let bArgs := b.getAppArgs
      if aArgs.size < bArgs.size then
        return true
      else if aArgs.size > bArgs.size then
        return false
      else
        let infos := (← getFunInfoNArgs aFn aArgs.size).paramInfo
        for i in [:infos.size] do
          -- We ignore instance implicit arguments during comparison
          if !infos[i]!.isInstImplicit then
            if (← lt aArgs[i]! bArgs[i]!) then
              return true
            else if (← lt bArgs[i]! aArgs[i]!) then
              return false
        for i in [infos.size:aArgs.size] do
          if (← lt aArgs[i]! bArgs[i]!) then
            return true
          else if (← lt bArgs[i]! aArgs[i]!) then
            return false
        return false

  lexSameCtor (a b : Expr) : MetaM Bool :=
    match a with
    -- Atomic
    | .bvar i ..    => return i < b.bvarIdx!
    | .fvar id ..   => return Name.lt id.name b.fvarId!.name
    | .mvar id ..   => return Name.lt id.name b.mvarId!.name
    | .sort u ..    => return Level.normLt u b.sortLevel!
    | .const n ..   => return Name.lt n b.constName! -- We ignore the levels
    | .lit v ..     => return Literal.lt v b.litValue!
    -- Composite
    | .proj _ i e ..    => if i != b.projIdx! then return i < b.projIdx! else lt e b.projExpr!
    | .app ..           => ltApp a b
    | .lam _ d e ..     => ltPair d e b.bindingDomain! b.bindingBody!
    | .forallE _ d e .. => ltPair d e b.bindingDomain! b.bindingBody!
    | .letE _ _ v e ..  => ltPair v e b.letValue! b.letBody!
    -- See main function
    | .mdata ..         => unreachable!

  allChildrenLt (a b : Expr) : MetaM Bool :=
    match a with
    | .proj _ _ e ..    => lt e b
    | .app ..           =>
      a.withApp fun f args => do
        let infos := (← getFunInfoNArgs f args.size).paramInfo
        for i in [:infos.size] do
          -- We ignore instance implicit arguments during comparison
          if !infos[i]!.isInstImplicit then
            if !(← lt args[i]! b) then
              return false
        for i in [infos.size:args.size] do
          if !(← lt args[i]! b) then
            return false
        return true
    | .lam _ d e ..     => lt d b <&&> lt e b
    | .forallE _ d e .. => lt d b <&&> lt e b
    | .letE _ _ v e ..  => lt v b <&&> lt e b
    | _ => return true

  someChildGe (a b : Expr) : MetaM Bool :=
    return !(← allChildrenLt a b)

  lpo (a b : Expr) : MetaM Bool := do
    -- Case 1: `a < b` if for some child `b_i` of `b`, we have `b_i >= a`
    if (← someChildGe b a) then
      return true
    else if a.ctorWeight > b.ctorWeight then
      return false
    else
      -- Case 2: `a < b` if `a.ctorWeight < b.ctorWeight` and for all children `a_i` of `a`, `a_i < b`
      -- Case 3: `a < b` if `a` & `b` have the same ctor, and `a` is lexicographically smaller, and for all children `a_i` of a, `a_i < b`
      if !(← allChildrenLt a b) then
        return false -- Cases 2 and 3 can't be true
      else if a.ctorWeight < b.ctorWeight then
        return true -- Case 2
      else
        -- `a.ctorWeight == b.ctorWeight`
        lexSameCtor a b -- Case 3

end

end ACLt

@[implemented_by ACLt.main, inherit_doc ACLt.main]
opaque Expr.acLt : Expr → Expr → (mode : ACLt.ReduceMode := .none) → MetaM Bool

end Lean.Meta
