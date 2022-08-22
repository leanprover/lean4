/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.CompilerM

namespace Lean.Compiler

/--
Proto expressions are an artifact to minimize the performance overhead of the locally nameless approach.
-/
structure PExpr where
  private expr : Expr
  deriving Inhabited

/-- Every `Expr` is a valid `PExpr`. -/
instance : Coe Expr PExpr where
  coe e := { expr := e }

namespace PExpr

def mkPBinding' (x : Expr) (body : PExpr) : PExpr :=
  ⟨.lam `_pbinding x body.expr .default⟩

def mkPBinding (xs : Array Expr) (body : PExpr) : PExpr :=
  xs.foldr (init := body) mkPBinding'

def mkPBindingFrom (start : Nat) (xs : Array Expr) (body : PExpr) : PExpr :=
  go xs.size body
where
  go (i : Nat) (body : PExpr) : PExpr :=
    if i > start then
      go (i - 1) (mkPBinding' xs[i - 1]! body)
    else
      body

@[inline] private def isPBinding? (e : PExpr) : Option (Expr × PExpr) :=
  if let .lam `_pbinding x body _ := e.expr then
    some (x, ⟨body⟩)
  else
    none

instance : ToMessageData PExpr where
  toMessageData e := e.expr

def visitLambda' (xs : Array Expr) (e : Expr) : CompilerM (Array Expr × Expr) :=
  go e xs
where
  go (e : Expr) (xs : Array Expr) := do
    if let .lam binderName type body binderInfo := e then
      let type := type.instantiateRev xs
      let x ← mkLocalDecl binderName type binderInfo
      go body (xs.push x)
    else
      return (xs, e)

@[inline] def visitLambdaImp (xs : Array Expr) (e : Expr) (visitBody : Array Expr → Expr → CompilerM (Array Expr × PExpr)) : CompilerM PExpr := do
  let start := xs.size
  let (xs, e) ← visitLambda' xs e
  let (xs, e) ← visitBody xs e
  return mkPBindingFrom start xs e

class VisitLambda (m : Type → Type) where
  visitLambda : Array Expr → Expr → (Array Expr → Expr → m (Array Expr × PExpr)) → m PExpr

export VisitLambda (visitLambda)

instance : VisitLambda CompilerM where
  visitLambda := visitLambdaImp

instance [VisitLambda m] : VisitLambda (ReaderT ρ m) where
  visitLambda := fun xs e f ctx => visitLambda xs e (f · · ctx)

instance [VisitLambda m] : VisitLambda (StateRefT' ω ρ m) :=
  inferInstanceAs (VisitLambda (ReaderT _ _))

@[inline] def visitCases [Monad m] (xs : Array Expr) (casesInfo : CasesInfo) (cases : Expr) (visitAlt : Array Expr → Expr → m PExpr) : m PExpr := do
  let mut args := cases.getAppArgs
  for i in [:args.size] do
    let arg := args[i]!
    let arg ← if casesInfo.altsRange.start ≤ i && i < casesInfo.altsRange.stop then
      pure (← visitAlt xs arg).expr
    else
      pure <| arg.instantiateRev xs
    args := args.set! i arg
  return mkAppN cases.getAppFn args

abbrev UsedSet := FVarIdHashSet

partial def toExpr' (env : Environment) (lctx : LocalContext) (e : PExpr) : Expr :=
  let e := filter e {} |>.1
  go #[] e
where
  filter (e : PExpr) (s : UsedSet) : PExpr × UsedSet :=
    if let some (x, e) := isPBinding? e then
      let (e, s) := filter e s
      match lctx.get! x.fvarId! with
      | .cdecl .. => (mkPBinding' x e, s)
      | .ldecl (value := value) .. =>
        if s.contains x.fvarId! then
          (mkPBinding' x e, collectLetFVars s value)
        else
          (e, s)
    else if let some casesInfo := isCasesApp?' env e.expr then
      Id.run do
        let mut args := e.expr.getAppArgs
        let mut s := s
        for i in [:args.size] do
          let arg := args[i]!
          let arg ← if casesInfo.altsRange.start ≤ i && i < casesInfo.altsRange.stop then
            let (arg, s') := filter arg s
            s := s'
            pure arg.expr
          else
            s := collectLetFVars s arg
            pure arg
          args := args.set! i arg
        return (mkAppN e.expr.getAppFn args, s)
    else
      (e, collectLetFVars s e.expr)

  go (xs : Array Expr) (e : PExpr) : Expr :=
    if let some (x, e) := isPBinding? e then
      match lctx.get! x.fvarId! with
      | .cdecl (userName := userName) (type := type) (bi := bi) .. =>
        let type := type.abstract xs
        .lam userName type (go (xs.push x) e) bi
      | .ldecl (userName := userName) (type := type) (value := value) .. =>
        let type  := type.abstract xs
        let value := value.abstract xs
        .letE userName type value (go (xs.push x) e) true
    else if let some casesInfo := isCasesApp?' env e.expr then
      Id.run do
        let mut args := e.expr.getAppArgs
        for i in [:args.size] do
          let arg := args[i]!
          let arg ← if casesInfo.altsRange.start ≤ i && i < casesInfo.altsRange.stop then
            go xs arg
          else
            arg.abstract xs
          args := args.set! i arg
        return mkAppN e.expr.getAppFn args
    else
      e.expr.abstract xs

partial def toExpr [Monad m] [MonadEnv m] [MonadLCtx m] (e : PExpr) : m Expr :=
  return toExpr' (← getEnv) (← getLCtx) e

end PExpr
end Lean.Compiler