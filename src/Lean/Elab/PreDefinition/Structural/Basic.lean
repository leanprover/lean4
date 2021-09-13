/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.ForEachExpr

namespace Lean.Elab.Structural

structure RecArgInfo where
  /- `fixedParams ++ ys` are the arguments of the function we are trying to justify termination using structural recursion. -/
  fixedParams : Array Expr
  ys          : Array Expr  -- recursion arguments
  pos         : Nat         -- position in `ys` of the argument we are recursing on
  indicesPos  : Array Nat   -- position in `ys` of the inductive datatype indices we are recursing on
  indName     : Name        -- inductive datatype name of the argument we are recursing on
  indLevels   : List Level  -- inductice datatype universe levels of the argument we are recursing on
  indParams   : Array Expr  -- inductive datatype parameters of the argument we are recursing on
  indIndices  : Array Expr  -- inductive datatype indices of the argument we are recursing on, it is equal to `indicesPos.map fun i => ys.get! i`
  reflexive   : Bool        -- true if we are recursing over a reflexive inductive datatype
  indPred     : Bool        -- true if the type is an inductive predicate

structure State where
  /- When compiling structural recursion we use the `brecOn` recursor automatically built by
     the `inductive` command. For an inductive datatype `C`, it has the form
     `C.brecOn As motive is c F`
     where `As` are the inductive datatype parameters, `is` are the inductive datatype indices,
     `c : C As is`, and `F : (js) → (d : C As js) → C.below d → motive d`
     The `C.below d` is used to eliminate recursive applications. We refine its type when we process
     a nested dependent pattern matcher using `MatcherApp.addArg`. See `replaceRecApps` for additional details.
     We store the names of the matcher where we used `MatcherApp.addArg` at `matcherBelowDep`.
     We use this information to generate the auxiliary `_sunfold` definition needed by the smart unfolding
     technique used at WHNF. -/
  matcherBelowDep : NameSet := {}
  /- As part of the inductive predicates case, we keep adding more and more discriminants from the
     local context and build up a bigger matcher application until we reach a fixed point.
     As a side-effect, this creates matchers. Here we capture all these side-effects, because
     the construction rolls back any changes done to the environment and the side-effects
     need to be replayed. -/
  addMatchers : Array $ MetaM Unit := #[]

abbrev M := StateRefT State MetaM

instance : Inhabited (M α) where
  default := throwError "failed"

def run (x : M α) (s : State := {}) : MetaM (α × State) :=
  StateRefT'.run x s

/--
  Return true iff `e` contains an application `recFnName .. t ..` where the term `t` is
  the argument we are trying to recurse on, and it contains loose bound variables.

  We use this test to decide whether we should process a matcher-application as a regular
  applicaton or not. That is, whether we should push the `below` argument should be affected by the matcher or not.
  If `e` does not contain an application of the form `recFnName .. t ..`, then we know
  the recursion doesn't depend on any pattern variable in this matcher.
-/
def recArgHasLooseBVarsAt (recFnName : Name) (recArgInfo : RecArgInfo) (e : Expr) : Bool :=
  let recArgPos := recArgInfo.fixedParams.size + recArgInfo.pos
  let app?   := e.find? fun e =>
     e.isAppOf recFnName && e.getAppNumArgs > recArgPos && (e.getArg! recArgPos).hasLooseBVars
  app?.isSome

private def containsRecFn (recFnName : Name) (e : Expr) : Bool :=
  (e.find? fun e => e.isConstOf recFnName).isSome

def ensureNoRecFn (recFnName : Name) (e : Expr) : MetaM Expr := do
  if containsRecFn recFnName e then
    Meta.forEachExpr e fun e => do
      if e.isAppOf recFnName then
        throwError "unexpected occurrence of recursive application{indentExpr e}"
    pure e
  else
    pure e

end Lean.Elab.Structural
