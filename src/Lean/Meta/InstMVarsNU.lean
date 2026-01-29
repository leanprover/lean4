
module
prelude

public import Lean.Meta.Basic

open Lean Meta

namespace Lean.Meta

namespace IntantiateMVars

structure DelayedLift where
  originalDepth : Nat
  expr : Expr -- Unshifted expression
  -- shifted : Thunk Expr -- Shifted expression

def DelayedLift.ofExpr (e : Expr) : DelayedLift where
  originalDepth := 0
  expr := e
  -- shifted := Thunk.pure e

/-
def DelayedLift.lift (n : Nat) (ds : DelayedLift) : DelayedLift :=
  if ds.expr.hasLooseBVars then
    let newLift := ds.currentLift + n
    { ds with
      currentLift := newLift
      -- shifted := Thunk.mk fun _ =>
      --   ds.expr.liftLooseBVars (s := 0) (d := newLift)
    }
  else
    ds
-/

structure Context where
  depth : Nat := 0
  fvarSubst : PersistentHashMap FVarId DelayedLift := {}

structure State where
  cache : Std.HashMap ExprStructEq Expr := {}

abbrev M := ReaderT Context (StateRefT State MetaM)

/-
When going under binders, we
* we record the increased depth
* empty the cache locally
-/
def withLift (n : Nat) (k : M α) : M α := do
  let cache ← modifyGet fun s => (s.cache, { s with cache := {} })
  let x ← withTheReader Context (fun ctx =>
    { ctx with depth := ctx.depth + n
              --  fvarSubst := ctx.fvarSubst.mapVal (fun ds => ds.lift n) -- TODO: avoid mapping eagerly
    }) do
      k
  modify fun s => { s with cache := cache }
  pure x

/--
When traversing a delayed-assigned metavariable assignment, extend the substitution
-/
def withSubst (fvarIds : Array Expr) (args : Array Expr) : M α → M α :=
  withTheReader Context fun ctx => Id.run do
    let mut mvarSubst := ctx.fvarSubst
    for fvarId in fvarIds, arg in args do
      mvarSubst := mvarSubst.erase fvarId.fvarId! |>.insert fvarId.fvarId! ⟨ctx.depth, arg⟩
    { ctx with fvarSubst := mvarSubst }

def lookup? (fvarId : FVarId) : M (Option Expr) := do
  let ctx ← read
  match ctx.fvarSubst.find? fvarId with
  | some ds => return ds.expr.liftLooseBVars (s := 0) (d := ctx.depth - ds.originalDepth)
  | none => return none

partial def go (e : Expr) : M Expr := do
  unless e.hasMVar || e.hasFVar do
    return e
  -- logInfo m!"Instantiating MVars in:{indentExpr e}\nfvarSubst: {(← read).fvarSubst.toList.map (fun (k, v) => (mkFVar k, v.expr, v.currentLift))}"
  if let some e' := (← get).cache[ExprStructEq.mk e]? then return e'

  let goApp (e : Expr) := e.withApp fun f args => do
    let args ← args.mapM go
    let instArgs (f' : Expr) : M Expr := do
      pure (mkAppN f' args)
    let instApp : M Expr := do
      let wasMVar := f.isMVar
      let f' ← go f
      if wasMVar && f'.isLambda then
        /- Some of the arguments in `args` are irrelevant after we beta
            reduce. Also, it may be a bug to not instantiate them, since they
            may depend on free variables that are not in the context (see
            issue #4375). So we pass `useZeta := true` to ensure that they are
            instantiated. -/
        go (f'.betaRev args.reverse (useZeta := true))
      else
        instArgs f'
    if let .mvar mvarId := f then
      let some {fvars, mvarIdPending} ← getDelayedMVarAssignment? mvarId | return ← instApp
      if fvars.size > args.size then
        /- We don't have sufficient arguments for instantiating the free variables `fvars`.
           This can only happen if a tactic or elaboration function is not implemented correctly.
           We decided to not use `panic!` here and report it as an error in the frontend
           when we are checking for unassigned metavariables in an elaborated term. -/
        return ← instArgs f
      let substArgs := args[:fvars.size].copy
      let extraArgs := args[fvars.size:].copy
      /-
          Example: suppose we have
            `?m t1 t2 t3`
          That is, `f := ?m` and `substArgs := #[t1, t2]` and `extraArgs := #[t3]`
          Moreover, `?m` is delayed assigned
            `?m #[x, y] := e`

          We want to instantiate `e` with a substitution `[x ↦ t1, y ↦ t2]`, and then apply `t3`
      -/
      let newVal ← withSubst fvars substArgs <|
        go (mkMVar mvarIdPending)
      -- logInfo m!"Resolved delayed mvar assignment to {newVal}"
      let result := mkAppN newVal extraArgs
      return result
    instApp

  let e' ← match e with
    | .bvar .. | .lit ..  => unreachable!
    | .proj _ _ s      => return e.updateProj! (← go s)
    | .forallE _ d b _ => return e.updateForallE! (← go d) (← withLift 1 <| go b)
    | .lam _ d b _     => return e.updateLambdaE! (← go d) (← withLift 1 <| go b)
    | .letE _ t v b nd => return e.updateLet! (← go t) (← go v) (← withLift 1 <| go b) nd
    | .const _ lvls    => return e.updateConst! (← lvls.mapM (instantiateLevelMVars ·))
    | .sort lvl        => return e.updateSort! (← instantiateLevelMVars lvl)
    | .mdata _ b       => return e.updateMData! (← go b)
    | .fvar fvarId     => return (← lookup? fvarId).getD e
    | .app ..          => goApp e
    | .mvar mvarId     => -- Not in function position, cannot be a delayed mvar assignment
        match (← getExprMVarAssignment? mvarId) with
        | some newE =>
          -- logInfo m!"Resolved {mkMVar mvarId} mvar assignment to {newE}"
          let newE ← go newE
          -- logInfo m!"Instantiated {mkMVar mvarId} mvar assignment to {newE}"
          return newE
        | none => pure e
  modify fun s => { s with cache := s.cache.insert (ExprStructEq.mk e) e' }
  return e'

end IntantiateMVars

public def instantiateMVarsNoUpdate (e : Expr) : MetaM Expr := do
  (IntantiateMVars.go e).run {} |>.run' {}

end Lean.Meta
