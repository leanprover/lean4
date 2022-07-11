/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.MonadCache
import Lean.LocalContext

namespace Lean

/-
The metavariable context stores metavariable declarations and their
assignments. It is used in the elaborator, tactic framework, unifier
(aka `isDefEq`), and type class resolution (TC). First, we list all
the requirements imposed by these modules.

- We may invoke TC while executing `isDefEq`. We need this feature to
be able to solve unification problems such as:
```
f ?a (ringAdd ?s) ?x ?y =?= f Int intAdd n m
```
where `(?a : Type) (?s : Ring ?a) (?x ?y : ?a)`
During `isDefEq` (i.e., unification), it will need to solve the constrain
```
ringAdd ?s =?= intAdd
```
We say `ringAdd ?s` is stuck because it cannot be reduced until we
synthesize the term `?s : Ring ?a` using TC. This can be done since we
have assigned `?a := Int` when solving `?a =?= Int`.

- TC uses `isDefEq`, and `isDefEq` may create TC problems as shown
above. Thus, we may have nested TC problems.

- `isDefEq` extends the local context when going inside binders. Thus,
the local context for nested TC may be an extension of the local
context for outer TC.

- TC should not assign metavariables created by the elaborator, simp,
tactic framework, and outer TC problems. Reason: TC commits to the
first solution it finds. Consider the TC problem `Coe Nat ?x`,
where `?x` is a metavariable created by the caller. There are many
solutions to this problem (e.g., `?x := Int`, `?x := Real`, ...),
and it doesn’t make sense to commit to the first one since TC does
not know the constraints the caller may impose on `?x` after the
TC problem is solved.
Remark: we claim it is not feasible to make the whole system backtrackable,
and allow the caller to backtrack back to TC and ask it for another solution
if the first one found did not work. We claim it would be too inefficient.

- TC metavariables should not leak outside of TC. Reason: we want to
get rid of them after we synthesize the instance.

- `simp` invokes `isDefEq` for matching the left-hand-side of
equations to terms in our goal. Thus, it may invoke TC indirectly.

- In Lean3, we didn’t have to create a fresh pattern for trying to
match the left-hand-side of equations when executing `simp`. We had a
mechanism called "tmp" metavariables. It avoided this overhead, but it
created many problems since `simp` may indirectly call TC which may
recursively call TC. Moreover, we may want to allow TC to invoke
tactics in the future. Thus, when `simp` invokes `isDefEq`, it may indirectly invoke
a tactic and `simp` itself.  The Lean3 approach assumed that
metavariables were short-lived, this is not true in Lean4, and to some
extent was also not true in Lean3 since `simp`, in principle, could
trigger an arbitrary number of nested TC problems.

- Here are some possible call stack traces we could have in Lean3 (and Lean4).
```
Elaborator (-> TC -> isDefEq)+
Elaborator -> isDefEq (-> TC -> isDefEq)*
Elaborator -> simp -> isDefEq (-> TC -> isDefEq)*
```
In Lean4, TC may also invoke tactics in the future.

- In Lean3 and Lean4, TC metavariables are not really short-lived. We
solve an arbitrary number of unification problems, and we may have
nested TC invocations.

- TC metavariables do not share the same local context even in the
same invocation. In the C++ and Lean implementations we use a trick to
ensure they do:
https://github.com/leanprover/lean/blob/92826917a252a6092cffaf5fc5f1acb1f8cef379/src/library/type_context.cpp#L3583-L3594

- Metavariables may be natural, synthetic or syntheticOpaque.
  a) Natural metavariables may be assigned by unification (i.e., `isDefEq`).

  b) Synthetic metavariables may still be assigned by unification,
     but whenever possible `isDefEq` will avoid the assignment. For example,
     if we have the unification constaint `?m =?= ?n`, where `?m` is synthetic,
     but `?n` is not, `isDefEq` solves it by using the assignment `?n := ?m`.
     We use synthetic metavariables for type class resolution.
     Any module that creates synthetic metavariables, must also check
     whether they have been assigned by `isDefEq`, and then still synthesize
     them, and check whether the sythesized result is compatible with the one
     assigned by `isDefEq`.

  c) SyntheticOpaque metavariables are never assigned by `isDefEq`.
     That is, the constraint `?n =?= Nat.succ Nat.zero` always fail
     if `?n` is a syntheticOpaque metavariable. This kind of metavariable
     is created by tactics such as `intro`. Reason: in the tactic framework,
     subgoals as represented as metavariables, and a subgoal `?n` is considered
     as solved whenever the metavariable is assigned.

  This distinction was not precise in Lean3 and produced
  counterintuitive behavior. For example, the following hack was added
  in Lean3 to work around one of these issues:
  https://github.com/leanprover/lean/blob/92826917a252a6092cffaf5fc5f1acb1f8cef379/src/library/type_context.cpp#L2751

- When creating lambda/forall expressions, we need to convert/abstract
free variables and convert them to bound variables. Now, suppose we a
trying to create a lambda/forall expression by abstracting free
variable `xs` and a term `t[?m]` which contains a metavariable `?m`,
and the local context of `?m` contains `xs`. The term
```
fun xs => t[?m]
```
will be ill-formed if we later assign a term `s` to `?m`, and
`s` contains free variables in `xs`. We address this issue by changing
the free variable abstraction procedure. We consider two cases: `?m`
is natural, `?m` is synthetic. Assume the type of `?m` is
`A[xs]`. Then, in both cases we create an auxiliary metavariable `?n` with
type `forall xs => A[xs]`, and local context := local context of `?m` - `xs`.
In both cases, we produce the term `fun xs => t[?n xs]`

  1- If `?m` is natural or synthetic, then we assign `?m := ?n xs`, and we produce
  the term `fun xs => t[?n xs]`

  2- If `?m` is syntheticOpaque, then we mark `?n` as a syntheticOpaque variable.
  However, `?n` is managed by the metavariable context itself.
  We say we have a "delayed assignment" `?n xs := ?m`.
  That is, after a term `s` is assigned to `?m`, and `s`
  does not contain metavariables, we replace any occurrence
  `?n ts` with `s[xs := ts]`.

Gruesome details:

  - When we create the type `forall xs => A` for `?n`, we may
  encounter the same issue if `A` contains metavariables. So, the
  process above is recursive. We claim it terminates because we keep
  creating new metavariables with smaller local contexts.

  - Suppose, we have `t[?m]` and we want to create a let-expression by
  abstracting a let-decl free variable `x`, and the local context of
  `?m` contatins `x`. Similarly to the previous case
  ```
  let x : T := v; t[?m]
  ```
  will be ill-formed if we later assign a term `s` to `?m`, and
  `s` contains free variable `x`. Again, assume the type of `?m` is `A[x]`.

    1- If `?m` is natural or synthetic, then we create `?n : (let x : T := v; A[x])` with
    and local context := local context of `?m` - `x`, we assign `?m := ?n`,
    and produce the term `let x : T := v; t[?n]`. That is, we are just making
    sure `?n` must never be assigned to a term containing `x`.

    2- If `?m` is syntheticOpaque, we create a fresh syntheticOpaque `?n`
    with type `?n : T -> (let x : T := v; A[x])` and local context := local context of `?m` - `x`,
    create the delayed assignment `?n #[x] := ?m`, and produce the term `let x : T := v; t[?n x]`.
    Now suppose we assign `s` to `?m`. We do not assign the term `fun (x : T) => s` to `?n`, since
    `fun (x : T) => s` may not even be type correct. Instead, we just replace applications `?n r`
    with `s[x/r]`. The term `r` may not necessarily be a bound variable. For example, a tactic
    may have reduced `let x : T := v; t[?n x]` into `t[?n v]`.
    We are essentially using the pair "delayed assignment + application" to implement a delayed
    substitution.

- We use TC for implementing coercions. Both Joe Hendrix and Reid Barton
reported a nasty limitation. In Lean3, TC will not be used if there are
metavariables in the TC problem. For example, the elaborator will not try
to synthesize `Coe Nat ?x`. This is good, but this constraint is too
strict for problems such as `Coe (Vector Bool ?n) (BV ?n)`. The coercion
exists independently of `?n`. Thus, during TC, we want `isDefEq` to throw
an exception instead of return `false` whenever it tries to assign
a metavariable owned by its caller. The idea is to sign to the caller that
it cannot solve the TC problem at this point, and more information is needed.
That is, the caller must make progress an assign its metavariables before
trying to invoke TC again.

In Lean4, we are using a simpler design for the `MetavarContext`.

- No distinction betwen temporary and regular metavariables.

- Metavariables have a `depth` Nat field.

- MetavarContext also has a `depth` field.

- We bump the `MetavarContext` depth when we create a nested problem.
  Example: Elaborator (depth = 0) -> Simplifier matcher (depth = 1) -> TC (level = 2) -> TC (level = 3) -> ...

- When `MetavarContext` is at depth N, `isDefEq` does not assign variables from `depth < N`.

- Metavariables from depth N+1 must be fully assigned before we return to level N.

- New design even allows us to invoke tactics from TC.

* Main concern
We don't have tmp metavariables anymore in Lean4. Thus, before trying to match
the left-hand-side of an equation in `simp`. We first must bump the level of the `MetavarContext`,
create fresh metavariables, then create a new pattern by replacing the free variable on the left-hand-side with
these metavariables. We are hoping to minimize this overhead by

  - Using better indexing data structures in `simp`. They should reduce the number of time `simp` must invoke `isDefEq`.

  - Implementing `isDefEqApprox` which ignores metavariables and returns only `false` or `undef`.
    It is a quick filter that allows us to fail quickly and avoid the creation of new fresh metavariables,
    and a new pattern.

  - Adding built-in support for arithmetic, Logical connectives, etc. Thus, we avoid a bunch of lemmas in the simp set.

  - Adding support for AC-rewriting. In Lean3, users use AC lemmas as
    rewriting rules for "sorting" terms. This is inefficient, requires
    a quadratic number of rewrite steps, and does not preserve the
    structure of the goal.

The temporary metavariables were also used in the "app builder" module used in Lean3. The app builder uses
`isDefEq`. So, it could, in principle, invoke an arbitrary number of nested TC problems. However, in Lean3,
all app builder uses are controlled. That is, it is mainly used to synthesize implicit arguments using
very simple unification and/or non-nested TC. So, if the "app builder" becomes a bottleneck without tmp metavars,
we may solve the issue by implementing `isDefEqCheap` that never invokes TC and uses tmp metavars.
-/

structure LocalInstance where
  className : Name
  fvar      : Expr
  deriving Inhabited

abbrev LocalInstances := Array LocalInstance

instance : BEq LocalInstance where
  beq i₁ i₂ := i₁.fvar == i₂.fvar

/-- Remove local instance with the given `fvarId`. Do nothing if `localInsts` does not contain any free variable with id `fvarId`. -/
def LocalInstances.erase (localInsts : LocalInstances) (fvarId : FVarId) : LocalInstances :=
  match localInsts.findIdx? (fun inst => inst.fvar.fvarId! == fvarId) with
  | some idx => localInsts.eraseIdx idx
  | _        => localInsts

inductive MetavarKind where
  | natural
  | synthetic
  | syntheticOpaque
  deriving Inhabited, Repr

def MetavarKind.isSyntheticOpaque : MetavarKind → Bool
  | MetavarKind.syntheticOpaque => true
  | _                           => false

def MetavarKind.isNatural : MetavarKind → Bool
  | MetavarKind.natural => true
  | _                   => false

structure MetavarDecl where
  userName       : Name := Name.anonymous
  lctx           : LocalContext
  type           : Expr
  depth          : Nat
  localInstances : LocalInstances
  kind           : MetavarKind
  numScopeArgs   : Nat := 0 -- See comment at `CheckAssignment` `Meta/ExprDefEq.lean`
  index          : Nat      -- We use this field to track how old a metavariable is. It is set using a counter at `MetavarContext`
  deriving Inhabited

/--
  A delayed assignment for a metavariable `?m`. It represents an assignment of the form `?m := (fun fvars => (mkMVar mvarIdPending))`.
  `mvarIdPending` is a `syntheticOpaque` metavariable that has not been synthesized yet. The delayed assignment becomes a real one
  as soon as `mvarIdPending` has been fully synthesized.
  `fvars` are variables in the `mvarIdPending` local context.
-/
structure DelayedMetavarAssignment where
  fvars         : Array Expr
  mvarIdPending : MVarId

open Std (HashMap PersistentHashMap)

structure MetavarContext where
  depth          : Nat := 0
  mvarCounter    : Nat := 0 -- Counter for setting the field `index` at `MetavarDecl`
  lDepth         : PersistentHashMap MVarId Nat := {}
  decls          : PersistentHashMap MVarId MetavarDecl := {}
  userNames      : PersistentHashMap Name MVarId := {}
  lAssignment    : PersistentHashMap MVarId Level := {}
  eAssignment    : PersistentHashMap MVarId Expr := {}
  dAssignment    : PersistentHashMap MVarId DelayedMetavarAssignment := {}
  usedAssignment : Bool := false

class MonadMCtx (m : Type → Type) where
  getMCtx    : m MetavarContext
  modifyMCtx : (MetavarContext → MetavarContext) → m Unit

export MonadMCtx (getMCtx modifyMCtx)

instance (m n) [MonadLift m n] [MonadMCtx m] : MonadMCtx n where
  getMCtx    := liftM (getMCtx : m _)
  modifyMCtx := fun f => liftM (modifyMCtx f : m _)

def markUsedAssignment [MonadMCtx m] : m Unit :=
  modifyMCtx fun mctx => { mctx with usedAssignment := true }

abbrev setMCtx [MonadMCtx m] (mctx' : MetavarContext) : m Unit :=
  modifyMCtx fun mctx => { mctx' with usedAssignment := mctx'.usedAssignment || mctx.usedAssignment }

abbrev getLevelMVarAssignment? [Monad m] [MonadMCtx m] (mvarId : MVarId) : m (Option Level) := do
  let result? := (← getMCtx).lAssignment.find? mvarId
  if result?.isSome then
    markUsedAssignment
  return result?

def MetavarContext.getExprAssignmentCore? (m : MetavarContext) (mvarId : MVarId) : Option Expr :=
  m.eAssignment.find? mvarId

def getExprMVarAssignment? [Monad m] [MonadMCtx m] (mvarId : MVarId) : m (Option Expr) := do
  let result? := (← getMCtx).getExprAssignmentCore? mvarId
  if result?.isSome then
    markUsedAssignment
  return result?

def getDelayedMVarAssignment? [Monad m] [MonadMCtx m] (mvarId : MVarId) : m (Option DelayedMetavarAssignment) := do
  let result? := (← getMCtx).dAssignment.find? mvarId
  if result?.isSome then
    markUsedAssignment
  return result?

/- Given a sequence of delayed assignments
   ```
   mvarId₁ := mvarId₂ ...;
   ...
   mvarIdₙ := mvarId_root ...  -- where `mvarId_root` is not delayed assigned
   ```
   in `mctx`, `getDelayedRoot mctx mvarId₁` return `mvarId_root`.
   If `mvarId₁` is not delayed assigned then return `mvarId₁` -/
partial def getDelayedMVarRoot [Monad m] [MonadMCtx m] (mvarId : MVarId) : m MVarId := do
  match (← getDelayedMVarAssignment? mvarId) with
  | some d => getDelayedMVarRoot d.mvarIdPending
  | none   => return mvarId

def isLevelMVarAssigned [Monad m] [MonadMCtx m] (mvarId : MVarId) : m Bool := do
  markUsedAssignment
  return (← getMCtx).lAssignment.contains mvarId

/-- Return `true` if the give metavariable is already assigned. -/
def isExprMVarAssigned [Monad m] [MonadMCtx m] (mvarId : MVarId) : m Bool := do
  markUsedAssignment
  return (← getMCtx).eAssignment.contains mvarId

def isMVarDelayedAssigned [Monad m] [MonadMCtx m] (mvarId : MVarId) : m Bool := do
  markUsedAssignment
  return (← getMCtx).dAssignment.contains mvarId

def isLevelMVarAssignable [Monad m] [MonadMCtx m] (mvarId : MVarId) : m Bool := do
  markUsedAssignment
  let mctx ← getMCtx
  match mctx.lDepth.find? mvarId with
  | some d => return d == mctx.depth
  | _      => panic! "unknown universe metavariable"

def MetavarContext.getDecl (mctx : MetavarContext) (mvarId : MVarId) : MetavarDecl :=
  match mctx.decls.find? mvarId with
  | some decl => decl
  | none      => panic! "unknown metavariable"

def isExprMVarAssignable [Monad m] [MonadMCtx m] (mvarId : MVarId) : m Bool := do
  markUsedAssignment
  let mctx ← getMCtx
  let decl := mctx.getDecl mvarId
  return decl.depth == mctx.depth

/-- Return true iff the given level contains an assigned metavariable. -/
def hasAssignedLevelMVar [Monad m] [MonadMCtx m] : Level → m Bool
  | Level.succ lvl       => pure lvl.hasMVar <&&> hasAssignedLevelMVar lvl
  | Level.max lvl₁ lvl₂  => (pure lvl₁.hasMVar <&&> hasAssignedLevelMVar lvl₁) <||> (pure lvl₂.hasMVar <&&> hasAssignedLevelMVar lvl₂)
  | Level.imax lvl₁ lvl₂ => (pure lvl₁.hasMVar <&&> hasAssignedLevelMVar lvl₁) <||> (pure lvl₂.hasMVar <&&> hasAssignedLevelMVar lvl₂)
  | Level.mvar mvarId    => isLevelMVarAssigned mvarId
  | Level.zero           => pure false
  | Level.param _        => pure false

/-- Return `true` iff expression contains assigned (level/expr) metavariables or delayed assigned mvars -/
def hasAssignedMVar [Monad m] [MonadMCtx m] : Expr → m Bool
  | Expr.const _ lvls    => lvls.anyM hasAssignedLevelMVar
  | Expr.sort lvl        => hasAssignedLevelMVar lvl
  | Expr.app f a         => (pure f.hasMVar <&&> hasAssignedMVar f) <||> (pure a.hasMVar <&&> hasAssignedMVar a)
  | Expr.letE _ t v b _  => (pure t.hasMVar <&&> hasAssignedMVar t) <||> (pure v.hasMVar <&&> hasAssignedMVar v) <||> (pure b.hasMVar <&&> hasAssignedMVar b)
  | Expr.forallE _ d b _ => (pure d.hasMVar <&&> hasAssignedMVar d) <||> (pure b.hasMVar <&&> hasAssignedMVar b)
  | Expr.lam _ d b _     => (pure d.hasMVar <&&> hasAssignedMVar d) <||> (pure b.hasMVar <&&> hasAssignedMVar b)
  | Expr.fvar _          => return false
  | Expr.bvar _          => return false
  | Expr.lit _           => return false
  | Expr.mdata _ e       => pure e.hasMVar <&&> hasAssignedMVar e
  | Expr.proj _ _ e      => pure e.hasMVar <&&> hasAssignedMVar e
  | Expr.mvar mvarId     => isExprMVarAssigned mvarId <||> isMVarDelayedAssigned mvarId

/-- Return true iff the given level contains a metavariable that can be assigned. -/
def hasAssignableLevelMVar [Monad m] [MonadMCtx m] : Level → m Bool
  | Level.succ lvl       => pure lvl.hasMVar <&&> hasAssignableLevelMVar lvl
  | Level.max lvl₁ lvl₂  => (pure lvl₁.hasMVar <&&> hasAssignableLevelMVar lvl₁) <||> (pure lvl₂.hasMVar <&&> hasAssignableLevelMVar lvl₂)
  | Level.imax lvl₁ lvl₂ => (pure lvl₁.hasMVar <&&> hasAssignableLevelMVar lvl₁) <||> (pure lvl₂.hasMVar <&&> hasAssignableLevelMVar lvl₂)
  | Level.mvar mvarId    => isLevelMVarAssignable mvarId
  | Level.zero           => return false
  | Level.param _        => return false

/-- Return `true` iff expression contains a metavariable that can be assigned. -/
def hasAssignableMVar [Monad m] [MonadMCtx m] : Expr → m Bool
  | Expr.const _ lvls    => lvls.anyM hasAssignableLevelMVar
  | Expr.sort lvl        => hasAssignableLevelMVar lvl
  | Expr.app f a         => (pure f.hasMVar <&&> hasAssignableMVar f) <||> (pure a.hasMVar <&&> hasAssignableMVar a)
  | Expr.letE _ t v b _  => (pure t.hasMVar <&&> hasAssignableMVar t) <||> (pure v.hasMVar <&&> hasAssignableMVar v) <||> (pure b.hasMVar <&&> hasAssignableMVar b)
  | Expr.forallE _ d b _ => (pure d.hasMVar <&&> hasAssignableMVar d) <||> (pure b.hasMVar <&&> hasAssignableMVar b)
  | Expr.lam _ d b _     => (pure d.hasMVar <&&> hasAssignableMVar d) <||> (pure b.hasMVar <&&> hasAssignableMVar b)
  | Expr.fvar _          => return false
  | Expr.bvar _          => return false
  | Expr.lit _           => return false
  | Expr.mdata _ e       => pure e.hasMVar <&&> hasAssignableMVar e
  | Expr.proj _ _ e      => pure e.hasMVar <&&> hasAssignableMVar e
  | Expr.mvar mvarId     => isExprMVarAssignable mvarId

/--
  Add `mvarId := u` to the universe metavariable assignment.
  This method does not check whether `mvarId` is already assigned, nor it checks whether
  a cycle is being introduced.
  This is a low-level API, and it is safer to use `isLevelDefEq (mkLevelMVar mvarId) u`.
-/
def assignLevelMVar [MonadMCtx m] (mvarId : MVarId) (val : Level) : m Unit :=
  modifyMCtx fun m => { m with lAssignment := m.lAssignment.insert mvarId val, usedAssignment := true }

def assignExprMVar [MonadMCtx m] (mvarId : MVarId) (val : Expr) : m Unit :=
  modifyMCtx fun m => { m with eAssignment := m.eAssignment.insert mvarId val, usedAssignment := true }

def assignDelayedMVar [MonadMCtx m] (mvarId : MVarId) (fvars : Array Expr) (mvarIdPending : MVarId) : m Unit :=
  modifyMCtx fun m => { m with dAssignment := m.dAssignment.insert mvarId { fvars, mvarIdPending }, usedAssignment := true }

/-
Notes on artificial eta-expanded terms due to metavariables.
We try avoid synthetic terms such as `((fun x y => t) a b)` in the output produced by the elaborator.
This kind of term may be generated when instantiating metavariable assignments.
This module tries to avoid their generation because they often introduce unnecessary dependencies and
may affect automation.

When elaborating terms, we use metavariables to represent "holes". Each hole has a context which includes
all free variables that may be used to "fill" the hole. Suppose, we create a metavariable (hole) `?m : Nat` in a context
containing `(x : Nat) (y : Nat) (b : Bool)`, then we can assign terms such as `x + y` to `?m` since `x` and `y`
are in the context used to create `?m`. Now, suppose we have the term `?m + 1` and we want to create the lambda expression
`fun x => ?m + 1`. This term is not correct since we may assign to `?m` a term containing `x`.
We address this issue by create a synthetic metavariable `?n : Nat → Nat` and adding the delayed assignment
`?n #[x] := ?m`, and the term `fun x => ?n x + 1`. When we later assign a term `t[x]` to `?m`, `fun x => t[x]` is assigned to
`?n`, and if we substitute it at `fun x => ?n x + 1`, we produce `fun x => ((fun x => t[x]) x) + 1`.
To avoid this term eta-expanded term, we apply beta-reduction when instantiating metavariable assignments in this module.
This operation is performed at `instantiateExprMVars`, `elimMVarDeps`, and `levelMVarToParam`.
-/
partial def instantiateLevelMVars [Monad m] [MonadMCtx m] : Level → m Level
  | lvl@(Level.succ lvl₁)      => return Level.updateSucc! lvl (← instantiateLevelMVars lvl₁)
  | lvl@(Level.max lvl₁ lvl₂)  => return Level.updateMax! lvl (← instantiateLevelMVars lvl₁) (← instantiateLevelMVars lvl₂)
  | lvl@(Level.imax lvl₁ lvl₂) => return Level.updateIMax! lvl (← instantiateLevelMVars lvl₁) (← instantiateLevelMVars lvl₂)
  | lvl@(Level.mvar mvarId)    => do
    match (← getLevelMVarAssignment? mvarId) with
    | some newLvl =>
      if !newLvl.hasMVar then pure newLvl
      else do
        let newLvl' ← instantiateLevelMVars newLvl
        assignLevelMVar mvarId newLvl'
        pure newLvl'
    | none        => pure lvl
  | lvl => pure lvl

/-- instantiateExprMVars main function -/
partial def instantiateExprMVars [Monad m] [MonadMCtx m] [STWorld ω m] [MonadLiftT (ST ω) m] (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
  if !e.hasMVar then
    pure e
  else checkCache { val := e : ExprStructEq } fun _ => do match e with
    | Expr.proj _ _ s      => return e.updateProj! (← instantiateExprMVars s)
    | Expr.forallE _ d b _ => return e.updateForallE! (← instantiateExprMVars d) (← instantiateExprMVars b)
    | Expr.lam _ d b _     => return e.updateLambdaE! (← instantiateExprMVars d) (← instantiateExprMVars b)
    | Expr.letE _ t v b _  => return e.updateLet! (← instantiateExprMVars t) (← instantiateExprMVars v) (← instantiateExprMVars b)
    | Expr.const _ lvls    => return e.updateConst! (← lvls.mapM instantiateLevelMVars)
    | Expr.sort lvl        => return e.updateSort! (← instantiateLevelMVars lvl)
    | Expr.mdata _ b       => return e.updateMData! (← instantiateExprMVars b)
    | Expr.app ..          => e.withApp fun f args => do
      let instArgs (f : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        let args ← args.mapM instantiateExprMVars
        pure (mkAppN f args)
      let instApp : MonadCacheT ExprStructEq Expr m Expr := do
        let wasMVar := f.isMVar
        let f ← instantiateExprMVars f
        if wasMVar && f.isLambda then
          /- Some of the arguments in args are irrelevant after we beta reduce. -/
          instantiateExprMVars (f.betaRev args.reverse)
        else
          instArgs f
      match f with
      | Expr.mvar mvarId =>
        match (← getDelayedMVarAssignment? mvarId) with
        | none => instApp
        | some { fvars, mvarIdPending } =>
          /-
             Apply "delayed substitution" (i.e., delayed assignment + application).
             That is, `f` is some metavariable `?m`, that is delayed assigned to `val`.
             If after instantiating `val`, we obtain `newVal`, and `newVal` does not contain
             metavariables, we replace the free variables `fvars` in `newVal` with the first
             `fvars.size` elements of `args`. -/
          if fvars.size > args.size then
            /- We don't have sufficient arguments for instantiating the free variables `fvars`.
               This can only happy if a tactic or elaboration function is not implemented correctly.
               We decided to not use `panic!` here and report it as an error in the frontend
               when we are checking for unassigned metavariables in an elaborated term. -/
            instArgs f
          else
            let newVal ← instantiateExprMVars (mkMVar mvarIdPending)
            if newVal.hasExprMVar then
              instArgs f
            else do
              let args ← args.mapM instantiateExprMVars
              /-
                 Example: suppose we have
                   `?m t1 t2 t3`
                 That is, `f := ?m` and `args := #[t1, t2, t3]`
                 Morever, `?m` is delayed assigned
                   `?m #[x, y] := f x y`
                 where, `fvars := #[x, y]` and `newVal := f x y`.
                 After abstracting `newVal`, we have `f (Expr.bvar 0) (Expr.bvar 1)`.
                 After `instantiaterRevRange 0 2 args`, we have `f t1 t2`.
                 After `mkAppRange 2 3`, we have `f t1 t2 t3` -/
              let newVal := newVal.abstract fvars
              let result := newVal.instantiateRevRange 0 fvars.size args
              let result := mkAppRange result fvars.size args.size args
              pure result
      | _ => instApp
    | e@(Expr.mvar mvarId) => checkCache { val := e : ExprStructEq } fun _ => do
      match (← getExprMVarAssignment? mvarId) with
      | some newE => do
        let newE' ← instantiateExprMVars newE
        assignExprMVar mvarId newE'
        pure newE'
      | none => pure e
    | e => pure e

instance : MonadMCtx (StateRefT MetavarContext (ST ω)) where
  getMCtx    := get
  modifyMCtx := modify

def instantiateMVarsCore (mctx : MetavarContext) (e : Expr) : Expr × MetavarContext :=
  let instantiate {ω} (e : Expr) : (MonadCacheT ExprStructEq Expr <| StateRefT MetavarContext (ST ω)) Expr :=
    instantiateExprMVars e
  runST fun _ => instantiate e |>.run |>.run mctx

def instantiateMVars [Monad m] [MonadMCtx m] (e : Expr) : m Expr := do
  if !e.hasMVar then
    return e
  else
    let (r, mctx) := instantiateMVarsCore (← getMCtx) e
    modifyMCtx fun _ => mctx
    return r

def instantiateLCtxMVars [Monad m] [MonadMCtx m] (lctx : LocalContext) : m LocalContext :=
  lctx.foldlM (init := {}) fun lctx ldecl => do
     match ldecl with
     | .cdecl _ fvarId userName type bi =>
       let type ← instantiateMVars type
       return lctx.mkLocalDecl fvarId userName type bi
     | .ldecl _ fvarId userName type value nonDep =>
       let type ← instantiateMVars type
       let value ← instantiateMVars value
       return lctx.mkLetDecl fvarId userName type value nonDep

def instantiateMVarDeclMVars [Monad m] [MonadMCtx m] (mvarId : MVarId) : m Unit := do
  let mvarDecl     := (← getMCtx).getDecl mvarId
  let lctx ← instantiateLCtxMVars mvarDecl.lctx
  let type ← instantiateMVars mvarDecl.type
  modifyMCtx fun mctx => { mctx with decls := mctx.decls.insert mvarId { mvarDecl with lctx, type } }

def instantiateLocalDeclMVars [Monad m] [MonadMCtx m] (localDecl : LocalDecl) : m LocalDecl := do
  match localDecl with
  | .cdecl idx id n type bi  =>
    return .cdecl idx id n (← instantiateMVars type) bi
  | .ldecl idx id n type val nonDep =>
    return .ldecl idx id n (← instantiateMVars type) (← instantiateMVars val) nonDep

namespace DependsOn

structure State where
  visited : ExprSet := {}
  mctx    : MetavarContext

private abbrev M := StateM State

instance : MonadMCtx M where
  getMCtx := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

private def shouldVisit (e : Expr) : M Bool := do
  if !e.hasMVar && !e.hasFVar then
    return false
  else if (← get).visited.contains e then
    return false
  else
    modify fun s => { s with visited := s.visited.insert e }
    return true

@[specialize] private partial def dep (pf : FVarId → Bool) (pm : MVarId →  Bool) (e : Expr) : M Bool :=
  let rec
    visit (e : Expr) : M Bool := do
      if !(← shouldVisit e) then
        pure false
      else
        visitMain e,
    visitApp : Expr → M Bool
      | Expr.app f a .. => visitApp f <||> visit a
      | e => visit e,
    visitMain : Expr → M Bool
      | Expr.proj _ _ s      => visit s
      | Expr.forallE _ d b _ => visit d <||> visit b
      | Expr.lam _ d b _     => visit d <||> visit b
      | Expr.letE _ t v b _  => visit t <||> visit v <||> visit b
      | Expr.mdata _ b       => visit b
      | e@(Expr.app ..)      => do
        let f := e.getAppFn
        if f.isMVar then
          let e' ← instantiateMVars e
          if e'.getAppFn != f then
            visitMain e'
          else if pm f.mvarId! then
            return true
          else
            visitApp e
        else
          visitApp e
      | Expr.mvar mvarId     => do
        match (← getExprMVarAssignment? mvarId) with
        | some a => visit a
        | none   =>
          if pm mvarId then
            return true
          else
            let lctx := (← getMCtx).getDecl mvarId |>.lctx
            return lctx.any fun decl => pf decl.fvarId
      | Expr.fvar fvarId     => return pf fvarId
      | _                    => pure false
  visit e

@[inline] partial def main (pf : FVarId → Bool) (pm : MVarId → Bool) (e : Expr) : M Bool :=
  if !e.hasFVar && !e.hasMVar then pure false else dep pf pm e

end DependsOn

/--
  Return `true` iff `e` depends on a free variable `x` s.t. `pf x` is `true`, or an unassigned metavariable `?m` s.t. `pm ?m` is true.
  For each metavariable `?m` (that does not satisfy `pm` occurring in `x`
  1- If `?m := t`, then we visit `t` looking for `x`
  2- If `?m` is unassigned, then we consider the worst case and check whether `x` is in the local context of `?m`.
     This case is a "may dependency". That is, we may assign a term `t` to `?m` s.t. `t` contains `x`. -/
@[inline] def findExprDependsOn [Monad m] [MonadMCtx m] (e : Expr) (pf : FVarId → Bool := fun _ => false) (pm : MVarId → Bool := fun _ => false) : m Bool := do
  let (result, { mctx, .. }) := DependsOn.main pf pm e |>.run { mctx := (← getMCtx) }
  setMCtx mctx
  return result

/--
  Similar to `findExprDependsOn`, but checks the expressions in the given local declaration
  depends on a free variable `x` s.t. `pf x` is `true` or an unassigned metavariable `?m` s.t. `pm ?m` is true. -/
@[inline] def findLocalDeclDependsOn [Monad m] [MonadMCtx m] (localDecl : LocalDecl) (pf : FVarId → Bool := fun _ => false) (pm : MVarId → Bool := fun _ => false) : m Bool := do
  match localDecl with
  | LocalDecl.cdecl (type := t) ..  => findExprDependsOn t pf pm
  | LocalDecl.ldecl (type := t) (value := v) .. =>
    let (result, { mctx, .. }) := (DependsOn.main pf pm t <||> DependsOn.main pf pm v).run { mctx := (← getMCtx) }
    setMCtx mctx
    return result

def exprDependsOn [Monad m] [MonadMCtx m] (e : Expr) (fvarId : FVarId) : m Bool :=
  findExprDependsOn e (fvarId == ·)

/-- Return true iff `e` depends on the free variable `fvarId` -/
def dependsOn [Monad m] [MonadMCtx m] (e : Expr) (fvarId : FVarId) : m Bool :=
  exprDependsOn e fvarId

/-- Return true iff `e` depends on the free variable `fvarId` -/
def localDeclDependsOn [Monad m] [MonadMCtx m] (localDecl : LocalDecl) (fvarId : FVarId) : m Bool :=
  findLocalDeclDependsOn localDecl (fvarId == ·)

/-- Similar to `exprDependsOn`, but `x` can be a free variable or an unassigned metavariable. -/
def exprDependsOn' [Monad m] [MonadMCtx m] (e : Expr) (x : Expr) : m Bool :=
  if x.isFVar then
    findExprDependsOn e (x.fvarId! == ·)
  else if x.isMVar then
    findExprDependsOn e (pm := (x.mvarId! == ·))
  else
    return false

/-- Similar to `localDeclDependsOn`, but `x` can be a free variable or an unassigned metavariable. -/
def localDeclDependsOn' [Monad m] [MonadMCtx m] (localDecl : LocalDecl) (x : Expr) : m Bool :=
  if x.isFVar then
    findLocalDeclDependsOn localDecl (x.fvarId! == ·)
  else if x.isMVar then
    findLocalDeclDependsOn localDecl (pm := (x.mvarId! == ·))
  else
    return false

/-- Return true iff `e` depends on a free variable `x` s.t. `pf x`, or an unassigned metavariable `?m` s.t. `pm ?m` is true. -/
def dependsOnPred [Monad m] [MonadMCtx m] (e : Expr) (pf : FVarId → Bool := fun _ => false) (pm : MVarId → Bool := fun _ => false) : m Bool :=
  findExprDependsOn e pf pm

/-- Return true iff the local declaration `localDecl` depends on a free variable `x` s.t. `pf x`, an unassigned metavariable `?m` s.t. `pm ?m` is true. -/
def localDeclDependsOnPred [Monad m] [MonadMCtx m] (localDecl : LocalDecl) (pf : FVarId → Bool := fun _ => false) (pm : MVarId → Bool := fun _ => false) : m Bool := do
  findLocalDeclDependsOn localDecl pf pm


namespace MetavarContext

instance : Inhabited MetavarContext := ⟨{}⟩

@[export lean_mk_metavar_ctx]
def mkMetavarContext : Unit → MetavarContext := fun _ => {}

/- Low level API for adding/declaring metavariable declarations.
   It is used to implement actions in the monads `MetaM`, `ElabM` and `TacticM`.
   It should not be used directly since the argument `(mvarId : MVarId)` is assumed to be "unique". -/
def addExprMVarDecl (mctx : MetavarContext)
    (mvarId : MVarId)
    (userName : Name)
    (lctx : LocalContext)
    (localInstances : LocalInstances)
    (type : Expr)
    (kind : MetavarKind := MetavarKind.natural)
    (numScopeArgs : Nat := 0) : MetavarContext :=
  { mctx with
    mvarCounter := mctx.mvarCounter + 1
    decls       := mctx.decls.insert mvarId {
      depth := mctx.depth
      index := mctx.mvarCounter
      userName
      lctx
      localInstances
      type
      kind
      numScopeArgs }
    userNames := if userName.isAnonymous then mctx.userNames else mctx.userNames.insert userName mvarId }

def addExprMVarDeclExp (mctx : MetavarContext) (mvarId : MVarId) (userName : Name) (lctx : LocalContext) (localInstances : LocalInstances)
    (type : Expr) (kind : MetavarKind) : MetavarContext :=
    addExprMVarDecl mctx mvarId userName lctx localInstances type kind

/- Low level API for adding/declaring universe level metavariable declarations.
   It is used to implement actions in the monads `MetaM`, `ElabM` and `TacticM`.
   It should not be used directly since the argument `(mvarId : MVarId)` is assumed to be "unique". -/
def addLevelMVarDecl (mctx : MetavarContext) (mvarId : MVarId) : MetavarContext :=
  { mctx with lDepth := mctx.lDepth.insert mvarId mctx.depth }

def findDecl? (mctx : MetavarContext) (mvarId : MVarId) : Option MetavarDecl :=
  mctx.decls.find? mvarId

def findUserName? (mctx : MetavarContext) (userName : Name) : Option MVarId :=
  mctx.userNames.find? userName

def setMVarKind (mctx : MetavarContext) (mvarId : MVarId) (kind : MetavarKind) : MetavarContext :=
  let decl := mctx.getDecl mvarId
  { mctx with decls := mctx.decls.insert mvarId { decl with kind := kind } }

/--
  Set the metavariable user facing name.
-/
def setMVarUserName (mctx : MetavarContext) (mvarId : MVarId) (userName : Name) : MetavarContext :=
  let decl := mctx.getDecl mvarId
  { mctx with
    decls := mctx.decls.insert mvarId { decl with userName := userName }
    userNames :=
      let userNames := mctx.userNames.erase decl.userName
      if userName.isAnonymous then userNames else userNames.insert userName mvarId }

/--
  Low-level version of `setMVarUserName`.
  It does not update the table `userNames`. Thus, `findUserName?` cannot see the modification.
  It is meant for `mkForallFVars'` where we temporarily set the user facing name of metavariables to get more
  meaningful binder names.
-/
def setMVarUserNameTemporarily (mctx : MetavarContext) (mvarId : MVarId) (userName : Name) : MetavarContext :=
  let decl := mctx.getDecl mvarId
  { mctx with decls := mctx.decls.insert mvarId { decl with userName := userName } }

/- Update the type of the given metavariable. This function assumes the new type is
   definitionally equal to the current one -/
def setMVarType (mctx : MetavarContext) (mvarId : MVarId) (type : Expr) : MetavarContext :=
  let decl := mctx.getDecl mvarId
  { mctx with decls := mctx.decls.insert mvarId { decl with type := type } }

def findLevelDepth? (mctx : MetavarContext) (mvarId : MVarId) : Option Nat :=
  mctx.lDepth.find? mvarId

def getLevelDepth (mctx : MetavarContext) (mvarId : MVarId) : Nat :=
  match mctx.findLevelDepth? mvarId with
  | some d => d
  | none   => panic! "unknown metavariable"

def isAnonymousMVar (mctx : MetavarContext) (mvarId : MVarId) : Bool :=
  match mctx.findDecl? mvarId with
  | none          => false
  | some mvarDecl => mvarDecl.userName.isAnonymous

def incDepth (mctx : MetavarContext) : MetavarContext :=
  { mctx with depth := mctx.depth + 1 }

instance : MonadMCtx (StateRefT MetavarContext (ST ω)) where
  getMCtx    := get
  modifyMCtx := modify

namespace MkBinding

inductive Exception where
  | revertFailure (mctx : MetavarContext) (lctx : LocalContext) (toRevert : Array Expr) (varName : String)

instance : ToString Exception where
  toString
    | Exception.revertFailure _ lctx toRevert varName =>
      "failed to revert "
      ++ toString (toRevert.map (fun x => "'" ++ toString (lctx.getFVar! x).userName ++ "'"))
      ++ ", '" ++ toString varName ++ "' depends on them, and it is an auxiliary declaration created by the elaborator"
      ++ " (possible solution: use tactic 'clear' to remove '" ++ toString varName ++ "' from local context)"

/--
 `MkBinding` and `elimMVarDepsAux` are mutually recursive, but `cache` is only used at `elimMVarDepsAux`.
  We use a single state object for convenience.

  We have a `NameGenerator` because we need to generate fresh auxiliary metavariables. -/
structure State where
  mctx           : MetavarContext
  nextMacroScope : MacroScope
  ngen           : NameGenerator
  cache          : HashMap ExprStructEq Expr := {}

structure Context where
  mainModule         : Name
  preserveOrder      : Bool
  /-- When creating binders for abstracted metavariables, we use the following `BinderInfo`. -/
  binderInfoForMVars : BinderInfo := BinderInfo.implicit
  /-- Set of unassigned metavariables being abstracted. -/
  mvarIdsToAbstract  : MVarIdSet := {}

abbrev MCore := EStateM Exception State
abbrev M     := ReaderT Context MCore

instance : MonadMCtx M where
  getMCtx := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

private def mkFreshBinderName (n : Name := `x) : M Name := do
  let fresh ← modifyGet fun s => (s.nextMacroScope, { s with nextMacroScope := s.nextMacroScope + 1 })
  return addMacroScope (← read).mainModule n fresh

def preserveOrder : M Bool :=
  return (← read).preserveOrder

instance : MonadHashMapCacheAdapter ExprStructEq Expr M where
  getCache    := do let s ← get; pure s.cache
  modifyCache := fun f => modify fun s => { s with cache := f s.cache }

/-- Return the local declaration of the free variable `x` in `xs` with the smallest index -/
private def getLocalDeclWithSmallestIdx (lctx : LocalContext) (xs : Array Expr) : LocalDecl := Id.run do
  let mut d : LocalDecl := lctx.getFVar! xs[0]!
  for x in xs[1:] do
    if x.isFVar then
      let curr := lctx.getFVar! x
      if curr.index < d.index then
        d := curr
  return d

/--
  Given `toRevert` an array of free variables s.t. `lctx` contains their declarations,
  return a new array of free variables that contains `toRevert` and all free variables
  in `lctx` that may depend on `toRevert`.

  Remark: the result is sorted by `LocalDecl` indices.

  Remark: We used to throw an `Exception.revertFailure` exception when an auxiliary declaration
  had to be reversed. Recall that auxiliary declarations are created when compiling (mutually)
  recursive definitions. The `revertFailure` due to auxiliary declaration dependency was originally
  introduced in Lean3 to address issue https://github.com/leanprover/lean/issues/1258.
  In Lean4, this solution is not satisfactory because all definitions/theorems are potentially
  recursive. So, even an simple (incomplete) definition such as
  ```
  variables {α : Type} in
  def f (a : α) : List α :=
  _
  ```
  would trigger the `Exception.revertFailure` exception. In the definition above,
  the elaborator creates the auxiliary definition `f : {α : Type} → List α`.
  The `_` is elaborated as a new fresh variable `?m` that contains `α : Type`, `a : α`, and `f : α → List α` in its context,
  When we try to create the lambda `fun {α : Type} (a : α) => ?m`, we first need to create
  an auxiliary `?n` which do not contain `α` and `a` in its context. That is,
  we create the metavariable `?n : {α : Type} → (a : α) → (f : α → List α) → List α`,
  add the delayed assignment `?n #[α, a, f] := ?m α a f`, and create the lambda
  `fun {α : Type} (a : α) => ?n α a f`.
  See `elimMVarDeps` for more information.
  If we kept using the Lean3 approach, we would get the `Exception.revertFailure` exception because we are
  reverting the auxiliary definition `f`.

  Note that https://github.com/leanprover/lean/issues/1258 is not an issue in Lean4 because
  we have changed how we compile recursive definitions.
-/
def collectForwardDeps (lctx : LocalContext) (toRevert : Array Expr) : M (Array Expr) := do
  if toRevert.size == 0 then
    pure toRevert
  else
    if (← preserveOrder) then
      -- Make sure toRevert[j] does not depend on toRevert[i] for j > i
      toRevert.size.forM fun i => do
        let fvar := toRevert[i]!
        i.forM fun j => do
          let prevFVar := toRevert[j]!
          let prevDecl := lctx.getFVar! prevFVar
          if (← localDeclDependsOn prevDecl fvar.fvarId!) then
            throw (Exception.revertFailure (← getMCtx) lctx toRevert prevDecl.userName.toString)
    let newToRevert      := if (← preserveOrder) then toRevert else Array.mkEmpty toRevert.size
    let firstDeclToVisit := getLocalDeclWithSmallestIdx lctx toRevert
    let initSize         := newToRevert.size
    lctx.foldlM (init := newToRevert) (start := firstDeclToVisit.index) fun (newToRevert : Array Expr) decl => do
      if initSize.any fun i => decl.fvarId == newToRevert[i]!.fvarId! then
        return newToRevert
      else if toRevert.any fun x => decl.fvarId == x.fvarId! then
        return newToRevert.push decl.toExpr
      else if (← findLocalDeclDependsOn decl (newToRevert.any fun x => x.fvarId! == ·)) then
        return newToRevert.push decl.toExpr
      else
        return newToRevert

/-- Create a new `LocalContext` by removing the free variables in `toRevert` from `lctx`.
    We use this function when we create auxiliary metavariables at `elimMVarDepsAux`. -/
def reduceLocalContext (lctx : LocalContext) (toRevert : Array Expr) : LocalContext :=
  toRevert.foldr (init := lctx) fun x lctx =>
    if x.isFVar then lctx.erase x.fvarId! else lctx

/-- Return free variables in `xs` that are in the local context `lctx` -/
private def getInScope (lctx : LocalContext) (xs : Array Expr) : Array Expr :=
  xs.foldl (init := #[]) fun scope x =>
    if !x.isFVar then
      scope
    else if lctx.contains x.fvarId! then
      scope.push x
    else
      scope

/-- Execute `x` with an empty cache, and then restore the original cache. -/
@[inline] private def withFreshCache (x : M α) : M α := do
  let cache ← modifyGet fun s => (s.cache, { s with cache := {} })
  let a ← x
  modify fun s => { s with cache := cache }
  pure a

/--
  Create an application `mvar ys` where `ys` are the free variables.
  See "Gruesome details" in the beginning of the file for understanding
  how let-decl free variables are handled. -/
private def mkMVarApp (lctx : LocalContext) (mvar : Expr) (xs : Array Expr) (kind : MetavarKind) : Expr :=
  xs.foldl (init := mvar) fun e x =>
    if !x.isFVar then
      e
    else
      match kind with
      | MetavarKind.syntheticOpaque => mkApp e x
      | _                           => if (lctx.getFVar! x).isLet then e else mkApp e x

mutual

  private partial def visit (xs : Array Expr) (e : Expr) : M Expr :=
    if !e.hasMVar then pure e else checkCache { val := e : ExprStructEq } fun _ => elim xs e

  private partial def elim (xs : Array Expr) (e : Expr) : M Expr :=
    match e with
    | Expr.proj _ _ s      => return e.updateProj! (← visit xs s)
    | Expr.forallE _ d b _ => return e.updateForallE! (← visit xs d) (← visit xs b)
    | Expr.lam _ d b _     => return e.updateLambdaE! (← visit xs d) (← visit xs b)
    | Expr.letE _ t v b _  => return e.updateLet! (← visit xs t) (← visit xs v) (← visit xs b)
    | Expr.mdata _ b       => return e.updateMData! (← visit xs b)
    | Expr.app ..          => e.withApp fun f args => elimApp xs f args
    | Expr.mvar _          => elimApp xs e #[]
    | e                    => return e

  private partial def mkAuxMVarType (lctx : LocalContext)  (xs : Array Expr) (kind : MetavarKind) (e : Expr) : M Expr := do
    let e ← abstractRangeAux xs xs.size e
    xs.size.foldRevM (init := e) fun i e => do
      let x := xs[i]!
      if x.isFVar then
        match lctx.getFVar! x with
        | LocalDecl.cdecl _ _ n type bi =>
          let type := type.headBeta
          let type ← abstractRangeAux xs i type
          return Lean.mkForall n bi type e
        | LocalDecl.ldecl _ _ n type value nonDep =>
          let type := type.headBeta
          let type  ← abstractRangeAux xs i type
          let value ← abstractRangeAux xs i value
          let e := mkLet n type value e nonDep
          match kind with
          | MetavarKind.syntheticOpaque =>
            -- See "Gruesome details" section in the beginning of the file
            let e := e.liftLooseBVars 0 1
            return mkForall n BinderInfo.default type e
          | _ => pure e
      else
        let mvarDecl := (← get).mctx.getDecl x.mvarId!
        let type := mvarDecl.type.headBeta
        let type ← abstractRangeAux xs i type
        let id ← if mvarDecl.userName.isAnonymous then mkFreshBinderName else pure mvarDecl.userName
        return Lean.mkForall id (← read).binderInfoForMVars type e
  where
    abstractRangeAux (xs : Array Expr) (i : Nat) (e : Expr) : M Expr := do
      let e ← elim xs e
      pure (e.abstractRange i xs)

  private partial def elimMVar (xs : Array Expr) (mvarId : MVarId) (args : Array Expr) : M (Expr × Array Expr) := do
    let mvarDecl  := (← getMCtx).getDecl mvarId
    let mvarLCtx  := mvarDecl.lctx
    let toRevert  := getInScope mvarLCtx xs
    if toRevert.size == 0 then
      let args ← args.mapM (visit xs)
      return (mkAppN (mkMVar mvarId) args, #[])
    else
      /- `newMVarKind` is the kind for the new auxiliary metavariable.
          There is an alternative approach where we use
          ```
          let newMVarKind := if !mctx.isExprAssignable mvarId || mvarDecl.isSyntheticOpaque then MetavarKind.syntheticOpaque else MetavarKind.natural
          ```
          In this approach, we use the natural kind for the new auxiliary metavariable if the original metavariable is synthetic and assignable.
          Since we mainly use synthetic metavariables for pending type class (TC) resolution problems,
          this approach may minimize the number of TC resolution problems that may need to be resolved.
          A potential disadvantage is that `isDefEq` will not eagerly use `synthPending` for natural metavariables.
          That being said, we should try this approach as soon as we have an extensive test suite.
      -/
      let newMVarKind := if !(← isExprMVarAssignable mvarId) then MetavarKind.syntheticOpaque else mvarDecl.kind
      let args ← args.mapM (visit xs)
      let toRevert ← collectForwardDeps mvarLCtx toRevert
      let newMVarLCtx   := reduceLocalContext mvarLCtx toRevert
      -- Note that `toRevert` only contains free variables since it is the result of `getInScope`
      let newLocalInsts := mvarDecl.localInstances.filter fun inst => toRevert.all fun x => inst.fvar != x
      -- Remark: we must reset the before processing `mkAuxMVarType` because `toRevert` may not be equal to `xs`
      let newMVarType ← withFreshCache do mkAuxMVarType mvarLCtx toRevert newMVarKind mvarDecl.type
      let newMVarId    := { name := (← get).ngen.curr }
      let newMVar      := mkMVar newMVarId
      let result       := mkMVarApp mvarLCtx newMVar toRevert newMVarKind
      let numScopeArgs := mvarDecl.numScopeArgs + result.getAppNumArgs
      modify fun s => { s with
          mctx := s.mctx.addExprMVarDecl newMVarId Name.anonymous newMVarLCtx newLocalInsts newMVarType newMVarKind numScopeArgs,
          ngen := s.ngen.next
        }
      if !mvarDecl.kind.isSyntheticOpaque then
        assignExprMVar mvarId result
      else
        /- If `mvarId` is the lhs of a delayed assignment `?m #[x_1, ... x_n] := ?mvarPending`,
           then `nestedFVars` is `#[x_1, ..., x_n]`.
           In this case, `newMVarId` is also `syntheticOpaque` and we add the delayed assignment delayed assignment
           ```
           ?newMVar #[y_1, ..., y_m, x_1, ... x_n] := ?m
           ```
           where `#[y_1, ..., y_m]` is `toRevert` after `collectForwardDeps`.
        -/
        let (mvarIdPending, nestedFVars) ← match (← getDelayedMVarAssignment? mvarId) with
          | none => pure (mvarId, #[])
          | some { fvars, mvarIdPending } => pure (mvarIdPending, fvars)
        assignDelayedMVar newMVarId (toRevert ++ nestedFVars) mvarIdPending
      return (mkAppN result args, toRevert)

  private partial def elimApp (xs : Array Expr) (f : Expr) (args : Array Expr) : M Expr := do
    match f with
    | Expr.mvar mvarId =>
      match (← getExprMVarAssignment? mvarId) with
      | some newF =>
        if newF.isLambda then
          let args ← args.mapM (visit xs)
          elim xs <| newF.betaRev args.reverse
        else
          elimApp xs newF args
      | none =>
        if (← read).mvarIdsToAbstract.contains mvarId then
          return mkAppN f (← args.mapM (visit xs))
        else
          return (← elimMVar xs mvarId args).1
    | _ =>
      return mkAppN (← visit xs f) (← args.mapM (visit xs))

end

partial def elimMVarDeps (xs : Array Expr) (e : Expr) : M Expr :=
  if !e.hasMVar then
    return e
  else
    withFreshCache do
      elim xs e

partial def revert (xs : Array Expr) (mvarId : MVarId) : M (Expr × Array Expr) :=
  withFreshCache do
    elimMVar xs mvarId #[]

/--
  Similar to `Expr.abstractRange`, but handles metavariables correctly.
  It uses `elimMVarDeps` to ensure `e` and the type of the free variables `xs` do not
  contain a metavariable `?m` s.t. local context of `?m` contains a free variable in `xs`.

  `elimMVarDeps` is defined later in this file. -/
@[inline] def abstractRange (xs : Array Expr) (i : Nat) (e : Expr) : M Expr := do
  let e ← elimMVarDeps xs e
  pure (e.abstractRange i xs)

/--
  Similar to `LocalContext.mkBinding`, but handles metavariables correctly.
  If `usedOnly == false` then `forall` and `lambda` expressions are created only for used variables.
  If `usedLetOnly == false` then `let` expressions are created only for used (let-) variables. -/
@[specialize] def mkBinding (isLambda : Bool) (lctx : LocalContext) (xs : Array Expr) (e : Expr) (usedOnly : Bool) (usedLetOnly : Bool) : M (Expr × Nat) := do
  let e ← abstractRange xs xs.size e
  xs.size.foldRevM (init := (e, 0)) fun i (e, num) => do
      let x := xs[i]!
      if x.isFVar then
        match lctx.getFVar! x with
        | LocalDecl.cdecl _ _ n type bi =>
          if !usedOnly || e.hasLooseBVar 0 then
            let type := type.headBeta;
            let type ← abstractRange xs i type
            if isLambda then
              return (Lean.mkLambda n bi type e, num + 1)
            else
              return (Lean.mkForall n bi type e, num + 1)
          else
            return (e.lowerLooseBVars 1 1, num)
        | LocalDecl.ldecl _ _ n type value nonDep =>
          if !usedLetOnly || e.hasLooseBVar 0 then
            let type  ← abstractRange xs i type
            let value ← abstractRange xs i value
            return (mkLet n type value e nonDep, num + 1)
          else
            return (e.lowerLooseBVars 1 1, num)
      else
        let mvarDecl := (← get).mctx.getDecl x.mvarId!
        let type := mvarDecl.type.headBeta
        let type ← abstractRange xs i type
        let id ← if mvarDecl.userName.isAnonymous then mkFreshBinderName else pure mvarDecl.userName
        if isLambda then
          return (Lean.mkLambda id (← read).binderInfoForMVars type e, num + 1)
        else
          return (Lean.mkForall id (← read).binderInfoForMVars type e, num + 1)

end MkBinding

structure MkBindingM.Context where
  mainModule : Name
  lctx       : LocalContext

abbrev MkBindingM := ReaderT MkBindingM.Context MkBinding.MCore

def elimMVarDeps (xs : Array Expr) (e : Expr) (preserveOrder : Bool) : MkBindingM Expr := fun ctx =>
  MkBinding.elimMVarDeps xs e { preserveOrder, mainModule := ctx.mainModule }

def revert (xs : Array Expr) (mvarId : MVarId) (preserveOrder : Bool) : MkBindingM (Expr × Array Expr) := fun ctx =>
  MkBinding.revert xs mvarId { preserveOrder, mainModule := ctx.mainModule }

def mkBinding (isLambda : Bool) (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) (binderInfoForMVars := BinderInfo.implicit) : MkBindingM (Expr × Nat) := fun ctx =>
  let mvarIdsToAbstract := xs.foldl (init := {}) fun s x => if x.isMVar then s.insert x.mvarId! else s
  MkBinding.mkBinding isLambda ctx.lctx xs e usedOnly usedLetOnly { preserveOrder := false, binderInfoForMVars, mvarIdsToAbstract, mainModule := ctx.mainModule }

@[inline] def mkLambda (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) (binderInfoForMVars := BinderInfo.implicit) : MkBindingM Expr :=
  return (← mkBinding (isLambda := true) xs e usedOnly usedLetOnly binderInfoForMVars).1

@[inline] def mkForall (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) (binderInfoForMVars := BinderInfo.implicit) : MkBindingM Expr :=
  return (← mkBinding (isLambda := false) xs e usedOnly usedLetOnly binderInfoForMVars).1

@[inline] def abstractRange (e : Expr) (n : Nat) (xs : Array Expr) : MkBindingM Expr := fun ctx =>
  MkBinding.abstractRange xs n e { preserveOrder := false, mainModule := ctx.mainModule }

@[inline] def collectForwardDeps (toRevert : Array Expr) (preserveOrder : Bool) : MkBindingM (Array Expr) := fun ctx =>
  MkBinding.collectForwardDeps ctx.lctx toRevert { preserveOrder, mainModule := ctx.mainModule }

/--
  `isWellFormed mctx lctx e` return true if
  - All locals in `e` are declared in `lctx`
  - All metavariables `?m` in `e` have a local context which is a subprefix of `lctx` or are assigned, and the assignment is well-formed. -/
partial def isWellFormed [Monad m] [MonadMCtx m] (lctx : LocalContext) : Expr → m Bool
  | Expr.mdata _ e           => isWellFormed lctx e
  | Expr.proj _ _ e          => isWellFormed lctx e
  | e@(Expr.app f a)         => pure (!e.hasExprMVar && !e.hasFVar) <||> (isWellFormed lctx f <&&> isWellFormed lctx a)
  | e@(Expr.lam _ d b _)     => pure (!e.hasExprMVar && !e.hasFVar) <||> (isWellFormed lctx d <&&> isWellFormed lctx b)
  | e@(Expr.forallE _ d b _) => pure (!e.hasExprMVar && !e.hasFVar) <||> (isWellFormed lctx d <&&> isWellFormed lctx b)
  | e@(Expr.letE _ t v b _)  => pure (!e.hasExprMVar && !e.hasFVar) <||> (isWellFormed lctx t <&&> isWellFormed lctx v <&&> isWellFormed lctx b)
  | Expr.const ..            => return true
  | Expr.bvar ..             => return true
  | Expr.sort ..             => return true
  | Expr.lit ..              => return true
  | Expr.mvar mvarId         => do
    let mvarDecl := (← getMCtx).getDecl mvarId;
    if mvarDecl.lctx.isSubPrefixOf lctx then
      return true
    else match (← getExprMVarAssignment? mvarId) with
      | none   => return false
      | some v => isWellFormed lctx v
  | Expr.fvar fvarId         => return lctx.contains fvarId

namespace LevelMVarToParam

structure Context where
  paramNamePrefix : Name
  alreadyUsedPred : Name → Bool
  except          : MVarId → Bool

structure State where
  mctx         : MetavarContext
  paramNames   : Array Name := #[]
  nextParamIdx : Nat
  cache        : HashMap ExprStructEq Expr := {}

abbrev M := ReaderT Context <| StateM State

instance : MonadMCtx M where
  getMCtx      := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

instance : MonadCache ExprStructEq Expr M where
  findCached? e   := return (← get).cache.find? e
  cache       e v := modify fun s => { s with cache := s.cache.insert e v }

partial def mkParamName : M Name := do
  let ctx ← read
  let s ← get
  let newParamName := ctx.paramNamePrefix.appendIndexAfter s.nextParamIdx
  if ctx.alreadyUsedPred newParamName then
    modify fun s => { s with nextParamIdx := s.nextParamIdx + 1 }
    mkParamName
  else do
    modify fun s => { s with nextParamIdx := s.nextParamIdx + 1, paramNames := s.paramNames.push newParamName }
    pure newParamName

partial def visitLevel (u : Level) : M Level := do
  match u with
  | Level.succ v      => return u.updateSucc! (← visitLevel v)
  | Level.max v₁ v₂   => return u.updateMax! (← visitLevel v₁) (← visitLevel v₂)
  | Level.imax v₁ v₂  => return u.updateIMax! (← visitLevel v₁) (← visitLevel v₂)
  | Level.zero        => return u
  | Level.param ..      => return u
  | Level.mvar mvarId =>
    match (← getLevelMVarAssignment? mvarId) with
    | some v => visitLevel v
    | none   =>
      if (← read).except mvarId then
        return u
      else
        let p ← mkParamName
        let p := mkLevelParam p
        assignLevelMVar mvarId p
        return p

partial def main (e : Expr) : M Expr :=
  if !e.hasMVar then
    return e
  else
    checkCache { val := e : ExprStructEq } fun _ => do
      match e with
      | Expr.proj _ _ s      => return e.updateProj! (← main s)
      | Expr.forallE _ d b _ => return e.updateForallE! (← main d) (← main b)
      | Expr.lam _ d b _     => return e.updateLambdaE! (← main d) (← main b)
      | Expr.letE _ t v b _  => return e.updateLet! (← main t) (← main v) (← main b)
      | Expr.app ..          => e.withApp fun f args => visitApp f args
      | Expr.mdata _ b       => return e.updateMData! (← main b)
      | Expr.const _ us      => return e.updateConst! (← us.mapM visitLevel)
      | Expr.sort u          => return e.updateSort! (← visitLevel u)
      | Expr.mvar ..         => visitApp e #[]
      | e                    => return e
where
  visitApp (f : Expr) (args : Array Expr) : M Expr := do
    match f with
    | Expr.mvar mvarId .. =>
      match (← getExprMVarAssignment? mvarId) with
      | some v => return (← visitApp v args).headBeta
      | none   => return mkAppN f (← args.mapM main)
    | _ => return mkAppN (← main f) (← args.mapM main)

end LevelMVarToParam

structure UnivMVarParamResult where
  mctx          : MetavarContext
  newParamNames : Array Name
  nextParamIdx  : Nat
  expr          : Expr

def levelMVarToParam (mctx : MetavarContext) (alreadyUsedPred : Name → Bool) (except : MVarId → Bool) (e : Expr) (paramNamePrefix : Name := `u) (nextParamIdx : Nat := 1)
    : UnivMVarParamResult :=
  let (e, s) := LevelMVarToParam.main e { except, paramNamePrefix, alreadyUsedPred } { mctx, nextParamIdx }
  { mctx          := s.mctx
    newParamNames := s.paramNames
    nextParamIdx  := s.nextParamIdx
    expr          := e }

def getExprAssignmentDomain (mctx : MetavarContext) : Array MVarId :=
  mctx.eAssignment.foldl (init := #[]) fun a mvarId _ => Array.push a mvarId

end MetavarContext

end Lean
