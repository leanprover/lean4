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
  A delayed assignment for a metavariable `?m`. It represents an assignment of the form
  `?m := (fun fvars => val)`. The local context `lctx` provides the declarations for `fvars`.
  Note that `fvars` may not be defined in the local context for `?m`.

  - TODO: after we delete the old frontend, we can remove the field `lctx`.
    This field is only used in old C++ implementation. -/
structure DelayedMetavarAssignment where
  lctx     : LocalContext
  fvars    : Array Expr
  val      : Expr

open Std (HashMap PersistentHashMap)

structure MetavarContext where
  depth       : Nat := 0
  mvarCounter : Nat := 0 -- Counter for setting the field `index` at `MetavarDecl`
  lDepth      : PersistentHashMap MVarId Nat := {}
  decls       : PersistentHashMap MVarId MetavarDecl := {}
  lAssignment : PersistentHashMap MVarId Level := {}
  eAssignment : PersistentHashMap MVarId Expr := {}
  dAssignment : PersistentHashMap MVarId DelayedMetavarAssignment := {}

class MonadMCtx (m : Type → Type) where
  getMCtx    : m MetavarContext
  modifyMCtx : (MetavarContext → MetavarContext) → m Unit

export MonadMCtx (getMCtx modifyMCtx)

instance (m n) [MonadLift m n] [MonadMCtx m] : MonadMCtx n where
  getMCtx    := liftM (getMCtx : m _)
  modifyMCtx := fun f => liftM (modifyMCtx f : m _)

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
      numScopeArgs } }

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

def getDecl (mctx : MetavarContext) (mvarId : MVarId) : MetavarDecl :=
  match mctx.decls.find? mvarId with
  | some decl => decl
  | none      => panic! "unknown metavariable"

def findUserName? (mctx : MetavarContext) (userName : Name) : Option MVarId :=
  let search : Except MVarId Unit := mctx.decls.forM fun mvarId decl =>
    if decl.userName == userName then throw mvarId else pure ()
  match search with
  | Except.ok _         => none
  | Except.error mvarId => some mvarId

def setMVarKind (mctx : MetavarContext) (mvarId : MVarId) (kind : MetavarKind) : MetavarContext :=
  let decl := mctx.getDecl mvarId
  { mctx with decls := mctx.decls.insert mvarId { decl with kind := kind } }

def setMVarUserName (mctx : MetavarContext) (mvarId : MVarId) (userName : Name) : MetavarContext :=
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

def renameMVar (mctx : MetavarContext) (mvarId : MVarId) (newUserName : Name) : MetavarContext :=
  match mctx.findDecl? mvarId with
  | none          => panic! "unknown metavariable"
  | some mvarDecl => { mctx with decls := mctx.decls.insert mvarId { mvarDecl with userName := newUserName } }

def assignLevel (m : MetavarContext) (mvarId : MVarId) (val : Level) : MetavarContext :=
  { m with lAssignment := m.lAssignment.insert mvarId val }

def assignExpr (m : MetavarContext) (mvarId : MVarId) (val : Expr) : MetavarContext :=
  { m with eAssignment := m.eAssignment.insert mvarId val }

def assignDelayed (m : MetavarContext) (mvarId : MVarId) (lctx : LocalContext) (fvars : Array Expr) (val : Expr) : MetavarContext :=
  { m with dAssignment := m.dAssignment.insert mvarId { lctx := lctx, fvars := fvars, val := val } }

def getLevelAssignment? (m : MetavarContext) (mvarId : MVarId) : Option Level :=
  m.lAssignment.find? mvarId

def getExprAssignment? (m : MetavarContext) (mvarId : MVarId) : Option Expr :=
  m.eAssignment.find? mvarId

def getDelayedAssignment? (m : MetavarContext) (mvarId : MVarId) : Option DelayedMetavarAssignment :=
  m.dAssignment.find? mvarId

def isLevelAssigned (m : MetavarContext) (mvarId : MVarId) : Bool :=
  m.lAssignment.contains mvarId

def isExprAssigned (m : MetavarContext) (mvarId : MVarId) : Bool :=
  m.eAssignment.contains mvarId

def isDelayedAssigned (m : MetavarContext) (mvarId : MVarId) : Bool :=
  m.dAssignment.contains mvarId

def eraseDelayed (m : MetavarContext) (mvarId : MVarId) : MetavarContext :=
  { m with dAssignment := m.dAssignment.erase mvarId }

/- Given a sequence of delayed assignments
   ```
   mvarId₁ := mvarId₂ ...;
   ...
   mvarIdₙ := mvarId_root ...  -- where `mvarId_root` is not delayed assigned
   ```
   in `mctx`, `getDelayedRoot mctx mvarId₁` return `mvarId_root`.
   If `mvarId₁` is not delayed assigned then return `mvarId₁` -/
partial def getDelayedRoot (m : MetavarContext) : MVarId → MVarId
  | mvarId => match getDelayedAssignment? m mvarId with
    | some d => match d.val.getAppFn with
      | Expr.mvar mvarId _ => getDelayedRoot m mvarId
      | _                  => mvarId
    | none   => mvarId

def isLevelAssignable (mctx : MetavarContext) (mvarId : MVarId) : Bool :=
  match mctx.lDepth.find? mvarId with
  | some d => d == mctx.depth
  | _      => panic! "unknown universe metavariable"

def isExprAssignable (mctx : MetavarContext) (mvarId : MVarId) : Bool :=
  let decl := mctx.getDecl mvarId
  decl.depth == mctx.depth

def incDepth (mctx : MetavarContext) : MetavarContext :=
  { mctx with depth := mctx.depth + 1 }

/-- Return true iff the given level contains an assigned metavariable. -/
def hasAssignedLevelMVar (mctx : MetavarContext) : Level → Bool
  | Level.succ lvl _       => lvl.hasMVar && hasAssignedLevelMVar mctx lvl
  | Level.max lvl₁ lvl₂ _  => (lvl₁.hasMVar && hasAssignedLevelMVar mctx lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar mctx lvl₂)
  | Level.imax lvl₁ lvl₂ _ => (lvl₁.hasMVar && hasAssignedLevelMVar mctx lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar mctx lvl₂)
  | Level.mvar mvarId _    => mctx.isLevelAssigned mvarId
  | Level.zero _           => false
  | Level.param _ _        => false

/-- Return `true` iff expression contains assigned (level/expr) metavariables or delayed assigned mvars -/
def hasAssignedMVar (mctx : MetavarContext) : Expr → Bool
  | Expr.const _ lvls _  => lvls.any (hasAssignedLevelMVar mctx)
  | Expr.sort lvl _      => hasAssignedLevelMVar mctx lvl
  | Expr.app f a _       => (f.hasMVar && hasAssignedMVar mctx f) || (a.hasMVar && hasAssignedMVar mctx a)
  | Expr.letE _ t v b _  => (t.hasMVar && hasAssignedMVar mctx t) || (v.hasMVar && hasAssignedMVar mctx v) || (b.hasMVar && hasAssignedMVar mctx b)
  | Expr.forallE _ d b _ => (d.hasMVar && hasAssignedMVar mctx d) || (b.hasMVar && hasAssignedMVar mctx b)
  | Expr.lam _ d b _     => (d.hasMVar && hasAssignedMVar mctx d) || (b.hasMVar && hasAssignedMVar mctx b)
  | Expr.fvar _ _        => false
  | Expr.bvar _ _        => false
  | Expr.lit _ _         => false
  | Expr.mdata _ e _     => e.hasMVar && hasAssignedMVar mctx e
  | Expr.proj _ _ e _    => e.hasMVar && hasAssignedMVar mctx e
  | Expr.mvar mvarId _   => mctx.isExprAssigned mvarId || mctx.isDelayedAssigned mvarId

/-- Return true iff the given level contains a metavariable that can be assigned. -/
def hasAssignableLevelMVar (mctx : MetavarContext) : Level → Bool
  | Level.succ lvl _       => lvl.hasMVar && hasAssignableLevelMVar mctx lvl
  | Level.max lvl₁ lvl₂ _  => (lvl₁.hasMVar && hasAssignableLevelMVar mctx lvl₁) || (lvl₂.hasMVar && hasAssignableLevelMVar mctx lvl₂)
  | Level.imax lvl₁ lvl₂ _ => (lvl₁.hasMVar && hasAssignableLevelMVar mctx lvl₁) || (lvl₂.hasMVar && hasAssignableLevelMVar mctx lvl₂)
  | Level.mvar mvarId _    => mctx.isLevelAssignable mvarId
  | Level.zero _           => false
  | Level.param _ _        => false

/-- Return `true` iff expression contains a metavariable that can be assigned. -/
def hasAssignableMVar (mctx : MetavarContext) : Expr → Bool
  | Expr.const _ lvls _  => lvls.any (hasAssignableLevelMVar mctx)
  | Expr.sort lvl _      => hasAssignableLevelMVar mctx lvl
  | Expr.app f a _       => (f.hasMVar && hasAssignableMVar mctx f) || (a.hasMVar && hasAssignableMVar mctx a)
  | Expr.letE _ t v b _  => (t.hasMVar && hasAssignableMVar mctx t) || (v.hasMVar && hasAssignableMVar mctx v) || (b.hasMVar && hasAssignableMVar mctx b)
  | Expr.forallE _ d b _ => (d.hasMVar && hasAssignableMVar mctx d) || (b.hasMVar && hasAssignableMVar mctx b)
  | Expr.lam _ d b _     => (d.hasMVar && hasAssignableMVar mctx d) || (b.hasMVar && hasAssignableMVar mctx b)
  | Expr.fvar _ _        => false
  | Expr.bvar _ _        => false
  | Expr.lit _ _         => false
  | Expr.mdata _ e _     => e.hasMVar && hasAssignableMVar mctx e
  | Expr.proj _ _ e _    => e.hasMVar && hasAssignableMVar mctx e
  | Expr.mvar mvarId _   => mctx.isExprAssignable mvarId

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
  | lvl@(Level.succ lvl₁ _)      => return Level.updateSucc! lvl (← instantiateLevelMVars lvl₁)
  | lvl@(Level.max lvl₁ lvl₂ _)  => return Level.updateMax! lvl (← instantiateLevelMVars lvl₁) (← instantiateLevelMVars lvl₂)
  | lvl@(Level.imax lvl₁ lvl₂ _) => return Level.updateIMax! lvl (← instantiateLevelMVars lvl₁) (← instantiateLevelMVars lvl₂)
  | lvl@(Level.mvar mvarId _)    => do
    match getLevelAssignment? (← getMCtx) mvarId with
    | some newLvl =>
      if !newLvl.hasMVar then pure newLvl
      else do
        let newLvl' ← instantiateLevelMVars newLvl
        modifyMCtx fun mctx => mctx.assignLevel mvarId newLvl'
        pure newLvl'
    | none        => pure lvl
  | lvl => pure lvl

/-- instantiateExprMVars main function -/
partial def instantiateExprMVars [Monad m] [MonadMCtx m] [STWorld ω m] [MonadLiftT (ST ω) m] (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
  if !e.hasMVar then
    pure e
  else checkCache { val := e : ExprStructEq } fun _ => do match e with
    | Expr.proj _ _ s _    => return e.updateProj! (← instantiateExprMVars s)
    | Expr.forallE _ d b _ => return e.updateForallE! (← instantiateExprMVars d) (← instantiateExprMVars b)
    | Expr.lam _ d b _     => return e.updateLambdaE! (← instantiateExprMVars d) (← instantiateExprMVars b)
    | Expr.letE _ t v b _  => return e.updateLet! (← instantiateExprMVars t) (← instantiateExprMVars v) (← instantiateExprMVars b)
    | Expr.const _ lvls _  => return e.updateConst! (← lvls.mapM instantiateLevelMVars)
    | Expr.sort lvl _      => return e.updateSort! (← instantiateLevelMVars lvl)
    | Expr.mdata _ b _     => return e.updateMData! (← instantiateExprMVars b)
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
      | Expr.mvar mvarId _ =>
        let mctx ← getMCtx
        match mctx.getDelayedAssignment? mvarId with
        | none => instApp
        | some { fvars := fvars, val := val, .. } =>
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
            let newVal ← instantiateExprMVars val
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
    | e@(Expr.mvar mvarId _)   => checkCache { val := e : ExprStructEq } fun _ => do
      let mctx ← getMCtx
      match mctx.getExprAssignment? mvarId with
      | some newE => do
        let newE' ← instantiateExprMVars newE
        modifyMCtx fun mctx => mctx.assignExpr mvarId newE'
        pure newE'
      | none => pure e
    | e => pure e

instance : MonadMCtx (StateRefT MetavarContext (ST ω)) where
  getMCtx    := get
  modifyMCtx := modify

def instantiateMVars (mctx : MetavarContext) (e : Expr) : Expr × MetavarContext :=
  if !e.hasMVar then
    (e, mctx)
  else
    let instantiate {ω} (e : Expr) : (MonadCacheT ExprStructEq Expr $ StateRefT MetavarContext $ ST ω) Expr :=
      instantiateExprMVars e
    runST fun _ => instantiate e |>.run |>.run mctx

def instantiateLCtxMVars (mctx : MetavarContext) (lctx : LocalContext) : LocalContext × MetavarContext :=
  lctx.foldl (init := ({}, mctx)) fun (lctx, mctx) ldecl =>
     match ldecl with
     | LocalDecl.cdecl _ fvarId userName type bi =>
       let (type, mctx) := mctx.instantiateMVars type
       (lctx.mkLocalDecl fvarId userName type bi, mctx)
     | LocalDecl.ldecl _ fvarId userName type value nonDep =>
       let (type, mctx)  := mctx.instantiateMVars type
       let (value, mctx) := mctx.instantiateMVars value
       (lctx.mkLetDecl fvarId userName type value nonDep, mctx)

def instantiateMVarDeclMVars (mctx : MetavarContext) (mvarId : MVarId) : MetavarContext :=
  let mvarDecl     := mctx.getDecl mvarId
  let (lctx, mctx) := mctx.instantiateLCtxMVars mvarDecl.lctx
  let (type, mctx) := mctx.instantiateMVars mvarDecl.type
  { mctx with decls := mctx.decls.insert mvarId { mvarDecl with lctx := lctx, type := type } }

namespace DependsOn

private abbrev M := StateM ExprSet

private def shouldVisit (e : Expr) : M Bool := do
  if !e.hasMVar && !e.hasFVar then
    return false
  else if (← get).contains e then
    return false
  else
    modify fun s => s.insert e
    return true

@[specialize] private partial def dep (mctx : MetavarContext) (p : FVarId → Bool) (e : Expr) : M Bool :=
  let rec
    visit (e : Expr) : M Bool := do
      if !(← shouldVisit e) then
        pure false
      else
        visitMain e,
    visitMain : Expr → M Bool
      | Expr.proj _ _ s _    => visit s
      | Expr.forallE _ d b _ => visit d <||> visit b
      | Expr.lam _ d b _     => visit d <||> visit b
      | Expr.letE _ t v b _  => visit t <||> visit v <||> visit b
      | Expr.mdata _ b _     => visit b
      | Expr.app f a _       => visit a <||> if f.isApp then visitMain f else visit f
      | Expr.mvar mvarId _   =>
        match mctx.getExprAssignment? mvarId with
        | some a => visit a
        | none   =>
          let lctx := (mctx.getDecl mvarId).lctx
          return lctx.any fun decl => p decl.fvarId
      | Expr.fvar fvarId _   => return p fvarId
      | e                    => pure false
  visit e

@[inline] partial def main (mctx : MetavarContext) (p : FVarId → Bool) (e : Expr) : M Bool :=
  if !e.hasFVar && !e.hasMVar then pure false else dep mctx p e

end DependsOn

/--
  Return `true` iff `e` depends on a free variable `x` s.t. `p x` is `true`.
  For each metavariable `?m` occurring in `x`
  1- If `?m := t`, then we visit `t` looking for `x`
  2- If `?m` is unassigned, then we consider the worst case and check whether `x` is in the local context of `?m`.
     This case is a "may dependency". That is, we may assign a term `t` to `?m` s.t. `t` contains `x`. -/
@[inline] def findExprDependsOn (mctx : MetavarContext) (e : Expr) (p : FVarId → Bool) : Bool :=
  DependsOn.main mctx p e |>.run' {}

/--
  Similar to `findExprDependsOn`, but checks the expressions in the given local declaration
  depends on a free variable `x` s.t. `p x` is `true`. -/
@[inline] def findLocalDeclDependsOn (mctx : MetavarContext) (localDecl : LocalDecl) (p : FVarId → Bool) : Bool :=
  match localDecl with
  | LocalDecl.cdecl (type := t) ..  => findExprDependsOn mctx t p
  | LocalDecl.ldecl (type := t) (value := v) .. => (DependsOn.main mctx p t <||> DependsOn.main mctx p v).run' {}

def exprDependsOn (mctx : MetavarContext) (e : Expr) (fvarId : FVarId) : Bool :=
  findExprDependsOn mctx e fun fvarId' => fvarId == fvarId'

def localDeclDependsOn (mctx : MetavarContext) (localDecl : LocalDecl) (fvarId : FVarId) : Bool :=
  findLocalDeclDependsOn mctx localDecl fun fvarId' => fvarId == fvarId'

namespace MkBinding

inductive Exception where
  | revertFailure (mctx : MetavarContext) (lctx : LocalContext) (toRevert : Array Expr) (decl : LocalDecl)

instance : ToString Exception where
  toString
    | Exception.revertFailure _ lctx toRevert decl =>
      "failed to revert "
      ++ toString (toRevert.map (fun x => "'" ++ toString (lctx.getFVar! x).userName ++ "'"))
      ++ ", '" ++ toString decl.userName ++ "' depends on them, and it is an auxiliary declaration created by the elaborator"
      ++ " (possible solution: use tactic 'clear' to remove '" ++ toString decl.userName ++ "' from local context)"

/--
 `MkBinding` and `elimMVarDepsAux` are mutually recursive, but `cache` is only used at `elimMVarDepsAux`.
  We use a single state object for convenience.

  We have a `NameGenerator` because we need to generate fresh auxiliary metavariables. -/
structure State where
  mctx  : MetavarContext
  ngen  : NameGenerator
  cache : HashMap ExprStructEq Expr := {}

abbrev MCore := EStateM Exception State
abbrev M     := ReaderT Bool MCore

def preserveOrder : M Bool := read

instance : MonadHashMapCacheAdapter ExprStructEq Expr M where
  getCache    := do let s ← get; pure s.cache
  modifyCache := fun f => modify fun s => { s with cache := f s.cache }

/-- Return the local declaration of the free variable `x` in `xs` with the smallest index -/
private def getLocalDeclWithSmallestIdx (lctx : LocalContext) (xs : Array Expr) : LocalDecl := do
  let mut d : LocalDecl := lctx.getFVar! xs[0]
  for i in [1:xs.size] do
    let curr := lctx.getFVar! xs[i]
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
def collectDeps (mctx : MetavarContext) (lctx : LocalContext) (toRevert : Array Expr) (preserveOrder : Bool) : Except Exception (Array Expr) := do
  if toRevert.size == 0 then
    pure toRevert
  else
    if preserveOrder then
      -- Make sure none of `toRevert` is an AuxDecl
      -- Make sure toRevert[j] does not depend on toRevert[i] for j > i
      toRevert.size.forM fun i => do
        let fvar := toRevert[i]
        let decl := lctx.getFVar! fvar
        i.forM fun j => do
          let prevFVar := toRevert[j]
          let prevDecl := lctx.getFVar! prevFVar
          if localDeclDependsOn mctx prevDecl fvar.fvarId! then
            throw (Exception.revertFailure mctx lctx toRevert prevDecl)
    let newToRevert      := if preserveOrder then toRevert else Array.mkEmpty toRevert.size
    let firstDeclToVisit := getLocalDeclWithSmallestIdx lctx toRevert
    let initSize         := newToRevert.size
    lctx.foldlM (init := newToRevert) (start := firstDeclToVisit.index) fun (newToRevert : Array Expr) decl =>
      if initSize.any fun i => decl.fvarId == (newToRevert.get! i).fvarId! then pure newToRevert
      else if toRevert.any fun x => decl.fvarId == x.fvarId! then
        pure (newToRevert.push decl.toExpr)
      else if findLocalDeclDependsOn mctx decl (fun fvarId => newToRevert.any fun x => x.fvarId! == fvarId) then
        pure (newToRevert.push decl.toExpr)
      else
        pure newToRevert

/-- Create a new `LocalContext` by removing the free variables in `toRevert` from `lctx`.
    We use this function when we create auxiliary metavariables at `elimMVarDepsAux`. -/
def reduceLocalContext (lctx : LocalContext) (toRevert : Array Expr) : LocalContext :=
  toRevert.foldr (init := lctx) fun x lctx =>
    lctx.erase x.fvarId!

@[inline] private def getMCtx : M MetavarContext :=
  return (← get).mctx

/-- Return free variables in `xs` that are in the local context `lctx` -/
private def getInScope (lctx : LocalContext) (xs : Array Expr) : Array Expr :=
  xs.foldl (init := #[]) fun scope x =>
    if lctx.contains x.fvarId! then
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
    match kind with
    | MetavarKind.syntheticOpaque => mkApp e x
    | _                           => if (lctx.getFVar! x).isLet then e else mkApp e x

/-- Return true iff some `e` in `es` depends on `fvarId` -/
private def anyDependsOn (mctx : MetavarContext) (es : Array Expr) (fvarId : FVarId) : Bool :=
  es.any fun e => exprDependsOn mctx e fvarId

mutual

  private partial def visit (xs : Array Expr) (e : Expr) : M Expr :=
    if !e.hasMVar then pure e else checkCache { val := e : ExprStructEq } fun _ => elim xs e

  private partial def elim (xs : Array Expr) (e : Expr) : M Expr :=
    match e with
    | Expr.proj _ _ s _    => return e.updateProj! (← visit xs s)
    | Expr.forallE _ d b _ => return e.updateForallE! (← visit xs d) (← visit xs b)
    | Expr.lam _ d b _     => return e.updateLambdaE! (← visit xs d) (← visit xs b)
    | Expr.letE _ t v b _  => return e.updateLet! (← visit xs t) (← visit xs v) (← visit xs b)
    | Expr.mdata _ b _     => return e.updateMData! (← visit xs b)
    | Expr.app _ _ _       => e.withApp fun f args => elimApp xs f args
    | Expr.mvar mvarId _   => elimApp xs e #[]
    | e                    => return e

  private partial def mkAuxMVarType (lctx : LocalContext)  (xs : Array Expr) (kind : MetavarKind) (e : Expr) : M Expr := do
    let e ← abstractRangeAux xs xs.size e
    xs.size.foldRevM (init := e) fun i e =>
      let x := xs[i]
      match lctx.getFVar! x with
      | LocalDecl.cdecl _ _ n type bi => do
        let type := type.headBeta
        let type ← abstractRangeAux xs i type
        pure <| Lean.mkForall n bi type e
      | LocalDecl.ldecl _ _ n type value nonDep => do
        let type := type.headBeta
        let type  ← abstractRangeAux xs i type
        let value ← abstractRangeAux xs i value
        let e := mkLet n type value e nonDep
        match kind with
        | MetavarKind.syntheticOpaque =>
          -- See "Gruesome details" section in the beginning of the file
          let e := e.liftLooseBVars 0 1
          pure <| mkForall n BinderInfo.default type e
        | _ => pure e
  where
    abstractRangeAux (xs : Array Expr) (i : Nat) (e : Expr) : M Expr := do
      let e ← elim xs e
      pure (e.abstractRange i xs)

  private partial def elimMVar (xs : Array Expr) (mvarId : MVarId) (args : Array Expr) : M (Expr × Array Expr) := do
    let mctx ← getMCtx
    let mvarDecl  := mctx.getDecl mvarId
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
      let newMVarKind := if !mctx.isExprAssignable mvarId then MetavarKind.syntheticOpaque else mvarDecl.kind
      /- If `mvarId` is the lhs of a delayed assignment `?m #[x_1, ... x_n] := val`,
         then `nestedFVars` is `#[x_1, ..., x_n]`.
         In this case, we produce a new `syntheticOpaque` metavariable `?n` and a delayed assignment
         ```
         ?n #[y_1, ..., y_m, x_1, ... x_n] := ?m x_1 ... x_n
         ```
         where `#[y_1, ..., y_m]` is `toRevert` after `collectDeps`.

         Remark: `newMVarKind != MetavarKind.syntheticOpaque ==> nestedFVars == #[]`
      -/
      let rec cont (nestedFVars : Array Expr) (nestedLCtx : LocalContext) : M (Expr × Array Expr) := do
        let args ← args.mapM (visit xs)
        let preserve ← preserveOrder
        match collectDeps mctx mvarLCtx toRevert preserve with
        | Except.error ex    => throw ex
        | Except.ok toRevert =>
          let newMVarLCtx   := reduceLocalContext mvarLCtx toRevert
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
          match newMVarKind with
          | MetavarKind.syntheticOpaque =>
            modify fun s => { s with mctx := assignDelayed s.mctx newMVarId nestedLCtx (toRevert ++ nestedFVars) (mkAppN (mkMVar mvarId) nestedFVars) }
          | _                           =>
            modify fun s => { s with mctx := assignExpr s.mctx mvarId result }
          return (mkAppN result args, toRevert)
      if !mvarDecl.kind.isSyntheticOpaque then
        cont #[] mvarLCtx
      else match mctx.getDelayedAssignment? mvarId with
      | none => cont #[] mvarLCtx
      | some { fvars := fvars, lctx := nestedLCtx, .. } => cont fvars nestedLCtx -- Remark: nestedLCtx is bigger than mvarLCtx

  private partial def elimApp (xs : Array Expr) (f : Expr) (args : Array Expr) : M Expr := do
    match f with
    | Expr.mvar mvarId _ =>
      match (← getMCtx).getExprAssignment? mvarId with
      | some newF =>
        if newF.isLambda then
          let args ← args.mapM (visit xs)
          elim xs <| newF.betaRev args.reverse
        else
          elimApp xs newF args
      | none => return (← elimMVar xs mvarId args).1
    | _ =>
      return mkAppN (← visit xs f) (← args.mapM (visit xs))

end

partial def elimMVarDeps (xs : Array Expr) (e : Expr) : M Expr :=
  if !e.hasMVar then
    pure e
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
  xs.size.foldRevM
    (fun i (p : Expr × Nat) => do
      let (e, num) := p;
      let x := xs[i]
      match lctx.getFVar! x with
      | LocalDecl.cdecl _ _ n type bi =>
        if !usedOnly || e.hasLooseBVar 0 then
          let type := type.headBeta;
          let type ← abstractRange xs i type
          if isLambda then
            pure (Lean.mkLambda n bi type e, num + 1)
          else
            pure (Lean.mkForall n bi type e, num + 1)
        else
          pure (e.lowerLooseBVars 1 1, num)
      | LocalDecl.ldecl _ _ n type value nonDep =>
        if !usedLetOnly || e.hasLooseBVar 0 then
          let type  ← abstractRange xs i type
          let value ← abstractRange xs i value
          pure (mkLet n type value e nonDep, num + 1)
        else
          pure (e.lowerLooseBVars 1 1, num))
    (e, 0)

end MkBinding

abbrev MkBindingM := ReaderT LocalContext MkBinding.MCore

def elimMVarDeps (xs : Array Expr) (e : Expr) (preserveOrder : Bool) : MkBindingM Expr := fun _ =>
  MkBinding.elimMVarDeps xs e preserveOrder

def revert (xs : Array Expr) (mvarId : MVarId) (preserveOrder : Bool) : MkBindingM (Expr × Array Expr) := fun _ =>
  MkBinding.revert xs mvarId preserveOrder

def mkBinding (isLambda : Bool) (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) : MkBindingM (Expr × Nat) := fun lctx =>
  MkBinding.mkBinding isLambda lctx xs e usedOnly usedLetOnly false

@[inline] def mkLambda (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) : MkBindingM Expr := do
  let (e, _) ← mkBinding (isLambda := true) xs e usedOnly usedLetOnly
  pure e

@[inline] def mkForall (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) : MkBindingM Expr := do
  let (e, _) ← mkBinding (isLambda := false) xs e usedOnly usedLetOnly
  pure e

@[inline] def abstractRange (e : Expr) (n : Nat) (xs : Array Expr) : MkBindingM Expr := fun _ =>
  MkBinding.abstractRange xs n e false

/--
  `isWellFormed mctx lctx e` return true if
  - All locals in `e` are declared in `lctx`
  - All metavariables `?m` in `e` have a local context which is a subprefix of `lctx` or are assigned, and the assignment is well-formed. -/
partial def isWellFormed (mctx : MetavarContext) (lctx : LocalContext) : Expr → Bool
  | Expr.mdata _ e _         => isWellFormed mctx lctx e
  | Expr.proj _ _ e _        => isWellFormed mctx lctx e
  | e@(Expr.app f a _)       => (!e.hasExprMVar && !e.hasFVar) || (isWellFormed mctx lctx f && isWellFormed mctx lctx a)
  | e@(Expr.lam _ d b _)     => (!e.hasExprMVar && !e.hasFVar) || (isWellFormed mctx lctx d && isWellFormed mctx lctx b)
  | e@(Expr.forallE _ d b _) => (!e.hasExprMVar && !e.hasFVar) || (isWellFormed mctx lctx d && isWellFormed mctx lctx b)
  | e@(Expr.letE _ t v b _)  => (!e.hasExprMVar && !e.hasFVar) || (isWellFormed mctx lctx t && isWellFormed mctx lctx v && isWellFormed mctx lctx b)
  | Expr.const ..            => true
  | Expr.bvar ..             => true
  | Expr.sort ..             => true
  | Expr.lit ..              => true
  | Expr.mvar mvarId _       =>
    let mvarDecl := mctx.getDecl mvarId;
    if mvarDecl.lctx.isSubPrefixOf lctx then true
    else match mctx.getExprAssignment? mvarId with
      | none   => false
      | some v => isWellFormed mctx lctx v
  | Expr.fvar fvarId _       => lctx.contains fvarId

namespace LevelMVarToParam

structure Context where
  paramNamePrefix : Name
  alreadyUsedPred : Name → Bool

structure State where
  mctx         : MetavarContext
  paramNames   : Array Name := #[]
  nextParamIdx : Nat
  cache        : HashMap ExprStructEq Expr := {}

abbrev M := ReaderT Context $ StateM State

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
  | Level.succ v _      => return u.updateSucc! (← visitLevel v)
  | Level.max v₁ v₂ _   => return u.updateMax! (← visitLevel v₁) (← visitLevel v₂)
  | Level.imax v₁ v₂ _  => return u.updateIMax! (← visitLevel v₁) (← visitLevel v₂)
  | Level.zero _        => pure u
  | Level.param ..      => pure u
  | Level.mvar mvarId _ =>
    let s ← get
    match s.mctx.getLevelAssignment? mvarId with
    | some v => visitLevel v
    | none   =>
      let p ← mkParamName
      let p := mkLevelParam p
      modify fun s => { s with mctx := s.mctx.assignLevel mvarId p }
      pure p

partial def main (e : Expr) : M Expr :=
  if !e.hasMVar then
    return e
  else
    checkCache { val := e : ExprStructEq } fun _ => do
      match e with
      | Expr.proj _ _ s _    => return e.updateProj! (← main s)
      | Expr.forallE _ d b _ => return e.updateForallE! (← main d) (← main b)
      | Expr.lam _ d b _     => return e.updateLambdaE! (← main d) (← main b)
      | Expr.letE _ t v b _  => return e.updateLet! (← main t) (← main v) (← main b)
      | Expr.app ..          => e.withApp fun f args => visitApp f args
      | Expr.mdata _ b _     => return e.updateMData! (← main b)
      | Expr.const _ us _    => return e.updateConst! (← us.mapM visitLevel)
      | Expr.sort u _        => return e.updateSort! (← visitLevel u)
      | Expr.mvar ..         => visitApp e #[]
      | e                    => return e
where
  visitApp (f : Expr) (args : Array Expr) : M Expr := do
    match f with
    | Expr.mvar mvarId .. =>
      match (← get).mctx.getExprAssignment? mvarId with
      | some v => return (← visitApp v args).headBeta
      | none   => return mkAppN f (← args.mapM main)
    | _ => return mkAppN (← main f) (← args.mapM main)

end LevelMVarToParam

structure UnivMVarParamResult where
  mctx          : MetavarContext
  newParamNames : Array Name
  nextParamIdx  : Nat
  expr          : Expr

def levelMVarToParam (mctx : MetavarContext) (alreadyUsedPred : Name → Bool) (e : Expr) (paramNamePrefix : Name := `u) (nextParamIdx : Nat := 1)
    : UnivMVarParamResult :=
  let (e, s) := LevelMVarToParam.main e { paramNamePrefix := paramNamePrefix, alreadyUsedPred := alreadyUsedPred } { mctx := mctx, nextParamIdx := nextParamIdx }
  { mctx          := s.mctx,
    newParamNames := s.paramNames,
    nextParamIdx  := s.nextParamIdx,
    expr          := e }

def getExprAssignmentDomain (mctx : MetavarContext) : Array MVarId :=
  mctx.eAssignment.foldl (init := #[]) fun a mvarId _ => Array.push a mvarId

end MetavarContext

end Lean
