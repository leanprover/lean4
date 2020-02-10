/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Init.Data.Nat
import Init.Data.Option
import Init.Lean.Util.MonadCache
import Init.Lean.LocalContext

namespace Lean

/-
The metavariable context stores metavariable declarations and their
assignments. It is used in the elaborator, tactic framework, unifier
(aka `isDefEq`), and type class resolution (TC). First, we list all
the requirements imposed by these modules.

- We may invoke TC while executing `isDefEq`. We need this feature to
be able to solve unification problems such as:
```
f ?a (ringHasAdd ?s) ?x ?y =?= f Int intHasAdd n m
```
where `(?a : Type) (?s : Ring ?a) (?x ?y : ?a)`
During `isDefEq` (i.e., unification), it will need to solve the constrain
```
ringHasAdd ?s =?= intHasAdd
```
We say `ringHasAdd ?s` is stuck because it cannot be reduced until we
synthesize the term `?s : Ring ?a` using TC. This can be done since we
have assigned `?a := Int` when solving `?a =?= Int`.

- TC uses `isDefEq`, and `isDefEq` may create TC problems as shown
aaa. Thus, we may have nested TC problems.

- `isDefEq` extends the local context when going inside binders. Thus,
the local context for nested TC may be an extension of the local
context for outer TC.

- TC should not assign metavariables created by the elaborator, simp,
tactic framework, and outer TC problems. Reason: TC commits to the
first solution it finds. Consider the TC problem `HasCoe Nat ?x`,
where `?x` is a metavariable created by the caller. There are many
solutions to this problem (e.g., `?x := Int`, `?x := Real`, ...),
and it doesn’t make sense to commit to the first one since TC does
not know the the constraints the caller may impose on `?x` after the
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
mechanism called tmp metavariables. It avoided this overhead, but it
created many problems since `simp` may indirectly call TC which may
recursively call TC. Moreover, we want to allow TC to invoke
tactics. Thus, when `simp` invokes `isDefEq`, it may indirectly invoke
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
In Lean4, TC may also invoke tactics.

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
variables `xs` and a term `t[?m]` which contains a metavariable `?m`,
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
to synthesize `HasCoe Nat ?x`. This is good, but this constraint is too
strict for problems such as `HasCoe (Vector Bool ?n) (BV ?n)`. The coercion
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

structure LocalInstance :=
(className : Name)
(fvar      : Expr)

abbrev LocalInstances := Array LocalInstance

def LocalInstance.beq (i₁ i₂ : LocalInstance) : Bool :=
i₁.fvar == i₂.fvar

instance LocalInstance.hasBeq : HasBeq LocalInstance := ⟨LocalInstance.beq⟩

/-- Remove local instance with the given `fvarId`. Do nothing if `localInsts` does not contain any free variable with id `fvarId`. -/
def LocalInstances.erase (localInsts : LocalInstances) (fvarId : FVarId) : LocalInstances :=
match localInsts.findIdx? (fun inst => inst.fvar.fvarId! == fvarId) with
| some idx => localInsts.eraseIdx idx
| _        => localInsts

inductive MetavarKind
| natural
| synthetic
| syntheticOpaque

def MetavarKind.isSyntheticOpaque : MetavarKind → Bool
| MetavarKind.syntheticOpaque => true
| _                           => false

structure MetavarDecl :=
(userName       : Name := Name.anonymous)
(lctx           : LocalContext)
(type           : Expr)
(depth          : Nat)
(localInstances : LocalInstances)
(kind           : MetavarKind)

namespace MetavarDecl
instance : Inhabited MetavarDecl := ⟨{ lctx := arbitrary _, type := arbitrary _, depth := 0, localInstances := #[], kind := MetavarKind.natural }⟩
end MetavarDecl

/--
  A delayed assignment for a metavariable `?m`. It represents an assignment of the form
  `?m := (fun fvars => val)`. The local context `lctx` provides the declarations for `fvars`.
  Note that `fvars` may not be defined in the local context for `?m`.

  - TODO: after we delete the old frontend, we can remove the field `lctx`.
    This field is only used in old C++ implementation. -/
structure DelayedMetavarAssignment :=
(lctx     : LocalContext)
(fvars    : Array Expr)
(val      : Expr)

structure MetavarContext :=
(depth       : Nat := 0)
(lDepth      : PersistentHashMap MVarId Nat := {})
(decls       : PersistentHashMap MVarId MetavarDecl := {})
(lAssignment : PersistentHashMap MVarId Level := {})
(eAssignment : PersistentHashMap MVarId Expr := {})
(dAssignment : PersistentHashMap MVarId DelayedMetavarAssignment := {})

namespace MetavarContext

instance : Inhabited MetavarContext := ⟨{}⟩

@[export lean_mk_metavar_ctx]
def mkMetavarContext : Unit → MetavarContext :=
fun _ => {}

/- Low level API for adding/declaring metavariable declarations.
   It is used to implement actions in the monads `MetaM`, `ElabM` and `TacticM`.
   It should not be used directly since the argument `(mvarId : MVarId)` is assumed to be "unique". -/
@[export lean_metavar_ctx_mk_decl]
def addExprMVarDecl (mctx : MetavarContext)
    (mvarId : MVarId)
    (userName : Name)
    (lctx : LocalContext)
    (localInstances : LocalInstances)
    (type : Expr) (kind : MetavarKind := MetavarKind.natural) : MetavarContext :=
{ decls := mctx.decls.insert mvarId {
    userName       := userName,
    lctx           := lctx,
    localInstances := localInstances,
    type           := type,
    depth          := mctx.depth,
    kind           := kind },
  .. mctx }

/- Low level API for adding/declaring universe level metavariable declarations.
   It is used to implement actions in the monads `MetaM`, `ElabM` and `TacticM`.
   It should not be used directly since the argument `(mvarId : MVarId)` is assumed to be "unique". -/
def addLevelMVarDecl (mctx : MetavarContext) (mvarId : MVarId) : MetavarContext :=
{ lDepth := mctx.lDepth.insert mvarId mctx.depth,
  .. mctx }

@[export lean_metavar_ctx_find_decl]
def findDecl? (mctx : MetavarContext) (mvarId : MVarId) : Option MetavarDecl :=
mctx.decls.find? mvarId

def getDecl (mctx : MetavarContext) (mvarId : MVarId) : MetavarDecl :=
match mctx.decls.find? mvarId with
| some decl => decl
| none      => panic! "unknown metavariable"

def setMVarKind (mctx : MetavarContext) (mvarId : MVarId) (kind : MetavarKind) : MetavarContext :=
let decl := mctx.getDecl mvarId;
{ decls := mctx.decls.insert mvarId { kind := kind, .. decl }, .. mctx }

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
| some mvarDecl => { decls := mctx.decls.insert mvarId { userName := newUserName, .. mvarDecl }, .. mctx }

@[export lean_metavar_ctx_assign_level]
def assignLevel (m : MetavarContext) (mvarId : MVarId) (val : Level) : MetavarContext :=
{ lAssignment := m.lAssignment.insert mvarId val, .. m }

@[export lean_metavar_ctx_assign_expr]
def assignExprCore (m : MetavarContext) (mvarId : MVarId) (val : Expr) : MetavarContext :=
{ eAssignment := m.eAssignment.insert mvarId val, .. m }

def assignExpr (m : MetavarContext) (mvarId : MVarId) (val : Expr) : MetavarContext :=
{ eAssignment := m.eAssignment.insert mvarId val, .. m }

@[export lean_metavar_ctx_assign_delayed]
def assignDelayed (m : MetavarContext) (mvarId : MVarId) (lctx : LocalContext) (fvars : Array Expr) (val : Expr) : MetavarContext :=
{ dAssignment := m.dAssignment.insert mvarId { lctx := lctx, fvars := fvars, val := val }, .. m }

@[export lean_metavar_ctx_get_level_assignment]
def getLevelAssignment? (m : MetavarContext) (mvarId : MVarId) : Option Level :=
m.lAssignment.find? mvarId

@[export lean_metavar_ctx_get_expr_assignment]
def getExprAssignment? (m : MetavarContext) (mvarId : MVarId) : Option Expr :=
m.eAssignment.find? mvarId

@[export lean_metavar_ctx_get_delayed_assignment]
def getDelayedAssignment? (m : MetavarContext) (mvarId : MVarId) : Option DelayedMetavarAssignment :=
m.dAssignment.find? mvarId

@[export lean_metavar_ctx_is_level_assigned]
def isLevelAssigned (m : MetavarContext) (mvarId : MVarId) : Bool :=
m.lAssignment.contains mvarId

@[export lean_metavar_ctx_is_expr_assigned]
def isExprAssigned (m : MetavarContext) (mvarId : MVarId) : Bool :=
m.eAssignment.contains mvarId

@[export lean_metavar_ctx_is_delayed_assigned]
def isDelayedAssigned (m : MetavarContext) (mvarId : MVarId) : Bool :=
m.dAssignment.contains mvarId

@[export lean_metavar_ctx_erase_delayed]
def eraseDelayed (m : MetavarContext) (mvarId : MVarId) : MetavarContext :=
{ dAssignment := m.dAssignment.erase mvarId, .. m }

def isLevelAssignable (mctx : MetavarContext) (mvarId : MVarId) : Bool :=
match mctx.lDepth.find? mvarId with
| some d => d == mctx.depth
| _      => panic! "unknown universe metavariable"

def isExprAssignable (mctx : MetavarContext) (mvarId : MVarId) : Bool :=
let decl := mctx.getDecl mvarId;
decl.depth == mctx.depth

def incDepth (mctx : MetavarContext) : MetavarContext :=
{ depth := mctx.depth + 1, .. mctx }

/-- Return true iff the given level contains an assigned metavariable. -/
def hasAssignedLevelMVar (mctx : MetavarContext) : Level → Bool
| Level.succ lvl _       => lvl.hasMVar && hasAssignedLevelMVar lvl
| Level.max lvl₁ lvl₂ _  => (lvl₁.hasMVar && hasAssignedLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar lvl₂)
| Level.imax lvl₁ lvl₂ _ => (lvl₁.hasMVar && hasAssignedLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar lvl₂)
| Level.mvar mvarId _    => mctx.isLevelAssigned mvarId
| Level.zero _           => false
| Level.param _ _        => false

/-- Return `true` iff expression contains assigned (level/expr) metavariables or delayed assigned mvars -/
def hasAssignedMVar (mctx : MetavarContext) : Expr → Bool
| Expr.const _ lvls _  => lvls.any (hasAssignedLevelMVar mctx)
| Expr.sort lvl _      => hasAssignedLevelMVar mctx lvl
| Expr.app f a _       => (f.hasMVar && hasAssignedMVar f) || (a.hasMVar && hasAssignedMVar a)
| Expr.letE _ t v b _  => (t.hasMVar && hasAssignedMVar t) || (v.hasMVar && hasAssignedMVar v) || (b.hasMVar && hasAssignedMVar b)
| Expr.forallE _ d b _ => (d.hasMVar && hasAssignedMVar d) || (b.hasMVar && hasAssignedMVar b)
| Expr.lam _ d b _     => (d.hasMVar && hasAssignedMVar d) || (b.hasMVar && hasAssignedMVar b)
| Expr.fvar _ _        => false
| Expr.bvar _ _        => false
| Expr.lit _ _         => false
| Expr.mdata _ e _     => e.hasMVar && hasAssignedMVar e
| Expr.proj _ _ e _    => e.hasMVar && hasAssignedMVar e
| Expr.mvar mvarId _   => mctx.isExprAssigned mvarId || mctx.isDelayedAssigned mvarId
| Expr.localE _ _ _ _  => unreachable!

/-- Return true iff the given level contains a metavariable that can be assigned. -/
def hasAssignableLevelMVar (mctx : MetavarContext) : Level → Bool
| Level.succ lvl _       => lvl.hasMVar && hasAssignableLevelMVar lvl
| Level.max lvl₁ lvl₂ _  => (lvl₁.hasMVar && hasAssignableLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignableLevelMVar lvl₂)
| Level.imax lvl₁ lvl₂ _ => (lvl₁.hasMVar && hasAssignableLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignableLevelMVar lvl₂)
| Level.mvar mvarId _    => mctx.isLevelAssignable mvarId
| Level.zero _           => false
| Level.param _ _        => false

/-- Return `true` iff expression contains a metavariable that can be assigned. -/
def hasAssignableMVar (mctx : MetavarContext) : Expr → Bool
| Expr.const _ lvls _  => lvls.any (hasAssignableLevelMVar mctx)
| Expr.sort lvl _      => hasAssignableLevelMVar mctx lvl
| Expr.app f a _       => (f.hasMVar && hasAssignableMVar f) || (a.hasMVar && hasAssignableMVar a)
| Expr.letE _ t v b _  => (t.hasMVar && hasAssignableMVar t) || (v.hasMVar && hasAssignableMVar v) || (b.hasMVar && hasAssignableMVar b)
| Expr.forallE _ d b _ => (d.hasMVar && hasAssignableMVar d) || (b.hasMVar && hasAssignableMVar b)
| Expr.lam _ d b _     => (d.hasMVar && hasAssignableMVar d) || (b.hasMVar && hasAssignableMVar b)
| Expr.fvar _ _        => false
| Expr.bvar _ _        => false
| Expr.lit _ _         => false
| Expr.mdata _ e _     => e.hasMVar && hasAssignableMVar e
| Expr.proj _ _ e _    => e.hasMVar && hasAssignableMVar e
| Expr.mvar mvarId _   => mctx.isExprAssignable mvarId
| Expr.localE _ _ _ _  => unreachable!

partial def instantiateLevelMVars : Level → StateM MetavarContext Level
| lvl@(Level.succ lvl₁ _)      => do lvl₁ ← instantiateLevelMVars lvl₁; pure (Level.updateSucc! lvl lvl₁)
| lvl@(Level.max lvl₁ lvl₂ _)  => do lvl₁ ← instantiateLevelMVars lvl₁; lvl₂ ← instantiateLevelMVars lvl₂; pure (Level.updateMax! lvl lvl₁ lvl₂)
| lvl@(Level.imax lvl₁ lvl₂ _) => do lvl₁ ← instantiateLevelMVars lvl₁; lvl₂ ← instantiateLevelMVars lvl₂; pure (Level.updateIMax! lvl lvl₁ lvl₂)
| lvl@(Level.mvar mvarId _)    => do
  mctx ← get;
  match getLevelAssignment? mctx mvarId with
  | some newLvl =>
    if !newLvl.hasMVar then pure newLvl
    else do
      newLvl' ← instantiateLevelMVars newLvl;
      modify $ fun mctx => mctx.assignLevel mvarId newLvl';
      pure newLvl'
  | none        => pure lvl
| lvl => pure lvl

namespace InstantiateExprMVars
private abbrev M := StateM (WithHashMapCache Expr Expr MetavarContext)

@[inline] def instantiateLevelMVars (lvl : Level) : M Level :=
WithHashMapCache.fromState $ MetavarContext.instantiateLevelMVars lvl

@[inline] private def visit (f : Expr → M Expr) (e : Expr) : M Expr :=
if !e.hasMVar then pure e else checkCache e f

@[inline] private def getMCtx : M MetavarContext := do
s ← get; pure s.state

@[inline] private def modifyCtx (f : MetavarContext → MetavarContext) : M Unit :=
modify $ fun s => { state := f s.state, .. s }

/-- instantiateExprMVars main function -/
partial def main : Expr → M Expr
| e@(Expr.proj _ _ s _)    => do s ← visit main s; pure (e.updateProj! s)
| e@(Expr.forallE _ d b _) => do d ← visit main d; b ← visit main b; pure (e.updateForallE! d b)
| e@(Expr.lam _ d b _)     => do d ← visit main d; b ← visit main b; pure (e.updateLambdaE! d b)
| e@(Expr.letE _ t v b _)  => do t ← visit main t; v ← visit main v; b ← visit main b; pure (e.updateLet! t v b)
| e@(Expr.const _ lvls _)  => do lvls ← lvls.mapM instantiateLevelMVars; pure (e.updateConst! lvls)
| e@(Expr.sort lvl _)      => do lvl ← instantiateLevelMVars lvl; pure (e.updateSort! lvl)
| e@(Expr.mdata _ b _)     => do b ← visit main b; pure (e.updateMData! b)
| e@(Expr.app _ _ _)       => e.withApp $ fun f args => do
  let instArgs (f : Expr) : M Expr := do {
    args ← args.mapM (visit main);
    pure (mkAppN f args)
  };
  let instApp : M Expr := do {
    let wasMVar := f.isMVar;
    f ← visit main f;
    if wasMVar && f.isLambda then
      /- Some of the arguments in args are irrelevant after we beta reduce. -/
      visit main (f.betaRev args.reverse)
    else
      instArgs f
  };
  match f with
  | Expr.mvar mvarId _ => do
    mctx ← getMCtx;
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
      else do
        newVal ← visit main val;
        if newVal.hasMVar then
          instArgs f
        else do
          args ← args.mapM (visit main);
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
          let newVal := newVal.abstract fvars;
          let result := newVal.instantiateRevRange 0 fvars.size args;
          let result := mkAppRange result fvars.size args.size args;
          pure $ result
  | _ => instApp
| e@(Expr.mvar mvarId _)   => checkCache e $ fun e => do
  mctx ← getMCtx;
  match mctx.getExprAssignment? mvarId with
  | some newE => do
    newE' ← visit main newE;
    modifyCtx $ fun mctx => mctx.assignExpr mvarId newE';
    pure newE'
  | none => pure e
| e => pure e

end InstantiateExprMVars

def instantiateMVars (mctx : MetavarContext) (e : Expr) : Expr × MetavarContext :=
if !e.hasMVar then (e, mctx)
else (WithHashMapCache.toState $ InstantiateExprMVars.main e).run mctx

def instantiateLCtxMVars (mctx : MetavarContext) (lctx : LocalContext) : LocalContext × MetavarContext :=
lctx.foldl
  (fun (result : LocalContext × MetavarContext) ldecl =>
     let (lctx, mctx) := result;
     match ldecl with
     | LocalDecl.cdecl _ fvarId userName type bi    =>
       let (type, mctx) := mctx.instantiateMVars type;
       (lctx.mkLocalDecl fvarId userName type bi, mctx)
     | LocalDecl.ldecl _ fvarId userName type value =>
       let (type, mctx)  := mctx.instantiateMVars type;
       let (value, mctx) := mctx.instantiateMVars value;
       (lctx.mkLetDecl fvarId userName type value, mctx))
  ({}, mctx)

def instantiateMVarDeclMVars (mctx : MetavarContext) (mvarId : MVarId) : MetavarContext :=
let mvarDecl     := mctx.getDecl mvarId;
let (lctx, mctx) := mctx.instantiateLCtxMVars mvarDecl.lctx;
let (type, mctx) := mctx.instantiateMVars mvarDecl.type;
{ decls := mctx.decls.insert mvarId { lctx := lctx, type := type, .. mvarDecl }, .. mctx }

namespace DependsOn

private abbrev M := StateM ExprSet

private def visit? (e : Expr) : M Bool :=
if !e.hasMVar && !e.hasFVar then
  pure false
else do
  s ← get;
  if s.contains e then
    pure false
  else do
    modify $ fun s => s.insert e;
    pure true

@[inline] private def visit (main : Expr → M Bool) (e : Expr) : M Bool :=
condM (visit? e) (main e) (pure false)

@[specialize] private partial def dep (mctx : MetavarContext) (p : FVarId → Bool) : Expr → M Bool
| e@(Expr.proj _ _ s _)    => visit dep s
| e@(Expr.forallE _ d b _) => visit dep d <||> visit dep b
| e@(Expr.lam _ d b _)     => visit dep d <||> visit dep b
| e@(Expr.letE _ t v b _)  => visit dep t <||> visit dep v <||> visit dep b
| e@(Expr.mdata _ b _)     => visit dep b
| e@(Expr.app f a _)       => visit dep a <||> if f.isApp then dep f else visit dep f
| e@(Expr.mvar mvarId _)   =>
  match mctx.getExprAssignment? mvarId with
  | some a => visit dep a
  | none   =>
    let lctx := (mctx.getDecl mvarId).lctx;
    pure $ lctx.any $ fun decl => p decl.fvarId
| e@(Expr.fvar fvarId _)   => pure $ p fvarId
| e                        => pure false

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
(DependsOn.main mctx p e).run' {}

/--
  Similar to `exprDependsOn`, but checks the expressions in the given local declaration
  depends on a free variable `x` s.t. `p x` is `true`. -/
@[inline] def findLocalDeclDependsOn (mctx : MetavarContext) (localDecl : LocalDecl) (p : FVarId → Bool) : Bool :=
match localDecl with
| LocalDecl.cdecl _ _ _ type _     => findExprDependsOn mctx type p
| LocalDecl.ldecl _ _ _ type value => (DependsOn.main mctx p type <||> DependsOn.main mctx p value).run' {}

def exprDependsOn (mctx : MetavarContext) (e : Expr) (fvarId : FVarId) : Bool :=
findExprDependsOn mctx e $ fun fvarId' => fvarId == fvarId'

def localDeclDependsOn (mctx : MetavarContext) (localDecl : LocalDecl) (fvarId : FVarId) : Bool :=
findLocalDeclDependsOn mctx localDecl $ fun fvarId' => fvarId == fvarId'

namespace MkBinding

inductive Exception
| revertFailure (mctx : MetavarContext) (lctx : LocalContext) (toRevert : Array Expr) (decl : LocalDecl)

def Exception.toString : Exception → String
| Exception.revertFailure _ lctx toRevert decl =>
  "failed to revert "
  ++ toString (toRevert.map (fun x => "'" ++ toString (lctx.getFVar! x).userName ++ "'"))
  ++ ", '" ++ toString decl.userName ++ "' depends on them, and it is an auxiliary declaration created by the elaborator"
  ++ " (possible solution: use tactic 'clear' to remove '" ++ toString decl.userName ++ "' from local context)"

instance Exception.hasToString : HasToString Exception := ⟨Exception.toString⟩

/--
 `MkBinding` and `elimMVarDepsAux` are mutually recursive, but `cache` is only used at `elimMVarDepsAux`.
  We use a single state object for convenience.

  We have a `NameGenerator` because we need to generate fresh auxiliary metavariables. -/
structure State :=
(mctx  : MetavarContext)
(ngen  : NameGenerator)
(cache : HashMap Expr Expr := {}) --

abbrev MCore := EStateM Exception State
abbrev M     := ReaderT Bool (EStateM Exception State)

def preserveOrder : M Bool := read

instance : MonadHashMapCacheAdapter Expr Expr M :=
{ getCache    := do s ← get; pure s.cache,
  modifyCache := fun f => modify $ fun s => { cache := f s.cache, .. s } }

/-- Return the local declaration of the free variable `x` in `xs` with the smallest index -/
private def getLocalDeclWithSmallestIdx (lctx : LocalContext) (xs : Array Expr) : LocalDecl :=
let d : LocalDecl := lctx.getFVar! $ xs.get! 0;
xs.foldlFrom
  (fun d x =>
    let decl := lctx.getFVar! x;
    if decl.index < d.index then decl else d)
  d 1

/-- Given `toRevert` an array of free variables s.t. `lctx` contains their declarations,
    return a new array of free variables that contains `toRevert` and all free variables
    in `lctx` that may depend on `toRevert`.

    Remark: the result is sorted by `LocalDecl` indices. -/
private def collectDeps (mctx : MetavarContext) (lctx : LocalContext) (toRevert : Array Expr) (preserveOrder : Bool) : Except Exception (Array Expr) :=
if toRevert.size == 0 then pure toRevert
else do
  when preserveOrder $ do {
    -- Make sure none of `toRevert` is an AuxDecl
    -- Make sure toRevert[j] does not depend on toRevert[i] for j > i
    toRevert.size.forM $ fun i => do
      let fvar := toRevert.get! i;
      let decl := lctx.getFVar! fvar;
      when decl.binderInfo.isAuxDecl $
        throw (Exception.revertFailure mctx lctx toRevert decl);
      i.forM $ fun j =>
        let prevFVar := toRevert.get! j;
        let prevDecl := lctx.getFVar! prevFVar;
        when (localDeclDependsOn mctx prevDecl fvar.fvarId!) $
          throw (Exception.revertFailure mctx lctx toRevert prevDecl)
  };
  let newToRevert      := if preserveOrder then toRevert else Array.mkEmpty toRevert.size;
  let firstDeclToVisit := if preserveOrder then lctx.getFVar! toRevert.back else getLocalDeclWithSmallestIdx lctx toRevert;
  let skipFirst        := preserveOrder;
  lctx.foldlFromM
    (fun (newToRevert : Array Expr) decl =>
      if skipFirst && decl.index == firstDeclToVisit.index then pure newToRevert
      else if toRevert.any (fun x => decl.fvarId == x.fvarId!) then
        pure (newToRevert.push decl.toExpr)
      else if findLocalDeclDependsOn mctx decl (fun fvarId => newToRevert.any $ fun x => x.fvarId! == fvarId) then
        if decl.binderInfo.isAuxDecl then
          throw (Exception.revertFailure mctx lctx toRevert decl)
        else
          pure (newToRevert.push decl.toExpr)
      else
        pure newToRevert)
    newToRevert
    firstDeclToVisit

/-- Create a new `LocalContext` by removing the free variables in `toRevert` from `lctx`.
    We use this function when we create auxiliary metavariables at `elimMVarDepsAux`. -/
private def reduceLocalContext (lctx : LocalContext) (toRevert : Array Expr) : LocalContext :=
toRevert.foldr
  (fun x lctx => lctx.erase x.fvarId!)
  lctx

@[inline] private def visit (f : Expr → M Expr) (e : Expr) : M Expr :=
if !e.hasMVar then pure e else checkCache e f

@[inline] private def getMCtx : M MetavarContext := do
s ← get; pure s.mctx

/-- Return free variables in `xs` that are in the local context `lctx` -/
private def getInScope (lctx : LocalContext) (xs : Array Expr) : Array Expr :=
xs.foldl
  (fun scope x =>
    if lctx.contains x.fvarId! then
      scope.push x
    else
      scope)
  #[]

/-- Execute `x` with an empty cache, and then restore the original cache. -/
@[inline] private def withFreshCache {α} (x : M α) : M α := do
cache ← modifyGet $ fun s => (s.cache, { cache := {}, .. s });
a ← x;
modify $ fun s => { cache := cache, .. s };
pure a

@[inline] private def abstractRangeAux (elimMVarDeps : Expr → M Expr) (xs : Array Expr) (i : Nat) (e : Expr) : M Expr := do
e ← elimMVarDeps e;
pure (e.abstractRange i xs)

private def mkAuxMVarType (elimMVarDeps : Expr → M Expr) (lctx : LocalContext) (xs : Array Expr) (kind : MetavarKind) (e : Expr) : M Expr := do
e ← abstractRangeAux elimMVarDeps xs xs.size e;
xs.size.foldRevM
  (fun i e =>
    let x := xs.get! i;
    match lctx.getFVar! x with
    | LocalDecl.cdecl _ _ n type bi => do
      type ← abstractRangeAux elimMVarDeps xs i type;
      pure $ Lean.mkForall n bi type e
    | LocalDecl.ldecl _ _ n type value => do
      type  ← abstractRangeAux elimMVarDeps xs i type;
      value ← abstractRangeAux elimMVarDeps xs i value;
      let e := mkLet n type value e;
      match kind with
      | MetavarKind.syntheticOpaque =>
        -- See "Gruesome details" section in the beginning of the file
        let e := e.liftLooseBVars 0 1;
        pure $ mkForall n BinderInfo.default type e
      | _ => pure e)
  e

/--
  Create an application `mvar ys` where `ys` are the free variables.
  See "Gruesome details" in the beginning of the file for understanding
  how let-decl free variables are handled. -/
private def mkMVarApp (lctx : LocalContext) (mvar : Expr) (xs : Array Expr) (kind : MetavarKind) : Expr :=
xs.foldl
  (fun e x =>
    match kind with
    | MetavarKind.syntheticOpaque => mkApp e x
    | _                           => if (lctx.getFVar! x).isLet then e else mkApp e x)
  mvar

private def mkAuxMVar (lctx : LocalContext) (localInsts : LocalInstances) (type : Expr) (kind : MetavarKind) : M MVarId := do
s ← get;
let mvarId := s.ngen.curr;
modify $ fun s => { mctx := s.mctx.addExprMVarDecl mvarId Name.anonymous lctx localInsts type kind, ngen := s.ngen.next, .. s };
pure mvarId

/-- Return true iff some `e` in `es` depends on `fvarId` -/
private def anyDependsOn (mctx : MetavarContext) (es : Array Expr) (fvarId : FVarId) : Bool :=
es.any $ fun e => exprDependsOn mctx e fvarId

private partial def elimMVarDepsApp (elimMVarDepsAux : Expr → M Expr) (xs : Array Expr) : Expr → Array Expr → M Expr
| f, args =>
  match f with
  | Expr.mvar mvarId _ => do
    let processDefault (newF : Expr) : M Expr := do {
      if newF.isLambda then do
        args ← args.mapM (visit elimMVarDepsAux);
        pure $ newF.betaRev args.reverse
      else if newF == f then do
        args ← args.mapM (visit elimMVarDepsAux);
        pure $ mkAppN newF args
      else
        elimMVarDepsApp newF args
    };
    mctx ← getMCtx;
    match mctx.getExprAssignment? mvarId with
    | some val => processDefault val
    | _        =>
      let mvarDecl  := mctx.getDecl mvarId;
      let mvarLCtx  := mvarDecl.lctx;
      let toRevert  := getInScope mvarLCtx xs;
      if toRevert.size == 0 then
        processDefault f
      else
        let newMVarKind := if !mctx.isExprAssignable mvarId then MetavarKind.syntheticOpaque else mvarDecl.kind;
        /- If `mvarId` is the lhs of a delayed assignment `?m #[x_1, ... x_n] := val`,
           then `nestedFVars` is `#[x_1, ..., x_n]`.
           In this case, we produce a new `syntheticOpaque` metavariable `?n` and a delayed assignment
           ```
           ?n #[y_1, ..., y_m, x_1, ... x_n] := ?m x_1 ... x_n
           ```
           where `#[y_1, ..., y_m]` is `toRevert` after `collectDeps`.

           Remark: `newMVarKind != MetavarKind.syntheticOpaque ==> nestedFVars == #[]`
        -/
        let continue (nestedFVars : Array Expr) : M Expr := do {
          args ← args.mapM (visit elimMVarDepsAux);
          preserve ← preserveOrder;
          match collectDeps mctx mvarLCtx toRevert preserve with
          | Except.error ex    => throw ex
          | Except.ok toRevert => do
            let newMVarLCtx   := reduceLocalContext mvarLCtx toRevert;
            let newLocalInsts := mvarDecl.localInstances.filter $ fun inst => toRevert.all $ fun x => inst.fvar != x;
            newMVarType ← mkAuxMVarType elimMVarDepsAux mvarLCtx toRevert newMVarKind mvarDecl.type;
            newMVarId   ← mkAuxMVar newMVarLCtx newLocalInsts newMVarType newMVarKind;
            let newMVar := mkMVar newMVarId;
            let result  := mkMVarApp mvarLCtx newMVar toRevert newMVarKind;
            match newMVarKind with
            | MetavarKind.syntheticOpaque =>
              modify $ fun s => { mctx := assignDelayed s.mctx newMVarId mvarLCtx (toRevert ++ nestedFVars) (mkAppN f nestedFVars), .. s }
            | _                           =>
              modify $ fun s => { mctx := assignExpr s.mctx mvarId result, .. s };
            pure (mkAppN result args)
        };
        if !mvarDecl.kind.isSyntheticOpaque then
          continue #[]
        else match mctx.getDelayedAssignment? mvarId with
        | none                        => continue #[]
        | some { fvars := fvars, .. } => continue fvars
  | _ => do
    f ← visit elimMVarDepsAux f;
    args ← args.mapM (visit elimMVarDepsAux);
    pure (mkAppN f args)

private partial def elimMVarDepsAux (xs : Array Expr) : Expr → M Expr
| e@(Expr.proj _ _ s _)    => do s ← visit elimMVarDepsAux s; pure (e.updateProj! s)
| e@(Expr.forallE _ d b _) => do d ← visit elimMVarDepsAux d; b ← visit elimMVarDepsAux b; pure (e.updateForallE! d b)
| e@(Expr.lam _ d b _)     => do d ← visit elimMVarDepsAux d; b ← visit elimMVarDepsAux b; pure (e.updateLambdaE! d b)
| e@(Expr.letE _ t v b _)  => do t ← visit elimMVarDepsAux t; v ← visit elimMVarDepsAux v; b ← visit elimMVarDepsAux b; pure (e.updateLet! t v b)
| e@(Expr.mdata _ b _)     => do b ← visit elimMVarDepsAux b; pure (e.updateMData! b)
| e@(Expr.app _ _ _)       => e.withApp $ fun f args => elimMVarDepsApp elimMVarDepsAux xs f args
| e@(Expr.mvar mvarId _)   => elimMVarDepsApp elimMVarDepsAux xs e #[]
| e                        => pure e

partial def elimMVarDeps (xs : Array Expr) (e : Expr) : M Expr :=
if !e.hasMVar then
  pure e
else
  withFreshCache $ elimMVarDepsAux xs e

/--
  Similar to `Expr.abstractRange`, but handles metavariables correctly.
  It uses `elimMVarDeps` to ensure `e` and the type of the free variables `xs` do not
  contain a metavariable `?m` s.t. local context of `?m` contains a free variable in `xs`.

  `elimMVarDeps` is defined later in this file. -/
@[inline] private def abstractRange (xs : Array Expr) (i : Nat) (e : Expr) : M Expr := do
e ← elimMVarDeps xs e;
pure (e.abstractRange i xs)

/--
  Similar to `LocalContext.mkBinding`, but handles metavariables correctly.
  If `usedOnly == false` then `forall` and `lambda` are created only for used variables. -/
@[specialize] def mkBinding (isLambda : Bool) (lctx : LocalContext) (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) : M (Expr × Nat) := do
e ← abstractRange xs xs.size e;
xs.size.foldRevM
  (fun i (p : Expr × Nat) =>
    let (e, num) := p;
    let x := xs.get! i;
    match lctx.getFVar! x with
    | LocalDecl.cdecl _ _ n type bi =>
      if !usedOnly || e.hasLooseBVar 0 then do
        type ← abstractRange xs i type;
        if isLambda then
          pure (Lean.mkLambda n bi type e, num + 1)
        else
          pure (Lean.mkForall n bi type e, num + 1)
      else
        pure (e.lowerLooseBVars 1 1, num)
    | LocalDecl.ldecl _ _ n type value => do
      if e.hasLooseBVar 0 then do
        type  ← abstractRange xs i type;
        value ← abstractRange xs i value;
        pure (mkLet n type value e, num + 1)
      else
        pure (e.lowerLooseBVars 1 1, num))
  (e, 0)

end MkBinding

abbrev MkBindingM := ReaderT LocalContext MkBinding.MCore

def elimMVarDeps (xs : Array Expr) (e : Expr) (preserveOrder : Bool) : MkBindingM Expr :=
fun _ => MkBinding.elimMVarDeps xs e preserveOrder

def mkBinding (isLambda : Bool) (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) : MkBindingM (Expr × Nat) :=
fun lctx => MkBinding.mkBinding isLambda lctx xs e usedOnly false

@[inline] def mkLambda (xs : Array Expr) (e : Expr) : MkBindingM Expr := do
(e, _) ← mkBinding true xs e;
pure e

@[inline] def mkForall (xs : Array Expr) (e : Expr) : MkBindingM Expr := do
(e, _) ← mkBinding false xs e;
pure e

@[inline] def mkForallUsedOnly (xs : Array Expr) (e : Expr) : MkBindingM (Expr × Nat) := do
mkBinding false xs e true

/--
  `isWellFormed mctx lctx e` return true if
  - All locals in `e` are declared in `lctx`
  - All metavariables `?m` in `e` have a local context which is a subprefix of `lctx` or are assigned, and the assignment is well-formed. -/
partial def isWellFormed (mctx : MetavarContext) (lctx : LocalContext) : Expr → Bool
| Expr.mdata _ e _         => isWellFormed e
| Expr.proj _ _ e _        => isWellFormed e
| e@(Expr.app f a _)       => (e.hasExprMVar || e.hasFVar) && isWellFormed f && isWellFormed a
| e@(Expr.lam _ d b _)     => (e.hasExprMVar || e.hasFVar) && isWellFormed d && isWellFormed b
| e@(Expr.forallE _ d b _) => (e.hasExprMVar || e.hasFVar) && isWellFormed d && isWellFormed b
| e@(Expr.letE _ t v b _)  => (e.hasExprMVar || e.hasFVar) && isWellFormed t && isWellFormed v && isWellFormed b
| Expr.const _ _ _         => true
| Expr.bvar _ _            => true
| Expr.sort _ _            => true
| Expr.lit _ _             => true
| Expr.mvar mvarId _       =>
  let mvarDecl := mctx.getDecl mvarId;
  if mvarDecl.lctx.isSubPrefixOf lctx then true
  else match mctx.getExprAssignment? mvarId with
    | none   => false
    | some v => isWellFormed v
| Expr.fvar fvarId _       => lctx.contains fvarId
| Expr.localE _ _ _ _      => unreachable!


namespace LevelMVarToParam

structure Context :=
(paramNamePrefix : Name)
(alreadyUsedPred : Name → Bool)

structure State :=
(mctx         : MetavarContext)
(paramNames   : Array Name := #[])
(nextParamIdx : Nat)

abbrev M := ReaderT Context $ StateM State

partial def mkParamName : Unit → M Name
| _ => do
  ctx ← read;
  s ← get;
  let newParamName := ctx.paramNamePrefix.appendIndexAfter s.nextParamIdx;
  if ctx.alreadyUsedPred newParamName then do
    modify $ fun s => { nextParamIdx := s.nextParamIdx + 1, .. s};
    mkParamName ()
  else do
    modify $ fun s => { nextParamIdx := s.nextParamIdx + 1, paramNames := s.paramNames.push newParamName, .. s};
    pure newParamName

partial def visitLevel : Level → M Level
| u@(Level.succ v _)      => do v ← visitLevel v; pure (u.updateSucc v rfl)
| u@(Level.max v₁ v₂ _)   => do v₁ ← visitLevel v₁; v₂ ← visitLevel v₂; pure (u.updateMax v₁ v₂ rfl)
| u@(Level.imax v₁ v₂ _)  => do v₁ ← visitLevel v₁; v₂ ← visitLevel v₂; pure (u.updateIMax v₁ v₂ rfl)
| u@(Level.zero _)        => pure u
| u@(Level.param _ _)     => pure u
| u@(Level.mvar mvarId _) => do
  s ← get;
  match s.mctx.getLevelAssignment? mvarId with
  | some v => visitLevel v
  | none   => do
    p ← mkParamName ();
    let p := mkLevelParam p;
    modify $ fun s => { mctx := s.mctx.assignLevel mvarId p, .. s };
    pure p

@[inline] private def visit (f : Expr → M Expr) (e : Expr) : M Expr :=
if e.hasLevelMVar then f e else pure e

partial def main : Expr → M Expr
| e@(Expr.proj _ _ s _)    => do s ← visit main s; pure (e.updateProj! s)
| e@(Expr.forallE _ d b _) => do d ← visit main d; b ← visit main b; pure (e.updateForallE! d b)
| e@(Expr.lam _ d b _)     => do d ← visit main d; b ← visit main b; pure (e.updateLambdaE! d b)
| e@(Expr.letE _ t v b _)  => do t ← visit main t; v ← visit main v; b ← visit main b; pure (e.updateLet! t v b)
| e@(Expr.app f a _)       => do f ← visit main f; a ← visit main a; pure (e.updateApp! f a)
| e@(Expr.mdata _ b _)     => do b ← visit main b; pure (e.updateMData! b)
| e@(Expr.const _ us _)    => do us ← us.mapM visitLevel; pure (e.updateConst! us)
| e@(Expr.sort u _)        => do u ← visitLevel u; pure (e.updateSort! u)
| e                        => pure e

end LevelMVarToParam

structure UnivMVarParamResult :=
(mctx          : MetavarContext)
(newParamNames : Array Name)
(nextParamIdx  : Nat)
(expr          : Expr)

def levelMVarToParam (mctx : MetavarContext) (alreadyUsedPred : Name → Bool) (e : Expr) (paramNamePrefix : Name := `u) (nextParamIdx : Nat := 1)
    : UnivMVarParamResult :=
let (e, s) := LevelMVarToParam.main e { paramNamePrefix := paramNamePrefix, alreadyUsedPred := alreadyUsedPred } { mctx := mctx, nextParamIdx := nextParamIdx };
{ mctx          := mctx,
  newParamNames := s.paramNames,
  nextParamIdx  := s.nextParamIdx,
  expr          := e }

end MetavarContext
end Lean
