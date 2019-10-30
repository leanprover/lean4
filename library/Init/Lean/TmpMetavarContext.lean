/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.MetavarContext

namespace Lean
/--
  Several procedures (e.g., type class resolution, simplifier) need
  to create metavariables that are needed for a short period of time.
  For example, when applying a simplification lemma such as
  ```
  forall x, f x x = x
  ```
  to a subterm `t`, we need need to check whether the term
  `t` is an instance of the pattern `f ?x ?x`, where `?x` is a fresh metavariable.
  That is, we need to find an assignment for `?x` such that `t`
  and `f ?x ?x` become definitionally equal. If the assignment is found,
  we replace the term `t` with the term assigned to `?x`. After that,
  we don't need the metavariable `?x` anymore. We don't want to
  use regular metavariables for this operation since we don't want
  to waste time declaring them at `MetavarContext`,
  then creating the term `f ?x ?x` with the newly created metavariable,
  and then performing the matching operation, and finally deleting `?x`.
  We avoid this overhead by using temporary metavariables.

  `TmpMetavarContext` implements `AbstractMetavarContext` for temporary metavariables.
  All temporary metavariables used to solve a particular problem (e.g., matching)
  share the same local context (field `mvarLCtx`), the type of a metavariable is stored in the
  field `mvarTypes`. The assignments are implemented using small arrays.
  We assume the number of temporary metavariables is usually small (< 1000),
  and their names store a small integer that is used to read the arrays.

  `TmpMetavarContext` also keeps a reference to the main `MetavarContext` used in the elaborator and
  tactic framework. -/
structure TmpMetavarContext :=
(mctx        : MetavarContext       := {})
(mvarLCtx    : LocalContext         := {})
(mvarTypes   : Array Expr           := #[])
(lAssignment : Array (Option Level) := #[])
(eAssignment : Array (Option Expr)  := #[])

def mkTmpMVarId (idx : Nat) :=
Name.mkNumeral `_tmp idx

def Name.isTmpMVarId : Name → Bool
| Name.mkNumeral `_tmp _ => true
| _                      => false

def Name.getTmpMVarIdx : Name → Nat
| Name.mkNumeral _ i => i
| _                  => panic! "expected a temporary metavariable name"

def Level.isTmpMVar : Level → Bool
| Level.mvar mvarId => mvarId.isTmpMVarId
| _                 => false

def Expr.isTmpMVar : Expr → Bool
| Expr.mvar mvarId => mvarId.isTmpMVarId
| _                => false

/--
  Create a temporary metavariable context with the following characteristics:
  - It contains `numLevelMVars` temporary `Level` metavariables
  - It contains `mvarTypes.size` temporary `Expr` metavariables
  - The temporary metavariable `i` has type `mvarTypes[i]`
  - All temporary metavariables have local context `mvarLCtx`

  `mctx` is the main metavariable context, and it is used to
  retrieve regular metavariable information.  -/
def mkTmpMetavarContext (mctx : MetavarContext) (mvarLCtx : LocalContext) (mvarTypes : Array Expr) (numLevelMVars : Nat) : TmpMetavarContext :=
{ mctx        := mctx,
  mvarLCtx    := mvarLCtx,
  mvarTypes   := mvarTypes,
  eAssignment := mkArray mvarTypes.size none,
  lAssignment := mkArray numLevelMVars none }

namespace TmpMetavarContext

instance : Inhabited TmpMetavarContext := ⟨{}⟩

def getLevelAssignment (m : TmpMetavarContext) (mvarId : Name) : Option Level :=
if mvarId.isTmpMVarId then
  m.lAssignment.get! mvarId.getTmpMVarIdx
else
  m.mctx.getLevelAssignment mvarId

def assignLevel (m : TmpMetavarContext) (mvarId : Name) (val : Level) : TmpMetavarContext :=
if mvarId.isTmpMVarId then
  { lAssignment := m.lAssignment.set! mvarId.getTmpMVarIdx val, .. m }
else
  { mctx := m.mctx.assignLevel mvarId val, .. }

def getExprAssignment (m : TmpMetavarContext) (mvarId : Name) : Option Expr :=
if mvarId.isTmpMVarId then
  m.eAssignment.get! mvarId.getTmpMVarIdx
else
  m.mctx.getExprAssignment mvarId

def assignExpr (m : TmpMetavarContext) (mvarId : Name) (val : Expr) : TmpMetavarContext :=
if mvarId.isTmpMVarId then
  { eAssignment := m.eAssignment.set! mvarId.getTmpMVarIdx val, .. m }
else
  { mctx := m.mctx.assignExpr mvarId val, .. }

def getDecl (m : TmpMetavarContext) (mvarId : Name) : MetavarDecl :=
if mvarId.isTmpMVarId then
  { userName := Name.anonymous, lctx := m.mvarLCtx, type := m.mvarTypes.get! mvarId.getTmpMVarIdx, synthetic := false }
else
  m.mctx.getDecl mvarId

instance isAbstractMetavarContext : AbstractMetavarContext TmpMetavarContext :=
{ empty                := {},
  isReadOnlyLevelMVar  := fun _ mvarId => !mvarId.isTmpMVarId,
  getLevelAssignment   := TmpMetavarContext.getLevelAssignment,
  assignLevel          := TmpMetavarContext.assignLevel,
  isReadOnlyExprMVar   := fun _ mvarId => !mvarId.isTmpMVarId,
  getExprAssignment    := TmpMetavarContext.getExprAssignment,
  assignExpr           := TmpMetavarContext.assignExpr,
  getDecl              := TmpMetavarContext.getDecl,
  -- TmpMetavarContext does not support delayed assignments or the creation of auxiliary metavariables.
  auxMVarSupport       := false,
  mkAuxMVar            := fun _ _ _ _ _ => panic! "TmpMetavarContex does not support the creation of auxiliary metavariables",
  assignDelayed        := fun _ _ _ _ _ => panic! "TmpMetavarContex does not support delayed assignments",
  eraseDelayed         := fun _ _ => panic! "TmpMetavarContex does not support delayed assignments",
  getDelayedAssignment := fun _ _ => none }

end TmpMetavarContext

end Lean
