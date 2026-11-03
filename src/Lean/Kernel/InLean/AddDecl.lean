/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductive
/- The kernel adds checked constants with `Kernel.Environment.add`, `markQuotInit` and
`Environment.updateBaseAfterKernelAdd`, which are private to `Lean.Environment` so that nothing
else bypasses the kernel. -/
import all Lean.Environment

/-!
# InLean: the entry points

Task #451.  `addDecl`, the twin of `Lean.Kernel.Environment.addDeclCore`:
check a `Lean.Declaration` with con-leche's checker (`InLean/Decl.lean`)
and add the constants it declares.  `kernelWhnf` and `kernelIsDefEq` are the twins
of `Kernel.whnf`/`Kernel.isDefEq`.

Every declaration kind is InLean's own: inductive declarations go to
`InLean/Inductive.lean` (lane B), which produces the inductive types',
constructors' and recursors' constants itself.
-/

public section

namespace Lean.Kernel.InLean

open Lean

/-- Add a constant to a kernel environment, unchecked (`Kernel.Environment.add`). -/
def addConst (env : Kernel.Environment) (ci : ConstantInfo) : Kernel.Environment :=
  env.add ci

/-- The InLean configuration: the mode (verified by default). -/
structure Config where
  mode : CheckMode := .verified
  /-- measurement probe, see `Ctx.probeNoMemo` -/
  probeNoMemo : String := ""
  /-- the axiom policy, see `Ctx.coreAxioms` -/
  coreAxioms : Bool := false
  /-- STOPGAP, see `Ctx.uncertifiedNatOps` -/
  uncertifiedNatOps : Bool := false

/-- Run a check in a fresh per-declaration state. -/
def runM (env : Kernel.Environment) (x : M α) (probe : String := "")
    (coreAxioms : Bool := false) (uncertifiedNatOps : Bool := false) : Except Err α :=
  match (x.run { env, probeNoMemo := probe, coreAxioms, uncertifiedNatOps }).run {} with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-- Check `decl`, returning what it adds. -/
def checkDecl (cfg : Config) (env : Kernel.Environment) (decl : Declaration) :
    Except Err Added :=
  let μ := cfg.mode
  runM env (do
    match decl with
    | .axiomDecl v => checkAxiom μ v
    | .defnDecl v => checkDefn μ addConst v
    | .thmDecl v => checkThm μ v
    | .opaqueDecl v => checkOpaque μ addConst v
    | .mutualDefnDecl vs => checkMutual μ addConst vs
    | .quotDecl => checkQuot
    | .inductDecl lps nparams types isUnsafe =>
      Ind.checkInductive μ addConst lps nparams types isUnsafe)
    cfg.probeNoMemo cfg.coreAxioms cfg.uncertifiedNatOps

/-- **Check `decl` and add the constants it declares** — the twin of
`Lean.Kernel.Environment.addDeclCore`.  A reject, a decline and an
internal error are all `Kernel.Exception.other` (ruling 7), the message
prefixed `(InLean)` and, for a decline, `declined:`. -/
def addDecl (env : Kernel.Environment) (decl : Declaration) (cfg : Config := {}) :
    Except Kernel.Exception Kernel.Environment :=
  match checkDecl cfg env decl with
  | .ok a =>
    let env := a.consts.foldl addConst env
    .ok (if a.quot then env.markQuotInit else env)
  | .error e => .error (.other e.toString)

/-- The twin of `Kernel.whnf` (a closed term; full reduction). -/
def kernelWhnf (env : Kernel.Environment) (e : Expr) (cfg : Config := {}) : Except Kernel.Exception Expr :=
  match runM env (InLean.whnf cfg.mode 0 e) with
  | .ok r => .ok r
  | .error err => .error (.other err.toString)

/-- The twin of `Kernel.isDefEq` (closed terms). -/
def kernelIsDefEq (env : Kernel.Environment) (a b : Expr) (cfg : Config := {}) :
    Except Kernel.Exception Bool :=
  match runM env (InLean.defeq cfg.mode 0 a b) with
  | .ok r => .ok r
  | .error err => .error (.other err.toString)

/-! ## The kernel's entry points in core

The C++ kernel's `extern "C"` functions, implemented here by `@[export]` with
the same signatures as their `@[extern]` declarations in `Lean.Environment`
(the `@&` borrow annotations were dropped from those declarations: an `@[export]` function takes owned arguments).  In core the axiom policy is the official
kernel's (`Config.coreAxioms := true`): every axiom is accepted and `sorryAx`
may be used.

Not honoured: `maxHeartbeats`, `maxRecDepth` and the cancellation token are
accepted and ignored (InLean has no heartbeat counter, no recursion-depth
guard beyond the native stack, and no interruption check). -/

/-- The configuration InLean runs with inside core. -/
def coreConfig : Config := { coreAxioms := true, uncertifiedNatOps := true }  -- STOPGAP flag

/-- `Kernel.Environment.addDeclCore` (`lean_add_decl`). -/
@[export lean_add_decl]
def addDeclExport (env : Kernel.Environment) (_maxHeartbeats : USize) (_maxRecDepth : USize)
    (decl : Declaration) (_cancelTk? : Option IO.CancelToken) :
    Except Kernel.Exception Kernel.Environment :=
  addDecl env decl coreConfig

/-- The constants a non-inductive, non-quotient declaration adds, unchecked. -/
def declConsts : Declaration → Option (List ConstantInfo)
  | .axiomDecl v => some [.axiomInfo v]
  | .defnDecl v => some [.defnInfo v]
  | .thmDecl v => some [.thmInfo v]
  | .opaqueDecl v => some [.opaqueInfo v]
  | .mutualDefnDecl vs => some (vs.map .defnInfo)
  | .quotDecl | .inductDecl .. => none

/-- `Kernel.Environment.addDeclWithoutChecking` (`lean_add_decl_without_checking`):
the declaration's constants unchecked; a quotient or inductive declaration still
runs the checker, which is what generates its constants. -/
@[export lean_add_decl_without_checking]
def addDeclWithoutCheckingExport (env : Kernel.Environment) (decl : Declaration) :
    Except Kernel.Exception Kernel.Environment :=
  match declConsts decl with
  | some cs => .ok (cs.foldl addConst env)
  | none => addDecl env decl coreConfig

/-- `Environment.addDeclCheck` (`lean_elab_add_decl`): the kernel step on the elab
environment's kernel environment, then the elab environment updated. -/
@[export lean_elab_add_decl]
def elabAddDeclExport (env : Lean.Environment) (maxHeartbeats : USize) (maxRecDepth : USize)
    (decl : Declaration) (cancelTk? : Option IO.CancelToken) :
    Except Kernel.Exception Lean.Environment := do
  let kenv ← addDeclExport env.toKernelEnv maxHeartbeats maxRecDepth decl cancelTk?
  return env.updateBaseAfterKernelAdd kenv decl

/-- `Environment.addDeclWithoutChecking` (`lean_elab_add_decl_without_checking`). -/
@[export lean_elab_add_decl_without_checking]
def elabAddDeclWithoutCheckingExport (env : Lean.Environment) (decl : Declaration) :
    Except Kernel.Exception Lean.Environment := do
  let kenv ← addDeclWithoutCheckingExport env.toKernelEnv decl
  return env.updateBaseAfterKernelAdd kenv decl

/-- Open a local context for InLean: each local declaration in order becomes an
interned free variable at its depth (a `let` local is replaced by its value, as the
official kernel's `whnf_fvar` would unfold it).  Returns the substitution
(original fvars ↦ InLean terms), the interned fvars with their originals (to map
results back), and the depth reached. -/
def openLCtx (lctx : LocalContext) :
    M (Array Expr × Array Expr × Array Expr × Array Expr × Nat) := do
  let mut origs : Array Expr := #[]
  let mut news : Array Expr := #[]
  let mut backFrom : Array Expr := #[]
  let mut backTo : Array Expr := #[]
  let mut d := 0
  for decl? in lctx.decls do
    let some decl := decl? | continue
    if decl.isImplementationDetail then continue
    let ty := decl.type.replaceFVars origs news
    match decl.value? with
    | some v =>
      origs := origs.push decl.toExpr
      news := news.push (v.replaceFVars origs.pop news)
    | none =>
      let fv ← mkFVar d ty
      origs := origs.push decl.toExpr
      news := news.push fv
      backFrom := backFrom.push fv
      backTo := backTo.push decl.toExpr
      d := d + 1
  return (origs, news, backFrom, backTo, d)

/-- Run `k` on `e`'s InLean form in the opened `lctx`, mapping the result back. -/
def withLCtx (env : Lean.Environment) (lctx : LocalContext) (es : Array Expr)
    (k : Nat → Array Expr → M α) : Except Kernel.Exception α :=
  match runM env.toKernelEnv (do
      let (origs, news, _, _, d) ← openLCtx lctx
      k d (es.map (·.replaceFVars origs news))) ""
      coreConfig.coreAxioms coreConfig.uncertifiedNatOps with
  | .ok r => .ok r
  | .error err => .error (.other err.toString)

/-- Map an InLean result back to `lctx`'s free variables. -/
def closeLCtx (lctx : LocalContext) (k : Nat → Array Expr → M Expr) :
    Nat → Array Expr → M Expr := fun d es => do
  let r ← k d es
  let (_, _, backFrom, backTo, _) ← openLCtx lctx
  return r.replaceFVars backFrom backTo

/-- `Kernel.isDefEq` (`lean_kernel_is_def_eq`). -/
@[export lean_kernel_is_def_eq]
def kernelIsDefEqExport (env : Lean.Environment) (lctx : LocalContext) (a b : Expr) :
    Except Kernel.Exception Bool :=
  withLCtx env lctx #[a, b] fun d es => defeq coreConfig.mode d es[0]! es[1]!

/-- `Kernel.whnf` (`lean_kernel_whnf`). -/
@[export lean_kernel_whnf]
def kernelWhnfExport (env : Lean.Environment) (lctx : LocalContext) (a : Expr) :
    Except Kernel.Exception Expr :=
  withLCtx env lctx #[a] (closeLCtx lctx fun d es => whnf coreConfig.mode d es[0]!)

/-- `Kernel.check` (`lean_kernel_check`): the full-grade type of `a`. -/
@[export lean_kernel_check]
def kernelCheckExport (env : Lean.Environment) (lctx : LocalContext) (a : Expr) :
    Except Kernel.Exception Expr :=
  withLCtx env lctx #[a] (closeLCtx lctx fun d es => infer coreConfig.mode d es[0]!)

end Lean.Kernel.InLean
