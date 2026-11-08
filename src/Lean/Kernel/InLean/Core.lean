/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.AddDecl
/- The core entry points update the elaborator's environment with the private
`Environment.updateBaseAfterKernelAdd`. -/
import all Lean.Environment

/-!
# InLean as the kernel

The kernel's entry points, by `@[export]` with the signatures of their `@[extern]` declarations
in `Lean.Environment`; those take owned arguments, as an `@[export]` function must.  Every axiom is
accepted and `sorryAx` may be used (`Config.coreAxioms`); the prelude is assumed good
(`Config.uncertifiedNatOps`).

Not honoured: `maxHeartbeats`, `maxRecDepth` and the cancellation token are accepted and ignored.
-/

public section

namespace Lean.Kernel.InLean

open Lean

/-- The configuration the kernel runs with inside core. -/
def coreConfig : Config := { coreAxioms := true, uncertifiedNatOps := true }

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

/-- `Kernel.Environment.addDeclWithoutChecking` (`lean_add_decl_without_checking`): the
declaration's constants unchecked; a quotient or inductive declaration still runs the checker,
which is what generates its constants. -/
@[export lean_add_decl_without_checking]
def addDeclWithoutCheckingExport (env : Kernel.Environment) (decl : Declaration) :
    Except Kernel.Exception Kernel.Environment :=
  match declConsts decl with
  | some cs => .ok (cs.foldl addConst env)
  | none => addDecl env decl coreConfig

/-- `Environment.addDeclCheck` (`lean_elab_add_decl`). -/
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

/-- Open a local context: each local declaration in order becomes an interned free variable at its
depth, a `let` local is replaced by its value.  Returns the substitution (original free variables
to the kernel's terms), the interned variables with their originals, and the depth reached. -/
def openLCtx (lctx : LocalContext) :
    CheckCM (Array Expr × Array Expr × Array Expr × Array Expr × Nat) := do
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
      news := news.push (v.replaceFVars origs news)
      origs := origs.push decl.toExpr
    | none =>
      let fv ← mkFVarM d ty
      origs := origs.push decl.toExpr
      news := news.push fv
      backFrom := backFrom.push fv
      backTo := backTo.push decl.toExpr
      d := d + 1
  return (origs, news, backFrom, backTo, d)

/-- Run `k` on the terms opened in `lctx`; `back` maps an expression result to `lctx`'s free
variables. -/
def withLCtx (env : Lean.Environment) (lctx : LocalContext) (es : Array Expr)
    (k : FEnv → Nat → Array Expr → CheckCM α) (back : Array Expr → Array Expr → α → α) :
    Except Kernel.Exception α :=
  let fe : FEnv := { env := env.toKernelEnv, coreAxioms := coreConfig.coreAxioms }
  match runC (do
      let (origs, news, backFrom, backTo, d) ← openLCtx lctx
      let r ← k fe d (es.map (·.replaceFVars origs news))
      return back backFrom backTo r) with
  | .ok r => .ok r
  | .error err => .error (.other err.toString)

/-- `Kernel.isDefEq` (`lean_kernel_is_def_eq`). -/
@[export lean_kernel_is_def_eq]
def kernelIsDefEqExport (env : Lean.Environment) (lctx : LocalContext) (a b : Expr) :
    Except Kernel.Exception Bool :=
  withLCtx env lctx #[a, b] (fun fe d es => opDefeq coreConfig.mode fe d es[0]! es[1]!)
    (fun _ _ r => r)

/-- `Kernel.whnf` (`lean_kernel_whnf`). -/
@[export lean_kernel_whnf]
def kernelWhnfExport (env : Lean.Environment) (lctx : LocalContext) (a : Expr) :
    Except Kernel.Exception Expr :=
  withLCtx env lctx #[a] (fun fe d es => opWhnf coreConfig.mode fe d es[0]!)
    (fun f t r => r.replaceFVars f t)

/-- `Kernel.check` (`lean_kernel_check`): the type of `a` at the full grade. -/
@[export lean_kernel_check]
def kernelCheckExport (env : Lean.Environment) (lctx : LocalContext) (a : Expr) :
    Except Kernel.Exception Expr :=
  withLCtx env lctx #[a] (fun fe d es => opInfer coreConfig.mode fe d es[0]!)
    (fun f t r => r.replaceFVars f t)

end Lean.Kernel.InLean
