/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductives.Decl
/- The core entry points update the elaborator's environment with the private
`Environment.updateBaseAfterKernelAdd`. -/
import all Lean.Environment

/-!
# InLean: the entry points

`addDecl`, the twin of `Lean.Kernel.Environment.addDeclCore`: check a
`Lean.Declaration` with con-leche's checker (`Lean/Kernel/InLean/CheckerC.lean`) and add
the constants it declares, as con-leche's fold step checks a record at the
view below it and then pushes what the record declares
(`ConLeche/Cached/Decls.lean`, `declStep`).  `kernelWhnf` and
`kernelIsDefEq` are the twins of `Kernel.whnf`/`Kernel.isDefEq`.
-/

public section

namespace Lean.Kernel.InLean

open Lean

/-- Run a check from a fresh per-declaration state. -/
def runC (x : CheckCM α) : Except CheckError α :=
  match x.run {} with
  | .ok (a, _) => .ok a
  | .error e => .error e

/-- Check `decl` (twin of `declStep`: the `And` pin, then `checkDeclStepC`),
returning what it adds. -/
def checkDecl (cfg : Config) (env : Kernel.Environment) (decl : Declaration) :
    Except CheckError Added :=
  let μ := cfg.mode
  let fe : FEnv := { env, coreAxioms := cfg.coreAxioms }
  if !andPinOk decl then .error (.invalid "`And` must be the standard `And`") else
  runC do
    match decl with
    | .axiomDecl v => checkAxiomC μ cfg fe v
    | .defnDecl v => checkDefnC μ cfg fe v
    | .thmDecl v => checkThmC μ fe v
    | .opaqueDecl v => checkOpaqueC μ fe v
    | .mutualDefnDecl vs => checkMutualC μ fe vs
    | .quotDecl => checkQuotC fe
    | .inductDecl lps nparams types isUnsafe => checkInductiveC μ fe lps nparams types isUnsafe

/-- **Check `decl` and add the constants it declares** — the twin of
`Lean.Kernel.Environment.addDeclCore`.  A reject, a decline and an error
are each `Kernel.Exception.other`, the message prefixed `(InLean)` and, for a
decline, `declined:`. -/
def addDecl (env : Kernel.Environment) (decl : Declaration) (cfg : Config := {}) :
    Except Kernel.Exception Kernel.Environment :=
  match checkDecl cfg env decl with
  | .ok a =>
    let env := a.consts.foldl addConst env
    .ok (if a.quot then markQuot env else env)
  | .error e => .error (.other e.toString)

/-- The twin of `Kernel.whnf` (a closed term; full reduction). -/
def kernelWhnf (env : Kernel.Environment) (e : Expr) (cfg : Config := {}) :
    Except Kernel.Exception Expr :=
  match runC (opWhnf cfg.mode { env, coreAxioms := cfg.coreAxioms } 0 e) with
  | .ok r => .ok r
  | .error err => .error (.other err.toString)

/-- The twin of `Kernel.isDefEq` (closed terms). -/
def kernelIsDefEq (env : Kernel.Environment) (a b : Expr) (cfg : Config := {}) :
    Except Kernel.Exception Bool :=
  match runC (opDefeq cfg.mode { env, coreAxioms := cfg.coreAxioms } 0 a b) with
  | .ok r => .ok r
  | .error err => .error (.other err.toString)

/-! ## The kernel's entry points in core

The kernel's entry points, by `@[export]` with the signatures of their `@[extern]` declarations
in `Lean.Environment`; those take owned arguments, as an `@[export]` function must.  Every axiom is
accepted and `sorryAx` may be used (`Config.coreAxioms`); the prelude is assumed good
(`Config.uncertifiedNatOps`).

Not honoured: `maxHeartbeats`, `maxRecDepth` and the cancellation token are accepted and ignored. -/

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
