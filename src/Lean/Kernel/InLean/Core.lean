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

`addDecl` runs under the official kernel's limits (`Limits`): the core's nesting depth is bounded
by 16 times `maxRecDepth` (official `scope_rec_depth`), the numerals by `LEAN_NAT_MAX_SIZE`, and
the core asks its poll at every body it runs whether the cancellation token is set or the
heartbeats (allocations) since the kernel was entered exceed `maxHeartbeats` (`addDeclRuntime`).
A limit of `0` is none.  The poll also counts the unfoldings for the kernel's diagnostics.
`Kernel.whnf`, `Kernel.isDefEq` and `Kernel.check` run without the recursion and heartbeat
limits, as the official kernel's do.
-/

public section

namespace Lean.Kernel.InLean

open Lean

/-- Official `read_nat_size_env("LEAN_NAT_MAX_SIZE", 128 MB)`: the size bound on numerals, read
once at initialization; a value that is not a decimal numeral is the default. -/
builtin_initialize natMaxSizeEnv : Nat ← do
  let dflt := 128 * 1024 * 1024
  match ← IO.getEnv "LEAN_NAT_MAX_SIZE" with
  | some s => return s.toNat?.getD dflt
  | none => return dflt

/-- The configuration the kernel runs with inside core. -/
def coreConfig : Config :=
  { coreAxioms := true, uncertifiedNatOps := true, limits := { maxNatSize := natMaxSizeEnv } }

/-- The configuration of one `addDecl` run: `coreConfig` under the elaborator's recursion limit
(`0` is none) and the poll `poll`. -/
def addDeclConfig (maxRecDepth : USize) (poll : Option (Event → Option Limit)) : Config :=
  { coreConfig with
    limits := { coreConfig.limits with
      recDepth := if maxRecDepth == 0 then none else some (16 * maxRecDepth.toNat)
      poll } }

/-- **The poll on the runtime**: at a body, whether the cancellation token is set or the
heartbeats since `start` exceed `maxHeartbeats` (`0` is no limit); at an unfolding, the
diagnostics' count of the constant in `unfolds?`, when diagnostics are enabled. -/
def pollIO (start maxHeartbeats : Nat) (cancelTk? : Option IO.CancelToken)
    (unfolds? : Option (IO.Ref (Std.HashMap Name Nat))) : Event → BaseIO (Option Limit)
  | .unfold n => do
    if let some ref := unfolds? then
      ref.modify fun m => m.insert n (m.getD n 0 + 1)
    return none
  | .body _ => do
    if let some tk := cancelTk? then
      if ← tk.isSet then return some .interrupted
    if maxHeartbeats != 0 then
      if (← IO.getNumHeartbeats) - start > maxHeartbeats then return some .heartbeats
    return none

/-- The diagnostics' unfold counter of `env` with the counts `unfolds` added (official
`scoped_diagnostics::update`). -/
def addUnfolds (env : Kernel.Environment) (unfolds : Std.HashMap Name Nat) : Kernel.Environment :=
  let d := env.diagnostics
  let counter := unfolds.fold (init := d.unfoldCounter) fun m n c =>
    m.insert n ((m.find? n).getD 0 + c)
  { env with diagnostics := { d with unfoldCounter := counter } }

private unsafe def addDeclRuntimeUnsafe (env : Kernel.Environment) (maxHeartbeats : USize)
    (maxRecDepth : USize) (decl : Declaration) (cancelTk? : Option IO.CancelToken) :
    Except Kernel.Exception Kernel.Environment :=
  let diag := env.diagnostics.enabled
  if maxHeartbeats == 0 && cancelTk?.isNone && !diag then
    addDecl env decl (addDeclConfig maxRecDepth none)
  else unsafeBaseIO do
    let start ← IO.getNumHeartbeats
    let unfolds? ← if diag then some <$> IO.mkRef {} else pure none
    let poll := fun ev => unsafeBaseIO (pollIO start maxHeartbeats.toNat cancelTk? unfolds? ev)
    match addDecl env decl (addDeclConfig maxRecDepth (some poll)) with
    | .ok env' =>
      match unfolds? with
      | some ref => return .ok (addUnfolds env' (← ref.get))
      | none => return .ok env'
    | .error e => return .error e

/-- **`addDecl` under the elaborator's limits.**  In the logic there is no poll; compiled
(`addDeclRuntimeUnsafe`) it reads the runtime (`pollIO`): the cancellation token and the heartbeat
counter (from the kernel's entry), and it counts the unfoldings, which are then added to the new
environment's diagnostics when they are enabled.  The checker's soundness holds for any poll, and
the diagnostics are no constant. -/
@[implemented_by addDeclRuntimeUnsafe]
def addDeclRuntime (env : Kernel.Environment) (_maxHeartbeats : USize) (maxRecDepth : USize)
    (decl : Declaration) (_cancelTk? : Option IO.CancelToken) :
    Except Kernel.Exception Kernel.Environment :=
  addDecl env decl (addDeclConfig maxRecDepth none)

/-- `Kernel.Environment.addDeclCore` (`lean_add_decl`).  As the C++ kernel's `add_theorem`
(`sharecommon_persistent_fn`), a theorem's type and value are checked with their common subterms
shared (`ShareCommon.shareCommon'`, the identity in the logic), and the environment gets the
original declaration, not the shared terms.  Nothing else is shared here (the elaborator shares
definitions itself).  The checker's memo maps and comparisons go pointer first, so on a term whose
repeated subterms are different objects each copy is checked and compared on its own. -/
@[export lean_add_decl]
def addDeclExport (env : Kernel.Environment) (maxHeartbeats : USize) (maxRecDepth : USize)
    (decl : Declaration) (cancelTk? : Option IO.CancelToken) :
    Except Kernel.Exception Kernel.Environment :=
  match decl with
  | .thmDecl v =>
    let shared := ShareCommon.shareCommon' v
    match addDeclRuntime env maxHeartbeats maxRecDepth (.thmDecl shared) cancelTk? with
    | .ok env' => .ok { env.add (.thmInfo v) with diagnostics := env'.diagnostics }
    | .error e => .error e
  | _ => addDeclRuntime env maxHeartbeats maxRecDepth decl cancelTk?

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
  return env.updateBaseAfterKernelAdd kenv

/-- `Environment.addDeclWithoutChecking` (`lean_elab_add_decl_without_checking`). -/
@[export lean_elab_add_decl_without_checking]
def elabAddDeclWithoutCheckingExport (env : Lean.Environment) (decl : Declaration) :
    Except Kernel.Exception Lean.Environment := do
  let kenv ← addDeclWithoutCheckingExport env.toKernelEnv decl
  return env.updateBaseAfterKernelAdd kenv

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
  let fe : FEnv :=
    { env := env.toKernelEnv, coreAxioms := coreConfig.coreAxioms, limits := coreConfig.limits }
  match runC (do
      let (origs, news, backFrom, backTo, d) ← openLCtx lctx
      let r ← k fe d (es.map (·.replaceFVars origs news))
      return back backFrom backTo r) with
  | .ok r => .ok r
  | .error err => .error err.toKernelException

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
