/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductives.Decl

/-!
# InLean: the entry points

`addDecl`, the twin of `Lean.Kernel.Environment.addDeclCore`: check a
`Lean.Declaration` with con-leche's checker (`Lean.Kernel.InLean.CheckerC`) and add
the constants it declares, as con-leche's fold step checks a record at the
view below it and then pushes what the record declares
(`ConLeche.Cached.Decls`, `declStep`).  `kernelWhnf` and
`kernelIsDefEq` are the twins of `Kernel.whnf`/`Kernel.isDefEq`.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-- Run a check from a fresh per-declaration state. -/
def runC (x : CheckCM α) : Except CheckError α :=
  match x.run {} with
  | .ok (a, _) => .ok a
  | .error e => .error e

/-- The kinds' checks, at a declaration's own environment. -/
def checkDeclKindC (μ : CheckMode) (cfg : Config) (fe : FEnv) : Declaration → CheckCM Added
  | .axiomDecl v => checkAxiomC μ cfg fe v
  | .defnDecl v => checkDefnC μ cfg fe v
  | .thmDecl v => checkThmC μ fe v
  | .opaqueDecl v => checkOpaqueC μ fe v
  | .mutualDefnDecl vs => checkMutualC μ fe vs
  | .quotDecl => checkQuotC fe
  | .inductDecl lps nparams types isUnsafe => checkInductiveC μ fe lps nparams types isUnsafe

/-- Twin of `basisNamesOk`, at what a declaration adds: an inductive
declaration's generated block under a pinned block's names must be that block
(`pinListOk`), up to its level parameters' names, and no other declaration may
take a reserved name; `Quot.sound` and the quotient package are compared with
their own pins.  An unsafe block takes no reserved name. -/
def basisNamesOk : Declaration → Added → Bool
  | .inductDecl _ _ _ isUnsafe, a =>
    let block := storedBlock a.consts
    match basisNameHit block with
    | some kind => !isUnsafe && pinListOk block kind.decls
    | none => block.all fun c => !reservedBasisNames.contains c.name
  | .axiomDecl v, _ => v.name == quotSoundName || !reservedBasisNames.contains v.name
  | .quotDecl, _ => true
  | .defnDecl v, _ => !reservedBasisNames.contains v.name
  | .thmDecl v, _ => !reservedBasisNames.contains v.name
  | .opaqueDecl v, _ => !reservedBasisNames.contains v.name
  | .mutualDefnDecl vs, _ => vs.all fun v => !reservedBasisNames.contains v.name

/-- Twin of `basisNamesError`. -/
def basisNamesError : Declaration → Added → CheckError
  | .inductDecl .., a =>
    let block := storedBlock a.consts
    match basisNameHit block with
    | some _ => .invalid "reserved basis name: the block is not the pinned one"
    | none => .invalid s!"reserved basis name in the block of \
        {(block.head?.map (·.name)).getD .anonymous}"
  | .axiomDecl v, _ | .defnDecl v, _ | .thmDecl v, _ | .opaqueDecl v, _ =>
    .invalid s!"reserved basis name {v.name}"
  | .quotDecl, _ => .invalid "reserved basis name"
  | .mutualDefnDecl vs, _ =>
    .invalid s!"reserved basis name {((vs.find? fun v => reservedBasisNames.contains v.name).map
      (·.name)).getD .anonymous}"

/-- A constant other than an axiom at `sorryAx`'s name.  At con-leche's axiom
policy (`coreAxioms` off) the name is hidden (`FEnv.sees`) and con-leche
installs nothing only for the axiom, so any other constant there is declined
(official's environments declare the axiom in `Init.Prelude`, so no stream
reaches this). -/
def sorryAxSquat (ci : ConstantInfo) : Bool :=
  ci.name == sorryAxName && !(ci matches .axiomInfo _)

/-- Check `decl` (twin of `declStep`: the `And` pin, then `checkDeclC`: the
kind's checks and the reserved names'), returning what it adds; at con-leche's
axiom policy, no constant but the axiom at `sorryAx`'s name (`sorryAxSquat`). -/
def checkDecl (cfg : Config) (env : Kernel.Environment) (decl : Declaration) :
    Except CheckError Added :=
  let fe : FEnv := { env, coreAxioms := cfg.coreAxioms, limits := cfg.limits }
  if !andPinOk decl then .error (.invalid "`And` must be the standard `And`") else
  runC do
    let a ← checkDeclKindC cfg.mode cfg fe decl
    unless basisNamesOk decl a do
      throw (basisNamesError decl a)
    if !cfg.coreAxioms && a.consts.any sorryAxSquat then
      throw (.notImplemented "a constant other than an axiom at `sorryAx`'s name")
    return a

/-- **Check `decl` and add the constants it declares** — the twin of
`Lean.Kernel.Environment.addDeclCore`.  A reject, a decline and an error
are each `Kernel.Exception.other`, the message prefixed `(InLean)` and, for a
decline, `declined:`; a resource limit is its own exception
(`CheckError.toKernelException`). -/
def addDecl (env : Kernel.Environment) (decl : Declaration) (cfg : Config := {}) :
    Except Kernel.Exception Kernel.Environment :=
  match checkDecl cfg env decl with
  | .ok a =>
    let env := a.consts.foldl addConst env
    .ok (if a.quot then markQuot env else env)
  | .error e => .error e.toKernelException

/-- The twin of `Kernel.whnf` (a closed term; full reduction). -/
def kernelWhnf (env : Kernel.Environment) (e : Expr) (cfg : Config := {}) :
    Except Kernel.Exception Expr :=
  match runC (opWhnf cfg.mode { env, coreAxioms := cfg.coreAxioms, limits := cfg.limits } 0 e) with
  | .ok r => .ok r
  | .error err => .error err.toKernelException

/-- The twin of `Kernel.isDefEq` (closed terms). -/
def kernelIsDefEq (env : Kernel.Environment) (a b : Expr) (cfg : Config := {}) :
    Except Kernel.Exception Bool :=
  match runC (opDefeq cfg.mode { env, coreAxioms := cfg.coreAxioms, limits := cfg.limits } 0 a b) with
  | .ok r => .ok r
  | .error err => .error err.toKernelException

end Lean.Kernel.InLean
