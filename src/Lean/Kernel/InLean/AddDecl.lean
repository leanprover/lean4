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

end Lean.Kernel.InLean
