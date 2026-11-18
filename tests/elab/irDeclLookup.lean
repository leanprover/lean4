module

import Lean
meta import Lean.Compiler.IR.Checker

/-!
Regression tests for #16045: IR checking resolves forward references and gives the current batch
precedence over the environment, preserving missing-declaration and application-arity diagnostics.
-/

open Lean IR

private def target (name : Name) (arity : Nat) : Decl :=
  .fdecl name (Array.ofFn fun i : Fin arity => { x := ⟨i⟩, borrow := false, ty := .object })
    .object .unreachable { maxJp := 0, maxVar := arity }

private def caller (name callee : Name) (numArgs : Nat) (partialApp := false) : Decl :=
  let args := Array.replicate numArgs Arg.erased
  let value : IR.Expr := if partialApp then .pap callee args else .fap callee args
  .fdecl name #[] .object (.vdecl ⟨0⟩ .object value (.ret (.var ⟨0⟩)))
    { maxJp := 0, maxVar := 1 }

private def expectFailure (message : String) (action : CoreM Unit) : CoreM Unit := do
  let error? ← try action; pure none catch e => pure (some e)
  let some error := error? | throwError "expected IR checker failure containing: {message}"
  let actual ← error.toMessageData.toString
  unless actual.contains message do
    throwError "unexpected IR checker failure: {actual}"

run_meta do
  checkDecls #[]
  checkDecls #[caller `forward `later 1, target `later 1]
  checkDecls #[caller `mutualA `mutualB 0, caller `mutualB `mutualA 0]
  checkDecls #[caller `self `self 0]
  checkDecls #[caller `partialCaller `later 0 true, target `later 1]

  IR.addDecl (target `environmentOnly 1)
  checkDecls #[caller `fallback `environmentOnly 1]

  IR.addDecl (target `shadowed 1)
  let batch := #[caller `batchCaller `shadowed 2, target `shadowed 2]
  checkDecls batch
  IR.checkDecl batch batch[0]!
  checkDecls #[caller `unchangedEnvironment `shadowed 1]

  -- Duplicate names resolve to the first declaration in the batch.
  checkDecls #[caller `duplicateCaller `duplicate 0, target `duplicate 0, target `duplicate 1]
  expectFailure "incorrect number of arguments to 'duplicate', 0 provided, 1 expected" do
    checkDecls #[caller `duplicateCaller `duplicate 0, target `duplicate 1, target `duplicate 0]

  expectFailure "depends on declaration 'missingDecl', which has no executable code" do
    checkDecls #[caller `missingCaller `missingDecl 0]
  expectFailure "incorrect number of arguments to 'later', 0 provided, 1 expected" do
    checkDecls #[caller `badFull `later 0, target `later 1]
  expectFailure "too many arguments to partial application 'later', num. args: 1, arity: 1" do
    checkDecls #[caller `badPartial `later 1 true, target `later 1]
  expectFailure "incorrect number of arguments to 'environmentOnly', 0 provided, 1 expected" do
    checkDecls #[caller `badFallback `environmentOnly 0]
