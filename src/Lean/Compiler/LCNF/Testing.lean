/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PrettyPrinter

namespace Lean.Compiler.LCNF

partial def Code.containsConst (constName : Name) (code : Code) : Bool :=
  match code with
  | .let decl k => goExpr decl.value || containsConst constName k
  | .fun decl k => containsConst constName decl.value || containsConst constName k
  | .jp decl k => containsConst constName decl.value || containsConst constName k
  | .jmp _ args => args.any goExpr
  | .cases cs => cs.alts.any goAlt
  | .return .. | .unreach .. => false
where
  goAlt (alt : Alt) : Bool :=
    match alt with
    | .alt _ _ body | .default body => containsConst constName body
  goExpr (e : Expr) : Bool :=
    match e with
    | .const name .. => name == constName
    | .app fn arg .. => goExpr fn || goExpr arg
    | .lam _ _ body .. => goExpr body
    | .letE _ _ value body .. => goExpr value || goExpr body
    | .proj _ _ struct .. => goExpr struct
    | _ => false

namespace Testing

/--
If `property` is `false` throw an exception with `msg`.
-/
def assert (property : Bool) (msg : String) : CompilerM Unit := do
  unless property do
    throwError msg

/--
Install an assertion pass right after a pass.
-/
def assertConditionAfter (passUnderTestName : Name) (testName : Name) (assertion : Array Decl → CompilerM Unit) : PassInstaller :=
  let assertion := {
    name := testName
    run := fun decls => do
      trace[Compiler.test] s!"Starting post condition test {testName} for {passUnderTestName}"
      assertion decls
      trace[Compiler.test] s!"Post condition test {testName} for {passUnderTestName} successful"
      return decls
  }
  .installAfter passUnderTestName assertion

def assertForEachDeclAfterM (passUnderTestName : Name) (testName : Name) (assertion : Decl → CompilerM Unit) : PassInstaller :=
  assertConditionAfter passUnderTestName testName (·.forM assertion)

def assertForEachDeclAfter (passUnderTestName : Name) (testName : Name) (assertion : Decl → Bool) (msg : String) : PassInstaller :=
  assertConditionAfter passUnderTestName testName (Array.forM (fun decl => assert (assertion decl) msg))

/--
Replace a pass with a wrapper one that allows the user to provide an assertion which
takes into account both the declarations that were sent to and produced by the pass
under test.
-/
def assertConditionAround (passUnderTestName : Name) (testName : Name) (assertion : Array Decl → Array Decl → CompilerM Unit) : PassInstaller :=
  let assertion := fun passUnderTest => pure {
    name := passUnderTestName
    run := fun decls => do
      trace[Compiler.test] s!"Starting condition test {testName} for {passUnderTestName}"
      let newDecls ← passUnderTest.run decls
      assertion decls newDecls
      trace[Compiler.test] s!"Condition test {testName} for {passUnderTestName} successful"
      return newDecls
  }
  .replacePass passUnderTestName assertion


private def throwFixPointError (err : String) (firstResult secondResult : Array Decl) : CompilerM Unit := do
  let mut err := err
  err := err ++ "Result after usual run:"
  let folder := fun err decl => do return err ++ s!"\n{←ppDecl decl}"
  err ← firstResult.foldlM (init := err) folder
  err := err ++ "Result after further run:"
  err ← secondResult.foldlM (init := err) folder
  throwError err

/--
Insert a pass after `passUnderTestName`, that ensures, that if
`passUnderTestName` is executed twice in a row, no change in the resulting
expression will occur, i.e. the pass is at a fix point.
-/
def assertIsAtFixPoint (passUnderTestName : Name) : PassInstaller where
  install passes :=  do
    let some idx := passes.findIdx? (·.name == passUnderTestName) | throwError s!"{passUnderTestName} not found in pass list"
    let passUnderTest := passes[idx]!
    let assertion : Pass := {
      name := passUnderTestName.append `isFixPoint
      run := fun decls => do
        trace[Compiler.test] s!"Running fixpoint test for {passUnderTestName}"
        let secondResult ← passUnderTest.run decls 
        if decls.size < secondResult.size then
          let err := s!"Pass {passUnderTestName} did not reach a fixpoint, it added declarations on further runs:\n"
          throwFixPointError err decls secondResult
        else if decls.size > secondResult.size then
          let err := s!"Pass {passUnderTestName} did not reach a fixpoint, it removed declarations on further runs:\n"
          throwFixPointError err decls secondResult
        else if decls != secondResult then
          let err := s!"Pass {passUnderTestName} did not reach a fixpoint, it either changed declarations or their order:\n"
          throwFixPointError err decls secondResult
        trace[Compiler.test] s!"Fixpoint test for {passUnderTestName} successful"
        return decls
    }
    return passes.insertAt (idx + 1) assertion

/--
Compare the overall sizes of the input and output of `passUnderTest` with `assertion`.
-/
def assertSizeM (passUnderTestName : Name) (testName : Name) (assertion : Nat → Nat → CompilerM Unit) : PassInstaller :=
  let sumDeclSizes := fun decls => decls.map Decl.size |>.foldl (init := 0) (· + ·)
  assertConditionAround passUnderTestName testName (fun inp out => assertion (sumDeclSizes inp) (sumDeclSizes out))

/--
Compare the overall sizes of the input and output of `passUnderTest` with `assertion`.
If `assertion inputSize outputSize` is `false` throw an exception with `msg`.
-/
def assertSize (passUnderTestName : Name) (testName : Name) (assertion : Nat → Nat → Bool) (msg : String) : PassInstaller :=
  assertSizeM passUnderTestName testName (fun beforeS afterS => Testing.assert (assertion afterS beforeS) msg)

/--
Assert that the overall size of the `Decl`s in the compilation pipeline does not change
after `passUnderTestName`.
-/
def assertPreservesSize (passUnderTestName : Name) (testName : Name) (msg : String) : PassInstaller :=
  assertSize passUnderTestName testName (· == ·) msg

/--
Assert that the overall size of the `Decl`s in the compilation pipeline gets reduced by `passUnderTestName`.
-/
def assertReducesSize (passUnderTestName : Name) (testName : Name) (msg : String) : PassInstaller :=
  assertSize passUnderTestName testName (· < ·) msg

/--
Assert that the overall size of the `Decl`s in the compilation pipeline gets reduced or stays unchanged
by `passUnderTestName`.
-/
def assertReducesOrPreservesSize (passUnderTestName : Name) (testName : Name) (msg : String) : PassInstaller :=
  assertSize passUnderTestName testName (· ≤ ·) msg

def assertDoesNotContainConstAfter (passUnderTestName : Name) (testName : Name) (constName : Name) (msg : String) : PassInstaller :=
  assertForEachDeclAfter passUnderTestName testName (fun decl => !decl.value.containsConst constName) msg

end Testing
end Lean.Compiler.LCNF
