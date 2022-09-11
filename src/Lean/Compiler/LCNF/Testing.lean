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
  | .cases cs => cs.alts.any fun alt => containsConst constName alt.getCode
  | .return .. | .unreach .. => false
where
  goExpr (e : Expr) : Bool :=
    match e with
    | .const name .. => name == constName
    | .app fn arg .. => goExpr fn || goExpr arg
    | .lam _ _ body .. => goExpr body
    | .proj _ _ struct .. => goExpr struct
    | .letE .. => unreachable! -- not possible in LCNF
    | _ => false

namespace Testing

structure TestInstallerContext where
  passUnderTestName : Name
  testName : Name

structure TestContext where
  passUnderTest : Pass
  testName : Name

structure SimpleAssertionContext where
  decls : Array Decl

structure InOutAssertionContext where
  input : Array Decl
  output : Array Decl

abbrev TestInstallerM := ReaderM TestInstallerContext
abbrev TestInstaller := TestInstallerM PassInstaller

abbrev TestM := ReaderT TestContext CompilerM
abbrev SimpleAssertionM := ReaderT SimpleAssertionContext TestM
abbrev InOutAssertionM := ReaderT InOutAssertionContext TestM
abbrev SimpleTest := SimpleAssertionM Unit
abbrev InOutTest := InOutAssertionM Unit

def TestInstaller.install (x : TestInstaller) (passUnderTestName testName : Name) : PassInstaller :=
  x { passUnderTestName, testName }

def TestM.run (x : TestM α) (passUnderTest : Pass) (testName : Name) : CompilerM α :=
  x { passUnderTest, testName }

def SimpleAssertionM.run (x : SimpleAssertionM α) (decls : Array Decl) (passUnderTest : Pass) (testName : Name) : CompilerM α :=
  x { decls } { passUnderTest, testName }

def InOutAssertionM.run (x : InOutAssertionM α) (input output : Array Decl) (passUnderTest : Pass) (testName : Name) : CompilerM α :=
  x { input, output } { passUnderTest, testName }

def getTestName : TestM Name := do
  return (←read).testName

def getPassUnderTest : TestM Pass := do
  return (←read).passUnderTest

def getDecls : SimpleAssertionM (Array Decl) := do
  return (←read).decls

def getInputDecls : InOutAssertionM (Array Decl) := do
  return (←read).input

def getOutputDecls : InOutAssertionM (Array Decl) := do
  return (←read).output

/--
If `property` is `false` throw an exception with `msg`.
-/
def assert (property : Bool) (msg : String) : TestM Unit := do
  unless property do
    throwError msg

private def assertAfterTest (test : SimpleTest) : TestInstallerM (Pass → Pass) := do
  let testName := (←read).testName
  return fun passUnderTest => {
    phase := passUnderTest.phase
    name := testName
    run := fun decls => do
      trace[Compiler.test] s!"Starting post condition test {testName} for {passUnderTest.name} occurence {passUnderTest.occurence}"
      test.run decls passUnderTest testName
      trace[Compiler.test] s!"Post condition test {testName} for {passUnderTest.name} occurence {passUnderTest.occurence} successful"
      return decls
  }

/--
Install an assertion pass right after a specific occurence of a pass,
default is first.
-/
def assertAfter (test : SimpleTest) (occurence : Nat := 0): TestInstaller := do
  let passUnderTestName := (←read).passUnderTestName
  let assertion ← assertAfterTest test
  return .installAfter passUnderTestName assertion occurence

/--
Install an assertion pass right after each occurence of a pass.
-/
def assertAfterEachOccurence (test : SimpleTest) : TestInstaller := do
  let passUnderTestName := (←read).passUnderTestName
  let assertion ← assertAfterTest test
  return .installAfterEach passUnderTestName assertion

/--
Install an assertion pass right after a specific occurence of a pass,
default is first. The assertion operates on a per declaration basis.
-/
def assertForEachDeclAfter (assertion : Pass → Decl → Bool) (msg : String) (occurence : Nat := 0) : TestInstaller :=
  let assertion := do
    let pass ← getPassUnderTest
    (←getDecls).forM (fun decl => assert (assertion pass decl) msg)
  assertAfter assertion occurence

/--
Install an assertion pass right after the each occurence of a pass. The
assertion operates on a per declaration basis.
-/
def assertForEachDeclAfterEachOccurence (assertion : Pass → Decl → Bool) (msg : String) : TestInstaller :=
  assertAfterEachOccurence <| do
    let pass ← getPassUnderTest
    (←getDecls).forM (fun decl => assert (assertion pass decl) msg)

private def assertAroundTest (test : InOutTest) : TestInstallerM (Pass → Pass) := do
  let testName := (←read).testName
  return fun passUnderTest => {
    phase := passUnderTest.phase
    name := passUnderTest.name
    run := fun decls => do
      trace[Compiler.test] s!"Starting wrapper test {testName} for {passUnderTest.name} occurence {passUnderTest.occurence}"
      let newDecls ← passUnderTest.run decls
      test.run decls newDecls passUnderTest testName
      trace[Compiler.test] s!"Wrapper test {testName} for {passUnderTest.name} occurence {passUnderTest.occurence} successful"
      return newDecls
  }

/--
Replace a specific occurence, default is first, of a pass with a wrapper one that allows
the user to provide an assertion which takes into account both the
declarations that were sent to and produced by the pass under test.
-/
def assertAround (test : InOutTest) (occurence : Nat := 0) : TestInstaller := do
  let passUnderTestName := (←read).passUnderTestName
  let assertion ← assertAroundTest test
  return .replacePass passUnderTestName assertion occurence

/--
Replace all occurences of a pass with a wrapper one that allows
the user to provide an assertion which takes into account both the
declarations that were sent to and produced by the pass under test.
-/
def assertAroundEachOccurence (test : InOutTest) : TestInstaller := do
  let passUnderTestName := (←read).passUnderTestName
  let assertion ← assertAroundTest test
  return .replaceEachOccurence passUnderTestName assertion

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
def assertIsAtFixPoint : TestInstaller :=
  let test := do
    let passUnderTest ← getPassUnderTest
    let decls ← getDecls
    let secondResult ← passUnderTest.run decls
    if decls.size < secondResult.size then
      let err := s!"Pass {passUnderTest.name} did not reach a fixpoint, it added declarations on further runs:\n"
      throwFixPointError err decls secondResult
    else if decls.size > secondResult.size then
      let err := s!"Pass {passUnderTest.name} did not reach a fixpoint, it removed declarations on further runs:\n"
      throwFixPointError err decls secondResult
    else if decls != secondResult then
      let err := s!"Pass {passUnderTest.name} did not reach a fixpoint, it either changed declarations or their order:\n"
      throwFixPointError err decls secondResult
  assertAfterEachOccurence test

/--
Compare the overall sizes of the input and output of `passUnderTest` with `assertion`.
If `assertion inputSize outputSize` is `false` throw an exception with `msg`.
-/
def assertSize (assertion : Nat → Nat → Bool) (msg : String) : TestInstaller :=
  let sumDeclSizes := fun decls => decls.map Decl.size |>.foldl (init := 0) (· + ·)
  let assertion := (fun inputS outputS => Testing.assert (assertion inputS outputS) s!"{msg}: input size {inputS} output size {outputS}")
  assertAroundEachOccurence (do assertion (sumDeclSizes (←getInputDecls)) (sumDeclSizes (←getOutputDecls)))

/--
Assert that the overall size of the `Decl`s in the compilation pipeline does not change
after `passUnderTestName`.
-/
def assertPreservesSize (msg : String) : TestInstaller :=
  assertSize (· == ·) msg

/--
Assert that the overall size of the `Decl`s in the compilation pipeline gets reduced by `passUnderTestName`.
-/
def assertReducesSize (msg : String) : TestInstaller :=
  assertSize (· > ·) msg

/--
Assert that the overall size of the `Decl`s in the compilation pipeline gets reduced or stays unchanged
by `passUnderTestName`.
-/
def assertReducesOrPreservesSize (msg : String) : TestInstaller :=
  assertSize (· ≥ ·) msg

/--
Assert that the pass under test produces `Decl`s that do not contain
`Expr.const constName` in their `Code.let` values anymore.
-/
def assertDoesNotContainConstAfter (constName : Name) (msg : String) : TestInstaller :=
  assertForEachDeclAfterEachOccurence (fun _ decl => !decl.value.containsConst constName) msg

end Testing
end Lean.Compiler.LCNF
