/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.FEnv
/- `Lean.Kernel.Environment.add` and `markQuotInit` are private to
`Lean.Environment`, so that nothing else adds a constant past the kernel;
`import all` makes them visible here.  The bodies that use them are
therefore not exposed (`public section`, not `@[expose]`). -/
import all Lean.Environment

/-!
# InLean: adding a constant

The one place InLean writes a kernel environment: core's private
`Kernel.Environment.add` (`addConst`), and the twin of `FEnv.push`.
-/

public section

namespace Lean.Kernel.InLean

open Lean

/-- Add a constant to a kernel environment, unchecked (core's private
`Kernel.Environment.add`). -/
def addConst (env : Kernel.Environment) (ci : ConstantInfo) : Kernel.Environment :=
  env.add ci

/-- Mark the quotient package as declared (core's private `markQuotInit`). -/
def markQuot (env : Kernel.Environment) : Kernel.Environment :=
  env.markQuotInit

/-- Is the quotient package declared (core's private `isQuotInit`, the flag
`markQuot` sets)? -/
def quotInitialized (env : Kernel.Environment) : Bool :=
  env.isQuotInit

/-- Twin of `FEnv.push`.  The literal flags are recomputed only at one of
their ten names (`litName`) and only while string literals are not yet
expandable, as master's push: every other push of a fresh name leaves them
as they are, so once the string-support constants are in, a push tests one
`Bool`. -/
def FEnv.push (fe : FEnv) (ci : ConstantInfo) : FEnv :=
  let env := addConst fe.env ci
  let upd := !fe.strLit && litName ci.name
  { fe with
    env := env
    natLit := if upd then natLitStoredBy (findAt env fe.safety fe.coreAxioms) else fe.natLit
    strLit := if upd then strLitStoredBy (findAt env fe.safety fe.coreAxioms) else fe.strLit }

/-- Twin of `FEnv.pushAll`. -/
def FEnv.pushAll : List ConstantInfo → FEnv → FEnv
  | [], fe => fe
  | ci :: rest, fe => FEnv.pushAll rest (fe.push ci)

end Lean.Kernel.InLean
