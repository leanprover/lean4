/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.FEnv
/- The kernel adds checked constants with `Kernel.Environment.add` and `markQuotInit`, which are
private to `Lean.Environment` so that nothing else bypasses the kernel. -/
import all Lean.Environment

/-!
# InLean: adding a constant

The one place InLean writes a kernel environment: the private
`Kernel.Environment.add` (`addConst`), and the twin of `FEnv.push`.
-/

public section

namespace Lean.Kernel.InLean

open Lean

/-- Add a constant to a kernel environment, unchecked (`Kernel.Environment.add`). -/
def addConst (env : Kernel.Environment) (ci : ConstantInfo) : Kernel.Environment :=
  env.add ci

/-- Mark the quotient package as declared (the private `markQuotInit`). -/
def markQuot (env : Kernel.Environment) : Kernel.Environment :=
  env.markQuotInit

/-- Twin of `FEnv.push`. -/
def FEnv.push (fe : FEnv) (ci : ConstantInfo) : FEnv := { fe with env := addConst fe.env ci }

/-- Twin of `FEnv.pushAll`. -/
def FEnv.pushAll : List ConstantInfo → FEnv → FEnv
  | [], fe => fe
  | ci :: rest, fe => FEnv.pushAll rest (fe.push ci)

end Lean.Kernel.InLean
