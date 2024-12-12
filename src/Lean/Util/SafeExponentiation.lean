/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.CoreM

namespace Lean

register_builtin_option exponentiation.threshold : Nat := {
  defValue := 256
  descr    := "maximum value for \
  which exponentiation operations are safe to evaluate. When an exponent \
  is a value greater than this threshold, the exponentiation will not be evaluated, \
  and a warning will be logged. This helps to prevent the system from becoming \
  unresponsive due to excessively large computations."
}

/--
Returns `true` if `n` is `≤ exponentiation.threshold`. Otherwise,
reports a warning and returns `false`.
This method ensures there is at most one warning message of this kind in the message log.
-/
def checkExponent (n : Nat) : CoreM Bool := do
  let threshold := exponentiation.threshold.get (← getOptions)
  if n > threshold then
    if (← logMessageKind `unsafe.exponentiation) then
      logWarning s!"exponent {n} exceeds the threshold {threshold}, exponentiation operation was not evaluated, use `set_option {exponentiation.threshold.name} <num>` to set a new threshold"
    return false
  else
    return true

end Lean
