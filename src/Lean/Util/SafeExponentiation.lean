/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.CoreM

public section

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
def checkExponent (n : Nat) (warning := true) : CoreM Bool := do
  let threshold ← getRecordedOption exponentiation.threshold
  if n > threshold then
    if (← pure warning <&&> logMessageKind `unsafe.exponentiation) then
      logWarning s!"exponent {n} exceeds the threshold {threshold}, exponentiation operation was not evaluated, use `set_option {exponentiation.threshold.name} <num>` to set a new threshold"
    return false
  else
    return true

register_builtin_option shiftLeft.threshold : Nat := {
  defValue := 65536
  descr    := "maximum shift amount for \
  which left shift operations are safe to evaluate. When a shift amount \
  is a value greater than this threshold, the left shift will not be evaluated, \
  and a warning will be logged. This helps to prevent the system from becoming \
  unresponsive due to excessively large computations."
}

/--
Returns `true` if the left shift `a <<< n` is safe to evaluate given the threshold `maxShift`:
`a` is `0`, or `n` is `≤ maxShift` and fits in 32 bits.

The runtime implementation of `Nat.shiftLeft` aborts the process when the shifted value is not `0`
and the shift amount does not fit in 32 bits. Thus, every procedure that evaluates a left shift of
literals whose shift amount is not bounded by a machine word size must use this function or
`checkShiftLeft`.
-/
def isSafeShiftLeft (a n maxShift : Nat) : Bool :=
  a == 0 || (n ≤ maxShift && n < UInt32.size)

/--
Returns `true` if `isSafeShiftLeft a n threshold`, where `threshold` is the value of the option
`shiftLeft.threshold`. Otherwise, reports a warning and returns `false`.
This method ensures there is at most one warning message of this kind in the message log.
-/
def checkShiftLeft (a n : Nat) (warning := true) : CoreM Bool := do
  if a == 0 then return true
  let threshold ← getRecordedOption shiftLeft.threshold
  if n > threshold then
    if (← pure warning <&&> logMessageKind `unsafe.shiftLeft) then
      logWarning s!"shift amount {n} exceeds the threshold {threshold}, left shift operation was not evaluated, use `set_option {shiftLeft.threshold.name} <num>` to set a new threshold"
    return false
  else if n ≥ UInt32.size then
    if (← pure warning <&&> logMessageKind `unsafe.shiftLeft) then
      logWarning s!"shift amount {n} does not fit in 32 bits, left shift operation was not evaluated"
    return false
  else
    return true

end Lean
