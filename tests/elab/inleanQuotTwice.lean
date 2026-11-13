import Lean

/-!
A quotient declaration in an environment whose quotient package is already
initialized adds nothing and succeeds, as in the C++ kernel's
`environment::add_quot`. `Lean.Replay` (and so `leanchecker`) sends one
`quotDecl` for each of the four quotient constants to the kernel.
-/

open Lean

run_meta do
  let kenv := (← getEnv).toKernelEnv
  let count (e : Kernel.Environment) : Nat := e.constants.map₂.toList.length
  match kenv.addDecl {} .quotDecl with
  | .error e => throwError "a second quotient declaration failed: {e.toMessageData {}}"
  | .ok kenv' =>
    unless count kenv == count kenv' do
      throwError "a second quotient declaration added constants"
    unless (kenv'.find? ``Quot.mk).isSome do
      throwError "Quot.mk is missing"
