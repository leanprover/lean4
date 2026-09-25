import Lean

/-!
Benchmark for #15312: realizing the equation lemmas of all functions in a mutual
`partial_fixpoint` block of `n` functions arranged in a ring, so that the block is one strongly
connected component.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Lean Elab Command

def numFuns : IO Nat := do
  return if (← IO.getEnv "TEST_BENCH") == some "1" then 100 else 5

def funName (i : Nat) : Ident := mkIdent (.mkSimple s!"f{i}")

elab "define_ring" : command => do
  let n ← numFuns
  let defs ← (List.range n).toArray.mapM fun i => do
    let callee := funName ((i + 1) % n)
    `(command|
      def $(funName i) (n : Nat) : Option Nat :=
        match n with
        | 0 => pure 0
        | m+1 => do
          let a ← $callee:ident m
          pure (a + 1)
      partial_fixpoint)
  elabCommand (← `(mutual $defs* end))

define_ring

run_meta do
  let n ← numFuns
  let t0 ← IO.monoNanosNow
  for i in [0:n] do
    let declName := (funName i).getId
    discard <| Meta.getEqnsFor? declName
    discard <| Meta.getUnfoldEqnFor? declName
  -- wait for the kernel to check the realized lemmas
  unless ((← getEnv).toKernelEnv.find? ``Nat).isSome do
    throwError "unreachable"
  let t1 ← IO.monoNanosNow
  if (← IO.getEnv "TEST_BENCH") == some "1" then
    IO.println s!"measurement: eqns {(t1 - t0).toFloat / 1e9} s"
