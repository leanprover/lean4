module

prelude

public import Lean.Elab.Tactic.Conv.Basic
public import Lean.Meta.Sym.Simp.Debug
public import Lean.Meta.Basic

public section

open Lean.Meta
namespace Lean.Elab.Tactic.Conv

@[builtin_tactic Lean.Parser.Tactic.Conv.cbv] def evalCbv : Tactic := fun _ => withMainContext do
  let lhs ← getLhs
  let startTime ← IO.monoNanosNow
  let res ← Lean.Meta.Sym.runCbv lhs
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  if let .step e proof _  := res then
    updateLhs e proof
    let startTime ← IO.monoNanosNow
    checkWithKernel (proof)
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    trace[Meta.Tactic] "perf: {ms}, {kernelMs}"


end Lean.Elab.Tactic.Conv
