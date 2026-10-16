import Lean.Fmt.Core.Formatter

open Lean.Fmt

-- Page width limit and optimality cutoff width used by this benchmark.
def width := 80
def cutoff := 100

abbrev BenchCost := DefaultCost width cutoff

def quadratic (n : Nat) : Doc τ :=
  if n = 0 then
    .text "line"
  else
    .maybeFlattened
      (Doc.joinUsing .nl #[quadratic (n - 1), .text "line"])

@[noinline]
def doc (n : Nat) : IO (Doc BenchCost) :=
  return quadratic n

@[noinline]
def format (doc : Doc BenchCost) : IO (Option String) := do
  return format? width cutoff doc (taintedResolution := true) |>.toOption.map (·.rendering)

def main (args : List String) : IO Unit := do
  let n := (args[0]!).toNat!
  let d ← doc n
  let startNs ← IO.monoNanosNow
  let r? ← format d
  let endNs ← IO.monoNanosNow
  let benchTime : Float := (endNs - startNs).toFloat / 1_000_000_000.0
  assert! r?.isSome
  IO.println s!"measurement: format {benchTime}"
