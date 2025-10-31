import Lean.Fmt.Core.Formatter

open Lean.Fmt

-- Page width limit and optimality cutoff width used by this benchmark.
def width := 80
def cutoff := 100

abbrev BenchCost := DefaultCost width cutoff

def fillSep (xs : Array String) : Doc τ := Id.run do
  let some hd := xs[0]?
    | return .text ""
  let mut r : Doc τ := .text hd
  for x in xs do
    r := Doc.either
      (Doc.joinUsing (.text " ") #[r, .text x])
      (Doc.joinUsing .hardNl #[r, .text x])
  return r

@[noinline]
def doc (n : Nat) : IO (Doc BenchCost) := do
  let words ← IO.FS.readFile "fmtFillSepWords"
  let words := words.splitOn "\n" |>.filter (!·.isEmpty) |>.toArray
  return fillSep <| Array.ofFn (n := n) fun i => words[i.val % words.size]!

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
