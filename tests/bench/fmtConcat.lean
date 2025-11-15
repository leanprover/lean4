import Lean.Data.Fmt.Basic

open Lean.Fmt

def n := 1000 --0

def pp (n : Nat) : Doc :=
  if n = 0 then
    .text ""
  else
    .concat (pp (n - 1)) (.text "line")

@[noinline]
def doc (n : Nat) : IO Doc :=
  return pp n

@[noinline]
def format (doc : Doc) : IO (Option String) := do
  return format? doc 80 100

def main (args : List String) : IO Unit := do
  let n := (args[0]!).toNat!
  let d ← doc n
  let startNs ← IO.monoNanosNow
  let r? ← format d
  let endNs ← IO.monoNanosNow
  let benchTime : Float := (endNs - startNs).toFloat / 1_000_000_000.0
  assert! r?.isSome
  IO.println s!"format: {benchTime}"
