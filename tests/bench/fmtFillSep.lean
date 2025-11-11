import Lean.Data.Fmt.Basic

open Lean.Fmt

def fillSep (xs : Array String) : Doc := Id.run do
  let some hd := xs[0]?
    | return .text ""
  let mut r : Doc := .text hd
  for x in xs do
    r := Doc.either
      (Doc.joinUsing (.text " ") #[r, .text x])
      (Doc.joinUsing .hardNl #[r, .text x])
  return r

@[noinline]
def doc (n : Nat) : IO Doc := do
  let words ← IO.FS.readFile "fmtFillSepWords"
  let words := words.splitOn "\n" |>.take n |>.toArray
  return fillSep words

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
