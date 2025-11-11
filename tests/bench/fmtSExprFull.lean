import Lean.Data.Fmt.Basic

open Lean.Fmt

inductive SExpr where
  | leaf (v : String)
  | node (cs : List SExpr)

def asConcat (ds : List Doc) : Doc :=
  match ds with
  | [] => .failure
  | [d] => d
  | d :: ds =>
    .joinUsing (.text " ") (#[d] ++ ds.toArray.map Doc.align)

def pp (s : SExpr) : Doc :=
  match s with
  | .leaf v =>
    .text v
  | .node cs =>
    let cs := cs.map pp
    .join #[
      .text "(",
      .align (.either
        (.joinUsing .hardNl cs.toArray)
        (asConcat cs)),
      .align (.text ")")
    ]

def testExpr (n c : Nat) : SExpr × Nat :=
  if n = 0 then
    (.leaf (toString c), c + 1)
  else
    let (t1, c1) := testExpr (n - 1) c
    let (t2, c2) := testExpr (n - 1) c1
    (.node [t1, t2], c2)

@[noinline]
def doc (n : Nat) : IO Doc :=
  return pp (testExpr n 0).1

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
