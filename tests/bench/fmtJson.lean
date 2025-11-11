import Lean.Data.Fmt.Basic
import Lean.Data.Json

open Lean.Fmt

def hConcat (ds : List Doc) : Doc :=
  match ds with
  | [] => .failure
  | [d] => d
  | d :: ds =>
    ds.foldl (init := d) fun acc d => (Doc.flatten acc).concat d

def encloseSep (left right sep : Doc) (ds : List Doc) : Doc :=
  match ds with
  | [] => .concat left (.align right)
  | [d] => .join #[left, .align d, .align right]
  | d :: ds =>
    .concat
      (.either
        (hConcat (left :: (d :: ds).intersperse sep))
        (Doc.joinUsing .hardNl (Doc.concat left (.align d) :: ds.map (fun d => Doc.concat sep (.align d))).toArray))
      (.align right)

partial def pp (j : Lean.Json) : Doc :=
  match j with
  | .null => .text "null"
  | .bool false => .text "false"
  | .bool true => .text "true"
  | .num n => .text n.toString
  | .str s => .text s!"\"{s}\""
  | .arr a =>
    let a := a.map pp
    encloseSep (.text "[") (.text "]") (.text ",") a.toList
  | .obj kvPairs =>
    let kvPairs := kvPairs.toList.map fun (k, v) =>
      let k := .text s!"\"{k}\": "
      let v := pp v
      Doc.concat k (.align v)
    encloseSep (.text "{") (.text "}") (.text ",") kvPairs

def readJson : IO Lean.Json := do
  let c ← IO.FS.readFile "./lean/run/fmtJson1k.json"
  IO.ofExcept <| Lean.Json.parse c

@[noinline]
def doc : IO Doc := do
  let json ← IO.FS.readFile "fmtJson10k.json"
  let json ← IO.ofExcept <| Lean.Json.parse json
  return pp json

@[noinline]
def format (doc : Doc) : IO (Option String) := do
  return format? doc 80 100

def main (_ : List String) : IO Unit := do
  let d ← doc
  let startNs ← IO.monoNanosNow
  let r? ← format d
  let endNs ← IO.monoNanosNow
  let benchTime : Float := (endNs - startNs).toFloat / 1_000_000_000.0
  assert! r?.isSome
  IO.println s!"format: {benchTime}"
