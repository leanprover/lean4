import Lean.Data.Fmt.Formatter
import Lean.Data.Json

open Lean.Fmt

def hConcat (ds : List Doc) : Doc :=
  match ds with
  | [] => .failure
  | [d] => d
  | d :: ds =>
    ds.foldl (init := d) fun acc d => (Doc.flattened acc).append d

def encloseSep (left right sep : Doc) (ds : List Doc) : Doc :=
  match ds with
  | [] => .append left (.aligned right)
  | [d] => .join #[left, .aligned d, .aligned right]
  | d :: ds =>
    .append
      (.either
        (hConcat (left :: (d :: ds).intersperse sep))
        (Doc.joinUsing .hardNl (Doc.append left (.aligned d) :: ds.map (fun d => Doc.append sep (.aligned d))).toArray))
      (.aligned right)

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
      Doc.append k (.aligned v)
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
