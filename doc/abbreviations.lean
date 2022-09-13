import Lean.Data.HashMap
import Lean.Data.Json

open Std (HashMap)
open Lean (Json)

def readJSonObject (data: String): Json :=
  let e := Json.parse data
  match e with
  | Except.error msg => Json.null
  | Except.ok j => j

def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '|' => acc ++ "\\|"
    | c => acc ++ toString c

partial def formatMarkdown (j: Json): String :=
  let header := "| Abbreviation | Unicode Characters |\n"
            ++  "|--------------|--------------------|\n"

  match j with
  | .null => "null"
  | .bool b => toString b
  | .num n => toString n
  | .str s => s
  | .arr _ => "Error: unexpected array type"
  | .obj kvs => kvs.fold (fun acc k j => acc ++ "| " ++ (escape k) ++ " | " ++ (formatMarkdown j |> escape) ++ "|\n") header


def main (args : List String) : IO Unit := do
  if args.length < 2 then
    IO.println "Usage: abbreviations <json_file> <markdown_file>"
    IO.println "Converts given json to formatted markdown"
    return

  let fileName := args[0]!
  let output := args[1]!
  let data ← IO.FS.readFile fileName
  let j := readJSonObject data
  let md := formatMarkdown j
  IO.FS.writeFile output md
