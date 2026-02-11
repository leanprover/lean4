import Lean.Data.Lsp

def genModuleRefs (n : Nat) : IO Lean.Lsp.ModuleRefs := do
  let someLoc : Lean.Lsp.RefInfo.Location :=
    .mk ⟨⟨333, 444⟩, ⟨444, 555⟩⟩ <| some "A.Reasonably.Long.ParentDecl.Name.barfoo"

  let mut someUsages : Array Lean.Lsp.RefInfo.Location := #[]
  for _ in [0, 200] do
    someUsages := someUsages.push someLoc

  let someInfo : Lean.Lsp.RefInfo := {
      definition? := someLoc
      usages := someUsages
    }

  let mut refs : Lean.Lsp.ModuleRefs := .empty
  for i in *...n do
    let someIdent := Lean.Lsp.RefIdent.const s!"A.Reasonably.Long.Module.Name{i}" s!"A.Reasonably.Long.Declaration.Name.foobar{i}"
    refs := refs.insert someIdent someInfo

  return refs

@[noinline]
def compress (refs : Lean.Lsp.ModuleRefs) : IO String := do
  return Lean.Json.compress (Lean.ToJson.toJson refs)

@[noinline]
def parse (s : String) : IO (Except String Lean.Json) := do
  return Lean.Json.parse s

def main (args : List String) : IO Unit := do
  let n := (args[0]!).toNat!
  let refs ← genModuleRefs n
  let compressStartTime ← IO.monoMsNow
  let s ← compress refs
  let compressEndTime ← IO.monoMsNow
  let compressTime : Float := (compressEndTime - compressStartTime).toFloat / 1000.0
  IO.println s!"measurement: compress {compressTime} s"
  let parseStartTime ← IO.monoMsNow
  let r ← parse s
  let parseEndTime ← IO.monoMsNow
  let parseTime : Float := (parseEndTime - parseStartTime).toFloat / 1000.0
  match r with
  | .ok _ =>
    IO.println s!"measurement: parse {parseTime} s"
  | .error _ =>
    IO.println s!"measurement: parse {parseTime} s"
    IO.println "error"
