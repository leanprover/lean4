import Lean.Data.Lsp

def genModuleRefs (n : Nat) : IO Lean.Lsp.ModuleRefs := do
  let someLoc : Lean.Lsp.RefInfo.Location := {
    range := ⟨⟨333, 444⟩, ⟨444, 555⟩⟩
    parentDecl? := some {
      name := "A.Reasonably.Long.ParentDecl.Name.barfoo",
      range := ⟨⟨1111, 2222⟩, ⟨3333, 4444⟩⟩
      selectionRange := ⟨⟨5555, 6666⟩, ⟨7777, 8888⟩⟩
    }
  }

  let mut someUsages : Array Lean.Lsp.RefInfo.Location := #[]
  for _ in [0, 200] do
    someUsages := someUsages.push someLoc

  let someInfo : Lean.Lsp.RefInfo := {
      definition? := someLoc
      usages := someUsages
    }

  let mut refs : Lean.Lsp.ModuleRefs := .empty
  for i in [0:n] do
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
  let n := (args.get! 0).toNat!
  let refs ← genModuleRefs n
  let compressStartTime ← IO.monoMsNow
  let s ← compress refs
  let compressEndTime ← IO.monoMsNow
  let compressTime : Float := (compressEndTime - compressStartTime).toFloat / 1000.0
  IO.println s!"compress: {compressTime}"
  let parseStartTime ← IO.monoMsNow
  let r ← parse s
  let parseEndTime ← IO.monoMsNow
  let parseTime : Float := (parseEndTime - parseStartTime).toFloat / 1000.0
  match r with
  | .ok _ =>
    IO.println s!"parse: {parseTime}"
  | .error _ =>
    IO.println s!"parse: {parseTime}"
    IO.println "error"
