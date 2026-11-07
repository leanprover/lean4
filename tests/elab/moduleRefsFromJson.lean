import Lean.Data.Lsp.Internal

open Lean Lsp

deriving instance Inhabited for RefInfo.Location, RefInfo

private def decodeJsonAs (α : Type) [FromJson α] (raw : String) : IO α := do
  let j ← IO.ofExcept (Json.parse raw)
  IO.ofExcept (fromJson? (α := α) j)

private def decodeFails (α : Type) [FromJson α] (raw : String) : IO Bool := do
  let j ← IO.ofExcept (Json.parse raw)
  return (fromJson? (α := α) j).toOption.isNone

unsafe def testModuleRefsAndRefInfoFromJson : IO Unit := do
  -- 1. Standalone `FromJson RefInfo`: shares `parentDecl` across `definition` and `usages`,
  --    preserves distinct `parentDecl` values, and supports 4-element locations.
  let rawRefInfo :=
    "{\"definition\":[1,0,1,3,\"MyNs.thmA\"]," ++
    "\"usages\":[[2,1,2,4,\"MyNs.thmA\"],[3,2,3,5,\"MyNs.thmA\"],[4,0,4,3,\"MyNs.thmB\"],[5,0,5,2]]}"
  let standaloneInfo ← decodeJsonAs RefInfo rawRefInfo
  let defLoc := standaloneInfo.definition?.get!
  let u0 := standaloneInfo.usages[0]!
  let u1 := standaloneInfo.usages[1]!
  let u2 := standaloneInfo.usages[2]!
  let u3 := standaloneInfo.usages[3]!
  assert! defLoc.parentDecl? == some "MyNs.thmA"
  assert! u0.parentDecl? == some "MyNs.thmA"
  assert! u1.parentDecl? == some "MyNs.thmA"
  assert! u2.parentDecl? == some "MyNs.thmB"
  assert! u3.parentDecl? == none
  assert! ptrAddrUnsafe defLoc.parentDecl == ptrAddrUnsafe u0.parentDecl
  assert! ptrAddrUnsafe u0.parentDecl == ptrAddrUnsafe u1.parentDecl
  assert! Json.compress (toJson standaloneInfo) == rawRefInfo

  -- 2. `FromJson ModuleRefs`: shares `parentDecl` within one `RefInfo`, across `definition` and
  --    `usages`, and across different `RefIdent` entries (`const` and `fvar`), while preserving
  --    distinct names, `definition := null`, empty `usages`, and 4-element locations.
  let rawModuleRefs :=
    "[[0,\"TestMod\",\"Nat.add\"]," ++
      "{\"definition\":[1,0,1,7,\"MyNs.thmA\"]," ++
       "\"usages\":[[10,2,10,5,\"MyNs.thmA\"],[11,4,11,7,\"MyNs.thmA\"],[12,1,12,4,\"MyNs.thmB\"],[15,0,15,3]]}," ++
     "[0,\"TestMod\",\"Nat.mul\"]," ++
      "{\"definition\":null," ++
       "\"usages\":[[20,2,20,5,\"MyNs.thmA\"],[22,4,22,7,\"MyNs.thmB\"]]}," ++
     "[1,\"TestMod\",\"fvar_1\"]," ++
      "{\"definition\":[30,0,30,1,\"MyNs.thmB\"]," ++
       "\"usages\":[]}]"
  let refs ← decodeJsonAs ModuleRefs rawModuleRefs
  let addInfo := refs.get! (.const "TestMod" "Nat.add")
  let mulInfo := refs.get! (.const "TestMod" "Nat.mul")
  let fvarInfo := refs.get! (.fvar "TestMod" "fvar_1")

  let addDef := addInfo.definition?.get!
  let addU0 := addInfo.usages[0]!
  let addU1 := addInfo.usages[1]!
  let addU2 := addInfo.usages[2]!
  let addU3 := addInfo.usages[3]!
  let mulU0 := mulInfo.usages[0]!
  let mulU1 := mulInfo.usages[1]!
  let fvarDef := fvarInfo.definition?.get!

  -- Values and optional fields
  assert! addDef.parentDecl? == some "MyNs.thmA"
  assert! addU0.parentDecl? == some "MyNs.thmA"
  assert! addU1.parentDecl? == some "MyNs.thmA"
  assert! addU2.parentDecl? == some "MyNs.thmB"
  assert! addU3.parentDecl? == none
  assert! mulInfo.definition?.isNone
  assert! mulU0.parentDecl? == some "MyNs.thmA"
  assert! mulU1.parentDecl? == some "MyNs.thmB"
  assert! fvarDef.parentDecl? == some "MyNs.thmB"
  assert! fvarInfo.usages.isEmpty

  -- Pointer sharing: within `RefInfo`, across `definition` and `usages`, and across `RefIdent`s
  assert! ptrAddrUnsafe addDef.parentDecl == ptrAddrUnsafe addU0.parentDecl
  assert! ptrAddrUnsafe addU0.parentDecl == ptrAddrUnsafe addU1.parentDecl
  assert! ptrAddrUnsafe addDef.parentDecl == ptrAddrUnsafe mulU0.parentDecl
  assert! ptrAddrUnsafe addU2.parentDecl == ptrAddrUnsafe mulU1.parentDecl
  assert! ptrAddrUnsafe addU2.parentDecl == ptrAddrUnsafe fvarDef.parentDecl

  -- Canonical round-trip equality
  assert! Json.compress (toJson refs) == rawModuleRefs

  -- 3. Explicit empty `parentDecl` in a 5-element location is accepted and normalized to 4 elements
  let rawExplicitEmptyParent := "{\"definition\":[1,2,3,4,\"\"],\"usages\":[]}"
  let emptyParentInfo ← decodeJsonAs RefInfo rawExplicitEmptyParent
  assert! emptyParentInfo.definition?.get!.parentDecl? == none
  assert! Json.compress (toJson emptyParentInfo) == "{\"definition\":[1,2,3,4],\"usages\":[]}"

  -- 4. Malformed inputs are rejected
  assert! (← decodeFails RefInfo "{\"definition\":[1,2,3],\"usages\":[]}")
  assert! (← decodeFails RefInfo "{\"definition\":[1,2,3,4,\"a\",\"b\"],\"usages\":[]}")
  assert! (← decodeFails RefInfo "{\"definition\":[1,2,3,4,99],\"usages\":[]}")
  assert! (← decodeFails ModuleRefs "[[0,\"TestMod\",\"Nat.add\"]]")
  assert! (← decodeFails ModuleRefs "{}")

  IO.println "ok"

/-- info: ok -/
#guard_msgs in
#eval testModuleRefsAndRefInfoFromJson
