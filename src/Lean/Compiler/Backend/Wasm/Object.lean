/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
-/
module

prelude
public import Lean.Compiler.Backend.Wasm.Module

public section

namespace Lean.Compiler.Backend.Wasm.Object

private def bytes (values : Array Nat) : ByteArray := ⟨values.map Nat.toUInt8⟩

structure FunctionSymbol where
  name : String
  functionIndex : Nat
  exported : Bool := false
  undefined : Bool := false
  global : Bool := false

structure DataSymbol where
  name : String
  segmentIndex : Nat
  offset : Nat := 0
  size : Nat

structure SegmentInfo where
  name : String
  alignment : Nat := 0
  flags : Nat := 1

structure Relocation where
  kind : UInt8 := 0
  offset : Nat
  symbolIndex : Nat
  addend : Option Int := none

private def customSection (name : String) (data : ByteArray) : Section :=
  ⟨0, Encoding.append (Encoding.encodeName name) data⟩

private def encodeSymbol (symbol : FunctionSymbol) : ByteArray :=
  -- Linking flags (lld wasm object format):
  --   0x10 undefined, 0x20 exported, 0x04 visibility hidden, 0x02 binding local.
  -- Non-exported defined functions must *not* be BINDING_LOCAL so other objects can
  -- resolve them (multi-module pure programs / core runtime).
  let flags :=
    if symbol.undefined then 0x10
    else if symbol.exported then 0xa4
    else if symbol.global then 0x04
    else 0x04  -- defined, hidden, global binding
  let base := Encoding.append (bytes #[0]) <|
    Encoding.append (Encoding.encodeULEB flags) (Encoding.encodeULEB symbol.functionIndex)
  if symbol.undefined then base else Encoding.append base (Encoding.encodeName symbol.name)

private def encodeDataSymbol (symbol : DataSymbol) : ByteArray :=
  appendMany #[bytes #[1], Encoding.encodeULEB 2, Encoding.encodeName symbol.name,
    Encoding.encodeULEB symbol.segmentIndex, Encoding.encodeULEB symbol.offset,
    Encoding.encodeULEB symbol.size]
where
  appendMany (parts : Array ByteArray) := parts.foldl (init := ByteArray.empty) Encoding.append

def linkingSection (symbols : Array FunctionSymbol) (dataSymbols : Array DataSymbol := #[])
    (segments : Array SegmentInfo := #[]) : Section :=
  let entries := symbols.foldl (init := Encoding.encodeULEB (symbols.size + dataSymbols.size + 1)) fun out symbol =>
    Encoding.append out (encodeSymbol symbol)
  let entries := dataSymbols.foldl (init := entries) fun out symbol =>
    Encoding.append out (encodeDataSymbol symbol)
  let entries := Encoding.append entries <|
    Encoding.append (bytes #[5]) <|
      Encoding.append (Encoding.encodeULEB 0x90) (Encoding.encodeULEB 0)
  let subsection := Encoding.append (bytes #[8]) <|
    Encoding.append (Encoding.encodeULEB entries.size) entries
  let segmentEntries := segments.foldl (init := Encoding.encodeULEB segments.size) fun out segment =>
    Encoding.append out <| Encoding.append (Encoding.encodeName segment.name) <|
      Encoding.append (Encoding.encodeULEB segment.alignment) (Encoding.encodeULEB segment.flags)
  let segmentSubsection := Encoding.append (bytes #[5]) <|
    Encoding.append (Encoding.encodeULEB segmentEntries.size) segmentEntries
  customSection "linking" <| Encoding.append (Encoding.encodeULEB 2) <|
    Encoding.append subsection segmentSubsection

def relocationSection (codeSectionIndex : Nat) (relocs : Array Relocation) : Section :=
  let entries := relocs.foldl (init := Encoding.encodeULEB relocs.size) fun out reloc =>
    let entry := Encoding.append (bytes #[reloc.kind.toNat]) <|
      Encoding.append (Encoding.encodeULEB reloc.offset) (Encoding.encodeULEB reloc.symbolIndex)
    let entry := match reloc.addend with
      | some addend => Encoding.append entry (Encoding.encodeSLEB addend)
      | none => entry
    Encoding.append out entry
  customSection "reloc.CODE" <| Encoding.append (Encoding.encodeULEB codeSectionIndex) entries

/-- WebAssembly `name` custom section: module name + function names (for debuggers). -/
def nameSection (moduleName : String) (functionNames : Array (Nat × String)) : Section :=
  let modSub := Encoding.append (bytes #[0]) <|
    Encoding.append (Encoding.encodeULEB (Encoding.encodeName moduleName).size)
      (Encoding.encodeName moduleName)
  let fnPayload := functionNames.foldl (init := Encoding.encodeULEB functionNames.size) fun out (idx, name) =>
    Encoding.append out <| Encoding.append (Encoding.encodeULEB idx) (Encoding.encodeName name)
  let fnSub := Encoding.append (bytes #[1]) <|
    Encoding.append (Encoding.encodeULEB fnPayload.size) fnPayload
  customSection "name" (Encoding.append modSub fnSub)

/-- WebAssembly `producers` custom section. -/
def producersSection (language : String := "Lean4") (processedBy : String := "lean") : Section :=
  let field (name value : String) : ByteArray :=
    Encoding.append (Encoding.encodeName name) <|
      Encoding.append (Encoding.encodeULEB 1) <|
        Encoding.append (Encoding.encodeName value) (Encoding.encodeName "")
  let payload := Encoding.append (Encoding.encodeULEB 2) <|
    Encoding.append (field "language" language) (field "processed-by" processedBy)
  customSection "producers" payload

def withLinking (module : Wasm.Module) (symbols : Array FunctionSymbol)
    (relocs : Array Relocation := #[]) (dataSymbols : Array DataSymbol := #[])
    (segments : Array SegmentInfo := #[])
    (moduleName : String := "lean")
    (functionNames : Array (Nat × String) := #[])
    (emitDebugNames : Bool := false) : Wasm.Module :=
  let codeSectionIndex := (module.sections.findIdx? fun sec => sec.id == 0x0a).getD 0
  -- Linking metadata first (what wasm-ld expects), then optional debug custom sections.
  let sections := module.sections.push (linkingSection symbols dataSymbols segments)
  let sections := if relocs.isEmpty then sections
    else sections.push (relocationSection codeSectionIndex relocs)
  let sections := if emitDebugNames then
    sections.push (nameSection moduleName functionNames) |>.push producersSection
  else sections
  { module with sections }

end Lean.Compiler.Backend.Wasm.Object
