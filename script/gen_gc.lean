/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

import Lean
import all Lean.Compiler.LCNF.EmitC
import all Lean.Compiler.LCNF.PhaseExt

/-!
Generate the runtime collector from its unboxed entry point, without module initialization.
Run with `lean --run script/gen_gc.lean SOURCE OUTPUT`.
-/

open Lean Lean.Compiler.LCNF

private def primitives : List (Name × String) :=
  [(`Lean.Runtime.GC.Native.readRC, "lean_gc_read_rc"),
   (`Lean.Runtime.GC.Native.writeRC, "lean_gc_write_rc"),
   (`Lean.Runtime.GC.Native.fetchAddRC, "lean_gc_fetch_add_rc"),
   (`Lean.Runtime.GC.Native.readNext, "lean_gc_read_next"),
   (`Lean.Runtime.GC.Native.writeNext, "lean_gc_write_next"),
   (`Lean.Runtime.GC.Native.readTag, "lean_gc_read_tag"),
   (`Lean.Runtime.GC.Native.ctorCount, "lean_gc_ctor_count"),
   (`Lean.Runtime.GC.Native.ctorBegin, "lean_gc_ctor_begin"),
   (`Lean.Runtime.GC.Native.closureCount, "lean_gc_closure_count"),
   (`Lean.Runtime.GC.Native.closureBegin, "lean_gc_closure_begin"),
   (`Lean.Runtime.GC.Native.arrayCount, "lean_gc_array_count"),
   (`Lean.Runtime.GC.Native.arrayBegin, "lean_gc_array_begin"),
   (`Lean.Runtime.GC.Native.refBegin, "lean_gc_ref_begin"),
   (`Lean.Runtime.GC.Native.fieldNext, "lean_gc_field_next"),
   (`Lean.Runtime.GC.Native.readField, "lean_gc_read_field"),
   (`Lean.Runtime.GC.Native.readThunkClosure, "lean_gc_read_thunk_closure"),
   (`Lean.Runtime.GC.Native.readThunkValue, "lean_gc_read_thunk_value"),
   (`Lean.Runtime.GC.Native.freeSmall, "lean_gc_free_small"),
   (`Lean.Runtime.GC.Native.freeClosure, "lean_gc_free_closure"),
   (`Lean.Runtime.GC.Native.freeArray, "lean_gc_free_array"),
   (`Lean.Runtime.GC.Native.freeScalarArray, "lean_gc_free_scalar_array"),
   (`Lean.Runtime.GC.Native.freeString, "lean_gc_free_string"),
   (`Lean.Runtime.GC.Native.destroyMPZ, "lean_gc_destroy_mpz"),
   (`Lean.Runtime.GC.Native.deactivateTask, "lean_gc_deactivate_task"),
   (`Lean.Runtime.GC.Native.deactivatePromise, "lean_gc_deactivate_promise"),
   (`Lean.Runtime.GC.Native.finalizeExternal, "lean_gc_finalize_external"),
   (`Lean.Runtime.GC.Native.unreachable, "lean_gc_unreachable"),
   (`USize.decEq, "lean_usize_dec_eq"),
   (`USize.land, "lean_usize_land"),
   (`USize.sub, "lean_usize_sub"),
   (`Int32.decLt, "lean_int32_dec_lt"),
   (`Int32.decEq, "lean_int32_dec_eq"),
   (`Int32.decLe, "lean_int32_dec_le"),
   (`Int32.sub, "lean_int32_sub"),
   (`UInt8.decEq, "lean_uint8_dec_eq"),
   (`UInt8.decLe, "lean_uint8_dec_le")]

private def checkType (owner : Name) (type : Expr) : CoreM Unit := do
  match type with
  | ImpureType.uint8 | ImpureType.uint16 | ImpureType.uint32 | ImpureType.uint64
  | ImpureType.usize | ImpureType.void | ImpureType.erased | ImpureType.tagged => pure ()
  | _ => throwError "collector audit: {owner} uses a potentially allocated type: {type}"

private def checkSignature (d : Signature .impure) : CoreM Unit := do
  checkType d.name d.type
  for p in d.params do checkType d.name p.type
  if d.params.isEmpty then
    throwError "collector audit: {d.name} needs a global initializer"

private def checkExtern (d : Signature .impure) : CoreM Unit := do
  let some expected := primitives.lookup d.name
    | throwError "collector audit: unapproved foreign call {d.name}"
  let some attr := getExternAttrData? (← getEnv) d.name
    | throwError "collector audit: missing foreign definition for {d.name}"
  unless getExternEntryFor attr `c == some (.standard `all expected) do
    throwError "collector audit: changed foreign definition for {d.name}"

/--
Fail closed on every reachable instruction. In particular, heap constructors, closures, boxing,
reference-counting instructions, and indirect or unapproved foreign calls are rejected.
Scalar constructors (such as `Unit.unit`) are immediate tagged values and require no allocation.
-/
private def audit (localDecls : Array (Decl .impure))
    (otherModuleDecls : Array (Signature .impure)) : CoreM Unit := do
  let names := localDecls.map (·.name)
  for d in otherModuleDecls do
    checkSignature d
    checkExtern d
  for d in localDecls do
    checkSignature d.toSignature
    match d.value with
    | .extern _ => checkExtern d.toSignature
    | .code code =>
      code.forM fun c => do
        match c with
        | .let decl _ =>
          checkType d.name decl.type
          match decl.value with
          | .lit (.uint8 _) | .lit (.uint16 _) | .lit (.uint32 _)
          | .lit (.uint64 _) | .lit (.usize _) | .erased => pure ()
          | .ctor info args _ =>
            unless info.isScalar && args.isEmpty do
              throwError "collector audit: allocating constructor in {d.name}"
          | .fvar _ args =>
            unless args.isEmpty do
              throwError "collector audit: indirect call in {d.name}"
          | .fap name _ _ =>
            unless names.contains name || primitives.any (·.1 == name) do
              throwError "collector audit: unapproved call to {name} in {d.name}"
          | _ => throwError "collector audit: rejected instruction in {d.name}: {decl.value.toExpr}"
        | .jp jp _ =>
          checkType d.name jp.type
          for p in jp.params do checkType d.name p.type
        | .cases cases => checkType d.name cases.resultType
        | .jmp .. | .return .. => pure ()
        | _ => throwError "collector audit: rejected control instruction in {d.name}"

private def emitCollector : CoreM String := do
  let (localDecls, otherModuleDecls) ← collectUsedDecls #[`Lean.Runtime.GC.Native.decRefCold]
  let names := localDecls.map (·.name)
  let indexMap := getImpureDeclIndices (← getEnv) names
  let localDecls := localDecls.qsort fun l r => indexMap[l.name]! < indexMap[r.name]!
  audit localDecls otherModuleDecls
  let action : EmitM Unit := do
    emitFileHeader
    -- Primitives are already defined by lean.h and object.cpp. Redeclaring lean.h's static
    -- functions inside namespace lean would hide them with unresolved external declarations.
    withReader (fun ctx => { ctx with
        otherModuleDecls := #[]
        localDecls := localDecls.filter fun d => match d.value with
          | .code _ => true
          | .extern _ => false }) emitFnDecls
    emitFns
    emitFileFooter
  let (_, { buf, .. }) ←
    action
      |>.run { localDecls, otherModuleDecls, modName := `Collector }
      |>.run {}
      |>.run (phase := .impure)
  -- This fragment is used in one C++ translation unit. Keep its helpers private and let the
  -- native compiler inline the scanner into the deletion loop; lean_dec_ref_cold is the ABI.
  let code := String.intercalate "\n" <|
    (buf.replace "LEAN_EXPORT " "static inline ").splitOn "\n" |>.map (·.trimAsciiEnd.toString)
  return "// Generated by script/gen_gc.lean; edit src/runtime/lean/Collector.lean.\n" ++
    code

public unsafe def main (args : List String) : IO UInt32 := do
  let [source, output] := args
    | throw <| IO.userError "usage: lean --run script/gen_gc.lean SOURCE OUTPUT"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile source
  let opts := Elab.async.set {} false
  let some env ← Elab.runFrontend input opts source `Collector
    | return 1
  let (code, state) ← emitCollector.toIO
    { fileName := source, fileMap := FileMap.ofString input } { env }
  for msg in state.messages.toList do
    IO.println (← msg.toString)
  IO.FS.writeFile output code
  return 0
