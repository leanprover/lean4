/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
-/
module

prelude
public import Lean.Compiler.Backend.Wasm
public import Lean.Compiler.ExportAttr
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.NameMangling
public import Lean.Compiler.ModPkgExt
public import Lean.Compiler.ClosedTermCache
public import Lean.Runtime
import Lean.Compiler.LCNF.Types
import Init.Data.List.Basic

public section

namespace Lean.Compiler.Backend.EmitWasm

open Lean.IR
open Lean.Compiler.Backend.Wasm
open Lean.Compiler.Backend.Wasm.Layout
open Lean.Compiler.Backend.Wasm.Types
open Lean.Compiler.Backend.Wasm.Instr
open Lean.Compiler.LCNF (isBoxedName)

/-!
# WebAssembly IR → relocatable object emitter

Lowers Lean IR through a typed WASM instruction AST into a relocatable
`wasm32` object (linking, reloc.CODE, name, producers sections).
-/

private def bytes (values : Array Nat) : ByteArray :=
  ⟨values.map Nat.toUInt8⟩

private def appendMany (parts : Array ByteArray) : ByteArray :=
  parts.foldl (init := ByteArray.empty) Encoding.append

/-- Host profile for the emitted object. -/
inductive HostProfile where
  /-- WASI reactor linked against `libleanrt.a` (default). -/
  | wasi
  /-- Browser/JS host: same object ABI (`env` memory/table imports). -/
  | js
  deriving BEq, Inhabited

structure EmitConfig where
  layout : ObjectLayout := Layout.default
  host : HostProfile := .wasi
  /-- Emit `name` + `producers` custom sections (off by default: some linkers reject mid/trailing name secs). -/
  emitDebugNames : Bool := false
  /-- Emit `return_call` for tail-position calls (requires WASM tail-call proposal). -/
  emitTailCalls : Bool := false
  deriving Inhabited

private structure ImportSpec where
  name : Name
  symbol : String
  params : Array IRType
  result : IRType

private def symbolName (env : Environment) (name : Name) : String :=
  match getExternAttrData? env name |>.bind (getExternEntryFor · `c) with
  | some (.standard _ symbol) => symbol
  | _ => match Lean.getExportNameFor? env name with
    | some (.str .anonymous symbol) => symbol
    | _ => Lean.getSymbolStem env name

private def ensureRuntimeImport (imports : Array ImportSpec) (symbol : String)
    (params : Array IRType) (result : IRType) : Array ImportSpec :=
  if imports.any fun spec => spec.symbol == symbol then imports
  else imports.push { name := Name.mkSimple symbol, symbol, params, result }

private def boxSymbol? : IRType → Option String
  | .uint32 => some "lean_box_uint32"
  | .uint64 => some "lean_box_uint64"
  | .usize => some "lean_box_usize"
  | .float => some "lean_box_float"
  | .float32 => some "lean_box_float32"
  | _ => none

private def unboxSymbol? : IRType → Option String
  | .uint32 => some "lean_unbox_uint32"
  | .uint64 => some "lean_unbox_uint64"
  | .usize => some "lean_unbox_usize"
  | .float => some "lean_unbox_float"
  | .float32 => some "lean_unbox_float32"
  | _ => none

/-- Primitive ops that lower to native WASM opcodes. -/
private inductive PrimOp where
  | bin (i32 i64 : Instr)
  | cmp (i32 i64 : Instr)
  | fbin (f32 f64 : Instr)
  | fneg (f32 f64 : Instr)

private def primitiveOp? : Name → Option PrimOp
  | ``UInt8.add | ``UInt16.add | ``UInt32.add | ``USize.add => some (.bin .i32Add .i64Add)
  | ``UInt64.add => some (.bin .i32Add .i64Add)
  | ``UInt8.sub | ``UInt16.sub | ``UInt32.sub | ``USize.sub => some (.bin .i32Sub .i64Sub)
  | ``UInt64.sub => some (.bin .i32Sub .i64Sub)
  | ``UInt8.mul | ``UInt16.mul | ``UInt32.mul | ``USize.mul => some (.bin .i32Mul .i64Mul)
  | ``UInt64.mul => some (.bin .i32Mul .i64Mul)
  | ``UInt8.div | ``UInt16.div | ``UInt32.div | ``USize.div => some (.bin .i32DivU .i64DivU)
  | ``UInt64.div => some (.bin .i32DivU .i64DivU)
  | ``UInt8.mod | ``UInt16.mod | ``UInt32.mod | ``USize.mod => some (.bin .i32RemU .i64RemU)
  | ``UInt64.mod => some (.bin .i32RemU .i64RemU)
  | ``UInt8.land | ``UInt16.land | ``UInt32.land | ``USize.land | ``UInt64.land =>
    some (.bin .i32And .i64And)
  | ``UInt8.lor | ``UInt16.lor | ``UInt32.lor | ``USize.lor | ``UInt64.lor =>
    some (.bin .i32Or .i64Or)
  | ``UInt8.xor | ``UInt16.xor | ``UInt32.xor | ``USize.xor | ``UInt64.xor =>
    some (.bin .i32Xor .i64Xor)
  | ``UInt8.shiftLeft | ``UInt16.shiftLeft | ``UInt32.shiftLeft | ``USize.shiftLeft
  | ``UInt64.shiftLeft => some (.bin .i32Shl .i64Shl)
  | ``UInt8.shiftRight | ``UInt16.shiftRight | ``UInt32.shiftRight | ``USize.shiftRight
  | ``UInt64.shiftRight => some (.bin .i32ShrU .i64ShrU)
  | ``UInt8.decEq | ``UInt16.decEq | ``UInt32.decEq | ``USize.decEq => some (.cmp .i32Eq .i64Eq)
  | ``UInt64.decEq => some (.cmp .i32Eq .i64Eq)
  | ``UInt8.decLt | ``UInt16.decLt | ``UInt32.decLt | ``USize.decLt => some (.cmp .i32LtU .i64LtU)
  | ``UInt64.decLt => some (.cmp .i32LtU .i64LtU)
  | ``UInt8.decLe | ``UInt16.decLe | ``UInt32.decLe | ``USize.decLe => some (.cmp .i32LeU .i64LeU)
  | ``UInt64.decLe => some (.cmp .i32LeU .i64LeU)
  | ``Float.add | ``Float32.add => some (.fbin .f32Add .f64Add)
  | ``Float.sub | ``Float32.sub => some (.fbin .f32Sub .f64Sub)
  | ``Float.mul | ``Float32.mul => some (.fbin .f32Mul .f64Mul)
  | ``Float.div | ``Float32.div => some (.fbin .f32Div .f64Div)
  | ``Float.neg | ``Float32.neg => some (.fneg .f32Neg .f64Neg)
  | _ => none

private def isPrimitiveName (name : Name) : Bool := (primitiveOp? name).isSome

private def natBinRuntime? : Name → Option String
  | ``Nat.add => some "lean_nat_add"
  | ``Nat.sub => some "lean_nat_sub"
  | ``Nat.mul => some "lean_nat_mul"
  | ``Nat.mod => some "lean_nat_mod"
  | _ => none

private def natCmpRuntime? : Name → Option String
  | ``Nat.decEq => some "lean_nat_dec_eq"
  | ``Nat.decLt => some "lean_nat_dec_lt"
  | _ => none

private partial def collectVarTypes (body : FnBody) (vars : Array (VarId × IRType)) :
    Array (VarId × IRType) :=
  match body with
  | .vdecl x ty _ rest => collectVarTypes rest (vars.push (x, ty))
  | .jdecl _ params value rest =>
    let vars := params.foldl (fun vars p => vars.push (p.x, p.ty)) vars
    collectVarTypes rest (collectVarTypes value vars)
  | .case _ _ _ alts => alts.foldl (fun vars alt => collectVarTypes alt.body vars) vars
  | .set _ _ _ rest | .uset _ _ _ rest | .sset _ _ _ _ _ rest | .setTag _ _ rest |
    .inc _ _ _ _ rest | .dec _ _ _ _ rest | .del _ rest => collectVarTypes rest vars
  | .ret _ | .jmp _ _ | .unreachable => vars

private def lookupVarType (vars : Array (VarId × IRType)) (x : VarId) : Except String IRType :=
  match vars.find? fun entry => entry.1.idx == x.idx with
  | some entry => .ok entry.2
  | none => .error s!"WebAssembly backend: unknown type for IR variable {x.idx}"

private def emitLoad (_layout : ObjectLayout) (ty : IRType) (offset : Nat) : Instr :=
  match ty with
  | .uint8 => .i32Load8U 0 offset
  | .uint16 => .i32Load16U 1 offset
  | .uint64 => .i64Load 3 offset
  | .float => .f64Load 3 offset
  | .float32 => .f32Load 2 offset
  | _ => .i32Load 2 offset

private def emitStore (_layout : ObjectLayout) (ty : IRType) (offset : Nat) : Instr :=
  match ty with
  | .uint8 => .i32Store8 0 offset
  | .uint16 => .i32Store16 1 offset
  | .uint64 => .i64Store 3 offset
  | .float => .f64Store 3 offset
  | .float32 => .f32Store 2 offset
  | _ => .i32Store 2 offset

private partial def gatherImportsBody (env : Environment) (funcs : Array Decl)
    (vars : Array (VarId × IRType)) (body : FnBody) (imports : Array ImportSpec) :
    Except String (Array ImportSpec) := do
  match body with
  | .vdecl _ _ (.ctor info _) rest =>
    let imports := if info.isRef then
      ensureRuntimeImport imports "lean_alloc_ctor" #[.uint32, .uint32, .uint32] .object
    else imports
    gatherImportsBody env funcs vars rest imports
  | .vdecl _ _ (.box ty _) rest =>
    let imports := match boxSymbol? ty with
      | some symbol => ensureRuntimeImport imports symbol #[ty] .tobject
      | none => imports
    gatherImportsBody env funcs vars rest imports
  | .vdecl _ ty (.unbox _) rest =>
    let imports := match unboxSymbol? ty with
      | some symbol => ensureRuntimeImport imports symbol #[.tobject] ty
      | none => imports
    gatherImportsBody env funcs vars rest imports
  | .vdecl _ ty (.fap name args) rest =>
    let mut imports := imports
    if let some sym := natBinRuntime? name then
      imports := ensureRuntimeImport imports sym #[.tobject, .tobject] .tobject
    else if let some sym := natCmpRuntime? name then
      imports := ensureRuntimeImport imports sym #[.tobject, .tobject] .uint8
    else if !isPrimitiveName name && !(funcs.any fun decl => decl.name == name) then
      let symbol := symbolName env name
      -- Dedupe by Lean name *or* C symbol (multiple decls may share one extern).
      unless imports.any fun spec => spec.name == name || spec.symbol == symbol do
        let mut params := #[]
        for arg in args do
          match arg with
          | .erased => pure ()
          | .var x => params := params.push (← lookupVarType vars x)
        imports := imports.push { name, symbol, params, result := ty }
    gatherImportsBody env funcs vars rest imports
  | .vdecl _ _ (.pap _ _) rest =>
    gatherImportsBody env funcs vars rest <|
      ensureRuntimeImport imports "lean_alloc_closure" #[.usize, .uint32, .uint32] .object
  | .vdecl _ _ (.ap _ args) rest =>
    if args.size >= 1 && args.size <= 16 then
      let symbol := s!"lean_apply_{args.size}"
      let params := Array.replicate (args.size + 1) .tobject
      gatherImportsBody env funcs vars rest (ensureRuntimeImport imports symbol params .tobject)
    else if args.size > 16 then
      let imports := ensureRuntimeImport imports "lean_wasm_apply_m_set" #[.uint32, .tobject] .void
      let imports := ensureRuntimeImport imports "lean_wasm_apply_m" #[.tobject, .uint32] .tobject
      gatherImportsBody env funcs vars rest imports
    else
      gatherImportsBody env funcs vars rest imports
  | .vdecl _ _ (.isShared _) rest =>
    gatherImportsBody env funcs vars rest imports
  | .vdecl _ _ (.reset _ _) rest =>
    gatherImportsBody env funcs vars rest <|
      ensureRuntimeImport imports "lean_wasm_reset" #[.object, .uint32] .object
  | .vdecl _ _ (.reuse _ _ _ _) rest =>
    gatherImportsBody env funcs vars rest <|
      ensureRuntimeImport imports "lean_wasm_reuse_ctor"
        #[.object, .uint32, .uint32, .uint32, .uint8] .object
  | .vdecl _ _ (.lit (.str _)) rest =>
    gatherImportsBody env funcs vars rest <|
      ensureRuntimeImport imports "lean_mk_string_unchecked" #[.usize, .usize, .usize] .object
  | .vdecl _ ty (.lit (.num value)) rest =>
    let imports := if ty.isObj then
      if value < UInt32.size then
        ensureRuntimeImport imports "lean_wasm_unsigned_to_nat" #[.uint32] .tobject
      else
        ensureRuntimeImport imports "lean_cstr_to_nat" #[.usize] .tobject
    else imports
    gatherImportsBody env funcs vars rest imports
  | .vdecl _ _ _ rest => gatherImportsBody env funcs vars rest imports
  | .jdecl _ _ value rest =>
    gatherImportsBody env funcs vars rest (← gatherImportsBody env funcs vars value imports)
  | .case _ _ _ alts =>
    alts.foldlM (fun imports alt => gatherImportsBody env funcs vars alt.body imports) imports
  | .inc _ n _ _ rest =>
    let imports :=
      if n > 1 then ensureRuntimeImport imports "lean_inc_ref_n" #[.object, .usize] .void
      else ensureRuntimeImport imports "lean_inc_ref" #[.object] .void
    gatherImportsBody env funcs vars rest imports
  | .dec _ n _ _ rest =>
    let imports :=
      if n > 1 then ensureRuntimeImport imports "lean_dec_ref_n" #[.object, .usize] .void
      else ensureRuntimeImport imports "lean_dec" #[.object] .void
    gatherImportsBody env funcs vars rest imports
  | .setTag _ _ rest => gatherImportsBody env funcs vars rest imports
  | .del _ rest =>
    gatherImportsBody env funcs vars rest <|
      ensureRuntimeImport imports "lean_wasm_del_object" #[.object] .void
  | .set _ _ _ rest | .uset _ _ _ rest | .sset _ _ _ _ _ rest =>
    gatherImportsBody env funcs vars rest imports
  | .ret _ | .jmp _ _ | .unreachable => return imports

private def gatherImports (env : Environment) (funcs : Array Decl) :
    Except String (Array ImportSpec) := do
  let mut imports := #[]
  for decl in funcs do
    if let .fdecl _ params _ body _ := decl then
      let vars := collectVarTypes body (params.map fun p => (p.x, p.ty))
      imports ← gatherImportsBody env funcs vars body imports
  return imports

private partial def collectStringsBody (body : FnBody) (strings : Array String) : Array String :=
  match body with
  | .vdecl _ _ (.lit (.str value)) rest =>
    collectStringsBody rest <| if strings.contains value then strings else strings.push value
  | .vdecl _ ty (.lit (.num value)) rest =>
    let literal := toString value
    let strings := if ty.isObj && value >= UInt32.size && !strings.contains literal then
      strings.push literal
    else strings
    collectStringsBody rest strings
  | .vdecl _ _ _ rest | .set _ _ _ rest | .uset _ _ _ rest | .sset _ _ _ _ _ rest |
    .setTag _ _ rest | .inc _ _ _ _ rest | .dec _ _ _ _ rest | .del _ rest =>
    collectStringsBody rest strings
  | .jdecl _ _ value rest => collectStringsBody rest (collectStringsBody value strings)
  | .case _ _ _ alts => alts.foldl (fun strings alt => collectStringsBody alt.body strings) strings
  | .ret _ | .jmp _ _ | .unreachable => strings

private def collectStrings (funcs : Array Decl) : Array String :=
  funcs.foldl (init := #[]) fun strings decl =>
    match decl with
    | .fdecl _ _ _ body _ => collectStringsBody body strings
    | _ => strings

private def moduleInitName (env : Environment) (moduleName : Name) : String :=
  let pkg? := (env.getModuleIdx? moduleName).bind env.getModulePackageByIdx?
  mkModuleInitializationFunctionName moduleName pkg?

private def lookupVar (vars : Array (VarId × Nat)) (x : VarId) : Except String Nat :=
  match vars.find? fun entry => entry.1.idx == x.idx with
  | some entry => .ok entry.2
  | none => .error s!"WebAssembly backend: unknown IR variable {x.idx}"

private def lookupFun (funcs : Array Decl) (name : Name) : Except String Nat :=
  match funcs.findIdx? fun decl => decl.name == name with
  | some idx => .ok idx
  | none => .error s!"WebAssembly backend: unsupported external call '{name}'"

private def lookupCall (env : Environment) (imports : Array ImportSpec) (funcs : Array Decl)
    (name : Name) : Except String (Nat × Nat) :=
  match imports.findIdx? fun spec => spec.name == name with
  | some idx => .ok (idx, idx)
  | none =>
    -- Same C symbol under a different Lean name (e.g. ofNat / ofNatLT).
    let sym := symbolName env name
    match imports.findIdx? fun spec => spec.symbol == sym with
    | some idx => .ok (idx, idx)
    | none => do
      let idx ← lookupFun funcs name
      let relocated := imports.size + idx
      return (relocated, relocated)

private def lookupRuntime (imports : Array ImportSpec) (symbol : String) : Except String Nat :=
  match imports.findIdx? fun spec => spec.symbol == symbol with
  | some idx => .ok idx
  | none => .error s!"WebAssembly backend: missing runtime import '{symbol}'"

private def emitArgs (vars : Array (VarId × Nat)) (args : Array Arg) :
    Except String (Array Instr) := do
  let mut out : Array Instr := #[]
  for arg in args do
    match arg with
    | .erased => pure ()
    | .var x => out := out.push (.localGet (← lookupVar vars x))
  return out

private def emitPrim (ty : IRType) (op : PrimOp) (args : Array Instr) : Array Instr :=
  match op with
  | .bin i32 i64 => args.push (if ty == .uint64 then i64 else i32)
  | .cmp i32 i64 => args.push (if ty == .uint64 then i64 else i32)
  | .fbin f32 f64 => args.push (if ty == .float32 then f32 else f64)
  | .fneg f32 f64 => args.push (if ty == .float32 then f32 else f64)

/-- Small-Nat binary: if both tagged, unbox-op-box; else runtime. -/
private def emitNatBinFast (op : Instr) (runtimeIdx aLocal bLocal : Nat) : Array Instr :=
  let fast : Array Instr :=
    #[.localGet aLocal, .i32Const 1, .i32ShrU, .localGet bLocal, .i32Const 1, .i32ShrU, op,
      .i32Const 1, .i32Shl, .i32Const 1, .i32Or]
  let slow : Array Instr := #[.localGet aLocal, .localGet bLocal, .call runtimeIdx runtimeIdx]
  #[.localGet aLocal, .i32Const 1, .i32And, .localGet bLocal, .i32Const 1, .i32And, .i32And,
    .«if» (.val .i32) fast slow]

private def emitNatCmpFast (cmp : Instr) (runtimeIdx aLocal bLocal : Nat) : Array Instr :=
  let fast : Array Instr :=
    #[.localGet aLocal, .i32Const 1, .i32ShrU, .localGet bLocal, .i32Const 1, .i32ShrU, cmp]
  let slow : Array Instr := #[.localGet aLocal, .localGet bLocal, .call runtimeIdx runtimeIdx]
  #[.localGet aLocal, .i32Const 1, .i32And, .localGet bLocal, .i32Const 1, .i32And, .i32And,
    .«if» (.val .i32) fast slow]

private def emitExpr (cfg : EmitConfig) (env : Environment) (imports : Array ImportSpec)
    (funcs : Array Decl) (strings : Array String) (dataSymbolBase : Nat)
    (vars : Array (VarId × Nat)) (ty : IRType) (expr : IR.Expr) : Except String (Array Instr) := do
  let layout := cfg.layout
  match expr with
  | .lit (IR.LitVal.num value) =>
    if ty.isObj then
      if value < UInt32.size then
        let idx ← lookupRuntime imports "lean_wasm_unsigned_to_nat"
        return #[.i32Const value, .call idx idx]
      else
        let literal := toString value
        let some dataIndex := strings.findIdx? (· == literal)
          | throw "WebAssembly backend: missing large natural data symbol"
        let idx ← lookupRuntime imports "lean_cstr_to_nat"
        return #[.i32ConstReloc 4 (dataSymbolBase + dataIndex) (some 0), .call idx idx]
    else if ty == .uint64 then
      return #[.i64Const value]
    else
      return #[.i32Const value]
  | .lit (IR.LitVal.str value) =>
    let some stringIndex := strings.findIdx? (· == value)
      | throw "WebAssembly backend: missing string data symbol"
    let idx ← lookupRuntime imports "lean_mk_string_unchecked"
    return #[.i32ConstReloc 4 (dataSymbolBase + stringIndex) (some 0),
      .i32Const value.toUTF8.size, .i32Const value.length, .call idx idx]
  | .fap name args =>
    let argInstrs ← emitArgs vars args
    if let some op := primitiveOp? name then
      return emitPrim ty op argInstrs
    else if let some sym := natBinRuntime? name then
      let idx ← lookupRuntime imports sym
      match args[0]?, args[1]? with
      | some (Arg.var a), some (Arg.var b) =>
        let op := match name with
          | ``Nat.add => Instr.i32Add | ``Nat.sub => Instr.i32Sub
          | ``Nat.mul => Instr.i32Mul | _ => Instr.i32RemU
        return emitNatBinFast op idx (← lookupVar vars a) (← lookupVar vars b)
      | _, _ => return argInstrs.push (.call idx idx)
    else if let some sym := natCmpRuntime? name then
      let idx ← lookupRuntime imports sym
      match args[0]?, args[1]? with
      | some (Arg.var a), some (Arg.var b) =>
        let cmp := if name == ``Nat.decEq then Instr.i32Eq else Instr.i32LtU
        return emitNatCmpFast cmp idx (← lookupVar vars a) (← lookupVar vars b)
      | _, _ => return argInstrs.push (.call idx idx)
    else
      let (idx, symbol) ← lookupCall env imports funcs name
      return argInstrs.push (.call idx symbol)
  | .ctor info args =>
    unless args.isEmpty do
      throw "WebAssembly backend: constructor arguments must be materialized by following stores"
    if info.isRef then
      let idx ← lookupRuntime imports "lean_alloc_ctor"
      return #[.i32Const info.cidx, .i32Const info.size,
        .i32Const (info.usize * layout.ptrSize + info.ssize), .call idx idx]
    else
      return #[.i32Const (info.cidx * 2 + 1)]
  | .proj index object =>
    return #[.localGet (← lookupVar vars object),
      emitLoad layout .object (layout.objField index)]
  | .uproj index object =>
    -- Match historical emitter: usize slots start at fieldBase (object-count baked by frontend).
    return #[.localGet (← lookupVar vars object),
      emitLoad layout .usize (layout.fieldBase + index * layout.ptrSize)]
  | .sproj numObjs offset object =>
    return #[.localGet (← lookupVar vars object),
      emitLoad layout ty (layout.scalarField numObjs 0 offset)]
  | .box boxedTy value =>
    let v := .localGet (← lookupVar vars value)
    match boxSymbol? boxedTy with
    | some symbol =>
      let idx ← lookupRuntime imports symbol
      return #[v, .call idx idx]
    | none => return #[v, .i32Const 1, .i32Shl, .i32Const 1, .i32Or]
  | .unbox value =>
    let v := .localGet (← lookupVar vars value)
    match unboxSymbol? ty with
    | some symbol =>
      let idx ← lookupRuntime imports symbol
      return #[v, .call idx idx]
    | none => return #[v, .i32Const 1, .i32ShrU]
  | .pap name args =>
    -- Closures always store the boxed entry point when arity is high (FNN ABI).
    let papName :=
      if let some decl := funcs.find? (·.name == name) then
        let n := (decl.params.filter fun p => !p.ty.isVoid && p.ty != .erased).size
        if n > closureMaxArgs && !isBoxedName name then
          Name.str name "_boxed"
        else name
      else name
    let targetName :=
      if funcs.any (·.name == papName) then papName else name
    let (_, symbol) ← lookupCall env imports funcs targetName
    let some decl := funcs.find? (·.name == targetName)
      | throw s!"WebAssembly backend: closure target '{targetName}' is not defined in this object"
    let arity := (decl.params.filter fun p => !p.ty.isVoid && p.ty != .erased).size
    let alloc ← lookupRuntime imports "lean_alloc_closure"
    return #[.i32ConstReloc 1 symbol, .i32Const arity, .i32Const args.size, .call alloc alloc]
  | .ap closure args =>
    if args.size >= 1 && args.size <= 16 then
      let idx ← lookupRuntime imports s!"lean_apply_{args.size}"
      return #[.localGet (← lookupVar vars closure)] ++ (← emitArgs vars args) ++ #[.call idx idx]
    else if args.size > 16 then
      if args.size > 64 then
        throw s!"WebAssembly backend: closure application arity {args.size} exceeds lean_wasm_apply_m limit (64)"
      let setIdx ← lookupRuntime imports "lean_wasm_apply_m_set"
      let applyIdx ← lookupRuntime imports "lean_wasm_apply_m"
      let mut code : Array Instr := #[]
      let mut i := 0
      for arg in args do
        match arg with
        | .erased => pure ()
        | .var x =>
          code := code ++ #[.i32Const i, .localGet (← lookupVar vars x), .call setIdx setIdx]
          i := i + 1
      return code ++ #[.localGet (← lookupVar vars closure), .i32Const args.size,
        .call applyIdx applyIdx]
    else
      throw "WebAssembly backend: empty closure application"
  | .isShared object =>
    let obj ← lookupVar vars object
    -- scalar → 0 (not shared); else RC > 1
    return #[.localGet obj, .i32Const 1, .i32And,
      .«if» (.val .i32) #[.i32Const 0]
        #[.localGet obj, emitLoad layout .uint32 layout.rcOffset, .i32Const 1, .i32GtU]]
  | .reset fields object =>
    let idx ← lookupRuntime imports "lean_wasm_reset"
    return #[.localGet (← lookupVar vars object), .i32Const fields, .call idx idx]
  | .reuse token info updateHeader _ =>
    let idx ← lookupRuntime imports "lean_wasm_reuse_ctor"
    return #[.localGet (← lookupVar vars token), .i32Const info.cidx, .i32Const info.size,
      .i32Const (info.usize * layout.ptrSize + info.ssize),
      .i32Const (if updateHeader then 1 else 0), .call idx idx]

/-- Expand an IR type to the sequence of scalar local types it occupies. -/
private def expandLocalTypes (ty : IRType) : Array IRType :=
  let flat := flattenValTypes ty
  if flat.isEmpty then #[]
  else
    flat.map fun
      | .i32 => .uint32
      | .i64 => .uint64
      | .f32 => .float32
      | .f64 => .float

private partial def collectLocals (body : FnBody) (next : Nat)
    (vars : Array (VarId × Nat)) (types : Array IRType) :
    Except String (Nat × Array (VarId × Nat) × Array IRType) :=
  match body with
  | .vdecl x ty _ rest =>
    let slots := expandLocalTypes ty
    let slots := if slots.isEmpty then #[.uint32] else slots
    collectLocals rest (next + slots.size) (vars.push (x, next)) (types ++ slots)
  | .jdecl _ params value rest => do
    let mut next := next
    let mut vars := vars
    let mut types := types
    for param in params do
      let slots := expandLocalTypes param.ty
      let slots := if slots.isEmpty then #[.uint32] else slots
      vars := vars.push (param.x, next)
      types := types ++ slots
      next := next + slots.size
    let (next', vars', types') ← collectLocals value next vars types
    collectLocals rest next' vars' types'
  | .case _ _ _ alts => do
    let mut next := next
    let mut vars := vars
    let mut types := types
    for alt in alts do
      let (next', vars', types') ← collectLocals alt.body next vars types
      next := next'
      vars := vars'
      types := types'
    return (next, vars, types)
  | .set _ _ _ rest | .uset _ _ _ rest | .sset _ _ _ _ _ rest | .setTag _ _ rest |
    .inc _ _ _ _ rest | .dec _ _ _ _ rest | .del _ rest => collectLocals rest next vars types
  | .ret _ | .jmp _ _ | .unreachable => .ok (next, vars, types)

/-- Pack consecutive locals of the same WASM valtype. -/
private def packLocals (types : Array IRType) : Except String ByteArray := do
  let mut groups : Array (Nat × UInt8) := #[]
  for ty in types do
    let flat := flattenValTypes ty
    let some v := flat[0]?
      | throw s!"WebAssembly backend: cannot allocate local ({unsupportedReason ty})"
    let b := v.toByte
    match groups.back? with
    | some (n, t) =>
      if t == b then groups := groups.pop.push (n + 1, t)
      else groups := groups.push (1, b)
    | none => groups := groups.push (1, b)
  let mut out := Encoding.encodeULEB groups.size
  for (n, t) in groups do
    out := appendMany #[out, Encoding.encodeULEB n, bytes #[t.toNat]]
  return out

/-- Base local index for `x` (first slot if multi-value). -/
private def lookupVarBase (vars : Array (VarId × Nat)) (x : VarId) : Except String Nat :=
  lookupVar vars x

/-- All local slots for a multi-value IR variable. -/
private def lookupVarSlots (vars : Array (VarId × Nat)) (varTypes : Array (VarId × IRType))
    (x : VarId) : Except String (Array Nat) := do
  let base ← lookupVar vars x
  let ty ← lookupVarType varTypes x
  let n := numSlots ty
  let n := if n == 0 then 1 else n
  return Array.ofFn (n := n) fun i => base + i.val

private structure JoinTarget where
  id : JoinPointId
  params : Array Param
  depth : Nat

private def pushControl (joins : Array JoinTarget) : Array JoinTarget :=
  joins.map fun join => { join with depth := join.depth + 1 }

private def emitJumpArgs (vars : Array (VarId × Nat)) (params : Array Param)
    (args : Array Arg) : Except String (Array Instr) := do
  let mut code : Array Instr := #[]
  let mut argIndex := 0
  for param in params do
    if param.ty.isVoid || param.ty == .erased then continue
    let some arg := args[argIndex]?
      | throw "WebAssembly backend: join point argument count mismatch"
    argIndex := argIndex + 1
    match arg with
    | .erased => pure ()
    | .var value =>
      code := code ++ #[.localGet (← lookupVar vars value), .localSet (← lookupVar vars param.x)]
  return code

private def asTailCall? : FnBody → Option (Name × Array Arg)
  | .vdecl x _ (.fap f ys) (.ret (.var y)) => if x.idx == y.idx then some (f, ys) else none
  | _ => none

/-- `scratch` is an extra i32 local reserved for case-tag materialization (`br_table`). -/
private partial def emitBody (cfg : EmitConfig) (env : Environment) (imports : Array ImportSpec)
    (funcs : Array Decl) (strings : Array String) (dataSymbolBase : Nat)
    (joins : Array JoinTarget) (varTypes : Array (VarId × IRType)) (vars : Array (VarId × Nat))
    (scratch : Nat) (body : FnBody) : Except String (Array Instr) := do
  let layout := cfg.layout
  if cfg.emitTailCalls then
    if let some (f, ys) := asTailCall? body then
      if !isPrimitiveName f && (natBinRuntime? f).isNone && (natCmpRuntime? f).isNone then
        match lookupCall env imports funcs f with
        | .ok (idx, symbol) =>
          let argInstrs ← emitArgs vars ys
          return argInstrs ++ #[.returnCall idx symbol]
        | .error _ => pure ()
  match body with
  | .vdecl x _ (.ctor info args) rest => do
    let value ← emitExpr cfg env imports funcs strings dataSymbolBase vars .object (.ctor info #[])
    let dst ← lookupVar vars x
    let mut code := value ++ #[.localSet dst]
    let mut objectIndex := 0
    let mut usizeIndex := 0
    let mut scalarOffset := 0
    for arg in args do
      match arg with
      | .erased => pure ()
      | .var value =>
        let valueTy ← lookupVarType varTypes value
        let mut storeTy := valueTy
        let mut offset := 0
        if objectIndex < info.size then
          storeTy := .object
          offset := layout.objField objectIndex
          objectIndex := objectIndex + 1
        else if usizeIndex < info.usize then
          storeTy := .usize
          offset := layout.usizeField info.size usizeIndex
          usizeIndex := usizeIndex + 1
        else
          offset := layout.scalarField info.size info.usize scalarOffset
          scalarOffset := scalarOffset + match valueTy with
            | .uint8 => 1 | .uint16 => 2 | .uint64 | .float => 8 | _ => 4
        code := code ++ #[.localGet dst, .localGet (← lookupVar vars value),
          emitStore layout storeTy offset]
    return code ++ (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .vdecl x _ (.pap name args) rest => do
    let value ← emitExpr cfg env imports funcs strings dataSymbolBase vars .object (.pap name args)
    let dst ← lookupVar vars x
    let mut code := value ++ #[.localSet dst]
    let mut fixedIndex := 0
    for arg in args do
      match arg with
      | .erased => pure ()
      | .var value =>
        code := code ++ #[.localGet dst, .localGet (← lookupVar vars value),
          emitStore layout .object (layout.closureFixedBase + fixedIndex * layout.ptrSize)]
        fixedIndex := fixedIndex + 1
    return code ++ (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .vdecl x _ (.reuse token info updateHeader args) rest => do
    let value ← emitExpr cfg env imports funcs strings dataSymbolBase vars .object
      (.reuse token info updateHeader args)
    let dst ← lookupVar vars x
    let mut code := value ++ #[.localSet dst]
    let mut objectIndex := 0
    let mut usizeIndex := 0
    let mut scalarOffset := 0
    for arg in args do
      match arg with
      | .erased => pure ()
      | .var source =>
        let sourceTy ← lookupVarType varTypes source
        let mut storeTy := sourceTy
        let mut offset := 0
        if objectIndex < info.size then
          storeTy := .object
          offset := layout.objField objectIndex
          objectIndex := objectIndex + 1
        else if usizeIndex < info.usize then
          storeTy := .usize
          offset := layout.usizeField info.size usizeIndex
          usizeIndex := usizeIndex + 1
        else
          offset := layout.scalarField info.size info.usize scalarOffset
          scalarOffset := scalarOffset + match sourceTy with
            | .uint8 => 1 | .uint16 => 2 | .uint64 | .float => 8 | _ => 4
        code := code ++ #[.localGet dst, .localGet (← lookupVar vars source),
          emitStore layout storeTy offset]
    return code ++ (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .vdecl x ty expr rest => do
    let value ← emitExpr cfg env imports funcs strings dataSymbolBase vars ty expr
    let idx ← lookupVar vars x
    return value ++ #[.localSet idx] ++
      (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .set object index value rest => do
    let valueInstr ← match value with
      | .erased => pure (.i32Const 1)
      | .var x => pure (.localGet (← lookupVar vars x))
    return #[.localGet (← lookupVar vars object), valueInstr,
      emitStore layout .object (layout.objField index)] ++
      (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .uset object index value rest => do
    return #[.localGet (← lookupVar vars object), .localGet (← lookupVar vars value),
      emitStore layout .usize (layout.fieldBase + index * layout.ptrSize)] ++
      (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .sset object numObjs offset value ty rest => do
    return #[.localGet (← lookupVar vars object), .localGet (← lookupVar vars value),
      emitStore layout ty (layout.scalarField numObjs 0 offset)] ++
      (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .setTag object tag rest => do
    return #[.localGet (← lookupVar vars object), .i32Const tag,
      emitStore layout .uint8 layout.tagOffset] ++
      (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .del object rest => do
    let idx ← lookupRuntime imports "lean_wasm_del_object"
    return #[.localGet (← lookupVar vars object), .call idx idx] ++
      (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .inc object n checkScalar _ rest => do
    let objectIdx ← lookupVar vars object
    let call ←
      if n > 1 then
        let idx ← lookupRuntime imports "lean_inc_ref_n"
        pure #[.localGet objectIdx, .i32Const n, .call idx idx]
      else
        let idx ← lookupRuntime imports "lean_inc_ref"
        pure #[.localGet objectIdx, .call idx idx]
    let inc := if checkScalar then
      #[.localGet objectIdx, .i32Const 1, .i32And, .i32Eqz, .«if» .void call #[]]
    else call
    return inc ++ (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .dec object n checkScalar _ rest => do
    let objectIdx ← lookupVar vars object
    let call ←
      if n > 1 then
        let idx ← lookupRuntime imports "lean_dec_ref_n"
        pure #[.localGet objectIdx, .i32Const n, .call idx idx]
      else
        let idx ← lookupRuntime imports "lean_dec"
        pure #[.localGet objectIdx, .call idx idx]
    let dec := if checkScalar then
      #[.localGet objectIdx, .i32Const 1, .i32And, .i32Eqz, .«if» .void call #[]]
    else call
    return dec ++ (← emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch rest)
  | .jdecl id params value rest => do
    let outer := pushControl joins
    let target : JoinTarget := { id, params, depth := 0 }
    let restCode ← emitBody cfg env imports funcs strings dataSymbolBase (outer.push target) varTypes vars scratch rest
    let valueCode ← emitBody cfg env imports funcs strings dataSymbolBase (outer.push target) varTypes vars scratch value
    return #[.block .void restCode, .loop .void valueCode]
  | .case _ discr discrTy alts => do
    let discrIdx ← lookupVar vars discr
    -- Materialize tag into `scratch` so `br_table` always sees a clean i32 operand.
    let tagToScratch : Array Instr :=
      if discrTy == .uint8 || discrTy == .uint16 || discrTy == .uint32 then
        #[.localGet discrIdx, .localSet scratch]
      else
        #[.localGet discrIdx, .i32Const 1, .i32And,
          .«if» (.val .i32)
            #[.localGet discrIdx, .i32Const 1, .i32ShrU]
            #[.localGet discrIdx, emitLoad layout .uint8 layout.tagOffset],
          .localSet scratch]
    let ctorAlts := alts.filterMap fun
      | .ctor info body => some (info.cidx, body)
      | .default _ => none
    let defaultBody? := alts.findSome? fun
      | .default b => some b
      | _ => none
    let sorted := ctorAlts.qsort (·.1 < ·.1)
    let n := sorted.size
    -- Dense 0..n-1, no default → br_table. Otherwise nested if-chain.
    let denseNoDefault := n >= 2 && defaultBody?.isNone && n == alts.size &&
      sorted[0]!.1 == 0 &&
      (Id.run do
        for i in [:n] do
          if sorted[i]!.1 != i then return false
        return true)
    if denseNoDefault then
      -- Canonical nested br_table (arm bodies sit *after* the block they label):
      --   block $outer {
      --     block {
      --       block {
      --         tag→scratch; br_table 0 1 2
      --       }
      --       arm0; br $outer
      --     }
      --     arm1; br $outer
      --   }
      let mut armCodes : Array (Array Instr) := #[]
      for i in [:n] do
        -- Open blocks while arm i runs: remaining arm wrappers (n-1-i) + outer (1) = n-i
        let extraDepth := n - i
        let mut armJoins := joins
        for _ in [:extraDepth] do
          armJoins := pushControl armJoins
        let (_, body) := sorted[i]!
        armCodes := armCodes.push
          (← emitBody cfg env imports funcs strings dataSymbolBase armJoins varTypes vars scratch body)
      let labels := Array.range n
      let mut core : Array Instr :=
        tagToScratch ++ #[.localGet scratch, .brTable labels n]
      for i in [:n] do
        -- Wrap previous core in a block, then append this arm (label i lands on that end).
        let depthToOuter := n - 1 - i
        core := #[.block .void core] ++ armCodes[i]! ++ #[.br depthToOuter]
      return #[.block .void core]
    -- Sparse / default: nested if-chain on the scratch tag
    let rec emitAlts (remaining : List Alt) (joins : Array JoinTarget) : Except String (Array Instr) := do
      match remaining with
      | [] => return #[.unreachable]
      | .default body :: _ =>
        emitBody cfg env imports funcs strings dataSymbolBase joins varTypes vars scratch body
      | .ctor info body :: rest =>
        let nested := pushControl joins
        let thenB ← emitBody cfg env imports funcs strings dataSymbolBase nested varTypes vars scratch body
        let elseB ← emitAlts rest nested
        return #[.localGet scratch, .i32Const info.cidx, .i32Eq, .«if» .void thenB elseB]
    return tagToScratch ++ (← emitAlts alts.toList joins)
  | .ret .erased => return #[.«return»]
  | .ret (.var x) => do
    -- Multi-value: push every slot (struct/union) then return.
    let slots ← lookupVarSlots vars varTypes x
    return slots.map Instr.localGet ++ #[.«return»]
  | .jmp id args => do
    let some target := joins.find? (·.id == id)
      | throw "WebAssembly backend: jump target is not in scope"
    return (← emitJumpArgs vars target.params args) ++ #[.br target.depth]
  | .unreachable => return #[.unreachable]

private def encodeTypeBytes (params : Array IRType) (result : IRType) : Except String ByteArray := do
  let mut paramVals : Array ValType := #[]
  for p in params do
    let flat := flattenValTypes p
    if flat.isEmpty && !(p.isVoid || p == .erased) then
      throw s!"WebAssembly backend: {unsupportedReason p}"
    paramVals := paramVals ++ flat
  let resultVals := flattenValTypes result
  let mut paramBytes := ByteArray.empty
  for v in paramVals do paramBytes := paramBytes.push v.toByte
  let mut resultBytes := Encoding.encodeULEB resultVals.size
  for v in resultVals do resultBytes := resultBytes.push v.toByte
  return appendMany #[bytes #[0x60], Encoding.encodeULEB paramVals.size, paramBytes, resultBytes]

/-- Boxed functions with arity > `closureMaxArgs` take a single `lean_object**` (FNN ABI). -/
private def isPackedBoxedDecl (decl : Decl) : Bool :=
  let params := decl.params.filter fun p => !p.ty.isVoid && p.ty != .erased
  params.size > closureMaxArgs && isBoxedName decl.name

private def encodeType (decl : Decl) : Except String ByteArray := do
  let params := decl.params.filter fun p => !p.ty.isVoid && p.ty != .erased
  if isPackedBoxedDecl decl then
    -- FNN: obj* (*)(obj**)  →  (i32) -> result
    encodeTypeBytes #[.usize] decl.resultType
  else
    encodeTypeBytes (params.map (·.ty)) decl.resultType

private def encodeImportType (spec : ImportSpec) : Except String ByteArray :=
  encodeTypeBytes spec.params spec.result

private structure EncodedFunction where
  bytes : ByteArray
  relocs : Array Reloc

/-- Unpack `_args[i]` into parameter locals for the FNN / packed-boxed ABI. -/
private def emitPackedArgsPrologue (layout : ObjectLayout) (argsLocal : Nat)
    (paramLocals : Array Nat) : Array Instr :=
  Id.run do
    let mut code : Array Instr := #[]
    for h : i in [:paramLocals.size] do
      let dst := paramLocals[i]
      code := code ++ #[
        .localGet argsLocal,
        emitLoad layout .object (i * layout.ptrSize),
        .localSet dst
      ]
    return code

private def encodeFunction (cfg : EmitConfig) (env : Environment) (imports : Array ImportSpec)
    (funcs : Array Decl) (strings : Array String) (dataSymbolBase : Nat) (decl : Decl) :
    Except String EncodedFunction := do
  let .fdecl _ params _ body _ := decl
    | throw "WebAssembly backend: cannot emit an extern declaration"
  let params := params.filter fun p => !p.ty.isVoid && p.ty != .erased
  let packed := isPackedBoxedDecl decl
  let layout := cfg.layout
  let varTypes := collectVarTypes body (params.map fun p => (p.x, p.ty))
  -- Local layout:
  --   unpacked: [param slots...] | body locals | scratch
  --   packed FNN: wasm param0=_args | [param slots as locals...] | body locals | scratch
  let mut paramVars : Array (VarId × Nat) := #[]
  let mut firstBodyLocal : Nat := 0
  let mut unpackPrologue : Array Instr := #[]
  let mut paramLocalTypes : Array IRType := #[]
  if packed then
    let argsLocal : Nat := 0
    let mut next := 1
    let mut paramLocals : Array Nat := #[]
    for p in params do
      paramVars := paramVars.push (p.x, next)
      paramLocals := paramLocals.push next
      paramLocalTypes := paramLocalTypes.push p.ty
      next := next + 1
    firstBodyLocal := next
    unpackPrologue := emitPackedArgsPrologue layout argsLocal paramLocals
  else
    let mut next := 0
    for p in params do
      let slots := expandLocalTypes p.ty
      let slots := if slots.isEmpty then #[.uint32] else slots
      paramVars := paramVars.push (p.x, next)
      -- wasm params occupy the first `slots.size` local indices (multi-value params)
      next := next + slots.size
    firstBodyLocal := next
  let (nextLocal, vars, bodyLocalTypes) ← collectLocals body firstBodyLocal paramVars #[]
  let scratch := nextLocal
  -- Locals section = non-parameter locals only (wasm params are outside this section).
  let localTypes : Array IRType :=
    if packed then
      paramLocalTypes ++ bodyLocalTypes.push .uint32
    else
      bodyLocalTypes.push .uint32
  let locals ← packLocals localTypes
  let bodyInstrs ← emitBody cfg env imports funcs strings dataSymbolBase #[] varTypes vars scratch body
  let instrs := unpackPrologue ++ bodyInstrs
  let code := encodeBody instrs
  let bodyBytes := Encoding.append locals code.bytes
  let size := Encoding.encodeULEB bodyBytes.size
  return {
    bytes := Encoding.append size bodyBytes
    relocs := code.relocs.map fun r => { r with offset := size.size + locals.size + r.offset }
  }

private def exportName? (env : Environment) (decl : Decl) : Option String :=
  match Lean.getExportNameFor? env decl.name with
  | some (.str .anonymous name) => some name
  | _ => none

/-- Refuse silent drops: every non-extern IR decl must be lowerable. -/
private def validateDecls (decls : Array Decl) : Except String (Array Decl) := do
  let mut funcs : Array Decl := #[]
  let mut errors : Array String := #[]
  for decl in decls do
    if decl.isExtern then continue
    if !isSupportedSignature decl then
      let params := decl.params.filter fun p => !p.ty.isVoid && p.ty != .erased
      let bad := params.filter fun p => !isSupportedType p.ty
      let reason :=
        if !isSupportedType decl.resultType then s!"result: {unsupportedReason decl.resultType}"
        else if let some p := bad[0]? then s!"param: {unsupportedReason p.ty}"
        else "unsupported signature"
      errors := errors.push s!"  {decl.name}: {reason}"
    else
      funcs := funcs.push decl
  if !errors.isEmpty then
    throw <| "WebAssembly backend: unsupported declarations (refusing silent drop):\n" ++
      "\n".intercalate errors.toList
  return funcs

def emitWasmWithConfig (cfg : EmitConfig) (env : Environment) (modName : Name) :
    Except String ByteArray := do
  if cfg.layout.ptrSize != 4 then
    throw "WebAssembly backend: only wasm32 object layout is supported until the runtime is ported"
  let decls := IR.getDecls env |>.toArray
  let funcs ← validateDecls decls
  let mut imports ← gatherImports env funcs
  for imported in env.imports do
    imports := ensureRuntimeImport imports (moduleInitName env imported.module) #[.uint8] .object
  imports := ensureRuntimeImport imports "lean_wasm_init_ok" #[] .object
  let strings := collectStrings funcs
  let dataSymbolBase := imports.size + funcs.size + 1
  let exported := funcs.filter fun decl => (exportName? env decl).isSome
  let mut typePayload := Encoding.encodeULEB (imports.size + funcs.size + 1)
  for spec in imports do
    typePayload := Encoding.append typePayload (← encodeImportType spec)
  let mut importPayload := Encoding.encodeULEB (imports.size + 2)
  importPayload := appendMany #[importPayload, Encoding.encodeName "env",
    Encoding.encodeName "__linear_memory", bytes #[0x02, 0x00], Encoding.encodeULEB 1]
  importPayload := appendMany #[importPayload, Encoding.encodeName "env",
    Encoding.encodeName "__indirect_function_table", bytes #[0x01, 0x70, 0x00], Encoding.encodeULEB 1]
  for h : idx in [:imports.size] do
    let spec := imports[idx]
    importPayload := appendMany #[importPayload, Encoding.encodeName "env",
      Encoding.encodeName spec.symbol, bytes #[0], Encoding.encodeULEB idx]
  let mut functionPayload := Encoding.encodeULEB (funcs.size + 1)
  let mut codePayload := Encoding.encodeULEB (funcs.size + 1)
  let mut relocs : Array Wasm.Object.Relocation := #[]
  for h : idx in [:funcs.size] do
    let decl := funcs[idx]
    typePayload := Encoding.append typePayload (← encodeType decl)
    functionPayload := Encoding.append functionPayload (Encoding.encodeULEB (imports.size + idx))
    let fn ← encodeFunction cfg env imports funcs strings dataSymbolBase decl
    let base := codePayload.size
    relocs := relocs ++ fn.relocs.map fun r =>
      { kind := r.kind, offset := base + r.offset, symbolIndex := r.symbolIndex, addend := r.addend }
    codePayload := Encoding.append codePayload fn.bytes
  typePayload := appendMany #[typePayload, bytes #[0x60, 0x01, 0x7f, 0x01, 0x7f]]
  functionPayload := Encoding.append functionPayload (Encoding.encodeULEB (imports.size + funcs.size))
  let mut initInstrs : Array Instr := #[]
  for imported in env.imports do
    let idx ← lookupRuntime imports (moduleInitName env imported.module)
    initInstrs := initInstrs ++ #[.localGet 0, .call idx idx, .drop]
  let initOk ← lookupRuntime imports "lean_wasm_init_ok"
  initInstrs := initInstrs ++ #[.call initOk initOk]
  let initCode := encodeBody initInstrs
  let initBody := Encoding.append (Encoding.encodeULEB 0) initCode.bytes
  let initSize := Encoding.encodeULEB initBody.size
  let initBase := codePayload.size
  relocs := relocs ++ initCode.relocs.map fun r =>
    { kind := r.kind, offset := initBase + initSize.size + 1 + r.offset,
      symbolIndex := r.symbolIndex, addend := r.addend }
  codePayload := Encoding.append codePayload <| Encoding.append initSize initBody
  let initName := mkModuleInitializationFunctionName modName env.getModulePackage?
  let mut exportPayload := Encoding.encodeULEB exported.size
  for decl in exported do
    let some name := exportName? env decl | unreachable!
    let idx := imports.size + (← lookupFun funcs decl.name)
    exportPayload := appendMany #[exportPayload, Encoding.encodeName name, bytes #[0x00],
      Encoding.encodeULEB idx]
  let mut elementPayload := appendMany #[Encoding.encodeULEB 1, bytes #[0x00, 0x41, 0x01, 0x0b],
    Encoding.encodeULEB funcs.size]
  for h : idx in [:funcs.size] do
    elementPayload := Encoding.append elementPayload (Encoding.encodeULEB (imports.size + idx))
  let mut sections : Array Wasm.Section := #[
    ⟨0x01, typePayload⟩, ⟨0x02, importPayload⟩, ⟨0x03, functionPayload⟩,
    ⟨0x07, exportPayload⟩, ⟨0x09, elementPayload⟩]
  if !strings.isEmpty then
    sections := sections.push ⟨0x0c, Encoding.encodeULEB strings.size⟩
  sections := sections.push ⟨0x0a, codePayload⟩
  let mut dataPayload := Encoding.encodeULEB strings.size
  for value in strings do
    let data := value.toUTF8.push 0
    dataPayload := appendMany #[dataPayload, bytes #[0x00, 0x41, 0x00, 0x0b],
      Encoding.encodeULEB data.size, data]
  if !strings.isEmpty then
    sections := sections.push ⟨0x0b, dataPayload⟩
  let module : Wasm.Module := { sections }
  let importSymbols := imports.mapIdx fun idx spec =>
    { name := spec.symbol, functionIndex := idx, undefined := true : Wasm.Object.FunctionSymbol }
  let symbols := importSymbols ++ funcs.mapIdx fun idx decl =>
    { name := (exportName? env decl).getD decl.name.mangle, functionIndex := imports.size + idx,
      exported := (exportName? env decl).isSome : Wasm.Object.FunctionSymbol }
  let symbols := symbols.push {
    name := initName, functionIndex := imports.size + funcs.size, global := true }
  let dataSymbols := strings.mapIdx fun idx value =>
    { name := s!".Llean.str.{idx}", segmentIndex := idx, size := value.toUTF8.size + 1 :
      Wasm.Object.DataSymbol }
  let segments := strings.mapIdx fun idx _ =>
    { name := s!".rodata.lean.str.{idx}" : Wasm.Object.SegmentInfo }
  let functionNames :=
    (imports.mapIdx fun idx spec => (idx, spec.symbol)) ++
    (funcs.mapIdx fun idx decl =>
      (imports.size + idx, (exportName? env decl).getD decl.name.toString)) ++
    #[(imports.size + funcs.size, initName)]
  return (Wasm.Object.withLinking module symbols relocs dataSymbols segments
    (moduleName := modName.toString) (functionNames := functionNames)
    (emitDebugNames := cfg.emitDebugNames)).encode

def emitWasm (env : Environment) (modName : Name) : Except String ByteArray :=
  emitWasmWithConfig {} env modName

end Lean.Compiler.Backend.EmitWasm
