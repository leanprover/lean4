/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.IR.CompilerM
public import Lean.EnvExtension
import Lean.Compiler.ClosedTermCache

namespace Lean

namespace IR

public inductive GroundArg where
  | tagged (val : Nat)
  | reference (n : Name)
  | rawReference (s : String)
  deriving Inhabited

public inductive GroundExpr where
  /--
  TODO: Crucial!!! scalarArgs must be padded to 8
  -/
  | ctor (idx : Nat) (objArgs : Array GroundArg) (usizeArgs : Array USize) (scalarArgs : Array UInt8)
  | string (data : String)
  | pap (func : FunId) (args : Array GroundArg)
  | nameMkStr (args : Array (Name × String))
  deriving Inhabited

public structure GroundExtState where
  constNames : PHashMap Name GroundExpr := {}
  revNames : List Name := []
  deriving Inhabited

builtin_initialize groundDeclExt : EnvExtension GroundExtState ←
  registerEnvExtension (pure {}) (asyncMode := .sync)
    (replay? := some fun oldState newState _ s =>
      let newNames := newState.revNames.take (newState.revNames.length - oldState.revNames.length)
      newNames.foldl (init := s) fun s n =>
        let g := newState.constNames.find! n
        { s with constNames := s.constNames.insert n g, revNames := n :: s.revNames }
    )

public def addGroundDecl (env : Environment) (declName : Name) (expr : GroundExpr) : Environment :=
  groundDeclExt.modifyState env fun s =>
    { s with constNames := s.constNames.insert declName expr, revNames := declName :: s.revNames }

public def getGroundExpr (env : Environment) (declName : Name) : Option GroundExpr :=
  (groundDeclExt.getState env).constNames.find? declName

public def isGroundDecl (env : Environment) (declName : Name) : Bool :=
  (groundDeclExt.getState env).constNames.contains declName

inductive GroundValue where
  | arg (arg : GroundArg)
  | uint8 (val : UInt8)
  | uint16 (val : UInt16)
  | uint32 (val : UInt32)
  | uint64 (val : UInt64)
  | usize (val : USize)
  deriving Inhabited

structure State where
  groundMap : Std.HashMap VarId GroundValue := {}

abbrev M := StateRefT State $ OptionT CompilerM

partial def compileToGroundExpr (b : FnBody) : CompilerM (Option GroundExpr) :=
  compileFnBody b |>.run' {} |>.run
where
  compileFnBody (b : FnBody) : M GroundExpr := do
    match b with
    | .vdecl id ty expr (.ret (.var id')) =>
      guard <| id == id'
      compileFinalExpr ty expr
    | .vdecl id ty expr b => compileNonFinalExpr id ty expr b
    | _ => failure

  @[inline]
  record (id : VarId) (val : GroundValue) : M Unit :=
    modify fun s => { s with groundMap := s.groundMap.insert id val }
    
  compileNonFinalExpr (id : VarId) (ty : IRType) (expr : Expr) (b : FnBody) : M GroundExpr := do
    match expr with
    | .fap c #[] =>
      guard <| isGroundDecl (← getEnv) c
      record id (.arg (.reference c))
      compileFnBody b
    | .lit v =>
      match v with
      | .num v =>
        match ty with
        | .tagged =>
          guard <| v < 2^31
          record id (.arg (.tagged v))
        | .uint8 => record id (.uint8 (.ofNat v))
        | .uint16 => record id (.uint16 (.ofNat v))
        | .uint32 => record id (.uint32 (.ofNat v))
        | .uint64 => record id (.uint64 (.ofNat v))
        | .usize => record id (.usize (.ofNat v))
        | _ => failure
        compileFnBody b
      | .str .. => failure
    | .ctor i objArgs =>
      if i.isScalar then
        record id (.arg (.tagged i.cidx))
        compileFnBody b
      else
        let objArgs ← compileArgs objArgs
        let usizeArgs := Array.replicate i.usize 0
        -- Align to 8 bytes for alignment with lean_object*
        let align (v a : Nat) : Nat :=
          (v / a) * a + a * (if v % a != 0 then 1 else 0)
        let alignedSsize := align i.ssize 8
        let ssizeArgs := Array.replicate alignedSsize 0
        compileSetChain id i.cidx objArgs usizeArgs ssizeArgs b
    | _ => failure

  compileSetChain (id : VarId) (idx : Nat) (objArgs : Array GroundArg) (usizeArgs : Array USize)
      (scalarArgs : Array UInt8) (b : FnBody) : M GroundExpr := do
    match b with
    | .ret (.var id') =>
      guard <| id == id'
      return .ctor idx objArgs usizeArgs scalarArgs
    | .sset id' i offset y _ b =>
      guard <| id == id'
      let i := i - objArgs.size - usizeArgs.size
      let offset := i * 8 + offset
      let scalarArgs ←
        match (← get).groundMap[y]! with
        | .uint8 v =>
          let scalarArgs := scalarArgs.set! offset v
          pure scalarArgs
        | .uint16 v =>
          let scalarArgs := scalarArgs.set! offset v.toUInt8
          let scalarArgs := scalarArgs.set! (offset + 1) (v >>> 0x08).toUInt8
          pure scalarArgs
        | .uint32 v =>
          let scalarArgs := scalarArgs.set! offset v.toUInt8
          let scalarArgs := scalarArgs.set! (offset + 1) (v >>> 0x08).toUInt8
          let scalarArgs := scalarArgs.set! (offset + 2) (v >>> 0x10).toUInt8
          let scalarArgs := scalarArgs.set! (offset + 3) (v >>> 0x18).toUInt8
          pure scalarArgs
        | .uint64 v =>
          let scalarArgs := scalarArgs.set! offset v.toUInt8
          let scalarArgs := scalarArgs.set! (offset + 1) (v >>> 0x08).toUInt8
          let scalarArgs := scalarArgs.set! (offset + 2) (v >>> 0x10).toUInt8
          let scalarArgs := scalarArgs.set! (offset + 3) (v >>> 0x18).toUInt8
          let scalarArgs := scalarArgs.set! (offset + 4) (v >>> 0x20).toUInt8
          let scalarArgs := scalarArgs.set! (offset + 5) (v >>> 0x28).toUInt8
          let scalarArgs := scalarArgs.set! (offset + 6) (v >>> 0x30).toUInt8
          let scalarArgs := scalarArgs.set! (offset + 7) (v >>> 0x38).toUInt8
          pure scalarArgs
        | _ => failure
      compileSetChain id idx objArgs usizeArgs scalarArgs b
    | .uset id' i y b =>
      guard <| id == id'
      let i := i - objArgs.size
      let .usize v := (← get).groundMap[y]! | failure
      let usizeArgs := usizeArgs.set! i v
      compileSetChain id idx objArgs usizeArgs scalarArgs b
    | _ => failure

  compileFinalExpr (ty : IRType) (e : Expr) : M GroundExpr := do
    match e with
    | .lit v =>
      match v with
      | .str v => return .string v
      | .num .. => failure
    | .ctor i args =>
      guard <| i.usize == 0 && i.ssize == 0 && !args.isEmpty
      return .ctor i.cidx (← compileArgs args) #[] #[]
    | .fap ``Name.mkStr1 args
    | .fap ``Name.mkStr2 args
    | .fap ``Name.mkStr3 args
    | .fap ``Name.mkStr4 args
    | .fap ``Name.mkStr5 args
    | .fap ``Name.mkStr6 args
    | .fap ``Name.mkStr7 args
    | .fap ``Name.mkStr8 args =>
      let args ← args.mapM fun arg => do
        let .var var := arg | failure
        let (.arg (.reference name)) := (← get).groundMap[var]! | failure
        let some (.string val) := getGroundExpr (← getEnv) name | failure
        return (name, val)
      return .nameMkStr args
    | .pap c ys => return .pap c (← compileArgs ys)
    | _ => failure

  compileArgs (args : Array Arg) : M (Array GroundArg) := do
    args.mapM fun arg => do
      match arg with
      | .var var =>
        let .arg arg := (← get).groundMap[var]! | failure
        return arg
      | .erased => return .tagged 0

public def Decl.detectGround (d : Decl) : CompilerM Unit := do
  if !isClosedTermName (← getEnv) d.name then return ()
  let .fdecl (body := body) (type := type) .. := d | unreachable!
  if type.isPossibleRef then
    if let some groundExpr ← compileToGroundExpr body then
      trace[compiler.ir.ground] m!"Marked {d.name} as ground expr"
      modifyEnv fun env => addGroundDecl env d.name groundExpr

builtin_initialize registerTraceClass `compiler.ir.ground (inherited := true)

end IR

end Lean
