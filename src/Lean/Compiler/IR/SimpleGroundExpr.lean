/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.IR.CompilerM
import Init.While

/-!
This module contains logic for detecting simple ground expressions that can be extracted into
statically initializable variables. To do this it attempts to compile declarations into
a simple language of expressions, `SimpleGroundExpr`. If this attempt succeeds it stores the result
in an environment extension, accessible through `getSimpleGroundExpr`. Later on the code emission
step can reference this environment extension to generate static initializers for the respective
declaration.
-/

namespace Lean

namespace IR

/--
An argument to a `SimpleGroundExpr`. They get compiled to `lean_object*` in various ways.
-/
public inductive SimpleGroundArg where
  /--
  A simple tagged literal.
  -/
  | tagged (val : Nat)
  /--
  A reference to another declaration that was marked as a simple ground expression. This gets
  compiled to a reference to the mangled version of the name.
  -/
  | reference (n : Name)
  /--
  A reference directly to a raw C name. This gets compiled to a reference to the name directly.
  -/
  | rawReference (s : String)
  deriving Inhabited

/--
A simple ground expression that can be turned into a static initializer.
-/
public inductive SimpleGroundExpr where
  /--
  Represents a `lean_ctor_object`. Crucially the `scalarArgs` array must have a size that is a
  multiple of 8.
  -/
  | ctor (cidx : Nat) (objArgs : Array SimpleGroundArg) (usizeArgs : Array USize) (scalarArgs : Array UInt8)
  /--
  A string literal, represented by a `lean_string_object`.
  -/
  | string (data : String)
  /--
  A partial application, represented by a `lean_closure_object`.
  -/
  | pap (func : FunId) (args : Array SimpleGroundArg)
  /--
  An application of `Lean.Name.mkStrX`. This expression is represented separately to ensure that
  long name literals get extracted into statically initializable constants. The arguments contain
  both the name of the string literal it references as well as the hash of the name up to that
  point. This is done to make emitting the literal as simple as possible.
  -/
  | nameMkStr (args : Array (Name × UInt64))
  /--
  A reference to another declaration that was marked as a simple ground expression. This gets
  compiled to a reference to the mangled version of the name.
  -/
  | reference (n : Name)
  deriving Inhabited

public structure SimpleGroundExtState where
  constNames : PHashMap Name SimpleGroundExpr := {}
  revNames : List Name := []
  deriving Inhabited

builtin_initialize simpleGroundDeclExt : EnvExtension SimpleGroundExtState ←
  registerEnvExtension (pure {}) (asyncMode := .sync)
    (replay? := some fun oldState newState _ s =>
      let newNames := newState.revNames.take (newState.revNames.length - oldState.revNames.length)
      newNames.foldl (init := s) fun s n =>
        let g := newState.constNames.find! n
        { s with constNames := s.constNames.insert n g, revNames := n :: s.revNames }
    )

/--
Record `declName` as mapping to the simple ground expr `expr`.
-/
public def addSimpleGroundDecl (env : Environment) (declName : Name) (expr : SimpleGroundExpr) :
    Environment :=
  simpleGroundDeclExt.modifyState env fun s =>
    { s with constNames := s.constNames.insert declName expr, revNames := declName :: s.revNames }

/--
Attempt to fetch a `SimpleGroundExpr` associated with `declName` if it exists.
-/
public def getSimpleGroundExpr (env : Environment) (declName : Name) : Option SimpleGroundExpr :=
  (simpleGroundDeclExt.getState env).constNames.find? declName

/--
Like `getSimpleGroundExpr` but recursively traverses `reference` exprs to get to actual ground
values.
-/
public def getSimpleGroundExprWithResolvedRefs (env : Environment) (declName : Name) :
    Option SimpleGroundExpr := Id.run do
  let mut declName := declName
  while true do
    let val := getSimpleGroundExpr env declName
    match val with
    | some (.reference ref) => declName := ref
    | other => return other
  return none

/--
Check if `declName` is recorded as being a `SimpleGroundExpr`.
-/
public def isSimpleGroundDecl (env : Environment) (declName : Name) : Bool :=
  (simpleGroundDeclExt.getState env).constNames.contains declName

public def uint64ToByteArrayLE (n : UInt64) : Array UInt8 :=
  #[
    n.toUInt8,
    (n >>> 0x08).toUInt8,
    (n >>> 0x10).toUInt8,
    (n >>> 0x18).toUInt8,
    (n >>> 0x20).toUInt8,
    (n >>> 0x28).toUInt8,
    (n >>> 0x30).toUInt8,
    (n >>> 0x38).toUInt8,
  ]


inductive SimpleGroundValue where
  | arg (arg : SimpleGroundArg)
  | uint8 (val : UInt8)
  | uint16 (val : UInt16)
  | uint32 (val : UInt32)
  | uint64 (val : UInt64)
  | usize (val : USize)
  deriving Inhabited

structure State where
  groundMap : Std.HashMap VarId SimpleGroundValue := {}

abbrev M := StateRefT State $ OptionT CompilerM

/--
Attempt to compile `b` into a `SimpleGroundExpr`. If `b` is not compileable return `none`.

The compiler currently supports the following patterns:
- String literals
- Partial applications with other simple expressions
- Constructor calls with other simple expressions
- `Name.mkStrX`, `Name.str._override`, and `Name.num._override`
- references to other declarations marked as simple ground expressions
-/
partial def compileToSimpleGroundExpr (b : FnBody) : CompilerM (Option SimpleGroundExpr) :=
  compileFnBody b |>.run' {} |>.run
where
  compileFnBody (b : FnBody) : M SimpleGroundExpr := do
    match b with
    | .vdecl id _ expr (.ret (.var id')) =>
      guard <| id == id'
      compileFinalExpr expr
    | .vdecl id ty expr b => compileNonFinalExpr id ty expr b
    | _ => failure

  @[inline]
  record (id : VarId) (val : SimpleGroundValue) : M Unit :=
    modify fun s => { s with groundMap := s.groundMap.insert id val }

  compileNonFinalExpr (id : VarId) (ty : IRType) (expr : Expr) (b : FnBody) : M SimpleGroundExpr := do
    match expr with
    | .fap c #[] =>
      guard <| isSimpleGroundDecl (← getEnv) c
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
        compileSetChain id i objArgs usizeArgs ssizeArgs b
    | _ => failure

  compileSetChain (id : VarId) (info : CtorInfo) (objArgs : Array SimpleGroundArg) (usizeArgs : Array USize)
      (scalarArgs : Array UInt8) (b : FnBody) : M SimpleGroundExpr := do
    match b with
    | .ret (.var id') =>
      guard <| id == id'
      return .ctor info.cidx objArgs usizeArgs scalarArgs
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
      compileSetChain id info objArgs usizeArgs scalarArgs b
    | .uset id' i y b =>
      guard <| id == id'
      let i := i - objArgs.size
      let .usize v := (← get).groundMap[y]! | failure
      let usizeArgs := usizeArgs.set! i v
      compileSetChain id info objArgs usizeArgs scalarArgs b
    | _ => failure

  compileFinalExpr (e : Expr) : M SimpleGroundExpr := do
    match e with
    | .lit v =>
      match v with
      | .str v => return .string v
      | .num .. => failure
    | .ctor i args =>
      guard <| i.usize == 0 && i.ssize == 0 && !args.isEmpty
      return .ctor i.cidx (← compileArgs args) #[] #[]
    | .fap ``Name.num._override args =>
      let pre ← compileArg args[0]!
      let .tagged i ← compileArg args[1]! | failure
      let name := Name.num (← interpNameLiteral pre) i
      let hash := name.hash
      return .ctor 2 #[pre, .tagged i] #[] (uint64ToByteArrayLE hash)
    | .fap ``Name.str._override args =>
      let pre ← compileArg args[0]!
      let (ref, str) ← compileStrArg args[1]!
      let name := Name.str (← interpNameLiteral pre) str
      let hash := name.hash
      return .ctor 1 #[pre, .reference ref] #[] (uint64ToByteArrayLE hash)
    | .fap ``Name.mkStr1 args
    | .fap ``Name.mkStr2 args
    | .fap ``Name.mkStr3 args
    | .fap ``Name.mkStr4 args
    | .fap ``Name.mkStr5 args
    | .fap ``Name.mkStr6 args
    | .fap ``Name.mkStr7 args
    | .fap ``Name.mkStr8 args =>
      let mut nameAcc := Name.anonymous
      let mut processedArgs := Array.emptyWithCapacity args.size
      for arg in args do
        let (ref, str) ← compileStrArg arg
        nameAcc := .str nameAcc str
        processedArgs := processedArgs.push (ref, nameAcc.hash)
      return .nameMkStr processedArgs
    | .pap c ys => return .pap c (← compileArgs ys)
    | .fap c #[] =>
      guard <| isSimpleGroundDecl (← getEnv) c
      return .reference c
    | _ => failure

  compileArg (arg : Arg) : M SimpleGroundArg := do
    match arg with
    | .var var =>
      let .arg arg := (← get).groundMap[var]! | failure
      return arg
    | .erased => return .tagged 0

  compileArgs (args : Array Arg) : M (Array SimpleGroundArg) := do
    args.mapM compileArg

  compileStrArg (arg : Arg) : M (Name × String) := do
    let .var var := arg | failure
    let (.arg (.reference ref)) := (← get).groundMap[var]! | failure
    let some (.string val) := getSimpleGroundExprWithResolvedRefs (← getEnv) ref | failure
    return (ref, val)

  interpStringLiteral (arg : SimpleGroundArg) : M String := do
    let .reference ref := arg | failure
    let some (.string val) := getSimpleGroundExprWithResolvedRefs (← getEnv) ref | failure
    return val

  interpNameLiteral (arg : SimpleGroundArg) : M Name := do
    match arg with
    | .tagged 0 => return .anonymous
    | .reference ref =>
      match getSimpleGroundExprWithResolvedRefs (← getEnv) ref with
      | some (.ctor 1 #[pre, .reference ref] _ _) =>
        let pre ← interpNameLiteral pre
        let str ← interpStringLiteral (.reference ref)
        return .str pre str
      | some (.ctor 2 #[pre, .tagged i] _ _) =>
        let pre ← interpNameLiteral pre
        return .num pre i
      | some (.nameMkStr args) =>
        args.foldlM (init := .anonymous) fun acc (ref, _) => do
          let part ← interpStringLiteral (.reference ref)
          return .str acc part
      | _ => failure
    | _ => failure


/--
Detect whether `d` can be compiled to a `SimpleGroundExpr`. If it can record the associated
`SimpleGroundExpr` into the environment for later processing by code emission.
-/
public def Decl.detectSimpleGround (d : Decl) : CompilerM Unit := do
  let .fdecl (body := body) (xs := params) (type := type) .. := d | return ()
  if type.isPossibleRef && params.isEmpty then
    if let some groundExpr ← compileToSimpleGroundExpr body then
      trace[compiler.ir.simple_ground] m!"Marked {d.name} as simple ground expr"
      modifyEnv fun env => addSimpleGroundDecl env d.name groundExpr

builtin_initialize registerTraceClass `compiler.ir.simple_ground (inherited := true)

end IR

end Lean
