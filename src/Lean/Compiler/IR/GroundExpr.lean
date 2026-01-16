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
  deriving Inhabited

public inductive GroundExpr where
  | ctor (idx : Nat) (args : Array GroundArg)
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

structure State where
  groundMap : Std.HashMap VarId GroundArg := {}

abbrev M := StateRefT State $ OptionT CompilerM

def compileToGroundExpr (b : FnBody) : CompilerM (Option GroundExpr) :=
  compileFnBody b |>.run' {} |>.run
where
  compileFnBody (b : FnBody) : M GroundExpr := do
    match b with
    | .vdecl id ty expr (.ret (.var id')) =>
      guard <| id == id'
      compileFinalExpr ty expr
    | .vdecl id ty expr b =>
      let groundArg ← compileArgExpr ty expr
      modify fun s => { s with groundMap := s.groundMap.insert id groundArg }
      compileFnBody b
    | _ => failure

  compileArgExpr (ty : IRType) (e : Expr) : M GroundArg := do
    match e with
    | .fap c #[] =>
      guard <| isGroundDecl (← getEnv) c
      return .reference c
    | .lit v =>
      match v with
      | .num v =>
        guard <| ty == .tagged && v < 2^31
        return .tagged v
      | .str .. => failure
    | .ctor i #[] => return .tagged i.cidx
    | _ => failure

  compileFinalExpr (ty : IRType) (e : Expr) : M GroundExpr := do
    match e with
    | .lit v =>
      match v with
      | .str v => return .string v
      | .num .. => failure
    | .ctor i args =>
      guard <| i.usize == 0 && i.ssize == 0 && !args.isEmpty
      return .ctor i.cidx (← compileArgs args)
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
        let .reference name := (← get).groundMap[var]! | failure
        let some (.string val) := getGroundExpr (← getEnv) name | failure
        return (name, val)
      return .nameMkStr args
    | .pap c ys => return .pap c (← compileArgs ys)
    | _ => failure

  compileArgs (args : Array Arg) : M (Array GroundArg) := do
    args.mapM fun arg => do
      match arg with
      | .var var => return (← get).groundMap[var]!
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
