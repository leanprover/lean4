/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez, Sebastian Ullrich
-/
module

prelude
public import Lean.Compiler.LCNF.Basic
public import Lean.Compiler.Bytecode.Instruction

/-!
`@[export]`ed evaluation primitives
-/

namespace Lean.Compiler.Bytecode

/--
Checks meta availability just before `evalConst`. This is a "last line of defense" as accesses
should have been checked at declaration time in case of attributes. We do not solely want to rely on
errors from the interpreter itself as those depend on whether we are running in the server.
-/
@[export lean_eval_check_meta]
partial def evalCheckMeta (env : Environment) (declName : Name) : Except String Unit := do
  if getIRPhases env declName == .runtime then
      throw s!"Cannot evaluate constant `{declName}` as it is neither marked nor imported as `meta`"

/-- `code` should put the result in register 0 -/
def simpleBytecodeDecl (code : Array Instruction) (symbols : Array Name) :
    BytecodeDecl where
  name := .anonymous
  code := assemble <| #[.skipIfCached (code.size + 1).toUInt32] ++ code ++ #[.storeCache 0, .ret 0]
  stackReserved := 1
  stackSpace := 0
  symbols
  cache := .mkEmpty ..
  arity := 0
  constants := #[]
  sorryDep? := none

open LCNF.ImpureType in
@[export lean_eval_const]
unsafe def evalConstCoreImpl (env : Environment)
    (_opts : Options) (constName : Name) : Except String NonScalar := do
  let boxedName := LCNF.mkBoxedName constName
  if let some _sig := LCNF.getSigCore? env LCNF.impureSigExt boxedName then
    if let some bytecode := findBytecodeDecl env boxedName then
      if let some sorryDep := bytecode.sorryDep? then
        throw s!"cannot evaluate code because '{sorryDep}' uses 'sorry' and/or contains errors"
    -- boxed declarations are nice, we don't need much glue code
    let runtimeDecl : BytecodeDecl := simpleBytecodeDecl #[.pap 0 0] #[boxedName]
    return runtimeDecl.eval NonScalar env
  let some sig := LCNF.getSigCore? env LCNF.impureSigExt constName |
    throw s!"(interpreter) unknown declaration {constName}"
  if let some bytecode := findBytecodeDecl env constName then
    if let some sorryDep := bytecode.sorryDep? then
      throw s!"cannot evaluate code because '{sorryDep}' uses 'sorry' and/or contains errors"
  let mut code : Array Instruction := #[]
  if sig.params.isEmpty then
    code := #[.loadConst 0]
    match sig.type with
    | uint8 | uint16 => code := code.push (.boxSmall 0 0)
    | uint32 => code := code.push (.boxUInt32 0 0)
    | uint64 => code := code.push (.boxUInt64 0 0)
    | usize => code := code.push (.boxUSize 0 0)
    | float => code := code.push (.boxFloat 0 0)
    | float32 => code := code.push (.boxFloat32 0 0)
    | tobject | object => code := code.push (.inc 0 1)
    | tagged | erased | void => pure ()
    | _ => unreachable!
  else
    assert! sig.params.all (!·.borrow) && !sig.type.isScalar && sig.params.all (!·.type.isScalar)
      && sig.params.all (!·.type.isVoid) && sig.params.size <= 16
    -- there are parameters but no boxed version
    -- so the declaration is `pap` compatible
    code := #[.pap 0 0]
  let runtimeDecl : BytecodeDecl := simpleBytecodeDecl code #[constName]
  return runtimeDecl.eval NonScalar env

@[export lean_run_init]
unsafe def runInitImpl (env : Environment) (opts : Options) (decl initDecl : Name) : IO Unit := do
  let some decl := findBytecodeDecl env decl |
    throw (.userError s!"Could not find declaration to be initialized: `{decl}`")
  let act ← IO.ofExcept <| evalConstCoreImpl env opts initDecl
  let out ← (unsafeCast act : IO NonScalar)
  let out ← Runtime.markPersistent out
  decl.setInitValue out

@[extern "lean_io_result_show_error"]
unsafe opaque showError (e : @& EST.Out IO.Error IO.RealWorld α) : BaseIO Unit

def isIOUnit (e : Expr) : Bool :=
  e matches .app (.const ``IO _) (.const ``Unit _) | .app (.const ``IO _) (.const ``PUnit _)

def isIOUInt32 (e : Expr) : Bool :=
  e matches .app (.const ``IO _) (.const ``UInt32 _)

def isListString (e : Expr) : Bool :=
  e matches .app (.const ``List _) (.const ``String _)

@[export lean_eval_main]
unsafe def runMain (env : Environment) (opts : Options) (args : List String) : BaseIO UInt32 := do
  let act : IO UInt32 := do
    let some info := env.find? `main | throw (.userError "Could not find `main`")
    let rec invalidMain (_ : Unit) : IO UInt32 :=
      throw (.userError s!"Invalid type for `main`: {info.type}")
    match info.type with
    | .forallE _ d b _ =>
      unless isListString d do
        return ← invalidMain ()
      if isIOUInt32 b then
        let res ← IO.ofExcept <| evalConstCoreImpl env opts `main
        (unsafeCast res : List String → IO UInt32) args
      else if isIOUnit b then
        let res ← IO.ofExcept <| evalConstCoreImpl env opts `main
        (unsafeCast res : List String → IO Unit) args
        return 0
      else
        invalidMain ()
    | e =>
      if isIOUInt32 e then
        let res ← IO.ofExcept <| evalConstCoreImpl env opts `main
        (unsafeCast res : IO UInt32)
      else if isIOUnit e then
        let res ← IO.ofExcept <| evalConstCoreImpl env opts `main
        (unsafeCast res : IO Unit)
        return 0
      else
        invalidMain ()
  fun void =>
    let res := act void
    match res with
    | .ok res s => .mk res s
    | .error _ s =>
      let ⟨(), s⟩ := showError res s
      .mk 1 s

end Lean.Compiler.Bytecode
