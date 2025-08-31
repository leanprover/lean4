/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.ScopedEnvExtension
public import Lean.Util.Recognizers
public import Lean.Util.ReplaceExpr

public section

namespace Lean.Compiler
namespace CSimp

structure Entry where
  fromDeclName : Name
  toDeclName   : Name
  thmName      : Name
  deriving Inhabited

structure State where
  map : SMap Name Name := {}
  thmNames : SSet Name := {}
  deriving Inhabited

def State.switch : State → State
  | { map, thmNames } => { map := map.switch, thmNames := thmNames.switch }

builtin_initialize ext : SimpleScopedEnvExtension Entry State ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := fun { map, thmNames } { fromDeclName, toDeclName, thmName } => { map := map.insert fromDeclName toDeclName, thmNames := thmNames.insert thmName }
    finalizeImport := fun s => s.switch
  }

private def isConstantReplacement? (declName : Name) : CoreM (Option Entry) := do
  let info ← getConstInfo declName
  match info.type.eq? with
  | some (_, Expr.const fromDeclName us .., Expr.const toDeclName vs ..) =>
    if us == vs then
      return some { fromDeclName, toDeclName, thmName := declName }
    else
      return none
  | _ => return none

def add (declName : Name) (kind : AttributeKind) : CoreM Unit := do
  if let some entry ← isConstantReplacement? declName then
    ext.add entry kind
  else
    throwError "invalid 'csimp' theorem, only constant replacement theorems (e.g., `@f = @g`) are currently supported."

/--
Tags compiler simplification theorems, which allow one value to be replaced by another equal value
in compiled code. This is typically used to replace a slow function whose definition is convenient
in proofs with a faster equivalent or to make noncomputable functions computable. In particular,
many operations on lists and arrays are replaced by tail-recursive equivalents.

A compiler simplification theorem cannot take any parameters and must prove a statement `@f = @g`
where `f` and `g` may be arbitrary constants. In functions defined after the theorem tagged
`@[csimp]`, any occurrence of `f` is replaced with `g` in compiled code, but not in the type
theory. In this sense, `@[csimp]` is a safer alternative to `@[implemented_by]`.

However it is still possible to register unsound `@[csimp]` lemmas by using `unsafe` or unsound
axioms (like `sorryAx`).
-/
@[builtin_init, builtin_doc]
private def initFn :=
  registerBuiltinAttribute {
    name  := `csimp
    descr := "simplification theorem for the compiler"
    add   := fun declName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      discard <| add declName attrKind
  }

def replaceConstants (env : Environment) (e : Expr) : Expr :=
  let s := ext.getState env
  e.replace fun e =>
    if e.isConst then
      match s.map.find? e.constName! with
      | some declNameNew => some (mkConst declNameNew e.constLevels!)
      | none => none
    else
      none

end CSimp

def hasCSimpAttribute (env : Environment) (declName : Name) : Bool :=
  CSimp.ext.getState env |>.thmNames.contains declName

end Lean.Compiler
