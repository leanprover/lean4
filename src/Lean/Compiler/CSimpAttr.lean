/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.ScopedEnvExtension
public import Lean.Util.Recognizers
public import Lean.Linter.Init
import Lean.Compiler.NoncomputableAttr
import Lean.ProjFns
import Lean.ExtraModUses

public section

namespace Lean

/--
Enables the `csimpNoncomputable` linter, which warns when a `@[csimp]` theorem replaces a
definition that is not marked `noncomputable`. A `@[csimp]` theorem only affects code compiled after
it, so code compiled before it may still call the slow definition; marking the definition
`noncomputable` turns such uses into errors.

Recursors and structure projections cannot be marked `noncomputable` and are exempt.

This linter is off by default. It is a member of the `linter.coreInternal` set, so it is enabled
when building Lean itself.
-/
register_builtin_option linter.csimpNoncomputable : Bool := {
  defValue := false
  descr := "enable the `csimpNoncomputable` linter, which warns when a `@[csimp]` theorem \
    replaces a definition that is not marked `noncomputable`."
}

namespace Compiler
namespace CSimp

structure Entry where
  fromDeclName : Name
  toDeclName   : Name
  thmName      : Name
  deriving Inhabited

structure State where
  /-- Map from `e.fromDeclName` to `e` -/
  map : SMap Name Entry := {}
  thmNames : SSet Name := {}
  deriving Inhabited

def State.switch : State → State
  | { map, thmNames } => { map := map.switch, thmNames := thmNames.switch }

builtin_initialize ext : SimpleScopedEnvExtension Entry State ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := fun { map, thmNames } e => { map := map.insert e.fromDeclName e, thmNames := thmNames.insert e.thmName }
    finalizeImport := fun s => s.switch
  }

private def isConstantReplacement? (declName : Name) : CoreM (Option Entry) := do
  let info ← getConstVal declName
  match info.type.eq? with
  | some (_, Expr.const fromDeclName us, Expr.const toDeclName vs) =>
    let set := Std.HashSet.ofList us
    if set.size == us.length && set.all Level.isParam && us == vs then
      return some { fromDeclName, toDeclName, thmName := declName }
    else
      return none
  | _ => return none

private def lintComputable (fromDeclName : Name) : CoreM Unit := do
  unless Linter.getLinterValue linter.csimpNoncomputable (← Linter.getLinterOptions) do
    return
  let env ← getEnv
  if isNoncomputable env fromDeclName then return
  if ← isRec fromDeclName then return
  if env.isProjectionFn fromDeclName then return
  Linter.logLint linter.csimpNoncomputable (← getRef)
    m!"`{.ofConstName fromDeclName}` is replaced by a `@[csimp]` theorem but is not marked \
      `noncomputable`, so code compiled before this theorem may still use the slow definition."

def add (declName : Name) (kind : AttributeKind) : CoreM Unit := do
  if let some entry ← isConstantReplacement? declName then
    lintComputable entry.fromDeclName
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
      ensureAttrDeclIsPublic `csimp declName attrKind
      discard <| add declName attrKind
  }

/-- If `e` (as a whole) matches a `[csimp]` theorem, returns the replacement expression. -/
def replaceConstant? (env : Environment) (e : Expr) : CoreM (Option Expr) := do
  let s := ext.getState env
  let .const declName _ := e | return none
  if let some ent := s.map.find? declName then
    withoutExporting <| recordExtraModUseFromDecl (isMeta := false) ent.thmName
    return some (mkConst ent.toDeclName e.constLevels!)
  else
    return none

/--
If `e` (as a whole) matches a `[csimp]` theorem, returns the replacement expression, or else `e`.
-/
def replaceConstant (env : Environment) (e : Expr) : CoreM Expr :=
  return (← replaceConstant? env e).getD e

end CSimp

def hasCSimpAttribute (env : Environment) (declName : Name) : Bool :=
  CSimp.ext.getState env |>.thmNames.contains declName

end Compiler
end Lean
