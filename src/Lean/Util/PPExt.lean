/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Environment
import Lean.Syntax
import Lean.MetavarContext
import Lean.Data.OpenDecl

namespace Lean
register_builtin_option pp.raw : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) print raw expression/syntax tree"
}
register_builtin_option pp.raw.showInfo : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) print `SourceInfo` metadata with raw printer"
}
register_builtin_option pp.raw.maxDepth : Nat := {
  defValue := 32
  group    := "pp"
  descr    := "(pretty printer) maximum `Syntax` depth for raw printer"
}

structure PPContext where
  env           : Environment
  mctx          : MetavarContext := {}
  lctx          : LocalContext := {}
  opts          : Options := {}
  currNamespace : Name := Name.anonymous
  openDecls     : List OpenDecl := []

structure PPFns where
  ppExpr : PPContext → Expr → IO Format
  ppTerm : PPContext → Syntax → IO Format
  ppGoal : PPContext → MVarId → IO Format

instance : Inhabited PPFns := ⟨⟨arbitrary, arbitrary, arbitrary⟩⟩

builtin_initialize ppFnsRef : IO.Ref PPFns ←
  IO.mkRef {
    ppExpr := fun ctx e      => return format (toString e),
    ppTerm := fun ctx stx    => return stx.formatStx (some <| pp.raw.maxDepth.get ctx.opts)
    ppGoal := fun ctx mvarId => return "goal"
  }

builtin_initialize ppExt : EnvExtension PPFns ←
  registerEnvExtension ppFnsRef.get

def ppExpr (ctx : PPContext) (e : Expr) : IO Format := do
  let e := ctx.mctx.instantiateMVars e |>.1
  if pp.raw.get ctx.opts then
    return format (toString e)
  else
    try
      ppExt.getState ctx.env |>.ppExpr ctx e
    catch ex =>
      pure f!"[Error pretty printing expression: {ex}. Falling back to raw printer.]{Format.line}{e}"

def ppTerm (ctx : PPContext) (stx : Syntax) : IO Format :=
  if pp.raw.get ctx.opts then
    return stx.formatStx (some <| pp.raw.maxDepth.get ctx.opts) (pp.raw.showInfo.get ctx.opts)
  else
    try
      ppExt.getState ctx.env |>.ppTerm ctx stx
    catch ex =>
      pure f!"[Error pretty printing syntax: {ex}. Falling back to raw printer.]{Format.line}{stx}"

def ppGoal (ctx : PPContext) (mvarId : MVarId) : IO Format :=
    ppExt.getState ctx.env |>.ppGoal ctx mvarId

end Lean
