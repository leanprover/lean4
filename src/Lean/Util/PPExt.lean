/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Lean.Environment
import Lean.MetavarContext
import Lean.Data.OpenDecl
import Lean.Elab.InfoTree.Types

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
register_builtin_option pp.rawOnError : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) fallback to 'raw' printer when pretty printer fails"
}

structure PPContext where
  env           : Environment
  mctx          : MetavarContext := {}
  lctx          : LocalContext := {}
  opts          : Options := {}
  currNamespace : Name := Name.anonymous
  openDecls     : List OpenDecl := []

abbrev PrettyPrinter.InfoPerPos := RBMap Nat Elab.Info compare
/-- A format tree with `Elab.Info` annotations.
Each `.tag n _` node is annotated with `infos[n]`.
This is used to attach semantic data such as expressions
to pretty-printer outputs. -/
structure FormatWithInfos where
  fmt : Format
  infos : PrettyPrinter.InfoPerPos
instance : Coe Format FormatWithInfos where
  coe fmt := { fmt, infos := ∅ }

structure PPFns where
  ppExprWithInfos : PPContext → Expr → IO FormatWithInfos
  ppConstNameWithInfos : PPContext → Name → IO FormatWithInfos
  ppTerm : PPContext → Term → IO Format
  ppLevel : PPContext → Level → IO Format
  ppGoal : PPContext → MVarId → IO Format
  deriving Inhabited

builtin_initialize ppFnsRef : IO.Ref PPFns ←
  IO.mkRef {
    ppExprWithInfos := fun _ e => return format (toString e)
    ppConstNameWithInfos := fun _ n => return format n
    ppTerm := fun ctx stx => return stx.raw.formatStx (some <| pp.raw.maxDepth.get ctx.opts)
    ppLevel := fun _ l => return format l
    ppGoal := fun _ _ => return "goal"
  }

builtin_initialize ppExt : EnvExtension PPFns ←
  registerEnvExtension ppFnsRef.get

def ppExprWithInfos (ctx : PPContext) (e : Expr) : IO FormatWithInfos := do
  if pp.raw.get ctx.opts then
    let e := instantiateMVarsCore ctx.mctx e |>.1
    return format (toString e)
  else
    try
      ppExt.getState ctx.env |>.ppExprWithInfos ctx e
    catch ex =>
      if pp.rawOnError.get ctx.opts then
        pure f!"[Error pretty printing expression: {ex}. Falling back to raw printer.]{Format.line}{e}"
      else
        pure f!"failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)"

def ppConstNameWithInfos (ctx : PPContext) (n : Name) : IO FormatWithInfos :=
  ppExt.getState ctx.env |>.ppConstNameWithInfos ctx n

def ppTerm (ctx : PPContext) (stx : Term) : IO Format :=
  let fmtRaw := fun () => stx.raw.formatStx (some <| pp.raw.maxDepth.get ctx.opts) (pp.raw.showInfo.get ctx.opts)
  if pp.raw.get ctx.opts then
    return fmtRaw ()
  else
    try
      ppExt.getState ctx.env |>.ppTerm ctx stx
    catch ex =>
      if pp.rawOnError.get ctx.opts then
        pure f!"[Error pretty printing syntax: {ex}. Falling back to raw printer.]{Format.line}{fmtRaw ()}"
      else
        pure f!"failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)"

def ppLevel (ctx : PPContext) (l : Level) : IO Format :=
  ppExt.getState ctx.env |>.ppLevel ctx l

def ppGoal (ctx : PPContext) (mvarId : MVarId) : IO Format :=
  ppExt.getState ctx.env |>.ppGoal ctx mvarId

end Lean
