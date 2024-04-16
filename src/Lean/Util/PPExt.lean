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
structure FormatWithInfos where
  fmt : Format
  infos : PrettyPrinter.InfoPerPos
deriving Inhabited

instance : Coe Format FormatWithInfos where
  coe fmt := { fmt, infos := ∅ }

/-- Adds `offset` to each tag in the `Format` -/
-- We could make this a constructor so that repated shifting is more efficient
def _root_.Std.Format.shiftTag (offset : Nat) : Format → Format
  | .tag tag fmt => .tag (tag + offset) (shiftTag offset fmt)
  | .nest i fmt  => .nest i (shiftTag offset fmt)
  | .group fmt b => .group (shiftTag offset fmt) b
  | .append x y  => .append (shiftTag offset x) (shiftTag offset y)
  | fmt => fmt

def FormatWithInfos.append : FormatWithInfos → FormatWithInfos → FormatWithInfos
  | ⟨fmt1, infos1⟩, ⟨fmt2, infos2⟩ => Id.run do
    if infos1.isEmpty then return ⟨fmt1 ++ fmt2, infos2⟩
    if infos2.isEmpty then return ⟨fmt1 ++ fmt2, infos1⟩
    let (offset, _) := infos1.max!
    let fmt2' := fmt2.shiftTag offset
    let infos2' := infos2.mapKeysMono (· + offset)
      (by intros; simp [compare, compareOfLessAndEq]
          all_goals repeat (split <;> ((try rfl); try omega)))
    ⟨fmt1 ++ fmt2', .mergeBy (fun _ _ _ => panic! "disjoint maps overlap") infos1 infos2'⟩

instance AppendFormatWithInfos : Append FormatWithInfos where
  append := FormatWithInfos.append

def FormatWithInfos.nestD : FormatWithInfos → FormatWithInfos
  | ⟨fmt, infos⟩ => ⟨fmt.nestD, infos⟩

def FormatWithInfos.indentD : FormatWithInfos → FormatWithInfos
  | ⟨fmt, infos⟩ => ⟨fmt.indentD, infos⟩

structure PPFns where
  ppExprWithInfos : PPContext → Expr → IO FormatWithInfos
  ppTerm : PPContext → Term → IO Format
  ppGoal : PPContext → MVarId → IO Format
  deriving Inhabited

builtin_initialize ppFnsRef : IO.Ref PPFns ←
  IO.mkRef {
    ppExprWithInfos := fun _ e => return format (toString e)
    ppTerm := fun ctx stx => return stx.raw.formatStx (some <| pp.raw.maxDepth.get ctx.opts)
    ppGoal := fun _ _ => return "goal"
  }

builtin_initialize ppExt : EnvExtension PPFns ←
  registerEnvExtension ppFnsRef.get

def ppExprWithInfos (ctx : PPContext) (e : Expr) : IO FormatWithInfos := do
  let e := instantiateMVarsCore ctx.mctx e |>.1
  if pp.raw.get ctx.opts then
    return format (toString e)
  else
    try
      ppExt.getState ctx.env |>.ppExprWithInfos ctx e
    catch ex =>
      if pp.rawOnError.get ctx.opts then
        pure f!"[Error pretty printing expression: {ex}. Falling back to raw printer.]{Format.line}{e}"
      else
        pure f!"failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)"

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

def ppGoal (ctx : PPContext) (mvarId : MVarId) : IO Format :=
    ppExt.getState ctx.env |>.ppGoal ctx mvarId

end Lean
