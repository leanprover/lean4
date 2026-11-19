/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Lean.Elab.ConfigEval.Instances

public section

namespace Lean.Elab.ConfigEval

open Meta Term

/--
Uses global option declarations with the prefix `optionPrefix` when setting `Options`.
Assumes that `item` is shifted, with the rest of the item being the option name suffix to use.
-/
def EvalConfigItem.evalSetOptions (optionPrefix : Name) (opts : Options) (item : ConfigItem) : TermElabM Options := do
  let optName := optionPrefix ++ item.getCurrOptionName
  -- TODO(kmill): record `optionPrefix` so that LSP can make correct suggestions
  addCompletionInfo <| CompletionInfo.option (mkNullNode #[item.prevRoot, mkNullNode item.optionComps.toArray])
  let decl ← getOptionDecl optName
  pushInfoLeaf <| .ofOptionInfo { stx := item.option, optionName := optName, declName := decl.declName }
  let set (α : Type) [EvalTerm α] [EvalExpr α] [KVMap.Value α] : TermElabM Options := do
    let value : α ← evalTermOrExprWithElab ⟨item.value⟩
    return opts.set optName value
  match decl.defValue with
  | .ofBool _   => set Bool
  | .ofNat _    => item.checkNotBool; set Nat
  | .ofInt _    => item.checkNotBool; set Int
  | .ofString _ => item.checkNotBool; set String
  | .ofName _   => item.checkNotBool; set Name
  | .ofSyntax _ => throwErrorAt item.option "Cannot set `Syntax` option `{optName}`"

end Lean.Elab.ConfigEval
