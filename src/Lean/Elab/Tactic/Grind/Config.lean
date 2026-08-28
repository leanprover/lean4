/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Lean.Elab.ConfigEval

public section
namespace Lean.Elab.Tactic

open ConfigEval

/--
Elaborator for grind configurations, with the `(config := ...)` elaborator exposed.
This allows overriding which structure is used as the expected type when elaborating
the term, which affects which default values are used in `{...}` structure instance notation.
-/
private declare_term_config_elab elabGrindConfigCore Grind.Config
    (evalConfig : Term → TermElabM Grind.Config) where
  option config := fun _ item => evalConfig ⟨item.value⟩

local macro "make_elab_grind_config" fn:ident struct:ident : command => do
  let cfg := mkIdent `cfg
  let init := mkIdent `init
  let logExceptions := mkIdent `logExceptions
  `(private local ensure_eval_expr_instance $struct
    def $fn ($cfg : Syntax)
        ($init : $struct := {})
        ($logExceptions : Bool := true) :
        TacticM Grind.Config := do
      elabGrindConfigCore $cfg { $init with }
        (evalConfig := fun c => do
          let cfg : $struct ← evalExprWithElab c
          return { cfg with })
        (logExceptions := $logExceptions && (← read).recover))

make_elab_grind_config elabGrindConfig Grind.Config
make_elab_grind_config elabGrindConfigInteractive Grind.ConfigInteractive
make_elab_grind_config elabCutsatConfig Grind.CutsatConfig
make_elab_grind_config elabLinarithConfig Grind.LinarithConfig
make_elab_grind_config elabOrderConfig Grind.OrderConfig
make_elab_grind_config elabGrobnerConfig Grind.GrobnerConfig

namespace Grind

def elabConfigItems (init : Grind.Config) (items : Array Syntax) :
    TermElabM Grind.Config := do
  elabGrindConfigCore (mkNullNode items) init
    (evalConfig := fun c => evalExprWithElab c)
    (logExceptions := false)

def withConfigItems (items : Array Syntax)
    (k : GrindTacticM α) : GrindTacticM α := do
  if items.isEmpty then
    k
  else
    let config := (← read).ctx.config
    let config ← elabConfigItems config items
    withReader (fun c => { c with ctx.config := config }) do k

end Lean.Elab.Tactic.Grind
