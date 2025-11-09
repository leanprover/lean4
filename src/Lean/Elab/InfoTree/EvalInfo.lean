/-
Copyright (c) 2025 Alissa Tung. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alissa Tung
-/

module

prelude
public import Lean.Elab.Command

public section

namespace Lean.Elab.Command

/-- Information about an evaluated `#eval` command, stored for hover and inlay hints. -/
structure EvalResultInfo where
  stx    : Syntax
  result : MessageData
  type   : Expr
  deriving TypeName

def EvalResultInfo.toCustomInfo (i : EvalResultInfo) : CustomInfo where
  stx   := i.stx
  value := .mk i

def EvalResultInfo.ofCustomInfo? (i : CustomInfo) : Option EvalResultInfo :=
  i.value.get? EvalResultInfo

public def EvalResultInfo.pushInfoLeaf (i : EvalResultInfo) (term : Syntax) : TermElabM Unit := do
  let { stx, result, type } := i
  let inlayHintPos : Option String.Pos.Raw :=
    term.getTailPos? (canonicalOnly := true) |>.or <|
    stx.getTailPos?  (canonicalOnly := true)
  let .some inlayHintPos := inlayHintPos | return

  let result := (← result.format).pretty.trim
  let type ← Meta.ppExpr (← Lean.instantiateMVars type)
  let inlayHint : InlayHint :=
    { lctx        := ← getLCtx
    , kind?       := some .type
    , paddingLeft := true
    , position    := inlayHintPos

    , label    := .name s!" -- {result}"
    , tooltip? := .some <|
        let result := s!"Result:\n```lean\n\t{result}\n```"
        let type   := s!"Type:\n```lean\n\t{type}\n```"
        s!"{result}\n\n{type}"
    }
  Elab.pushInfoLeaf <| .ofCustomInfo inlayHint.toCustomInfo

end Lean.Elab.Command
