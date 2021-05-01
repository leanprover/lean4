/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.App

/-
Auxiliary elaboration functions: AKA custom elaborators
-/

namespace Lean.Elab.Term
open Meta

@[builtinTermElab binrel] def elabBinRel : TermElab :=  fun stx expectedType? => do
  match (← resolveId? stx[1]) with
  | some f =>
    let s ← saveState
    let (lhs, rhs) ← withSynthesize (mayPostpone := true) do
      let mut lhs ← elabTerm stx[2] none
      let mut rhs ← elabTerm stx[3] none
      if lhs.isAppOfArity `OfNat.ofNat 3 then
        lhs ← ensureHasType (← inferType rhs) lhs
      else if rhs.isAppOfArity `OfNat.ofNat 3 then
        rhs ← ensureHasType (← inferType lhs) rhs
      return (lhs, rhs)
    let lhsType ← inferType lhs
    let rhsType ← inferType rhs
    let (lhs, rhs) ←
      try
        pure (lhs, ← withRef stx[3] do ensureHasType lhsType rhs)
      catch _ =>
        try
          pure (← withRef stx[2] do ensureHasType rhsType lhs, rhs)
        catch _ =>
          s.restore
          -- Use default approach
          let lhs ← elabTerm stx[2] none
          let rhs ← elabTerm stx[3] none
          let lhsType ← inferType lhs
          let rhsType ← inferType rhs
          pure (lhs, ← withRef stx[3] do ensureHasType lhsType rhs)
    elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] expectedType? (explicit := false) (ellipsis := false)
  | none   => throwUnknownConstant stx[1].getId

-- TODO: move to another file?
private def hasUnknownType (e : Expr) : MetaM Bool :=
  return (← inferType e).getAppFn.isMVar

@[builtinTermElab binop] def elabBinOp : TermElab :=  fun stx expectedType? => do
  match stx with
  | `(binop% $f $lhs $rhs) =>
    match expectedType? with
    | none =>
      -- We elaborate as a normal application when expected type is not available
      let stxNew ← `($f:ident $lhs $rhs)
      withMacroExpansion stx stxNew <| elabTerm stxNew none
    | some expectedType =>
      match (← resolveId? f) with
      | some f =>
        let syntheticMVarsSaved := (← get).syntheticMVars
        modify fun s => { s with syntheticMVars := [] }
        try
          let lhs ← elabTerm lhs none
          let rhs ← elabTerm rhs none
          if (← hasUnknownType lhs) && (← hasUnknownType rhs) then
            -- We want the numerals in terms such as `(1 + 1)` `(2 * 3 + 4)` to be elaborated using the expected type
            -- This is particularly important when there is no coercion from `Nat` to the expected type.
            elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] expectedType (explicit := false) (ellipsis := false)
          else
            -- We force TC resolution and default instances to be used.
            -- Note that we do not provide the expected type to make sure it can be inferred by the TC procedure. See issue #382
            let r ← elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] (expectedType? := none) (explicit := false) (ellipsis := false)
            synthesizeSyntheticMVarsUsingDefault
            return r
        finally
          modify fun s => { s with syntheticMVars := s.syntheticMVars ++ syntheticMVarsSaved }
       | none   => throwUnknownConstant stx[1].getId
  | _ => throwUnsupportedSyntax

@[builtinTermElab forInMacro] def elabForIn : TermElab :=  fun stx expectedType? => do
  match stx with
  | `(forIn% $col $init $body) =>
      match (← isLocalIdent? col) with
      | none   => elabTerm (← `(let col := $col; forIn% col $init $body)) expectedType?
      | some colFVar =>
        tryPostponeIfNoneOrMVar expectedType?
        let m ← getMonad expectedType?
        let colType ← inferType colFVar
        let elemType ← mkFreshExprMVar (mkSort (mkLevelSucc (← mkFreshLevelMVar)))
        let forInInstance ←
          try
            mkAppM `ForIn #[m, colType, elemType]
          catch
            ex => tryPostpone; throwError "failed to construct 'ForIn' instance for collection{indentExpr colType}\nand monad{indentExpr m}"
        match (← trySynthInstance forInInstance) with
        | LOption.some val =>
          let ref ← getRef
          let forInFn ← mkConst ``forIn
          let namedArgs : Array NamedArg := #[
            { ref := ref, name := `m, val := Arg.expr m},
            { ref := ref, name := `ρ, val := Arg.expr colType},
            { ref := ref, name := `α, val := Arg.expr elemType},
            { ref := ref, name := `self, val := Arg.expr forInInstance},
            { ref := ref, name := `inst, val := Arg.expr val} ]
          elabAppArgs forInFn #[] #[Arg.stx col, Arg.stx init, Arg.stx body] expectedType? (explicit := false) (ellipsis := false)
        | LOption.undef    => tryPostpone; throwFailure forInInstance
        | LOption.none     => throwFailure forInInstance
  | _ => throwUnsupportedSyntax
where
  getMonad (expectedType? : Option Expr) : TermElabM Expr := do
    match expectedType? with
    | none => throwError "invalid 'forIn%' notation, expected type is not available"
    | some expectedType =>
      match (← isTypeApp? expectedType) with
      | some (m, _) => return m
      | none => throwError "invalid 'forIn%' notation, expected type is not of of the form `M α`{indentExpr expectedType}"
  throwFailure (forInInstance : Expr) : TermElabM Expr :=
    throwError "failed to synthesize instance for 'forIn%' notation{indentExpr forInInstance}"

end Lean.Elab.Term
