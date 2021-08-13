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
      if lhs.isAppOfArity ``OfNat.ofNat 3 then
        lhs ← ensureHasType (← inferType rhs) lhs
      else if rhs.isAppOfArity ``OfNat.ofNat 3 then
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
            mkAppM ``ForIn #[m, colType, elemType]
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

namespace BinOp
/- Elaborator for `binop%` -/

private inductive Tree where
  | term  (ref : Syntax) (val : Expr)
  | op    (ref : Syntax) (f : Expr) (lhs rhs : Tree)

private partial def toTree (s : Syntax) : TermElabM Tree :=
  withSynthesizeLight do
    go (← liftMacroM <| expandMacros s)
where
  go (s : Syntax) := do
    match s with
    | `(binop% $f $lhs $rhs) =>
       let some f ← resolveId? f | throwUnknownConstant f.getId
       return Tree.op s f (← go lhs) (← go rhs)
    | `(($e)) => (← go e)
    | _ =>
       return Tree.term s (← elabTerm s none)

-- Auxiliary function used at `analyze`
private def hasCoe (fromType toType : Expr) : TermElabM Bool := do
  let u ← getLevel fromType
  let v ← getLevel toType
  let coeInstType := mkAppN (Lean.mkConst ``CoeHTCT [u, v]) #[fromType, toType]
  match ← trySynthInstance coeInstType (some (maxCoeSize.get (← getOptions))) with
  | LOption.some _ => return true
  | LOption.none   => return false
  | LOption.undef  => return false -- TODO: should we do something smarter here?

private structure AnalyzeResult where
  max?            : Option Expr := none
  hasUncomparable : Bool := false -- `true` if there are two types `α` and `β` where we don't have coercions in any direction.

private def isUnknow (e : Expr) : Bool :=
  e.getAppFn.isMVar

private def analyze (t : Tree) (expectedType? : Option Expr) : TermElabM AnalyzeResult := do
  let max? ←
    match expectedType? with
    | none => pure none
    | some expectedType =>
      let expectedType ← instantiateMVars expectedType
      if isUnknow expectedType then pure none else pure (some expectedType)
  (go t *> get).run' { max? }
where
   go (t : Tree) : StateRefT AnalyzeResult TermElabM Unit := do
     unless (← get).hasUncomparable do
       match t with
       | Tree.op _ _ lhs rhs => go lhs; go rhs
       | Tree.term _ val =>
         let type ← instantiateMVars (← inferType val)
         unless isUnknow type do
           match (← get).max? with
           | none     => modify fun s => { s with max? := type }
           | some max =>
             unless (← withNewMCtxDepth <| isDefEqGuarded max type) do
               if (← hasCoe type max) then
                 return ()
               else if (← hasCoe max type) then
                 modify fun s => { s with max? := type }
               else
                 trace[Elab.binop] "uncomparable types: {max}, {type}"
                 modify fun s => { s with hasUncomparable := true }

private def mkOp (f : Expr) (lhs rhs : Expr) : TermElabM Expr :=
  elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] (expectedType? := none) (explicit := false) (ellipsis := false)

private def toExpr (t : Tree) : TermElabM Expr := do
  match t with
  | Tree.term _ e         => return e
  | Tree.op ref f lhs rhs => withRef ref <| mkOp f (← toExpr lhs) (← toExpr rhs)

private def applyCoe (t : Tree) (maxType : Expr) : TermElabM Tree := do
  go t
where
  go (t : Tree) : TermElabM Tree := do
    match t with
    | Tree.op ref f lhs rhs => return Tree.op ref f (← go lhs) (← go rhs)
    | Tree.term ref e       =>
      let type ← inferType e
      if (← isDefEqGuarded maxType type) then
        return t
      else
        withRef ref <| return Tree.term ref (← mkCoe maxType type e)

@[builtinTermElab binop]
def elabBinOp' : TermElab :=  fun stx expectedType? => do
  let tree ← toTree stx
  let r    ← analyze tree expectedType?
  trace[Elab.binop] "hasUncomparable: {r.hasUncomparable}, maxType: {r.max?}"
  if r.hasUncomparable || r.max?.isNone then
    let result ← toExpr tree
    ensureHasType expectedType? result
  else
    let result ← toExpr (← applyCoe tree r.max?.get!)
    ensureHasType expectedType? result

builtin_initialize
  registerTraceClass `Elab.binop

end BinOp

end Lean.Elab.Term
