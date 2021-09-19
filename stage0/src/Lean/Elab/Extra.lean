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
/-

The elaborator for `binop%` terms works as follows:

1- Expand macros.
2- Convert `Syntax` object corresponding to the `binop%` term into a `Tree`.
   The `toTree` method visits nested `binop%` terms and parentheses.
3- Synthesize pending metavariables without applying default instances and using the
   `(mayPostpone := true)`.
4- Tries to compute a maximal type for the tree computed at step 2.
   We say a type α is smaller than type β if there is a (nondependent) coercion from α to β.
   We are currently ignoring the case we may have cycles in the coercion graph.
   If there are "uncomparable" types α and β in the tree, we skip the next step.
   We say two types are "uncomparable" if there isn't a coercion between them.
   Note that two types may be "uncomparable" because some typing information may still be missing.
5- We traverse the tree and inject coercions to the "maximal" type when needed.

Recall that the coercions are expanded eagerly by the elaborator.

Properties:

a) Given `n : Nat` and `i : Nat`, it can successfully elaborate `n + i` and `i + n`. Recall that Lean 3
   fails on the former.

b) The coercions are inserted in the "leaves" like in Lean 3.

c) There are no coercions "hidden" inside instances, and we can elaborate
```
axiom Int.add_comm (i j : Int) : i + j = j + i

example (n : Nat) (i : Int) : n + i = i + n := by
  rw [Int.add_comm]
```
Recall that the `rw` tactic used to fail because our old `binop%` elaborator would hide
coercions inside of a `HAdd` instance.

Remarks:

In the new `binop%` elaborator the decision whether a coercion will be inserted or not
is made at `binop%` elaboration time. This was not the case in the old elaborator.
For example, an instance, such as `HAdd Int ?m ?n`, could be created when executing
the `binop%` elaborator, and only resolved much later. We try to minimize this problem
by synthesizing pending metavariables at step 3.

For types containing heterogeneous operators (e.g., matrix multiplication), step 4 will fail
and we will skip coercion insertion. For example, `x : Matrix Real 5 4` and `y : Matrix Real 4 8`,
there is no coercion `Matrix Real 5 4` from `Matrix Real 4 8` and vice-versa, but
`x * y` is elaborated successfully and has type `Matrix Real 5 8`.
-/

private inductive Tree where
  | term  (ref : Syntax) (val : Expr)
  | op    (ref : Syntax) (lazy : Bool) (f : Expr) (lhs rhs : Tree)

private partial def toTree (s : Syntax) : TermElabM Tree := do
  let result ← go (← liftMacroM <| expandMacros s)
  synthesizeSyntheticMVars (mayPostpone := true)
  return result
where
  go (s : Syntax) := do
    match s with
    | `(binop% $f $lhs $rhs) => processOp (lazy := false) f lhs rhs
    | `(binop_lazy% $f $lhs $rhs) => processOp (lazy := true) f lhs rhs
    | `(($e)) => (← go e)
    | _ =>
       return Tree.term s (← elabTerm s none)

  processOp (f lhs rhs : Syntax) (lazy : Bool) := do
    let some f ← resolveId? f | throwUnknownConstant f.getId
    return Tree.op s (lazy := lazy) f (← go lhs) (← go rhs)

-- Auxiliary function used at `analyze`
private def hasCoe (fromType toType : Expr) : TermElabM Bool := do
  if (← getEnv).contains ``CoeHTCT then
    let u ← getLevel fromType
    let v ← getLevel toType
    let coeInstType := mkAppN (Lean.mkConst ``CoeHTCT [u, v]) #[fromType, toType]
    match ← trySynthInstance coeInstType (some (maxCoeSize.get (← getOptions))) with
    | LOption.some _ => return true
    | LOption.none   => return false
    | LOption.undef  => return false -- TODO: should we do something smarter here?
  else
    return false

private structure AnalyzeResult where
  max?            : Option Expr := none
  hasUncomparable : Bool := false -- `true` if there are two types `α` and `β` where we don't have coercions in any direction.

private def isUnknow : Expr → Bool
  | Expr.mvar ..        => true
  | Expr.app f ..       => isUnknow f
  | Expr.letE _ _ _ b _ => isUnknow b
  | Expr.mdata _ b _    => isUnknow b
  | _                   => false

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
       | Tree.op _ _ _ lhs rhs => go lhs; go rhs
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
  | Tree.term _ e               => return e
  | Tree.op ref true f lhs rhs  => withRef ref <| mkOp f (← toExpr lhs) (← mkFunUnit (← toExpr rhs))
  | Tree.op ref false f lhs rhs => withRef ref <| mkOp f (← toExpr lhs) (← toExpr rhs)

private def applyCoe (t : Tree) (maxType : Expr) : TermElabM Tree := do
  go t
where
  go (t : Tree) : TermElabM Tree := do
    match t with
    | Tree.op ref lazy f lhs rhs => return Tree.op ref lazy f (← go lhs) (← go rhs)
    | Tree.term ref e       =>
      let type ← inferType e
      trace[Elab.binop] "visiting {e} : {type} =?= {maxType}"
      if (← isDefEqGuarded maxType type) then
        return t
      else
        trace[Elab.binop] "added coercion: {e} : {type} => {maxType}"
        withRef ref <| return Tree.term ref (← mkCoe maxType type e)

@[builtinTermElab binop]
def elabBinOp : TermElab :=  fun stx expectedType? => do
  let tree ← toTree stx
  let r    ← analyze tree expectedType?
  trace[Elab.binop] "hasUncomparable: {r.hasUncomparable}, maxType: {r.max?}"
  if r.hasUncomparable || r.max?.isNone then
    let result ← toExpr tree
    ensureHasType expectedType? result
  else
    let result ← toExpr (← applyCoe tree r.max?.get!)
    trace[Elab.binop] "result: {result}"
    ensureHasType expectedType? result

@[builtinTermElab binop_lazy]
def elabBinOpLazy : TermElab := elabBinOp

/--
  Decompose `e` into `(r, a, b)`.

  Remark: it assumes the last two arguments are explicit. -/
private def relation? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) :=
  if e.getAppNumArgs < 2 then
    return none
  else
    return some (e.appFn!.appFn!, e.appFn!.appArg!, e.appArg!)

@[builtinTermElab «calc»]
def elabBinCalc : TermElab :=  fun stx expectedType? => do
  let stepStxs := stx[1].getArgs
  let mut proofs := #[]
  let mut types  := #[]
  for stepStx in stepStxs do
    let type  ← elabType stepStx[0]
    let some (_, lhs, _) ← relation? type |
      throwErrorAt stepStx[0] "invalid 'calc' step, relation expected{indentExpr type}"
    if types.size > 0 then
      let some (_, _, prevRhs) ← relation? types.back | unreachable!
      unless (← isDefEqGuarded lhs prevRhs) do
        throwErrorAt stepStx[0] "invalid 'calc' step, left-hand-side is {indentD m!"{lhs} : {← inferType lhs}"}\nprevious right-hand-side is{indentD m!"{prevRhs} : {← inferType prevRhs}"}"
    types := types.push type
    let proof ← elabTermEnsuringType stepStx[2] type
    synthesizeSyntheticMVars
    proofs := proofs.push proof
  let mut result := proofs[0]
  let mut resultType := types[0]
  for i in [1:proofs.size] do
    let some (r, a, b) ← relation? resultType | unreachable!
    let some (s, _, c) ← relation? (← instantiateMVars types[i]) | unreachable!
    let (α, β, γ)       := (← inferType a, ← inferType b, ← inferType c)
    let (u_1, u_2, u_3) := (← getLevel α, ← getLevel β, ← getLevel γ)
    let t ← mkFreshExprMVar (← mkArrow α (← mkArrow γ (mkSort levelZero)))
    let selfType := mkAppN (Lean.mkConst ``Trans [u_1, u_2, u_3]) #[α, β, γ, r, s, t]
    match (← trySynthInstance selfType) with
    | LOption.some self =>
      result := mkAppN (Lean.mkConst ``Trans.trans [u_1, u_2, u_3]) #[α, β, γ, r, s, t, self, a, b, c, result, proofs[i]]
      resultType := (← instantiateMVars (← inferType result)).headBeta
      unless (← relation? resultType).isSome do
        throwErrorAt stepStxs[i] "invalid 'calc' step, step result is not a relation{indentExpr resultType}"
    | _ => throwErrorAt stepStxs[i] "invalid 'calc' step, failed to synthesize `Trans` instance{indentExpr selfType}"
    pure ()
  ensureHasType expectedType? result

builtin_initialize
  registerTraceClass `Elab.binop

end BinOp

end Lean.Elab.Term
