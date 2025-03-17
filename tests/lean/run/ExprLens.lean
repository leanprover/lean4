import Lean.Meta.ExprLens
import Lean.Meta.ExprTraverse
import Lean

open Lean Meta Elab Term SubExpr

def Lean.LocalContext.subtract (Γ Δ : LocalContext) : Array Expr :=
  -- have Δ = Γ ++ E
  let Δ := Δ.getFVars
  let Γ := Γ.getFVars
  let E := Δ[:(Δ.size - Γ.size)]
  E.toArray

def ExprTraversal := ∀{M : _} [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M] [MonadOptions M], (Pos → Expr → M Expr) → Pos → Expr → M Expr

instance : Inhabited ExprTraversal where
  default := traverseChildrenWithPos

partial def traverseAll : ExprTraversal := fun
  | visit, p, e => visit p e >>= traverseChildrenWithPos (fun p e => traverseAll visit p e) p

def testTraversal
  (traversalWithPos : ExprTraversal)
  (expectedLen : Nat): TermElabM Unit := do
  -- make a sample expression `e` that has all of the different kinds of expressions.
  let s ← `(
    ∀ x y : Nat,
    ∀ {zz : Fin x},
    ∃ (z : {z: Nat // z = x + y}),
    let p := z.1
    p + x + y = 3
    )
  let e ← elabTerm s none
  let Γ ← getLCtx

  -- traverse `e` using the `traversalWithPos` function
  -- leave `e` unmodified but at each point accumulate
  -- the abstracted subexpression
  let (e', subexprs) ← StateT.run (
    traversalWithPos (fun p s => do
      let a ← get
      let Δ ← getLCtx
      let E := Lean.LocalContext.subtract Γ Δ

      -- check that numBinders works
      let nBinders ← Lean.Core.numBinders p e
      if E.size != nBinders then
        throwError "bad number of binders"

      set <| a.push (p, Expr.abstract s E)
      return s
    ) Pos.root e) #[]
  -- the traversal output should be equal to the original
  -- that is: `traversal pure e ≡ e`
  if not (← liftM $ isDefEq e e') then
    throwError "\n{e} \nand \n{e'} are different!"

  -- check that the number of subexpressions is what we expect
  -- and if it isn't then print them out for debugging.
  if subexprs.size != expectedLen then
    for (p, s) in subexprs do
      let ppt ← PrettyPrinter.ppExpr s
      dbg_trace s!"{p}, {ppt}\n"
    throwError "expected size: {expectedLen}\nactual size: {subexprs.size}"

  -- for each subexpression `p`, make sure that viewSubexpr produces the same
  -- subexpression as that found in the traversal.
  for (p, s) in subexprs do
    viewSubexpr (fun fvars t => do
      let t := Expr.abstract t fvars
      let de ← liftM $ isDefEq t s
      if not de then
        throwError "\n{t} \nand \n{s} are different!"
      return ()
    ) p e

    -- check that replaceSubexpr pure is the identity
    let e' ← replaceSubexpr pure p e
    if not (← liftM $ isDefEq e e') then
      throwError "\n{e} \nand \n{e'} are different!"

#guard_msgs in
#eval ((do
  testTraversal traverseLambdaWithPos 1
  testTraversal traverseChildrenWithPos 4
  testTraversal traverseAll 103
  return ())
  : TermElabM Unit
)
