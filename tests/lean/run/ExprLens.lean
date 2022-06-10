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
  let s ← `(
    ∀ x y : Nat,
    ∃ (z : {z: Nat // z = x + y}),
    let p := z.1
    p + x + y = 3
    )
  let e ← elabTerm s none
  let Γ ← getLCtx
  let (e', subexprs) ← StateT.run (
    traversalWithPos (fun p e => do
      let a ← get
      let Δ ← getLCtx
      let s := Expr.abstract e <| Lean.LocalContext.subtract Γ Δ
      set <| a.push (p, s)
      return e
    ) Pos.root e) #[]
  if not (← liftM $ isDefEq e e') then
    throwError "{e} and {e'} are different!"
  if subexprs.size != expectedLen then
    for (p, s) in subexprs do
      let ppt ← PrettyPrinter.delab s >>= (liftM ∘ PrettyPrinter.ppTerm)
      dbg_trace s!"{p}, {ppt}\n"
    throwError "expected size: {expectedLen}\nactual size: {subexprs.size}"
  for (p, s) in subexprs do
    let _ ← viewSubexpr (fun fvars t => do
      let t := Expr.abstract t fvars
      let de ← liftM $ isDefEq t s
      if not de then
        throwError "{t} and {s} are different!"
    ) p e


#eval ((do
  testTraversal traverseLambdaWithPos 1
  testTraversal traverseChildrenWithPos 3
  testTraversal traverseAll 100
  return ())
  : TermElabM Unit
)
