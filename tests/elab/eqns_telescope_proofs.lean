module
import Lean
public meta import Lean.Meta.Tactic.Refl
import all Lean.Elab.PreDefinition.Eqns

/-!
Checks the kernel proofs produced by equation normalization for simultaneous binding-value and
body rewrites, mixed let/have telescopes, transitive type dependencies, dependent results, and
matcher rewriting under local assumptions.
-/

open Lean Meta Elab

def valueAndBody (x y : Nat) : Nat :=
  have a := match x with | 5 => 1 | _ => 2
  have b := a + 1
  have c := match y with | 5 => b | _ => b + b
  match x with | 5 => c | _ => c + a

set_option cleanup.letToHave false in
def mixedDependent (x y : Nat) : Nat :=
  have a := match x with | 5 => 1 | _ => 2
  let t := Fin (a + 1)
  have z : t := ⟨a, Nat.lt_succ_self a⟩
  have b := match y with | 5 => z.val | _ => z.val + z.val
  match y with | 5 => b | _ => b + a

set_option cleanup.letToHave false in
def dependentResult (x y : Nat) : Fin (x + 2) :=
  let n := x + 1
  have _a := match y with | 5 => 0 | _ => 1
  have b : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  match y with | 5 => ⟨0, Nat.zero_lt_succ n⟩ | _ => b

meta def checkNormalizationProof (body : Expr) : MetaM Expr := do
  let lhs ← mkFreshExprMVar (← inferType body)
  let goal ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs body)
  let normalized ← Lean.Elab.Eqns.normalizeEqn goal.mvarId!
  let some (_, _, rhs) := (← normalized.getType').eq? | throwError "expected an equation"
  if ← isDefEq body rhs then throwError "expected a nondefinitional rewrite"
  normalized.refl
  let proof ← instantiateMVars goal
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) (← mkEq rhs body) do
    throwError "incorrect telescope proof type"
  return rhs

run_meta do
  for name in #[``valueAndBody, ``mixedDependent, ``dependentResult] do
    let info ← getConstInfoDefn name
    lambdaTelescope info.value fun xs body => do
      withLocalDeclD `hx (mkNot (← mkEq xs[0]! (mkNatLit 5))) fun _ => do
        withLocalDeclD `hy (mkNot (← mkEq xs[1]! (mkNatLit 5))) fun _ => do
          discard <| checkNormalizationProof body

def literalMatcher (x : Nat) : Nat := match x with | 5 => 1 | _ => 2

-- Reusing a matcher across a lambda boundary must respect the hypothesis's scope in either order.
run_meta do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let .lam _ _ body _ := (← getConstInfoDefn ``literalMatcher).value
      | throwError "unexpected matcher template"
    let matcher := body.instantiate1 x
    let fn := mkLambda `h .default (mkNot (← mkEq x (mkNatLit 5))) matcher
    for reverse in [false, true] do
      let pair ← mkAppM ``Prod.mk (if reverse then #[matcher, fn] else #[fn, matcher])
      let rhs ← checkNormalizationProof pair
      let_expr Prod.mk _ _ fst snd := rhs | throwError "expected a pair"
      let (fn', matcher') := if reverse then (snd, fst) else (fst, snd)
      let .lam _ _ body' _ := fn' | throwError "expected a lambda"
      unless ← isDefEq body' (mkNatLit 2) do
        throwError "matcher did not simplify under the local hypothesis"
      unless matcher' == matcher do
        throwError "matcher changed outside the hypothesis's scope"

def zeroMatcher (x : Nat) : Nat := match x with | 0 => 1 | _ => 2

-- A proof binding can enable rewriting a matcher whose earlier occurrence was unchanged.
run_meta do
  lambdaTelescope (← getConstInfoDefn ``zeroMatcher).value fun xs matcher => do
    let x := xs[0]!
    let nat := mkConst ``Nat
    withLocalDeclD `hx (← mkEq (mkNatAdd x x) (mkNatLit 0)) fun hx => do
      let proof ← mkAppM ``Nat.eq_zero_of_add_eq_zero_left #[hx]
      let body ← withLetDecl `a nat matcher (nondep := true) fun a => do
        withLetDecl `h (← mkEq x (mkNatLit 0)) proof (nondep := true) fun h => do
          withLetDecl `b nat matcher (nondep := true) fun b => do
            mkLetFVars #[a, h, b] (mkNatAdd a b) (usedLetOnly := false) (generalizeNondepLet := false)
      let rhs ← checkNormalizationProof body
      let .letE _ _ valueA (.letE _ _ valueB _ true) true := rhs
        | throwError "expected both shared bindings"
      unless valueA == matcher do throwError "earlier matcher changed before the proof binding"
      unless ← isDefEq valueB (mkNatLit 1) do
        throwError "later matcher did not simplify under the proof binding"
