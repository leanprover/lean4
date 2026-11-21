import Lean

/-!
Tests for the dependency rules of `Meta.letToHave` on hand-built terms: a `have` whose value
mentions a dependent `let`, and applications of delayed-assigned metavariables.
-/

open Lean Meta

/-- Prints the `nondep` flags of the outermost `let`/`have` telescope of `e`. -/
partial def flags (e : Expr) : List (Name × Bool) :=
  match e with
  | .letE n _ _ b nondep => (n, nondep) :: flags b
  | _ => []

/-!
`let x : Type := Nat; let y : Type := x; (fun (a : y) => a) 5`: checking the application unfolds
`y` and then `x`, so both remain `let`s.
-/
def transitive : Expr :=
  .letE `x (mkSort 1) (mkConst ``Nat)
    (.letE `y (mkSort 1) (.bvar 0)
      (mkApp (.lam `a (.bvar 0) (.bvar 0) .default) (mkNatLit 5)) false) false

/-- info: [(x, false), (y, false)] -/
#guard_msgs in
run_meta do logInfo m!"{flags (← letToHave transitive)}"

/--
Builds `let x : Nat := 1; ?d x`, where `?d #[z] := ?p` is a delayed assignment. `z` is a local
hypothesis if `zIsLet` is false, and `let z := 0` otherwise.
-/
def delayed (zIsLet : Bool) : MetaM Expr := do
  let k (z : Expr) : MetaM Expr := do
    let p ← mkFreshExprSyntheticOpaqueMVar (mkConst ``Nat)
    match ← mkLambdaFVars #[z] p (usedLetOnly := false) with
    | .lam _ _ b _ | .letE _ _ _ b _ => pure b
    | e => throwError "unexpected {e}"
  let b ← if zIsLet then
    withLetDecl `z (mkConst ``Nat) (mkNatLit 0) k
  else
    withLocalDeclD `z (mkConst ``Nat) k
  let .mvar d := b.getAppFn | throwError "expected a delayed-assigned metavariable, got {b}"
  return .letE `x (mkConst ``Nat) (mkNatLit 1) (mkApp (.mvar d) (.bvar 0)) false

/-- info: [(x, true)] -/
#guard_msgs in
run_meta do logInfo m!"{flags (← letToHave (← delayed false))}"

/-- info: [(x, false)] -/
#guard_msgs in
run_meta do logInfo m!"{flags (← letToHave (← delayed true))}"
