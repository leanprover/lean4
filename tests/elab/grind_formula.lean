module

public meta import Lean
public meta import Lean.Meta.Tactic.Grind.Formula

/-!
Exercise the formula summary interface with a target-directed common-equality client.
Symmetry and a shared subformula require independent evidence from each alternative.
-/

open Lean Meta Elab Tactic Grind

private meta def commonEq (target source h : Expr) : MetaM Expr := do
  let_expr Eq _ lhs rhs := target | throwError "expected an equality"
  let classify := fun atom => do
    let_expr Eq _ a b := atom | return none
    if lhs == a && rhs == b then return some false
    if lhs == b && rhs == a then return some true
    return none
  let s ← Formula.foldM classify (· <|> ·) (· <* ·) source
  unless s.root.isSome do throwError "equality is not common"
  Formula.prove source target h (fun e => (s.find? e).join) fun reverse _ p =>
    if reverse then mkEqSymm p else pure p

elab "common_eq " h:ident : tactic => withMainContext do
  let h ← getLocalDeclFromUserName h.getId
  closeMainGoalUsing `common_eq fun target _ => commonEq target h.type h.toExpr

example {α : Type} (x y : α) (f : α → α) (p q : Prop)
    (h : ((x = y ∧ p) ∨ (q ∧ y = x)) ∧ (p ∨ q)) : f x = f y := by
  have : x = y := by common_eq h
  grind (branches := 0)

example {α : Type} (x y : α) (p q : Prop) (h : p ∧ ((x = y ∧ q) ∧ p)) : x = y := by
  common_eq h

example {α : Type} (x y : α) (p : Prop) (_h : x = y ∨ p) (h' : y = x) : x = y := by
  fail_if_success common_eq _h
  common_eq h'

/- Shared subformulas can have different incoming paths and annotations on the connective spine. -/
run_meta do
  withLocalDeclD `p (mkSort 0) fun p => do
    let x := mkNatLit 0
    let target ← mkEq x x
    let tagged (op : Name) (a b : Expr) := mkMData {} (mkApp (mkMData {} (mkApp (mkConst op) a)) b)
    let mut e := tagged ``And p target
    for _ in [:22] do
      e := mkOr (mkAnd p e) (mkAnd e p)
    e := tagged ``Or e e
    withLocalDeclD `h e fun h => do
      let proof ← commonEq target e h
      checkWithKernel (← mkLambdaFVars #[p, h] proof)

/- The fold respects binary grouping, including when an entire conjunction is pruned. -/
run_meta do
  let p := mkConst ``False
  let q := mkConst ``True
  let admits := fun (e : Expr) => e == q
  let atom := fun e => pure <| if admits e then 1 else 0
  let both a b := 2*a + 3*b
  for (e, expected) in [(mkAnd (mkAnd p p) q, 3), (mkAnd p (mkAnd p q), 9)] do
    let all ← Formula.foldM atom both min e
    let relevant ← Formula.foldRelevantM admits 0 (· == 0) atom both min e
    unless all.root == expected && relevant.root == all.root do
      throwError "binary conjunction grouped incorrectly: {all.root}, {relevant.root}"

/- Effects run in source order. Rejected alternatives and alternatives after an empty result are skipped. -/
run_meta do
  let p := mkConst ``True
  let q := mkConst ``False
  let empty := mkNot p
  let unused := mkNot q
  let rejected := mkNot empty
  let blocked := mkOr rejected unused
  let shared := mkOr p q
  let mixed := mkAnd (mkOr empty unused) blocked
  let e := mkAnd shared (mkAnd shared mixed)
  let classify := fun (e : Expr) => (do
    modify (·.push e)
    return if e == empty || e == rejected then 0 else 1 : StateRefT (Array Expr) MetaM Nat)
  let (v, seen) ← (Formula.foldRelevantM (· != rejected) 0 (· == 0) classify max min e
    (admitConjunct := fun c supported => do
      if c == blocked then throwError "checked an unsupported conjunct"
      if c == mixed then
        let unexpected := fun _ => throwError "descended into a ruled-out disjunction"
        discard <| (Formula.foldCachedM unexpected max min blocked
          (known? := fun sub => if sub == blocked && !supported sub then some (0 : Nat) else none)).run
      return true)).run #[]
  unless v.root == 1 && seen == #[p, q, empty] do throwError "unexpected atom visits: {seen}"
  unless v.find? e == some 1 && v.find? empty == some 0 && (v.find? unused).isNone do
    throwError "unexpected summaries for visited or skipped nodes"
  let (v', seen') ← (Formula.foldRelevantM (fun _ => true) 0 (· == 0) classify max min e
    (admitConjunct := fun c _ => pure (c != blocked))).run #[]
  unless v'.root == v.root && seen' == seen && (v'.find? blocked).isNone && (v'.find? rejected).isNone do
    throwError "the fold visited an excluded subformula"

/- Skipping an incoming conjunction edge must not memoize the child as visited. -/
run_meta do
  let p := mkConst ``True
  let q := mkConst ``False
  let r := mkNot p
  let shared := mkOr p q
  let classify := fun (a : Expr) => (do
    modify (·.push a)
    return if a == q then 2 else 1 : StateRefT (Array Expr) MetaM Nat)
  let either := fun a b => if a == b then a else 0
  for left in [mkAnd shared r, mkAnd r shared] do
    let e := mkOr left shared
    let (s, seen) ← (Formula.foldRelevantM (fun _ => true) 0 (· == 0) classify max either e
      (admitConjunct := fun c _ => pure (c != shared))).run #[]
    unless seen == #[r, p, q] && s.find? shared == some 0 && s.root == 0 do
      throwError "unexpected visits to shared disjunction: {seen}"

/- Shared nodes are summarized once, even when the unfolded conjunction has 2^30 leaves. -/
run_meta do
  let mut shared := mkConst ``True
  for _ in [:30] do shared := mkAnd shared shared
  let classify := fun (_ : Expr) => (do modify (· + 1); return 0 : StateRefT Nat MetaM Nat)
  let heights := do
    let both := fun a b => 1 + max a b
    let h₁ ← Formula.foldCachedM classify both max shared
    let h₂ ← Formula.foldCachedM classify both max (mkAnd shared shared)
    return (h₁, h₂)
  let ((h₁, h₂), calls) ← heights.run.run 0
  unless (h₁, h₂, calls) == (30, 31, 1) do
    throwError "unexpected shared conjunction summaries: {(h₁, h₂, calls)}"
