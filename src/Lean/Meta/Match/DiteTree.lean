/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Subst
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Meta.Match.Value
import Lean.Util.ForEachExpr

/-!
Support for proving the equations of `match` expressions with value patterns.

The match compiler generates a tree of tests `dite (x = v) (Eq.ndrec_symm m) e` for value
patterns, where `x` is a variable and `v` a value. When proving the equation of an alternative with
overlapping patterns, the goal `tree = rhs` contains a hypothesis such as
`x = "a" → y = 0 → False`, or `∀ ys, some (x, y) = some ("a", ys) → False`, for each previous
alternative.

`splitDiteTree` proves such a goal by traversing the tree. It does not use general purpose
tactics because their cost at each test is proportional to the number of hypotheses, and there is
one test and one hypothesis for each alternative.
- At a test `x = v`, it keeps the hypothesis `h : x = v` in the `then` branch, and replaces `x`
  with `v` only in the right-hand side `rhs`. The other hypotheses still mention `x`.
- It indexes the hypotheses of the form `... → False` using the tests `x = v` occurring in them.
  At a test `x = v`, the index returns the hypotheses whose tests have all been performed. Only
  these hypotheses are rewritten using the kept equalities, and used to close the `then` branch.
- At a leaf that is not a test, e.g., a `casesOn` application, it substitutes the kept
  equalities, and returns the goal.
-/

namespace Lean.Meta.Match
namespace DiteTree

/--
A test `x = v`. The value `v` is in normal form: two tests on the same variable denote the same
test iff they are structurally equal. See `mkTest`.
-/
abbrev Test := FVarId × Expr

/-- Returns `true` if `v` is a value that can be used in a test: it does not depend on the context. -/
def isValue (v : Expr) : Bool :=
  !v.hasFVar && !v.hasLooseBVars && !v.hasMVar

/--
Creates the test `x = v`. The value `v` is normalized because the same value can be written in
different ways, and tests are compared structurally.
- Literals of types such as `Nat`, `Int`, `Fin`, `BitVec`, and `UInt8` are normalized using
  `normLitValue`. For example, `(7 : Fin 3)` and `(1 : Fin 3)` denote the same value.
- `Float` and `Float32` literals are normalized using `normMatchValue`. For example, `5` and `5.0`
  denote the same value.
-/
def mkTest (x : FVarId) (v : Expr) : MetaM Test := do
  let type ← withTransparency .implicit do whnf (← x.getType)
  if type.isConstOf ``Float || type.isConstOf ``Float32 then
    return (x, ← normMatchValue v)
  else
    return (x, ← normLitValue v)

/--
A node of the index. See `Index`.
-/
structure Node where
  /--
  The hypotheses whose tests are exactly the ones in the path from the root to this node.
  Different hypotheses may have the same tests because only the equalities between a variable
  and a value are tests. For example, the only test in the following two hypotheses is `x = "a"`.
  ```
  H₁ : x = "a" → o = none → False
  H₂ : ∀ n, x = "a" → o = some n → False
  ```
  When this node is reached, `closeUsing` tries each of them.
  -/
  hyps     : Array FVarId := #[]
  /--
  The edges leaving this node. An edge is a test, and the target is a position in `Index.nodes`.

  Remark: we use positions to workaround a limitation of nested inductive types. Lean rejects
  `children : Std.HashMap Test Node`, and we would have to use `Std.HashMap.Raw` instead.
  -/
  children : Std.HashMap Test Nat := {}
  deriving Inhabited

/--
Index for the hypotheses of the form `... → False`. Given the tests `x = v` that succeeded in the
path from the root of the tree to the current position, it retrieves the hypotheses that can be
used to close the goal: the ones whose tests have all succeeded.

The index is a trie with a single root. Each edge is a test `x = v`, and each hypothesis is stored
at the node reached by its tests. A hypothesis has one path in the trie because its tests are sorted
using a fixed order on the variables (`varPos`).

Example: suppose `x` is before `y` in this order, and the local context contains
```
H₁ : x = "a" → y = 0 → False
H₂ : x = "a" → y = 1 → False
H₃ : y = 5 → False
```
Then, the index is
```
root ──(x, "a")──▶ n₁ ──(y, 0)──▶ n₂ [H₁]
  │                 └───(y, 1)──▶ n₃ [H₂]
  └────(y, 5)────▶ n₄ [H₃]
```
`H₃` does not test `x`. Thus, its path starts at the root with a test on `y`.

A hypothesis can be used when all its tests have succeeded, i.e., when every edge in its path is
a test that succeeded. Thus, `Index.retrieve` visits the nodes that can be reached from the root
using only edges that are tests that succeeded, and returns the hypotheses stored at them.
In the example, suppose `x = "a"` and `y = 5` succeeded. The nodes visited are `root`,
`n₁` (edge `(x, "a")` from `root`), and `n₄` (edge `(y, 5)` from `root`). The nodes `n₂` and `n₃`
are not visited because `y = 0` and `y = 1` did not succeed. Thus, `H₃` is retrieved.

`Index.retrieve` sorts the tests that succeeded using `varPos` because the edges in every path are
sorted, but the tree does not test the variables in the same order in every branch.
-/
structure Index where
  /--
  The variables tested in the tree, and their positions in a fixed order. This order is only used
  to sort tests: the tests of a hypothesis when it is inserted, and the tests that succeeded when
  hypotheses are retrieved.
  -/
  varPos : Std.HashMap FVarId Nat := {}
  /-- The nodes of the trie. The root is the node at position `0`. -/
  nodes  : Array Node := #[{}]

/-- Collects the variables tested in `tree`, and assigns a position to each one of them. -/
def collectVars (tree : Expr) : MetaM (Std.HashMap FVarId Nat) := do
  let (_, varPos) ← tree.forEach visit |>.run {}
  return varPos
where
  visit (e : Expr) : StateRefT (Std.HashMap FVarId Nat) MetaM Unit := do
    let_expr dite _ c _ _ _ := e | return ()
    let_expr Eq _ x v := c | return ()
    let .fvar fvarId := x | return ()
    if isValue v then
      modify fun varPos => if varPos.contains fvarId then varPos else varPos.insert fvarId varPos.size

/--
Collects the tests `x = v` occurring in the hypothesis type `type`, where `x` is a variable in
`varPos`. For example, the tests of `∀ ys, some (x, y) = some ("a", ys) → z = 0 → False` are
`x = "a"` and `z = 0`.
-/
partial def collectTests (varPos : Std.HashMap FVarId Nat) (type : Expr) : MetaM (Array Test) :=
  go type #[]
where
  go (type : Expr) (tests : Array Test) : MetaM (Array Test) := do
    let .forallE _ d b _ := type | return tests
    let some (_, lhs, rhs) := d.eq? | go b tests
    if b.hasLooseBVar 0 then go b tests else go b (← visit lhs rhs tests)

  visit (lhs rhs : Expr) (tests : Array Test) : MetaM (Array Test) := do
    if let .fvar fvarId := lhs then
      if varPos.contains fvarId && isValue rhs then
        return tests.push (← mkTest fvarId rhs)
      return tests
    let .const declName₁ _ := lhs.getAppFn | return tests
    let .const declName₂ _ := rhs.getAppFn | return tests
    unless declName₁ == declName₂ && lhs.getAppNumArgs == rhs.getAppNumArgs do return tests
    let mut tests := tests
    for lhsArg in lhs.getAppArgs, rhsArg in rhs.getAppArgs do
      tests ← visit lhsArg rhsArg tests
    return tests

/-- Sorts the tests using `varPos`. The variables in `tests` must be in `varPos`. -/
def Index.sort (index : Index) (tests : Array Test) : Array Test :=
  tests.qsort fun (x₁, _) (x₂, _) => index.varPos[x₁]! < index.varPos[x₂]!

/--
Inserts the hypothesis `fvarId` with the given tests into the index. It sorts the tests using
`varPos`, follows the corresponding path from the root, creating the missing nodes, and stores
`fvarId` at the last node.
-/
def Index.insert (index : Index) (fvarId : FVarId) (tests : Array Test) : Index := Id.run do
  let tests := index.sort tests
  let mut nodes := index.nodes
  let mut i := 0
  for test in tests do
    if let some j := nodes[i]!.children[test]? then
      i := j
    else
      let j := nodes.size
      nodes := nodes.modify i fun node => { node with children := node.children.insert test j }
      nodes := nodes.push {}
      i := j
  nodes := nodes.modify i fun node => { node with hyps := node.hyps.push fvarId }
  return { index with nodes }

/-- Creates the index for the hypotheses of the form `... → False` using the variables tested in `tree`. -/
def mkIndex (tree : Expr) : MetaM Index := do
  let mut index : Index := { varPos := (← collectVars tree) }
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if Simp.isEqnThmHypothesis type then
        let tests ← collectTests index.varPos type
        unless tests.isEmpty do
          index := index.insert localDecl.fvarId tests
  return index

/-- An equality `h : x = v` kept in the local context after a test. -/
structure KeptEq where
  test : Test
  /-- The value in the type of `h`. It is not necessarily in normal form. -/
  v    : Expr
  h    : FVarId

/--
Returns the hypotheses whose tests are all in `kept` and include `test`, the last test that
succeeded. The other ones have already been tried.

It follows the tests in `kept`, sorted using `varPos`, from the root. `active` contains the nodes
reached by a subset of the tests visited so far, and whether `test` is in the path to the node.
-/
def Index.retrieve (index : Index) (kept : Array KeptEq) (test : Test) : Array FVarId := Id.run do
  let tests := kept.filterMap fun { test, .. } => if index.varPos.contains test.1 then some test else none
  let mut active : Array (Nat × Bool) := #[(0, false)]
  for test' in index.sort tests do
    let isTest := test' == test
    for (i, hasTest) in active do
      if let some j := index.nodes[i]!.children[test']? then
        active := active.push (j, hasTest || isTest)
  let mut hyps := #[]
  for (i, hasTest) in active do
    if hasTest then
      hyps := hyps ++ index.nodes[i]!.hyps
  return hyps

/--
Tries to close `mvarId` using the hypothesis `hyp` of the form `... → False`, after rewriting
its type with the kept equalities.
-/
def closeUsing (mvarId : MVarId) (kept : Array KeptEq) (hyp : FVarId) : MetaM Bool := mvarId.withContext do
  let mut proof := mkFVar hyp
  let mut type ← instantiateMVars (← hyp.getType)
  for { test := (x, _), v, h } in kept do
    if type.containsFVar x then
      let motive := mkLambda `x .default (← x.getType) (type.abstract #[mkFVar x])
      proof ← mkEqNDRec motive proof (mkFVar h)
      type := type.replaceFVar (mkFVar x) v
  let some falseProof ← mkGenDiseqFalseProof? proof type | return false
  mvarId.assign (← mkFalseElim (← mvarId.getType) falseProof)
  return true

/-- Result of splitting the goal `dite (x = v) (Eq.ndrec_symm m) e = rhs`. -/
structure Split where
  test        : Test
  /-- The value `v`. -/
  v           : Expr
  /-- Goal `m = rhs[x := v]`. -/
  mvarIdTrue  : MVarId
  /-- Hypothesis `x = v` in `mvarIdTrue`. -/
  h           : FVarId
  /-- Goal `e h = rhs` where `h : ¬ x = v`. -/
  mvarIdFalse : MVarId

/--
Splits the goal `dite (x = v) (Eq.ndrec_symm m) e = rhs` using `dite_ndrec_symm_eq`.
Returns `none` if the goal is not of this form, or `x` cannot be replaced with `v` in `rhs`
without rewriting the hypotheses, e.g., `rhs` contains a variable whose type depends on `x`.
-/
def split? (mvarId : MVarId) : MetaM (Option Split) := mvarId.withContext do
  let some (_, lhs, rhs) := (← mvarId.getType).eq? | return none
  let_expr dite@dite β c inst t e := lhs | return none
  let_expr Eq@Eq α x v := c | return none
  let .fvar fvarId := x | return none
  unless isValue v do return none
  let_expr Eq.ndrec_symm _ v' motive m x' := t | return none
  unless v' == v && x' == x do return none
  let r := mkLambda `x .default α (rhs.abstract #[x])
  unless (← isTypeCorrect r) do return none
  let rType := mkForall `x .default α (motive.beta #[mkBVar 0])
  unless (← isDefEq (← inferType r) rType) do return none
  let v₁ := dite.constLevels!
  let mkGoal (lhs rhs : Expr) (type : Expr) : Expr := mkApp3 (mkConst ``Eq v₁) type lhs rhs
  let tag ← mvarId.getTag
  let mvarTrue ← mkFreshExprSyntheticOpaqueMVar (← mkArrow c (mkGoal m (rhs.replaceFVar x v) (motive.beta #[v]))) tag
  -- We do not use `mkForallFVars` here because it would traverse the remaining tree.
  let typeFalse := mkForall `h .default (mkNot c) (mkGoal (e.beta #[mkBVar 0]) rhs β)
  let mvarFalse ← mkFreshExprSyntheticOpaqueMVar typeFalse tag
  mvarId.assign <| mkAppN (mkConst ``dite_ndrec_symm_eq (Eq.constLevels! ++ v₁))
    #[α, v, x, inst, motive, m, e, r, mvarTrue, mvarFalse]
  let (h, mvarIdTrue) ← mvarTrue.mvarId!.intro1
  let (_, mvarIdFalse) ← mvarFalse.mvarId!.intro1
  return some { test := (← mkTest fvarId v), v, mvarIdTrue, h, mvarIdFalse }

/-- Substitutes the kept equalities in `mvarId`. -/
def substKept (mvarId : MVarId) (kept : Array KeptEq) : MetaM MVarId := do
  let mut mvarId := mvarId
  let mut fvarSubst : FVarSubst := {}
  for { h, .. } in kept do
    (fvarSubst, mvarId) ← substCore mvarId (fvarSubst.get h).fvarId! (fvarSubst := fvarSubst)
  return mvarId

/-- The goals that are not closed by `visit` are stored in the state. -/
abbrev M := StateRefT (Array MVarId) MetaM

mutual
/--
Traverses the tree in the goal `mvarId : tree = rhs`. `kept` are the equalities for the tests that
succeeded.
-/
partial def visit (index : Index) (mvarId : MVarId) (kept : Array KeptEq) : M Unit := do
  let mvarId ← mvarId.modifyTargetEqLHS whnfCore
  if let some s ← split? mvarId then
    visitSplit index s kept
  else unless (← (do mvarId.refl; return true) <|> return false) do
    let mvarId ← substKept mvarId kept
    modify (·.push mvarId)

partial def visitSplit (index : Index) (s : Split) (kept : Array KeptEq) : M Unit := do
  let keptTrue := kept.push { test := s.test, v := s.v, h := s.h }
  let hyps := index.retrieve keptTrue s.test
  unless (← hyps.anyM (closeUsing s.mvarIdTrue keptTrue ·)) do
    visit index s.mvarIdTrue keptTrue
  visit index s.mvarIdFalse kept
end

end DiteTree

/--
Given a goal `tree = rhs` where `tree` is a tree of tests `dite (x = v) (Eq.ndrec_symm m) e`,
traverses the tree and closes the branches that are refuted by a hypothesis of the form
`... → False`, or where both sides are definitionally equal. Returns the goals for the remaining
branches. Throws an exception if the goal is not of this form.
-/
public def splitDiteTree (mvarId : MVarId) : MetaM (Array MVarId) := mvarId.withContext do
  let some (_, tree, _) := (← mvarId.getType).eq? | throwError "equality expected"
  let some s ← DiteTree.split? mvarId | throwError "`dite (x = v) (Eq.ndrec_symm m) e` expected"
  let index ← DiteTree.mkIndex tree
  let (_, mvarIds) ← DiteTree.visitSplit index s #[] |>.run #[]
  return mvarIds

end Lean.Meta.Match
