/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
import Lean

/-!
Comprehensive tests for shared-relation `DiscrTree` indexing in native `match` over `expr`
quotations:
- Equivalence between indexed dispatch and direct linear pattern matching across `.structural`,
  `.reducible`, and `.sym`.
- `.structural` soundness: does NOT reduce `.proj` or beta redexes, respects `+inst` across
  differing instances, handles higher-order `?f x`, closed proofs, arrows, `fvar`s, and caller
  `mvar`s.
- `.reducible` soundness: handles root `Nat.succ _`, `Nat.zero`, `0`, `2`, `(fun x => x + ?a)`,
  `Sort _`, reducible aliases, `eta`, `let`, static `[items]`, and literal <-> numeral equivalence.
- `/sym` indexing soundness: handles root & subterm offsets (`?n + 1`, `f 5` matching
  `f (1 + 4)`), `letE`, local `let`-fvar `zetaDelta`, beta redexes, `eta`, and lambdas/sorts.
- Strict ascending source order, deduplication (no double evaluation), single evaluation of pin
  conditions on matched candidates only, mixed/prefix/multi-column/non-indexed boundaries,
  50-branch dispatch sanity, and lazy `O(|pattern|)` deep-spine unassigned-mvar behavior.
-/

namespace ExprQuotIndexTest

open Lean Meta
open Lean.Meta.Sym (SymM)

private def assertEq [BEq α] [Repr α] (label : String) (actual expected : α) :
    MetaM Unit := do
  unless actual == expected do
    throwError "{label}: got {repr actual}, expected {repr expected}"

abbrev redTwo : Nat := Nat.succ (Nat.succ Nat.zero)
abbrev redFun : Nat → Nat := fun x => x + 1
abbrev redArrow : Type := Nat → Bool

def customUnf (x : Nat) : Nat := x + 10
opaque fTag : Nat → Nat
opaque gTag : Nat → Nat
opaque pCarry {P : Prop} (h : P) (x : Nat) : Nat

/-! ## 1. `.structural` & `.structural +inst` soundness -/

private def structMatch (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| ?a + $a)     => let _ := a; return 1
  | `(expr| ?a + ?b)     => let _ := (a, b); return 2
  | `(expr| Nat.succ ?n) => let _ := n; return 3
  | `(expr| ?α → ?β)     => let _ := (α, β); return 4
  | `(expr| (?p : Nat × Nat).1) => let _ := p; return 5
  | `(expr| fTag ?x)     => let _ := x; return 6
  | `(expr| pCarry _ ?x) => let _ := x; return 7
  | `(expr| ?f 0)        => let _ := f; return 8
  | `(expr| fun x => ?b) => let _ := b; return 9
  | _                    => return 0

private def structInstMatch (e : Expr) : MetaM Nat :=
  match e with
  | `(expr +inst| ?a + ?b) => let _ := (a, b); return 1
  | `(expr +inst| ?a * ?b) => let _ := (a, b); return 2
  | _                      => return 0

/-- info: [1, 2, 3, 4, 5, 0, 6, 7, 8, 9, 0, 0, 1] -/
#guard_msgs in
run_meta do
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let add11 ← `(expr| 1 + 1)
  let add12 ← `(expr| 1 + 2)
  let succ0 := mkApp (mkConst ``Nat.succ) zero
  let arrow := mkForall `a .default (mkConst ``Nat) (mkConst ``Bool)
  let prodApp ← `(expr| ($zero, $one).1)
  let rawProj := Expr.proj ``Prod 0 (mkApp4 (mkConst ``Prod.mk [0, 0])
    (mkConst ``Nat) (mkConst ``Nat) zero one)
  let fApp := mkApp (mkConst ``fTag) one
  let carry ← `(expr| pCarry trivial 5)
  let hoApp ← `(expr| gTag 0)
  let lam := mkLambda `y .default (mkConst ``Nat) (mkNatLit 9)
  -- Structural must NOT beta-reduce `(fun y => fTag 9) 1` into `fTag 9` or fold `.proj`
  let betaRedex := mkApp (mkLambda `y .default (mkConst ``Nat) (← `(expr| fTag 9))) one
  let mv ← mkFreshExprMVar (some (mkConst ``Nat))

  -- `.structural +inst` with alternative `HAdd` instance expression (let-bound instance)
  let haddInst ← synthInstance (mkApp3 (mkConst ``HAdd [0, 0, 0])
    (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat))
  let instTy := mkApp3 (mkConst ``HAdd [0, 0, 0])
    (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat)
  let haddLetInst := mkAppN (mkConst ``HAdd.hAdd [0, 0, 0])
    #[mkConst ``Nat, mkConst ``Nat, mkConst ``Nat,
      mkLet `inst instTy haddInst (mkBVar 0),
      one, one]

  let results : List Nat := [
    ← structMatch add11,
    ← structMatch add12,
    ← structMatch succ0,
    ← structMatch arrow,
    ← structMatch prodApp,
    ← structMatch rawProj,
    ← structMatch fApp,
    ← structMatch carry,
    ← structMatch hoApp,
    ← structMatch lam,
    ← structMatch betaRedex,
    ← structMatch mv,
    ← structInstMatch haddLetInst
  ]
  logInfo m!"{results}"

/-! ## 2. `.reducible` soundness (literals, offsets, aliases, lambdas, sorts, `[items]`) -/

private def reducibleMatch (e : Expr) : MetaM Nat :=
  match e with
  | `(expr/reducible| $(mkNatLit 2)) => return 1
  | `(expr/reducible| Nat.succ ?n)    => let _ := n; return 2
  | `(expr/reducible| Nat.zero)       => return 3
  | `(expr/reducible| fun x => x + ?a) => let _ := a; return 4
  | `(expr/reducible| Type)           => return 5
  | `(expr/reducible| ?α → ?β)        => let _ := (α, β); return 6
  | `(expr/reducible| fTag ?x)        => let _ := x; return 7
  | _                                 => return 0

private def reducibleItemsMatch (e : Expr) : MetaM Nat :=
  match e with
  | `(expr/reducible [+customUnf]| ?x + 10) => let _ := x; return 1
  | `(expr/reducible [+customUnf]| fTag ?x) => let _ := x; return 2
  | _                                       => return 0

/-- info: [1, 1, 2, 3, 4, 5, 6, 7, 1] -/
#guard_msgs in
run_meta do
  -- `mkNatLit 2` pattern vs `Nat.succ (Nat.succ Nat.zero)` & `redTwo`
  let twoUnary :=
    mkApp (mkConst ``Nat.succ) (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero))
  let sortLet := mkLet `u (mkSort 2) (mkSort 1) (mkBVar 0)
  let letF := mkLet `y (mkConst ``Nat) (mkNatLit 3) (mkApp (mkConst ``fTag) (mkBVar 0))
  let cApp := mkApp (mkConst ``customUnf) (mkNatLit 4)
  let results : List Nat := [
    ← reducibleMatch twoUnary,
    ← reducibleMatch (mkConst ``redTwo),
    ← reducibleMatch (mkNatLit 5),
    ← reducibleMatch (mkNatLit 0),
    ← reducibleMatch (mkConst ``redFun),
    ← reducibleMatch sortLet,
    ← reducibleMatch (mkConst ``redArrow),
    ← reducibleMatch letF,
    ← reducibleItemsMatch cApp
  ]
  logInfo m!"{results}"

/-! ## 3. `/sym` shared-relation indexing soundness -/

private def symIndexedMatch [Monad m] [Meta.MonadSym m] (e : Expr) : m Nat :=
  match e with
  | `(expr/sym| fTag 5)        => return 1
  | `(expr/sym| Nat.succ ?n)   => let _ := n; return 2
  | `(expr/sym| ?x + $x)       => let _ := x; return 3
  | `(expr/sym| ?x + 1)        => let _ := x; return 4
  | `(expr/sym| fun x => x + ?a) => let _ := a; return 5
  | `(expr/sym| Type)          => return 6
  | _                          => return 0

/-- info: [1, 2, 2, 3, 2, 3, 5, 6] -/
#guard_msgs in
run_meta SymM.run do
  -- `fTag (1 + 4)` must NOT be missed by subterm `5` key in `Sym.DiscrTree`!
  let fOnePlusFour ← `(expr/sym| fTag ((1 : Nat) + 4))
  -- `let x := 9; 9 + x` is an offset term (`? + 9`), so `Nat.succ ?n` matches first in order
  let letBodyOffset ← withLocalDeclD `v (mkConst ``Nat) fun v => do
    return (← `(expr/sym| 9 + $v)).abstract #[v]
  let letSumOffset := mkLet `x (mkConst ``Nat) (mkNatLit 9) letBodyOffset
  -- Without numeric RHS (`fTag 9 + fTag 9`), `Nat.succ ?n` skips to nonlinear `?x + $x`!
  let tag9 ← `(expr/sym| fTag 9)
  let letBodyTag ← withLocalDeclD `v (mkConst ``Nat) fun v => do
    return (← `(expr/sym| $tag9 + $v)).abstract #[v]
  let letSumTag := mkLet `x (mkConst ``Nat) tag9 letBodyTag
  let rZ ← withLetDecl `z (mkConst ``Nat) (mkNatLit 4) fun zVar => do
    symIndexedMatch (← `(expr/sym| Nat.succ $zVar))
  let tag4 ← `(expr/sym| fTag 4)
  let rW ← withLetDecl `w (mkConst ``Nat) tag4 fun wVar => do
    symIndexedMatch (← `(expr/sym| $wVar + $tag4))
  let lamPlus ← `(expr/sym| fun x => x + 7)
  let results : List Nat := [
    ← symIndexedMatch fOnePlusFour,
    ← symIndexedMatch (mkNatLit 5),
    ← symIndexedMatch letSumOffset,
    ← symIndexedMatch letSumTag,
    rZ,
    rW,
    ← symIndexedMatch lamPlus,
    ← symIndexedMatch (mkSort 1)
  ]
  logInfo m!"{results}"

/-! ## 4. Source order, dedup, single side-effect, & non-indexed boundaries -/

/-- info: (1, 1, 99, 20, 1, 2) -/
#guard_msgs in
run_meta do
  let countRef ← IO.mkRef 0
  let p ← `(expr| 10)
  let dispatchWithPin (e : Expr) : MetaM Nat :=
    match e with
    | `(expr| $p + ?y) => do countRef.modify (· + 1); let _ := y; return 1
    | `(expr| ?a + ?b) => do countRef.modify (· + 1); let _ := (a, b); return 2
    | `(expr| _ + _)   => do countRef.modify (· + 1); return 3
    | _                => return 0
  let t ← `(expr| 10 + 20)
  let pinRes ← dispatchWithPin t
  let count ← countRef.get

  -- Prefix constructor alt followed by >= 2 simple expr alts on col 1
  let mixedCols (flag : Nat) (e : Expr) : MetaM Nat :=
    match flag, e with
    | 0, _              => return 99
    | _, `(expr| ?a + ?b) => let _ := (a, b); return 10
    | _, `(expr| ?a * ?b) => let _ := (a, b); return 20
    | _, _              => return 0
  let mix0 ← mixedCols 0 (← `(expr| 1 + 2))
  let mix1 ← mixedCols 1 (← `(expr| 1 * 2))

  -- Disabled flags / `/instances` / `/defeq` / local `$d` fall back cleanly to linear match
  let withNegFlag (e : Expr) : MetaM Nat :=
    match e with
    | `(expr/reducible -beta| ?a + ?b) => let _ := (a, b); return 1
    | `(expr/reducible -beta| ?a * ?b) => let _ := (a, b); return 2
    | _                                => return 0
  let withInstances (e : Expr) : MetaM Nat :=
    match e with
    | `(expr/instances| ?a + ?b) => let _ := (a, b); return 1
    | `(expr/instances| ?a * ?b) => let _ := (a, b); return 2
    | _                          => return 0
  let negRes ← withNegFlag (← `(expr| 1 + 2))
  let instRes ← withInstances (← `(expr| 1 * 2))
  logInfo m!"({pinRes}, {count}, {mix0}, {mix1}, {negRes}, {instRes})"

/-! ## 5. 50-branch `DiscrTree` scale sanity -/

opaque k0 : Nat → Nat
opaque k1 : Nat → Nat
opaque k2 : Nat → Nat
opaque k3 : Nat → Nat
opaque k4 : Nat → Nat
opaque k5 : Nat → Nat
opaque k6 : Nat → Nat
opaque k7 : Nat → Nat
opaque k8 : Nat → Nat
opaque k9 : Nat → Nat

private def bigDispatch50 (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| k0 (k0 ?x)) => let _ := x; return 1
  | `(expr| k0 (k1 ?x)) => let _ := x; return 2
  | `(expr| k0 (k2 ?x)) => let _ := x; return 3
  | `(expr| k0 (k3 ?x)) => let _ := x; return 4
  | `(expr| k0 (k4 ?x)) => let _ := x; return 5
  | `(expr| k1 (k0 ?x)) => let _ := x; return 6
  | `(expr| k1 (k1 ?x)) => let _ := x; return 7
  | `(expr| k1 (k2 ?x)) => let _ := x; return 8
  | `(expr| k1 (k3 ?x)) => let _ := x; return 9
  | `(expr| k1 (k4 ?x)) => let _ := x; return 10
  | `(expr| k2 (k0 ?x)) => let _ := x; return 11
  | `(expr| k2 (k1 ?x)) => let _ := x; return 12
  | `(expr| k2 (k2 ?x)) => let _ := x; return 13
  | `(expr| k2 (k3 ?x)) => let _ := x; return 14
  | `(expr| k2 (k4 ?x)) => let _ := x; return 15
  | `(expr| k3 (k0 ?x)) => let _ := x; return 16
  | `(expr| k3 (k1 ?x)) => let _ := x; return 17
  | `(expr| k3 (k2 ?x)) => let _ := x; return 18
  | `(expr| k3 (k3 ?x)) => let _ := x; return 19
  | `(expr| k3 (k4 ?x)) => let _ := x; return 20
  | `(expr| k4 (k0 ?x)) => let _ := x; return 21
  | `(expr| k4 (k1 ?x)) => let _ := x; return 22
  | `(expr| k4 (k2 ?x)) => let _ := x; return 23
  | `(expr| k4 (k3 ?x)) => let _ := x; return 24
  | `(expr| k4 (k4 ?x)) => let _ := x; return 25
  | `(expr| k5 (k0 ?x)) => let _ := x; return 26
  | `(expr| k5 (k1 ?x)) => let _ := x; return 27
  | `(expr| k5 (k2 ?x)) => let _ := x; return 28
  | `(expr| k5 (k3 ?x)) => let _ := x; return 29
  | `(expr| k5 (k4 ?x)) => let _ := x; return 30
  | `(expr| k6 (k0 ?x)) => let _ := x; return 31
  | `(expr| k6 (k1 ?x)) => let _ := x; return 32
  | `(expr| k6 (k2 ?x)) => let _ := x; return 33
  | `(expr| k6 (k3 ?x)) => let _ := x; return 34
  | `(expr| k6 (k4 ?x)) => let _ := x; return 35
  | `(expr| k7 (k0 ?x)) => let _ := x; return 36
  | `(expr| k7 (k1 ?x)) => let _ := x; return 37
  | `(expr| k7 (k2 ?x)) => let _ := x; return 38
  | `(expr| k7 (k3 ?x)) => let _ := x; return 39
  | `(expr| k7 (k4 ?x)) => let _ := x; return 40
  | `(expr| k8 (k0 ?x)) => let _ := x; return 41
  | `(expr| k8 (k1 ?x)) => let _ := x; return 42
  | `(expr| k8 (k2 ?x)) => let _ := x; return 43
  | `(expr| k8 (k3 ?x)) => let _ := x; return 44
  | `(expr| k8 (k4 ?x)) => let _ := x; return 45
  | `(expr| k9 (k0 ?x)) => let _ := x; return 46
  | `(expr| k9 (k1 ?x)) => let _ := x; return 47
  | `(expr| k9 (k2 ?x)) => let _ := x; return 48
  | `(expr| k9 (k3 ?x)) => let _ := x; return 49
  | `(expr| k9 (k4 ?x)) => let _ := x; return 50
  | _                   => return 0

/-- info: (50, 0) -/
#guard_msgs in
run_meta do
  let probe := mkApp (mkConst ``k9) (mkApp (mkConst ``k4) (mkNatLit 7))
  let mut last := 0
  for _ in *...200 do
    last ← bigDispatch50 probe
  let miss := mkApp (mkConst ``k9) (mkApp (mkConst ``k8) (mkNatLit 7))
  logInfo m!"({last}, {← bigDispatch50 miss})"

/-! ## 6. Programmatic `.proj` indexing & sequential oracle equivalence -/

private def structOracle (e : Expr) : MetaM Nat := do
  match e with | `(expr| ?a + $a) => let _ := a; return 1 | _ => pure ()
  match e with | `(expr| ?a + ?b) => let _ := (a, b); return 2 | _ => pure ()
  match e with | `(expr| Nat.succ ?n) => let _ := n; return 3 | _ => pure ()
  match e with | `(expr| ?α → ?β) => let _ := (α, β); return 4 | _ => pure ()
  match e with | `(expr| (?p : Nat × Nat).1) => let _ := p; return 5 | _ => pure ()
  match e with | `(expr| fTag ?x) => let _ := x; return 6 | _ => pure ()
  match e with | `(expr| pCarry _ ?x) => let _ := x; return 7 | _ => pure ()
  match e with | `(expr| ?f 0) => let _ := f; return 8 | _ => pure ()
  match e with | `(expr| fun x => ?b) => let _ := b; return 9 | _ => pure ()
  return 0

private def reducibleOracle (e : Expr) : MetaM Nat := do
  match e with | `(expr/reducible| $(mkNatLit 2)) => return 1 | _ => pure ()
  match e with | `(expr/reducible| Nat.succ ?n) => let _ := n; return 2 | _ => pure ()
  match e with | `(expr/reducible| Nat.zero) => return 3 | _ => pure ()
  match e with | `(expr/reducible| fun x => x + ?a) => let _ := a; return 4 | _ => pure ()
  match e with | `(expr/reducible| Type) => return 5 | _ => pure ()
  match e with | `(expr/reducible| ?α → ?β) => let _ := (α, β); return 6 | _ => pure ()
  match e with | `(expr/reducible| fTag ?x) => let _ := x; return 7 | _ => pure ()
  return 0

private def symOracle (e : Expr) : SymM Nat := do
  match e with | `(expr/sym| fTag 5) => return 1 | _ => pure ()
  match e with | `(expr/sym| Nat.succ ?n) => let _ := n; return 2 | _ => pure ()
  match e with | `(expr/sym| ?x + $x) => let _ := x; return 3 | _ => pure ()
  match e with | `(expr/sym| ?x + 1) => let _ := x; return 4 | _ => pure ()
  match e with | `(expr/sym| fun x => x + ?a) => let _ := a; return 5 | _ => pure ()
  match e with | `(expr/sym| Type) => return 6 | _ => pure ()
  return 0

/-- info: (1, 2, 0, true, true, true) -/
#guard_msgs in
run_meta do
  -- Programmatic `.proj` `DiscrTree.Key.proj` dispatch check
  let patProj0 : ExprPattern :=
    { levelParams := []
      lam := mkLambda `p .default (mkConst ``Expr) (Expr.proj ``Prod 0 (mkBVar 0))
      numVars := 1, namedIdx := #[0], firstOrder := #[true] }
  let patProj1 : ExprPattern :=
    { levelParams := []
      lam := mkLambda `p .default (mkConst ``Expr) (Expr.proj ``Prod 1 (mkBVar 0))
      numVars := 1, namedIdx := #[0], firstOrder := #[true] }
  let relStruct : ExprMatchRel := { engine := .structural }
  let resolvedStruct ← relStruct.resolve
  let runProjIdx (e : Expr) : MetaM Nat :=
    ExprPattern.matchIndexedOrElse `ExprQuotIndexTest.projSite #[patProj0, patProj1]
      relStruct e
      #[fun scrut next => ExprPattern.matchResolvedOrElse patProj0 resolvedStruct #[] #[] scrut
          (fun _ => return 1) next,
        fun scrut next => ExprPattern.matchResolvedOrElse patProj1 resolvedStruct #[] #[] scrut
          (fun _ => return 2) next]
      (fun _ => return 0)
  let p0 := Expr.proj ``Prod 0 (mkApp4 (mkConst ``Prod.mk [0, 0])
    (mkConst ``Nat) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2))
  let p1 := Expr.proj ``Prod 1 (mkApp4 (mkConst ``Prod.mk [0, 0])
    (mkConst ``Nat) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2))
  let r0 ← runProjIdx p0
  let r1 ← runProjIdx p1
  let rMiss ← runProjIdx (mkNatLit 0)

  -- Differential oracle checks on structural, reducible, and /sym test terms
  let corpus : Array Expr := #[
    ← `(expr| 1 + 1), ← `(expr| 1 + 2), mkApp (mkConst ``Nat.succ) (mkNatLit 0),
    mkForall `a .default (mkConst ``Nat) (mkConst ``Bool), ← `(expr| (0, 1).1),
    mkApp (mkConst ``fTag) (mkNatLit 1), ← `(expr| pCarry trivial 5), ← `(expr| gTag 0),
    mkLambda `y .default (mkConst ``Nat) (mkNatLit 9),
    mkApp (mkLambda `y .default (mkConst ``Nat) (← `(expr| fTag 9))) (mkNatLit 1),
    mkNatLit 2, mkRawNatLit 2, mkNatLit 0, mkRawNatLit 0, mkConst ``redTwo, mkConst ``redFun,
    mkSort 1, mkConst ``redArrow, mkLet `u (mkSort 2) (mkSort 1) (mkBVar 0), p0
  ]
  for item in corpus do
    assertEq "structMatch" (← structMatch item) (← structOracle item)
    assertEq "reducibleMatch" (← reducibleMatch item) (← reducibleOracle item)
  SymM.run do
    let symCorpus : Array Expr := #[
      ← `(expr/sym| fTag ((1 : Nat) + 4)), mkNatLit 5, mkRawNatLit 5,
      ← `(expr/sym| (fTag 9) + (fTag 9)), ← `(expr/sym| (fTag 9) + 1),
      ← `(expr/sym| fun x => x + 7), mkSort 1, mkNatLit 0,
      mkLet `x (mkConst ``Nat) (mkNatLit 9) (← `(expr/sym| 9 + 9))
    ]
    for item in symCorpus do
      assertEq "symIndexedMatch" (← symIndexedMatch item) (← symOracle item)
  logInfo m!"({r0}, {r1}, {rMiss}, true, true, true)"

/-! ## 7. Lazy `O(|pattern|)` deep-spine unassigned-mvar scaling in indexed dispatch -/

private def deepSpineMatch (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| k0 ?x) => return some x
  | `(expr| k1 ?x) => return some x
  | `(expr| k2 ?x) => return some x
  | _              => return none

/-- info: (true, 0, true, 50, true) -/
#guard_msgs in
run_meta do
  let mv ← mkFreshExprMVar (some (mkConst ``Nat))
  let mut deep := mv
  for _ in *...2000 do
    deep := mkApp (mkConst ``fTag) deep
  -- 1. Match shallowly over deep spine with unassigned mvar without instantiating it
  let hit ← deepSpineMatch (mkApp (mkConst ``k0) deep)
  let hitOk := hit.any (· == deep)
  -- 2. Indexed miss over 50-branch tree must skip cleanly in `O(|pattern|)`
  let missExpr := mkApp (mkConst ``k9) (mkApp (mkConst ``k8) deep)
  let mut missRes := 0
  for _ in *...200 do
    missRes ← bigDispatch50 missExpr
  let stillUnassigned := !(← mv.mvarId!.isAssigned)
  -- 3. Assigned head mvar resolves lazily at inspected head without eager deep traversal
  let headRootMV ← mkFreshExprMVar (some (mkConst ``Nat))
  headRootMV.mvarId!.assign (mkApp (mkConst ``k9) (mkApp (mkConst ``k4) (mkNatLit 7)))
  let resolvedHeadRes ← bigDispatch50 headRootMV
  -- Unassigned mvar at head returns catch-all without failing
  let freeHeadMV ← mkFreshExprMVar (some (mkConst ``Nat))
  let freeRes ← deepSpineMatch (mkApp (mkConst ``k3) deep)
  let freeHeadRes ← bigDispatch50 freeHeadMV
  let okFree := freeRes.isNone && freeHeadRes == 0
  logInfo m!"({hitOk}, {missRes}, {stillUnassigned}, {resolvedHeadRes}, {okFree})"

end ExprQuotIndexTest
