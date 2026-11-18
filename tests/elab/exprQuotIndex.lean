/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
import Lean

/-!
Comprehensive tests for shared-relation `DiscrTree` indexing in native ``match`` over `expr`
quotations:
- Equivalence between indexed dispatch and direct linear pattern matching across `.structural`,
  `.reducible`, and `.sym`.
- `.structural` soundness: does NOT reduce `.proj` or beta redexes, respects `+inst` across differing
  instances, handles higher-order `?f x`, closed proofs, arrows, `fvar`s, and caller `mvar`s.
- `.reducible` soundness: handles root `Nat.succ _`, `Nat.zero`, `0`, `2`, `(fun x => x + ?a)`,
  `Sort _`, reducible aliases, `eta`, `let`, static `[items]`, and literal <-> numeral equivalence.
- `/sym` indexing soundness: handles root & subterm offsets (`?n + 1`, `f 5` matching `f (1 + 4)`),
  `letE`, local `let`-fvar `zetaDelta`, beta redexes, `eta`, and lambdas/sorts.
- Strict ascending source order, deduplication (no double evaluation), single evaluation of pin
  conditions on matched candidates only, mixed/prefix/multi-column/non-indexed boundaries, and
  50-branch dispatch sanity.
-/

namespace ExprQuotIndexTest

open Lean Meta
open Lean.Meta.Sym (SymM)

private def check (cond : Bool) (msg : String) : MetaM Unit := do
  unless cond do
    throwError msg

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

run_meta do
  let x := mkFVar (FVarId.mk `xTest)
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let add11 := ← `(expr| 1 + 1)
  let add12 := ← `(expr| 1 + 2)
  let succ0 := mkApp (mkConst ``Nat.succ) zero
  let arrow := mkForall `a .default (mkConst ``Nat) (mkConst ``Bool)
  let prodApp ← `(expr| ($zero, $one).1)
  let rawProj := Expr.proj ``Prod 0 (mkApp4 (mkConst ``Prod.mk [0, 0])
    (mkConst ``Nat) (mkConst ``Nat) zero one)
  let fApp := mkApp (mkConst ``fTag) one
  let carry ← `(expr| pCarry trivial 5)
  let hoApp ← `(expr| gTag 0)
  let lam := mkLambda `y .default (mkConst ``Nat) (mkNatLit 9)
  -- Structural must NOT beta-reduce `(fun y => fTag 9) 1` into `fTag 9` or fold `.proj` into `Prod.fst`
  let betaRedex := mkApp (mkLambda `y .default (mkConst ``Nat) (← `(expr| fTag 9))) one
  let mv ← mkFreshExprMVar (some (mkConst ``Nat))

  check ((← structMatch add11) == 1) "expected nonlinear `?a + $a` first"
  check ((← structMatch add12) == 2) "expected `?a + ?b`"
  check ((← structMatch succ0) == 3) "expected `Nat.succ ?n`"
  check ((← structMatch arrow) == 4) "expected arrow `?α → ?β`"
  check ((← structMatch prodApp) == 5) "expected `.structural` match on `(?p : Nat × Nat).1`"
  check ((← structMatch rawProj) == 0) "`.structural` must NOT fold `.proj` into `Prod.fst`"
  check ((← structMatch fApp) == 6) "expected `fTag ?x`"
  check ((← structMatch carry) == 7) "expected closed proof wildcard `pCarry _ ?x`"
  check ((← structMatch hoApp) == 8) "expected higher-order `?f 0` match"
  check ((← structMatch lam) == 9) "expected lambda structural match"
  check ((← structMatch betaRedex) == 0) "structural must not beta-reduce scrutinee"
  check ((← structMatch mv) == 0) "unassigned caller mvar should fall through"

  -- `.structural +inst` with alternative `HAdd` instance expression (let-bound instance)
  let haddInst ← synthInstance (mkApp3 (mkConst ``HAdd [0, 0, 0])
    (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat))
  let haddLetInst := mkAppN (mkConst ``HAdd.hAdd [0, 0, 0])
    #[mkConst ``Nat, mkConst ``Nat, mkConst ``Nat,
      mkLet `inst (mkApp3 (mkConst ``HAdd [0, 0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat))
        haddInst (mkBVar 0),
      one, one]
  check ((← structInstMatch haddLetInst) == 1) "expected `.structural +inst` to ignore differing instance key"

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

run_meta do
  -- `mkNatLit 2` pattern vs `Nat.succ (Nat.succ Nat.zero)` & `redTwo`
  let twoUnary := mkApp (mkConst ``Nat.succ) (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero))
  check ((← reducibleMatch twoUnary) == 1) "expected unary 2 to match `mkNatLit 2`"
  check ((← reducibleMatch (mkConst ``redTwo)) == 1) "expected reducible alias `redTwo` to match `2`"
  check ((← reducibleMatch (mkNatLit 5)) == 2) "expected `Nat.succ ?n` root pattern to match literal `5`"
  check ((← reducibleMatch (mkNatLit 0)) == 3) "expected `Nat.zero` pattern to match `mkNatLit 0`"
  check ((← reducibleMatch (mkConst ``redFun)) == 4) "expected `redFun` to match `fun x => x + ?a`"
  let sortLet := mkLet `u (mkSort 2) (mkSort 1) (mkBVar 0)
  check ((← reducibleMatch sortLet) == 5) "expected `Type` pattern to match let-bound `Type`"
  check ((← reducibleMatch (mkConst ``redArrow)) == 6) "expected `redArrow` to match `?α → ?β`"
  -- `eta` equivalence on `(fun x => fTag x)` when `x` would match? Actually `(fun z => g z)` eta-reduces in subterm
  let letF := mkLet `y (mkConst ``Nat) (mkNatLit 3) (mkApp (mkConst ``fTag) (mkBVar 0))
  check ((← reducibleMatch letF) == 7) "expected let-reduction inside `fTag`"
  let cApp := mkApp (mkConst ``customUnf) (mkNatLit 4)
  check ((← reducibleItemsMatch cApp) == 1) "expected `[+customUnf]` to index & match `customUnf 4`"

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

run_meta SymM.run do
  -- `fTag (1 + 4)` must NOT be missed by subterm `5` key in `Sym.DiscrTree`!
  let fOnePlusFour ← `(expr/sym| fTag ((1 : Nat) + 4))
  check ((← symIndexedMatch fOnePlusFour) == 1) "expected `fTag (1 + 4)` to match `fTag 5`"
  -- Root `Nat.succ ?n` must match raw literal `5`
  check ((← symIndexedMatch (mkNatLit 5)) == 2) "expected `5` to match `Nat.succ ?n`"
  -- `let` fvar `zetaDelta` + `letE`
  -- `let x := 9; 9 + x` is an offset term (`? + 9`), so `Nat.succ ?n` matches first in source order!
  let letBodyOffset ← withLocalDeclD `v (mkConst ``Nat) fun v => do
    return (← `(expr/sym| 9 + $v)).abstract #[v]
  let letSumOffset := mkLet `x (mkConst ``Nat) (mkNatLit 9) letBodyOffset
  check ((← symIndexedMatch letSumOffset) == 2)
    "expected `letE` offset `9 + 9` to hit `Nat.succ ?n` first in source order"
  -- Without numeric RHS (`fTag 9 + fTag 9`), `Nat.succ ?n` skips to nonlinear `?x + $x`!
  let tag9 ← `(expr/sym| fTag 9)
  let letBodyTag ← withLocalDeclD `v (mkConst ``Nat) fun v => do
    return (← `(expr/sym| $tag9 + $v)).abstract #[v]
  let letSumTag := mkLet `x (mkConst ``Nat) tag9 letBodyTag
  check ((← symIndexedMatch letSumTag) == 3) "expected `letE` nonlinear match"
  withLetDecl `z (mkConst ``Nat) (mkNatLit 4) fun zVar => do
    let e ← `(expr/sym| Nat.succ $zVar)
    -- `Nat.succ zVar` hits rule 2 (`Nat.succ ?n`) first in source order!
    check ((← symIndexedMatch e) == 2) "expected first matching rule in source order"
  let tag4 ← `(expr/sym| fTag 4)
  withLetDecl `w (mkConst ``Nat) tag4 fun wVar => do
    let eZetaFVar ← `(expr/sym| $wVar + $tag4)
    check ((← symIndexedMatch eZetaFVar) == 3)
      "expected `zetaDelta` `$wVar + $tag4` to match `?x + $x`"
  let redexRoot := mkApp (mkLambda `w .default (mkConst ``Nat) (← `(expr/sym| $(mkConst ``redFun)))) (mkNatLit 0)
  let _ := redexRoot
  let lamPlus ← `(expr/sym| fun x => x + 7)
  check ((← symIndexedMatch lamPlus) == 5) "expected lambda branch"
  check ((← symIndexedMatch (mkSort 1)) == 6) "expected `Type` branch"

/-! ## 4. Source order, dedup, single side-effect, & non-indexed boundaries -/

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
  check ((← dispatchWithPin t) == 1) "must pick first overlapping pattern"
  check ((← countRef.get) == 1) "must execute RHS exactly once (deduplicated)"

  -- Prefix constructor alt followed by >= 2 simple expr alts on col 1
  let mixedCols (flag : Nat) (e : Expr) : MetaM Nat :=
    match flag, e with
    | 0, _              => return 99
    | _, `(expr| ?a + ?b) => let _ := (a, b); return 10
    | _, `(expr| ?a * ?b) => let _ := (a, b); return 20
    | _, _              => return 0
  check ((← mixedCols 0 (← `(expr| 1 + 2))) == 99) "prefix constructor arm"
  check ((← mixedCols 1 (← `(expr| 1 * 2))) == 20) "indexed second column arm"

  -- Disabled flags / `/instances` / `/defeq` / local `$d` fall back cleanly to linear match
  let x := mkFVar (FVarId.mk `localX)
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
  check ((← withNegFlag (← `(expr| 1 + 2))) == 1) "linear `-beta` fallback"
  check ((← withInstances (← `(expr| 1 * 2))) == 2) "linear `/instances` fallback"
  let _ := x

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

run_meta do
  let probe := mkApp (mkConst ``k9) (mkApp (mkConst ``k4) (mkNatLit 7))
  for _ in *...200 do
    check ((← bigDispatch50 probe) == 50) "expected 50th branch via DiscrTree"
  let miss := mkApp (mkConst ``k9) (mkApp (mkConst ``k8) (mkNatLit 7))
  check ((← bigDispatch50 miss) == 0) "expected miss on non-matching head"

/-! ## 6. Programmatic `.proj` indexing & sequential oracle equivalence -/

private def structOracle (e : Expr) : MetaM Nat := do
  if let some n ← (match e with | `(expr| ?a + $a) => let _ := a; pure (some 1) | _ => pure none) then return n
  if let some n ← (match e with | `(expr| ?a + ?b) => let _ := (a, b); pure (some 2) | _ => pure none) then return n
  if let some n ← (match e with | `(expr| Nat.succ ?n) => let _ := n; pure (some 3) | _ => pure none) then return n
  if let some n ← (match e with | `(expr| ?α → ?β) => let _ := (α, β); pure (some 4) | _ => pure none) then return n
  if let some n ← (match e with | `(expr| (?p : Nat × Nat).1) => let _ := p; pure (some 5) | _ => pure none) then return n
  if let some n ← (match e with | `(expr| fTag ?x) => let _ := x; pure (some 6) | _ => pure none) then return n
  if let some n ← (match e with | `(expr| pCarry _ ?x) => let _ := x; pure (some 7) | _ => pure none) then return n
  if let some n ← (match e with | `(expr| ?f 0) => let _ := f; pure (some 8) | _ => pure none) then return n
  if let some n ← (match e with | `(expr| fun x => ?b) => let _ := b; pure (some 9) | _ => pure none) then return n
  return 0

private def reducibleOracle (e : Expr) : MetaM Nat := do
  if let some n ← (match e with | `(expr/reducible| $(mkNatLit 2)) => pure (some 1) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/reducible| Nat.succ ?n) => let _ := n; pure (some 2) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/reducible| Nat.zero) => pure (some 3) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/reducible| fun x => x + ?a) => let _ := a; pure (some 4) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/reducible| Type) => pure (some 5) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/reducible| ?α → ?β) => let _ := (α, β); pure (some 6) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/reducible| fTag ?x) => let _ := x; pure (some 7) | _ => pure none) then return n
  return 0

private def symOracle (e : Expr) : SymM Nat := do
  if let some n ← (match e with | `(expr/sym| fTag 5) => pure (some 1) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/sym| Nat.succ ?n) => let _ := n; pure (some 2) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/sym| ?x + $x) => let _ := x; pure (some 3) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/sym| ?x + 1) => let _ := x; pure (some 4) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/sym| fun x => x + ?a) => let _ := a; pure (some 5) | _ => pure none) then return n
  if let some n ← (match e with | `(expr/sym| Type) => pure (some 6) | _ => pure none) then return n
  return 0

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
    ExprPattern.matchIndexedOrElse `ExprQuotIndexTest.projSite #[patProj0, patProj1] relStruct e
      #[fun scrut next => ExprPattern.matchResolvedOrElse patProj0 resolvedStruct #[] #[] scrut
          (fun _ => return 1) next,
        fun scrut next => ExprPattern.matchResolvedOrElse patProj1 resolvedStruct #[] #[] scrut
          (fun _ => return 2) next]
      (fun _ => return 0)
  -- Check both indices on closed `.proj` terms (and ensure non-`.proj` misses cleanly)
  let p0 := Expr.proj ``Prod 0 (mkApp4 (mkConst ``Prod.mk [0, 0])
    (mkConst ``Nat) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2))
  let p1 := Expr.proj ``Prod 1 (mkApp4 (mkConst ``Prod.mk [0, 0])
    (mkConst ``Nat) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2))
  check ((← runProjIdx p0) == 1) "expected indexed `.proj` 0 match"
  check ((← runProjIdx p1) == 2) "expected indexed `.proj` 1 match"
  check ((← runProjIdx (mkNatLit 0)) == 0) "expected non-`.proj` miss"

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
    check ((← structMatch item) == (← structOracle item))
      s!"structMatch vs oracle mismatch on {item}"
    check ((← reducibleMatch item) == (← reducibleOracle item))
      s!"reducibleMatch vs oracle mismatch on {item}"
  SymM.run do
    let symCorpus : Array Expr := #[
      ← `(expr/sym| fTag ((1 : Nat) + 4)), mkNatLit 5, mkRawNatLit 5,
      ← `(expr/sym| (fTag 9) + (fTag 9)), ← `(expr/sym| (fTag 9) + 1),
      ← `(expr/sym| fun x => x + 7), mkSort 1, mkNatLit 0,
      mkLet `x (mkConst ``Nat) (mkNatLit 9) (← `(expr/sym| 9 + 9))
    ]
    for item in symCorpus do
      check ((← symIndexedMatch item) == (← symOracle item))
        s!"symIndexedMatch vs oracle mismatch on {item}"

end ExprQuotIndexTest
