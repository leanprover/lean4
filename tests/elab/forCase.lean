/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
import Lean

/-!
# Comprehensive Tests for `for case pat in xs do ...`

Covers spec §5 requirements:
- Ordinary refutable patterns (`Option`, `Sum`, tuples, literals, nested constructors, annotated
  binders, membership proofs `for h : case pat in xs` and `for case h : pat in xs`).
- Identifier safety when binding a variable literally named `case` (`for case in cases do ...`).
- `Expr` quotation patterns (`` `(expr[rel]| p) ``) and mixed `(H, `(expr| ...))` patterns.
- `do` control flow preservation: `let mut`, `continue`, `break`, `return` (including nested
  loops), monad lifting, parallel multi-collection `for` loops, term-position `for case`, and
  `backward.do.legacy true`.
- Composition with `localHypTypes`, `localHypDecls`, `subterms`, and `matchDiscriminants` streams,
  including nested multi-hypothesis loops and `break`/`return` early termination.
- Redundant-alternative diagnostics when `case` is written on irrefutable patterns (`x`, `(a, b)`,
  `⟨a, b⟩`, `_`, nested pairs, multi-collection, and `backward.do.legacy true`) without internal
  name leaks, plus pretty-printer round-tripping.
-/

namespace ForCaseTest

open Lean Meta

private inductive Item where
  | num (n : Nat)
  | tag (name : String) (val : Option Nat)
  deriving BEq, Repr

/-! ## 1. Ordinary Refutable Patterns, Annotated Binders, Multi-Collection, Term Position -/

private def sumSome (xs : List (Option Nat)) : Nat := Id.run do
  let mut acc := 0
  for case (some x) in xs do
    acc := acc + x
  return acc

#guard sumSome [] == 0
#guard sumSome [none, none] == 0
#guard sumSome [none, some 3, none, some 7, some 2] == 12

private def collectTagged (xs : List Item) : List (String × Nat) := Id.run do
  let mut out := []
  for case (.tag s (some n)) in xs do
    out := out.concat (s, n)
  return out

#guard collectTagged [.num 1, .tag "a" none, .tag "b" (some 4), .num 9, .tag "c" (some 8)] ==
  [("b", 4), ("c", 8)]

private def tupleAndLiteral (xs : List (Bool × Nat × String)) : List Nat := Id.run do
  let mut out := []
  for case (true, n, "ok") in xs do
    out := out.concat n
  return out

#guard tupleAndLiteral [(false, 1, "ok"), (true, 2, "no"), (true, 5, "ok"), (true, 9, "ok")] ==
  [5, 9]

private def sumAnnotatedAndProof (xs : List (Option Nat)) : Nat := Id.run do
  let mut acc := 0
  for case (some (x : Nat)) in xs do
    acc := acc + x
  for h : case (some x) in xs do
    let _ := h
    acc := acc + x
  for case h : (some (x : Nat)) in xs do
    let _ := h
    acc := acc + x
  return acc

#guard sumAnnotatedAndProof [none, some 2, some 5] == 21

private def zipMultiCase1 (xs : List (Option Nat)) (ys : List Nat) : List (Nat × Nat) := Id.run do
  let mut out := []
  for case (some x) in xs, y in ys do
    out := out.concat (x, y)
  return out

private def zipMultiCase2 (xs : List Nat) (ys : List (Option Nat)) : List (Nat × Nat) := Id.run do
  let mut out := []
  for x in xs, case (some y) in ys do
    out := out.concat (x, y)
  return out

private def zipMultiCaseBoth (xs ys : List (Option Nat)) : List (Nat × Nat) := Id.run do
  let mut out := []
  for case (some x) in xs, case (some y) in ys do
    if x == 0 then continue
    if x == 9 then break
    out := out.concat (x, y)
  return out

#guard zipMultiCase1 [none, some 1, some 2, none] [10, 20, 30, 40] == [(1, 20), (2, 30)]
#guard zipMultiCase2 [10, 20, 30, 40] [none, some 1, none, some 2] == [(20, 1), (40, 2)]
#guard zipMultiCaseBoth [some 0, some 1, none, some 9, some 5]
  [some 10, some 20, some 30, some 40, some 50] == [(1, 20)]
#guard zipMultiCaseBoth [some 1, some 2, some 3] [some 10, none, some 30] == [(1, 10), (3, 30)]

/--
error: Type mismatch
  h
has type
  x✝ ∈ xs
but is expected to have type
  some x ∈ xs
-/
#guard_msgs in
private def proofBinderTypeCheck (xs : List (Option Nat)) : Id Nat := do
  let mut acc := 0
  for h : case (some x) in xs do
    have : some x ∈ xs := h
    acc := acc + x
  return acc

private def sumCaseIdent (cases : List Nat) : Nat := Id.run do
  let mut acc := 0
  for case in cases do
    acc := acc + case
  for h : case in cases do
    let _ : case ∈ cases := h
    acc := acc + 1
  return acc

#guard sumCaseIdent [4, 6, 10] == 23

private def termForCase (xs : List (Option Nat)) : IO Nat := do
  let r ← IO.mkRef 0
  for case (some x) in xs do
    r.modify (· + x)
  r.get

#guard_msgs in
#eval show IO Unit from do
  let v ← termForCase [none, some 4, none, some 9]
  unless v == 13 do
    throw <| IO.userError s!"expected 13, got {v}"

/-! ## 2. `do` Control Flow, Monad Lifting, Nested Loops, `backward.do.legacy true` -/

private def controlFlowSeq (xs : List (Option Nat)) : Option (Nat × List Nat) := Id.run do
  let mut seen : List Nat := []
  for case (some x) in xs do
    if x == 0 then
      continue
    if x == 99 then
      return some (99, seen)
    if x > 10 then
      break
    seen := seen.concat x
  return some (seen.length, seen)

#guard controlFlowSeq [none, some 0, some 2, none, some 5, some 20, some 3] == some (2, [2, 5])
#guard controlFlowSeq [none, some 0, some 4, some 99, some 5] == some (99, [4])

private def nestedLoopsFlow (rows : List (List (Option Nat))) : Nat × List (List Nat) := Id.run do
  let mut acc := 0
  let mut log := []
  for row in rows do
    let mut rowVals := []
    for case (some x) in row do
      if x == 0 then continue
      if x == 999 then return (acc, log)
      if x > 50 then break
      acc := acc + x
      rowVals := rowVals.concat x
    log := log.concat rowVals
  return (acc, log)

#guard nestedLoopsFlow
  [[none, some 0, some 2, some 60, some 3], [some 4, some 5], [some 999, some 1]] ==
  (11, [[2], [4, 5]])

private def monadLiftExceptState (xs : List (Sum String Nat)) : Except String (Nat × Nat) :=
  StateT.run (s := 0) do
    for case (.inr n) in xs do
      if n == 0 then
        continue
      if n == 77 then
        throw "hit-77"
      if n > 10 then
        return 100
      modify (· + n)
    return 0

#guard (monadLiftExceptState [.inl "a", .inr 0, .inr 3, .inl "b", .inr 4] matches .ok (0, 7))
#guard (monadLiftExceptState [.inr 3, .inr 20, .inr 5] matches .ok (100, 3))
#guard (monadLiftExceptState [.inr 2, .inr 77, .inr 5] matches .error "hit-77")

section LegacyMode

set_option backward.do.legacy true

private def legacyFlow (xs : List (Option Nat)) : Id (Nat × List Nat) := do
  let mut acc := 0
  let mut out : List Nat := []
  for case (some x) in xs do
    if x == 0 then continue
    if x == 99 then return (99, out)
    if x > 10 then break
    acc := acc + x
    out := out.concat x
  return (acc, out)

#guard Id.run (legacyFlow [none, some 0, some 2, none, some 4, some 20, some 8]) == (6, [2, 4])
#guard Id.run (legacyFlow [none, some 3, some 99, some 7]) == (99, [3])

private def legacyMulti (xs ys : List (Option Nat)) : Id (List (Nat × Nat)) := do
  let mut out := []
  for case (some x) in xs, case (some y) in ys do
    out := out.concat (x, y)
  return out

#guard Id.run (legacyMulti [none, some 1, some 2] [some 10, none, some 20]) == [(2, 20)]

private def legacyExprQuot (xs : List (Expr × Expr)) : MetaM (List (Expr × Expr)) := do
  let mut out := []
  for case (h, `(expr| ?P → _)) in xs do
    out := out.concat (h, P)
  return out

end LegacyMode

/-! ## 3. `Expr` Quotations & Composition with All 4 Sources (`localHypTypes`, etc.) -/

private def myAliasDef := Nat

private def testExprQuotSources : MetaM Unit := do
  let natTy := mkConst ``Nat
  let propSort := mkSort 0
  withLocalDeclD `P propSort fun p =>
  withLocalDeclD `Q propSort fun q =>
  withLocalDeclD `hNat natTy fun hNat =>
  withLocalDeclD `hImp1 (mkForall `a .default p q) fun hImp1 =>
  withLocalDeclD `hImp2 (mkForall `b .default q natTy) fun hImp2 =>
  withLetDecl `v natTy (mkNatLit 7) (nondep := false) fun v =>
  withLocalDeclD `hAlias (mkConst ``myAliasDef) fun hAlias => do
    -- 1. Nested `for case` over `localHypTypes` implementing chain rule matching.
    let hyps ← localHypTypes
    let mut chains : List (Expr × Expr × Expr × Expr) := []
    for case (hx, `(expr| ?A → ?B)) in hyps do
      for case (hy, `(expr| $B → ?C)) in hyps do
        chains := chains.concat (hx, hy, A, C)
    unless chains == [(hImp1, hImp2, p, natTy)] do
      throwError "unexpected nested localHypTypes match result"

    -- 2. Relation modifier on quotation pattern inside `for case`.
    let mut aliasHits : List Expr := []
    for case (h, `(expr/structural [myAliasDef]| Nat)) in hyps do
      aliasHits := aliasHits.concat h
    unless aliasHits == [hNat, v, hAlias] do
      throwError "expected `hNat`, `v`, and `hAlias` match via `[myAliasDef]`"

    -- 3. `localHypDecls` including `let` values and early `return`.
    let decls ← localHypDecls
    let mut foundLet : Option Expr := none
    for case (hv, _, some `(expr| 7)) in decls do
      foundLet := some hv
      break
    unless foundLet == some v do
      throwError "expected `let v := 7` match in `localHypDecls`"

    -- 4. `subterms` + `for case` + `ExprContext.fill` + early `break`.
    let e := mkApp2 (mkConst ``Nat.add)
      (mkApp2 (mkConst ``Nat.mul) (mkNatLit 2) (mkNatLit 3))
      (mkApp2 (mkConst ``Nat.mul) (mkNatLit 4) (mkNatLit 5))
    let mut firstReplaced := e
    for case (`(expr| Nat.mul ?u ?v), ctx) in subterms e do
      firstReplaced := ctx.fill (← `(expr| Nat.add $v $u))
      break
    let expectedFirst := mkApp2 (mkConst ``Nat.add)
      (mkApp2 (mkConst ``Nat.add) (mkNatLit 3) (mkNatLit 2))
      (mkApp2 (mkConst ``Nat.mul) (mkNatLit 4) (mkNatLit 5))
    unless firstReplaced == expectedFirst do
      throwError "unexpected subterms + fill result"

    -- 5. `matchDiscriminants` + `for case` + early `return` from helper.
    let matchE :=
      mkApp4 (mkConst ``Nat.casesOn [1]) (mkLambda `n .default natTy natTy)
        (mkApp2 (mkConst ``Nat.add) (mkNatLit 8) (mkNatLit 9))
        (mkNatLit 0)
        (mkLambda `n .default natTy (mkBVar 0))
    let findAddDiscr : MetaM (Option Expr) := do
      for case (`(expr| Nat.add ?a ?b), ctx) in matchDiscriminants matchE (alsoCasesOn := true) do
        return some (ctx.fill (← `(expr| Nat.add $b $a)))
      return none
    let some swappedMatchE ← findAddDiscr
      | throwError "expected early return hit in `matchDiscriminants`"
    let expectedMatchE :=
      mkApp4 (mkConst ``Nat.casesOn [1]) (mkLambda `n .default natTy natTy)
        (mkApp2 (mkConst ``Nat.add) (mkNatLit 9) (mkNatLit 8))
        (mkNatLit 0)
        (mkLambda `n .default natTy (mkBVar 0))
    unless swappedMatchE == expectedMatchE do
      throwError "unexpected `matchDiscriminants` + fill result"

    -- 6. Legacy mode `for case (h, `(expr| ?P → _))` check.
    let legacyOut ← legacyExprQuot hyps.toList
    unless legacyOut == [(hImp1, p), (hImp2, q)] do
      throwError "unexpected `legacyExprQuot` output"

#guard_msgs in
#eval show MetaM Unit from testExprQuotSources

/-! ## 4. Irrefutable Pattern Redundant-Alternative Diagnostics & Pretty-Printing -/

/--
@ +3:6...10
error: Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
def irrefVar (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for case x in xs do
    acc := acc + x
  return acc

/--
@ +3:6...10
error: Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
def irrefTuple (xs : List (Nat × Nat)) : Id Nat := do
  let mut acc := 0
  for case (a, b) in xs do
    acc := acc + a + b
  return acc

/--
@ +3:6...10
error: Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
def irrefAnonCtor (xs : List (Nat × Nat)) : Id Nat := do
  let mut acc := 0
  for case ⟨a, b⟩ in xs do
    acc := acc + a + b
  return acc

/--
@ +3:6...10
error: Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
def irrefWildcard (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for case _ in xs do
    acc := acc + 1
  return acc

/--
@ +3:6...10
error: Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
def irrefNestedTuple (xs : List (Nat × Nat × Nat)) : Id Nat := do
  let mut acc := 0
  for case (a, (b, c)) in xs do
    acc := acc + a + b + c
  return acc

/--
@ +3:15...19
error: Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
def irrefSecondDecl (xs ys : List Nat) : Id Nat := do
  let mut acc := 0
  for x in xs, case y in ys do
    acc := acc + x + y
  return acc

/--
@ +4:6...10
error: Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
set_option backward.do.legacy true in
def irrefLegacy (xs : List (Nat × Nat)) : Id Nat := do
  let mut acc := 0
  for case (a, b) in xs do
    acc := acc + a + b
  return acc

/--
info: "for case (some x) in xs do\n  pure ()"
"for h : case (some x) in xs do\n  pure ()"
"for case h : (some x) in xs do\n  pure ()"
"for case in cases do\n  pure ()"
-/
#guard_msgs in
#eval show Elab.Term.TermElabM Unit from do
  let env ← getEnv
  for src in [
    "for case (some x) in xs do pure ()",
    "for h : case (some x) in xs do pure ()",
    "for case h : (some x) in xs do pure ()",
    "for case in cases do pure ()"
  ] do
    let .ok stx := Parser.runParserCategory env `term src | throwError "parse failed: {src}"
    IO.println (repr (← PrettyPrinter.ppTerm ⟨stx⟩).pretty)

end ForCaseTest
