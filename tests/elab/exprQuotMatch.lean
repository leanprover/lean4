import Lean

/-!
Tests for `Lean.Elab.ExprQuot` pattern elaboration and native `match`/`do` integration:
- Syntax/tokenization coexistence (`expr + 1`, `(exprFoo)`, `(expression|$x)`, `(expr|$a + $b)`)
- Basic, nonlinear `$x`, higher-order `?P x`, `?f ?a`, wildcard `_`/`?_`, `(?x : T)`, and stuck vs
  concrete invalid typeclass synthesis (`1 + "hello"`, `(?x : Bool) + 1`, `toString ?x`)
- Engines, `[items]`, `±flags`, `match (modulo := rel)`, and local `$v` relation items
- Nested, multi-discriminant, `as`-pattern, or-pattern, struct pattern, and `do` integration
  (`if let`, `let ... |`, `let ... <- ... |`, `let mut pat := ... |`, `backward.do.legacy true`)
- Join-point fall-through (no code duplication), single discriminant evaluation, `sorryAx`-free
  `match.ignoreUnusedAlts true`, deduplicated `exprPatExt` constants, and clean error diagnostics
  (exhaustiveness, `match h : e`, repeated `?x`, type mismatch, redundancy, inaccessible position,
  structured `MonadLiftT MetaM` check)
-/

open Lean Meta

namespace ExprQuotMatchTest

private def check (cond : Bool) (msg : String) : MetaM Unit := do
  unless cond do
    throwError msg

private def checkTerm (cond : Bool) (msg : String) : Lean.Elab.TermElabM Unit := do
  unless cond do
    throwError msg

/-! ## 1. Syntax & tokenization coexistence -/

section SyntaxQuotCoexistence

def checkSyntaxQuotCoexist (x : TSyntax `term) (instVar : Term) : MacroM (Array Syntax) := do
  let a ← `(expr + 1)
  let b ← `(expr + $instVar)
  let c ← `(expr + inst)
  let d ← `(expr1 + 1)
  let e ← `(match $x:term with | `(expr + 1) => 1 | _ => 0)
  pure #[a.raw, b.raw, c.raw, d.raw, e.raw]

#guard_msgs in
#eval show Lean.Elab.TermElabM Unit from do
  let co ← Lean.Elab.liftMacroM <| checkSyntaxQuotCoexist (← `(1)) (← `(2))
  checkTerm (co.size == 5) "checkSyntaxQuotCoexist size failed"

end SyntaxQuotCoexistence

section ExpressionCategorySpacing

declare_syntax_cat expression
syntax ident : expression

def checkExpressionCategoryNoSpace (x : Ident) : MacroM (TSyntax `expression) :=
  `(expression|$x:ident)

def checkExpressionCategorySpace (x : Ident) : MacroM (TSyntax `expression) :=
  `(expression| $x:ident)

#guard_msgs in
#eval show Lean.Elab.TermElabM Unit from do
  let ex1 ← Lean.Elab.liftMacroM <| checkExpressionCategoryNoSpace (mkIdent `foo)
  let ex2 ← Lean.Elab.liftMacroM <| checkExpressionCategorySpace (mkIdent `foo)
  checkTerm (ex1.raw == ex2.raw) "expression category spacing mismatch"

end ExpressionCategorySpacing

section LeadingAntiquotSpacing

def checkLeadingAntiquotNoSpace (a b : Expr) (e : Expr) : MetaM Bool := do
  match e with
  | `(expr|$a + $b) => return true
  | _ => return false

def checkLeadingAntiquotWithSpace (a b : Expr) (e : Expr) : MetaM Bool := do
  match e with
  | `(expr| $a + $b) => return true
  | _ => return false

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  let e1 := mkNatAdd x y
  check (← checkLeadingAntiquotNoSpace x y e1) "no-space leading antiquot match failed"
  check (← checkLeadingAntiquotWithSpace x y e1) "spaced leading antiquot match failed"
  check (!(← checkLeadingAntiquotNoSpace y x e1)) "swapped leading antiquot unexpectedly matched"

end LeadingAntiquotSpacing

/-! ## 2. Basic, non-linear, HO, `(?x : T)`, stuck TC, and relations -/

section BasicNonLinearAndWildcards

def matchAddSplit (e : Expr) : MetaM (Option (Expr × Expr)) :=
  match e with
  | `(expr| ?a + ?b) => return some (a, b)
  | _ => return none

def matchSameAdd (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| ?x + $x) => return some x
  | _ => return none

def matchWithWildcards (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| ?x + _ + ?_) => return some x
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  let e1 := mkNatAdd x y
  check (← matchAddSplit e1).isSome "matchAddSplit failed"
  check ((← matchSameAdd (mkNatAdd x x)) == some x) "matchSameAdd equal failed"
  check (← matchSameAdd e1).isNone "matchSameAdd distinct unexpectedly matched"
  check (← matchWithWildcards (mkNatAdd (mkNatAdd x y) (mkNatLit 1))).isSome
    "matchWithWildcards failed"

end BasicNonLinearAndWildcards

section FirstOrderAndHigherOrder

def matchHigherOrder (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| fun x => ?P x) => return some P
  | _ => return none

def matchFirstOrderApp (e : Expr) : MetaM (Option (Expr × Expr)) :=
  match e with
  | `(expr| ?f ?a) => return some (f, a)
  | _ => return none

def matchConstBinder (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| fun (_ : Nat) => ?c) => return some c
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  let appExpr := mkApp (mkConst ``Nat.succ) x
  check ((← matchFirstOrderApp appExpr) == some (mkConst ``Nat.succ, x))
    "first-order ?f ?a failed"
  let natTy := mkConst ``Nat
  let lamApp := mkLambda `x .default natTy (mkNatAdd (mkBVar 0) (mkNatLit 1))
  check (← matchHigherOrder lamApp).isSome "higher-order ?P x failed"
  check (← matchConstBinder lamApp).isNone "const-binder matched dependent body"
  let constLam := mkLambda `x .default natTy (mkNatLit 5)
  check ((← matchConstBinder constLam) == some (mkNatLit 5)) "matchConstBinder failed"

end FirstOrderAndHigherOrder

section TypeAscriptionAndStuckTC

def matchTypeAscribedProj (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| (?p : Nat × Nat).1) => return some p
  | _ => return none

def matchDefEqTypedBinder (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr/defeq| (?x : Nat)) => return some x
  | _ => return none

def matchStuckToStringImplicit (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| toString ?x) => return some x
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let pairVal ← mkAppM ``Prod.mk #[mkNatLit 1, mkNatLit 2]
  check ((← matchTypeAscribedProj (← mkAppM ``Prod.fst #[pairVal])) == some pairVal)
    "type-ascribed projection (?p : Nat × Nat).1 failed"
  check ((← matchDefEqTypedBinder (mkNatLit 3)) == some (mkNatLit 3))
    "defeq typed binder on Nat failed"
  check (← matchDefEqTypedBinder (mkConst ``Bool.true)).isNone
    "defeq typed binder (?x : Nat) must reject Bool.true"
  let toStrNat ← mkAppM ``toString #[mkNatLit 7]
  check ((← matchStuckToStringImplicit toStrNat) == some (mkNatLit 7))
    "stuck implicit toString ?x failed"

end TypeAscriptionAndStuckTC

section RelationsAndItems

abbrev myAbbrevId (n : Nat) : Nat := n
-- Shared across relation, `modulo`, and cache-isolation tests below.
def myDefId (n : Nat) : Nat := n
@[simp] def mySimpId (n : Nat) : Nat := n

def testRelations (e : Expr) : MetaM (Array String) := do
  let mut hits : Array String := #[]
  if let `(expr| myAbbrevId ?x) := e then hits := hits.push s!"structural_abbrev:{x.isFVar}"
  if let `(expr/reducible| Nat.zero) := e then hits := hits.push "reducible_0"
  if let `(expr/structural| myDefId ?x) := e then
    let _ := x; hits := hits.push "structural_def"
  if let `(expr/defeq| Nat.zero) := e then hits := hits.push "defeq_def_0"
  if let `(expr/structural[+myDefId]| Nat.zero) := e then hits := hits.push "structural_plus_item"
  if let `(expr/reducible[-myAbbrevId]| Nat.zero) := e then
    hits := hits.push "reducible_minus_item"
  if let `(expr/structural[+simp]| Nat.zero) := e then hits := hits.push "simp_set_0"
  if let `(expr/structural +beta| Nat.add ?a Nat.zero) := e then
    if a == mkNatLit 2 then hits := hits.push "beta"
  if let `(expr/structural +zeta| Nat.add ?a Nat.zero) := e then
    if a == mkLet `z (mkConst ``Nat) (mkNatLit 2) (mkBVar 0) then hits := hits.push "zeta"
  if let `(expr/structural +proj| Nat.zero) := e then hits := hits.push "proj"
  if let `(expr/structural +eta| Nat.succ) := e then hits := hits.push "eta"
  return hits

#guard_msgs in
#eval show MetaM Unit from do
  let abbrevTarget := mkApp (mkConst ``myAbbrevId) (mkConst ``Nat.zero)
  let h1 ← testRelations abbrevTarget
  check (h1.contains "structural_abbrev:false") "structural_abbrev check failed"
  check (h1.contains "reducible_0") "reducible_0 failed"
  check (!h1.contains "reducible_minus_item") "reducible_minus_item failed"
  check (!h1.contains "structural_plus_item") "structural_plus_item failed"

  let defTarget := mkApp (mkConst ``myDefId) (mkConst ``Nat.zero)
  let h2 ← testRelations defTarget
  check (h2.contains "structural_def") "structural_def failed"
  check (!h2.contains "reducible_0") "reducible unfolded myDefId"
  check (h2.contains "defeq_def_0") "defeq_def_0 failed"
  check (h2.contains "structural_plus_item") "structural_plus_item failed"

  let simpTarget := mkApp (mkConst ``mySimpId) (mkConst ``Nat.zero)
  check ((← testRelations simpTarget).contains "simp_set_0") "simp_set_0 failed"

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  let betaTarget := mkApp
    (mkLambda `z .default natTy (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkConst ``Nat.zero)))
    (mkNatLit 2)
  check ((← testRelations betaTarget).contains "beta") "+beta failed"

  let zetaTarget :=
    mkLet `z natTy (mkNatLit 2) (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkConst ``Nat.zero))
  check ((← testRelations zetaTarget).contains "zeta") "+zeta failed"

  let zeroPair := mkApp4 (mkConst ``Prod.mk [0, 0]) natTy natTy
    (mkConst ``Nat.zero) (mkConst ``Nat.zero)
  let projTarget := mkProj ``Prod 0 zeroPair
  check ((← testRelations projTarget).contains "proj") "+proj failed"

  let etaTarget := mkLambda `z .default natTy (mkApp (mkConst ``Nat.succ) (mkBVar 0))
  check ((← testRelations etaTarget).contains "eta") "+eta failed"

end RelationsAndItems

section BlockedZetaInDefeq

def testBlockedFlagInDefeq (e : Expr) : MetaM Bool :=
  match e with
  | `(expr/defeq -zeta| Nat.add 2 1) => return true
  | _ => return false

#guard_msgs in
#eval show MetaM Unit from do
  let zetaTargetLits := mkLet `z (mkConst ``Nat) (mkNatLit 2)
    (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkNatLit 1))
  check (!(← testBlockedFlagInDefeq zetaTargetLits)) "-zeta unexpectedly unfolded let"

end BlockedZetaInDefeq

section LocalLetPinItem

def testLocalLetPinItem : MetaM Bool := do
  withLocalDeclD `z (mkConst ``Nat) fun z =>
    withLetDecl `v (mkConst ``Nat) (mkConst ``Nat.zero) fun v =>
      withLetDecl `w (mkConst ``Nat) (mkConst ``Nat.zero) fun w => do
        let targetV := mkNatAdd z v
        let targetW := mkNatAdd z w
        let structuralDefaultBlocked ← match targetV with
          | `(expr/structural| $z + Nat.zero) => pure true
          | _ => pure false
        let structuralPlusV ← match targetV with
          | `(expr/structural[+$v]| $z + Nat.zero) => pure true
          | _ => pure false
        let structuralUnsignedV ← match targetV with
          | `(expr/structural[$v]| $z + Nat.zero) => pure true
          | _ => pure false
        let structuralPlusVLeavesWBlocked ← match targetW with
          | `(expr/structural[+$v]| $z + Nat.zero) => pure true
          | _ => pure false
        let defeqDefaultUnfolds ← match targetV with
          | `(expr/defeq| $z + Nat.zero) => pure true
          | _ => pure false
        let defeqMinusVBlocked ← match targetV with
          | `(expr/defeq[-$v]| $z + Nat.zero) => pure true
          | _ => pure false
        return !structuralDefaultBlocked && structuralPlusV && structuralUnsignedV &&
          !structuralPlusVLeavesWBlocked && defeqDefaultUnfolds && !defeqMinusVBlocked

#guard_msgs in
#eval show MetaM Unit from do
  check (← testLocalLetPinItem) "local let item overrides failed"

end LocalLetPinItem

/-! ## 3. Nested, multi-discriminant, `as`-pattern, or-pattern, cross-pattern pins -/

section NestedAsAndOrPatterns

inductive Wrap where
  | pair (a b : Expr)
  | single (e : Expr)
  | none

def matchNested (w : Option (Wrap × List Expr)) : MetaM String :=
  match w with
  | some (.pair `(expr| ?a + ?b) `(expr| $a * ?c), [`(expr| $b + $c)]) =>
    return s!"matched1:{a.dbgToString != ""}:{c.dbgToString != ""}"
  | some (.single e@`(expr| ?a + ?b), _) =>
    return s!"as:{e.isApp}:{a.isFVar}:{b.isFVar}"
  | some (.pair `(expr| ?x + 0) `(expr| ?y), [])
  | some (.pair `(expr| 0 + ?x) `(expr| ?y), []) =>
    return s!"or:{x.dbgToString != ""}:{y.dbgToString != ""}"
  | _ => return "miss"

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  let e1 := mkNatAdd x y
  let eMul := mkNatMul x (mkNatLit 3)
  let eTail := mkNatAdd y (mkNatLit 3)
  check ((← matchNested (some (.pair e1 eMul, [eTail]))) == "matched1:true:true")
    "matchNested pair failed"
  check ((← matchNested (some (.single e1, []))) == "as:true:true:true")
    "matchNested as-pattern failed"
  check ((← matchNested (some (.pair (mkNatAdd (mkNatLit 0) x) y, []))) == "or:true:true")
    "matchNested or-pattern failed"

end NestedAsAndOrPatterns

section CrossPatternPin

def matchPairOrdPin (p : Expr × Expr) : MetaM Bool :=
  match p with
  | (x, `(expr| $x + _)) => return true
  | _ => return false

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  check (← matchPairOrdPin (x, mkNatAdd x y)) "matchPairOrdPin failed"

end CrossPatternPin

section GeneralizeShadow

def matchGeneralizeShadow (a : Nat) (h : a = a) (e : Expr) : MetaM (Nat × Nat) :=
  let _ := h
  match e with
  | `(expr| ?a + _) =>
    let _ := a
    return (1, 0)
  | _ => return (0, a)

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  check ((← matchGeneralizeShadow 42 rfl (mkNatAdd x y)) == (1, 0))
    "matchGeneralizeShadow hit failed"
  check ((← matchGeneralizeShadow 42 rfl (mkNatLit 0)) == (0, 42))
    "matchGeneralizeShadow miss failed"

end GeneralizeShadow

/-! ## 4. Term `if let` & `let ... |`, `do` control flow, `let mut pat`, `backward.do.legacy` -/

section TermIfLet

def termIfLet (e : Expr) : MetaM (Option Expr) :=
  if let `(expr| ?a + ?b) := e then
    let _ := b
    pure (some a)
  else
    pure none

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  check ((← termIfLet (mkNatAdd x y)) == some x) "termIfLet hit failed"
  check (← termIfLet (mkNatLit 0)).isNone "termIfLet miss failed"

end TermIfLet

section TermAndDoLetElse

def termAndDoLetElse (e : Expr) : MetaM Nat := do
  let x ← if let `(expr| ?a + ?b) := e then let _ := b; pure a else pure (mkNatLit 0)
  let `(expr| ?u * ?v) := x | return 99
  let _ := (u, v)
  return 1

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  check ((← termAndDoLetElse (mkNatAdd x y)) == 99) "termAndDoLetElse fallback failed"
  check ((← termAndDoLetElse (mkNatAdd (mkNatMul x y) (mkNatLit 1))) == 1)
    "termAndDoLetElse hit failed"

end TermAndDoLetElse

section DoControlFlow

def doControlFlowTest (xs : List Expr) : MetaM (Nat × List Expr) := do
  let mut sum := 0
  let mut out : List Expr := []
  for x in xs do
    if let `(expr| 0 + ?r) := x then
      sum := sum + 10
      out := r :: out
      continue
    else if let `(expr| ?a + ?b) := x then
      sum := sum + 1
      out := b :: a :: out
    else
      sum := sum + 100
      break
    match x with
    | `(expr| ?p + $p) =>
      sum := sum + 5
      return (sum, out)
    | _ =>
      let `(expr| ?u + _) := x | continue
      out := u :: out
  return (sum, out)

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  let doInputs := [mkNatAdd (mkNatLit 0) x, mkNatAdd x y, mkNatMul (mkNatLit 5) (mkNatLit 6)]
  let (s, outs) ← doControlFlowTest doInputs
  check (s == 111 && outs.length == 4) "doControlFlowTest failed"

end DoControlFlow

section MonadicDiscrInDo

def monadicDiscrInDo (mk : MetaM Expr) : MetaM Nat := do
  match ← mk with
  | `(expr| 1 + 1) => return 10
  | _ => return 20

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  check ((← monadicDiscrInDo (pure (mkNatAdd (mkNatLit 1) (mkNatLit 1)))) == 10)
    "monadicDiscrInDo hit failed"
  check ((← monadicDiscrInDo (pure (mkNatAdd x y))) == 20) "monadicDiscrInDo miss failed"

end MonadicDiscrInDo

section DoLetArrowElse

def doLetArrowElse (mk : MetaM Expr) : MetaM Nat := do
  let `(expr| ?a + ?b) ← mk | return 42
  let _ := (a, b)
  return 7

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  check ((← doLetArrowElse (pure (mkNatAdd x y))) == 7) "doLetArrowElse hit failed"
  check ((← doLetArrowElse (pure (mkNatLit 0))) == 42) "doLetArrowElse fallback failed"

end DoLetArrowElse

section DoLetMutExprBinders

def doLetMutExprBinders (e : Expr) : MetaM Nat := do
  let mut `(expr| ?a + ?b) := e | return 0
  if a == b then
    a := mkNatLit 99
  return if a == mkNatLit 99 then 2 else 1

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  check ((← doLetMutExprBinders (mkNatAdd x x)) == 2) "doLetMutExprBinders equal failed"
  check ((← doLetMutExprBinders (mkNatAdd x y)) == 1) "doLetMutExprBinders distinct failed"

end DoLetMutExprBinders

section DoLetMutTuple

def doLetMutTupleAndLegacy (e : Expr) : MetaM (Option Expr) := do
  let `(expr| ?a + ?b) := e | return none
  let mut k := 1
  if a == b then
    k := k + 1
  return some (if k == 2 then a else b)

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  check ((← doLetMutTupleAndLegacy (mkNatAdd x x)) == some x) "doLetMutTupleAndLegacy failed"

end DoLetMutTuple

section LegacyDo
set_option backward.do.legacy true

def legacyDoPatterns (e : Expr) (mk : MetaM Expr) : MetaM Nat := do
  let `(expr| ?a + ?b) := e | return 100
  let _ := (a, b)
  let `(expr| ?c * _) ← mk | return 200
  let _ := c
  if let `(expr| 0 + ?r) := e then
    let _ := r
    return 1
  else
    match e with
    | `(expr| ?x + $x) => return 2
    | _ => return 3

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  let e1 := mkNatAdd x y
  check ((← legacyDoPatterns e1 (pure (mkNatMul x y))) == 3) "legacyDoPatterns distinct failed"
  check ((← legacyDoPatterns (mkNatAdd x x) (pure (mkNatMul x y))) == 2)
    "legacyDoPatterns equal failed"
  check ((← legacyDoPatterns (mkNatLit 0) (pure e1)) == 100)
    "legacyDoPatterns fallback 1 failed"
  check ((← legacyDoPatterns e1 (pure (mkNatLit 0))) == 200)
    "legacyDoPatterns fallback 2 failed"

/--
error: repeated pattern variable `?x`; use `$x` to pin
-/
#guard_msgs in
def rejectLegacyDoRepeatedLetElse (e : Expr) : MetaM Nat := do
  let mut k := 0
  let `(expr| ?x + ?x) := e | return k
  let _ := x
  return k + 1

end LegacyDo

section TermElabStateAndOption

def matchInTermElabAndStateAndOption (e : Expr) : Lean.Elab.TermElabM (Option Nat) := do
  let act : OptionT (StateT Nat MetaM) Nat := do
    let s ← get
    match e with
    | `(expr| ?a + ?b) =>
      let _ := (a, b)
      set (s + 10)
      return s + 10
    | _ =>
      set (s + 1)
      failure
  let (res?, finalState) ← act.run.run 5
  match res? with
  | some v => return some (v + finalState)
  | none => return some finalState

#guard_msgs in
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  checkTerm ((← matchInTermElabAndStateAndOption (mkNatAdd x y)) == some 30)
    "TermElabM + StateT + OptionT hit failed"
  checkTerm ((← matchInTermElabAndStateAndOption (mkNatLit 0)) == some 6)
    "TermElabM + StateT + OptionT miss failed"

end TermElabStateAndOption

/-! ## 5. Zero code duplication, single discriminant eval, and `exprPatExt` deduplication -/

section CodeDedupAndSingleDiscrEval

@[noinline] def markerA (n : Nat) : Nat := n + 1
@[noinline] def markerB (n : Nat) : Nat := n + 2
@[noinline] def markerCont (n : Nat) : Nat := n + 3
@[noinline] def markerElse (n : Nat) : Nat := n + 4

def dupCheckTerm (e : Option (Expr × Expr)) : MetaM Nat :=
  match e with
  | some (`(expr| ?a + ?b), `(expr| $a * ?c)) =>
    let _ := (b, c); pure (markerA 1)
  | some (`(expr| ?x + ?y), `(expr| ?z + $x)) =>
    let _ := (y, z); pure (markerB 2)
  | _ => pure (markerElse 3)

def dupCheckDo (xs : List Expr) : MetaM Nat := do
  let mut acc := 0
  for e in xs do
    match e with
    | `(expr| ?a + ?b) =>
      let _ := (a, b)
      acc := acc + markerA 1
    | `(expr| ?c * ?d) =>
      let _ := (c, d)
      acc := acc + markerB 2
    | _ =>
      acc := acc + markerElse 3
    acc := acc + markerCont 4
  return acc

-- Identical patterns across branches / or-patterns must reuse one `exprPat` aux constant.
def sharedPatDedup (p : Expr × Nat) : MetaM Nat :=
  match p with
  | (`(expr| Nat.add ?a (Nat.succ ?b)), 0)
  | (`(expr| Nat.add ?a (Nat.succ ?b)), 1) => let _ := (a, b); return 1
  | (`(expr| Nat.add ?x (Nat.succ ?y)), _) => let _ := (x, y); return 2
  | _ => return 3

private def countConstOccs (target : Name) (e : Expr) : Nat :=
  e.foldConsts 0 fun n acc => if n == target then acc + 1 else acc

private def collectDecodePayloads (decodeFn : Name) (e : Expr) : Nat × Array String :=
  go e (0, #[])
where
  go (e : Expr) (st : Nat × Array String) : Nat × Array String :=
    let st := match e with
      | .app (.const fn _) (.lit (.strVal s)) =>
        if fn == decodeFn then
          let (cnt, uniq) := st
          (cnt + 1, if uniq.contains s then uniq else uniq.push s)
        else
          st
      | _ => st
    match e with
    | .app f a         => go a (go f st)
    | .lam _ t b _     => go b (go t st)
    | .forallE _ t b _ => go b (go t st)
    | .letE _ t v b _  => go b (go v (go t st))
    | .mdata _ b       => go b st
    | .proj _ _ b      => go b st
    | _                => st

#guard_msgs in
#eval show MetaM Unit from do
  let env ← getEnv
  for (declName, checks) in [
    (``dupCheckTerm, [(``markerA, 1), (``markerB, 1), (``markerElse, 1)]),
    (``dupCheckDo, [(``markerA, 1), (``markerB, 1), (``markerElse, 1), (``markerCont, 1)])
  ] do
    let some info := env.find? declName
      | throwError "missing declaration {declName}"
    let some val := info.value?
      | throwError "expected value for {declName}"
    for (mName, expected) in checks do
      let cnt := countConstOccs mName val
      check (cnt == expected)
        s!"expected {expected} occurrence(s) of {mName} in {declName}, got {cnt}"

  -- Verify `sharedPatDedup` emits 0 extra `exprPat` aux constants and 1 unique
  -- `ExprPattern.decode` payload across its 3 quotation slots (hoisted via `ExtractClosed`).
  let mut sharedPatConsts : Array Name := #[]
  for (n, _) in env.constants do
    if (``sharedPatDedup).isPrefixOf n && n.toString.contains "exprPat" then
      sharedPatConsts := sharedPatConsts.push n
  check (sharedPatConsts.isEmpty)
    s!"expected 0 extra exprPat constants in sharedPatDedup, got {sharedPatConsts.size}"
  let some sharedVal := (env.find? ``sharedPatDedup).bind (·.value?)
    | throwError "expected value for sharedPatDedup"
  let (patDecodeCalls, patPayloads) := collectDecodePayloads ``ExprPattern.decode sharedVal
  check (patDecodeCalls >= 1 && patPayloads.size == 1)
    s!"expected >=1 decode call and 1 unique payload in sharedPatDedup, \
       got calls={patDecodeCalls} uniq={patPayloads.size}"
  let hasClosedIR := (Array.range 32).any fun i =>
    (Lean.IR.findEnvDecl env (``sharedPatDedup ++ (`_closed).appendIndexAfter i)).isSome
  check hasClosedIR "expected ExtractClosed `_closed_` IR decl for sharedPatDedup"

def testSingleDiscrEval : MetaM Unit := do
  let counter ← IO.mkRef 0
  let mkExpr : MetaM Expr := do
    counter.modify (· + 1)
    return mkNatAdd (mkNatLit 2) (mkNatLit 3)
  let act : MetaM Nat := do
    match ← mkExpr with
    | `(expr| 1 + 1) => return 1
    | `(expr| 2 + 2) => return 2
    | `(expr| 2 + 3) => return 3
    | _ => return 4
  let env ← getEnv
  let (res, _, _) ← act.toIO { fileName := "", fileMap := default } { env }
  let c ← counter.get
  check (res == 3) s!"expected res = 3, got {res}"
  check (c == 1) s!"expected single discriminant evaluation c = 1, got {c}"

#guard_msgs in
#eval show MetaM Unit from testSingleDiscrEval

end CodeDedupAndSingleDiscrEval

/-! ## 6. `match (modulo := rel)` integration checks -/

section MatchModuloSharedAndOverride

def matchModuloSharedAndOverride (e : Expr) : MetaM String :=
  match (modulo := defeq) e with
  | `(expr/structural| myDefId 0) => return "exact_structural"
  | `(expr| myDefId 0) => return "modulo_defeq"
  | _ => return "other"

#guard_msgs in
#eval show MetaM Unit from do
  let defTarget := mkApp (mkConst ``myDefId) (mkConst ``Nat.zero)
  let defLitTarget := mkApp (mkConst ``myDefId) (mkNatLit 0)
  check ((← matchModuloSharedAndOverride defLitTarget) == "exact_structural")
    "modulo structural override failed"
  check ((← matchModuloSharedAndOverride defTarget) == "modulo_defeq")
    "modulo defeq fallback failed"
  check ((← matchModuloSharedAndOverride (mkNatLit 0)) == "modulo_defeq")
    "modulo defeq literal failed"

end MatchModuloSharedAndOverride

section MatchModuloWithItemsAndFlags

def matchModuloWithItemsAndFlags (e : Expr) : MetaM String :=
  match (modulo := structural[+myDefId] +beta) e with
  | `(expr[-myDefId]| myDefId 0) => return "wait"
  | `(expr| myDefId 0) => return "merged"
  | _ => return "other"

#guard_msgs in
#eval show MetaM Unit from do
  check ((← matchModuloWithItemsAndFlags (mkNatLit 0)) == "merged")
    "modulo merged items/flags failed"

end MatchModuloWithItemsAndFlags

section MatchModuloDoAndNested

def matchModuloDoAndNested (mk : MetaM Expr) (n : Nat) : MetaM Nat := do
  match (dependent := false) (modulo := defeq) ← mk with
  | `(expr| myDefId 0) =>
    let p := (n, n + 1)
    match p with
    | (0, k) => return k
    | (a, b) => return a + b
  | _ => return 0

#guard_msgs in
#eval show MetaM Unit from do
  check ((← matchModuloDoAndNested (pure (mkNatLit 0)) 0) == 1)
    "modulo do and nested failed"

end MatchModuloDoAndNested

section MatchModuloMultiDiscr

def matchModuloMultiDiscr (e : Expr) (n : Nat) : MetaM Nat :=
  match (modulo := defeq) e, n with
  | `(expr| myDefId 0), 0 => return 10
  | `(expr| myDefId 0), k => return k + 1
  | _, _ => return 0

#guard_msgs in
#eval show MetaM Unit from do
  check ((← matchModuloMultiDiscr (mkNatLit 0) 0) == 10) "modulo multi-discr 0 failed"
  check ((← matchModuloMultiDiscr (mkNatLit 0) 4) == 5) "modulo multi-discr k failed"

end MatchModuloMultiDiscr

section OrdinaryTupleMatchAfterModulo

def ordinaryTupleMatchAfterModulo (p : Nat × Nat) : Nat :=
  match (p.1, p.2) with
  | (0, b) => b
  | (a, b) => a + b

end OrdinaryTupleMatchAfterModulo

section MatchModuloGeneralizingFalse

def matchModuloGeneralizingFalse (e : Expr) (h : e = e) : MetaM Bool :=
  let _ := h
  match (generalizing := false) (modulo := defeq) e with
  | `(expr| myDefId 0) => return true
  | _ => return false

#guard_msgs in
#eval show Lean.Elab.TermElabM Unit from do
  checkTerm (← matchModuloGeneralizingFalse (mkNatLit 0) rfl)
    "matchModuloGeneralizingFalse failed"

end MatchModuloGeneralizingFalse

section MatchNoSpacePipeWithEngine

def matchNoSpacePipeWithEngine (a b e : Expr) : MetaM Bool :=
  match e with
  | `(expr/defeq|$a + $b) => return true
  | _ => return false

#guard_msgs in
#eval show Lean.Elab.TermElabM Unit from do
  let folded := mkNatAdd (mkApp (mkConst ``myDefId) (mkNatLit 0)) (mkNatLit 1)
  checkTerm (← matchNoSpacePipeWithEngine (mkNatLit 0) (mkNatLit 1) folded)
    "matchNoSpacePipeWithEngine failed"

end MatchNoSpacePipeWithEngine

/-! ## 7. Exhaustiveness, `match.ignoreUnusedAlts` without `sorryAx`, redundancy, diagnostics -/

/-! ### Exhaustiveness and redundancy -/

/--
error: Missing cases:
_
-/
#guard_msgs in
def missingCatchAll (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| ?x) => let _ := x; return 1

/--
error: Missing cases:
(some _)
-/
#guard_msgs in
def missingNestedCatchAll (o : Option Expr) : MetaM Nat :=
  match o with
  | none => return 0
  | some `(expr| ?x) => let _ := x; return 1

/--
error: Redundant alternative: Any expression matching
  `(expr| ?x)
will match one of the preceding alternatives
-/
#guard_msgs in
def redundantAfterWildcard (e : Expr) : MetaM Nat :=
  match e with
  | _ => return 0
  | `(expr| ?x) => let _ := x; return 1

/--
error: Redundant alternative: Any expression matching
  some `(expr| ?x)
will match one of the preceding alternatives
-/
#guard_msgs in
def redundantNestedAfterSome (o : Option Expr) : MetaM Nat :=
  match o with
  | none => return 0
  | some _ => return 1
  | some `(expr| ?x) => let _ := x; return 2

/-! ### `match.ignoreUnusedAlts` without `sorryAx` -/

set_option match.ignoreUnusedAlts true in
def ignoreUnusedNonDepNoSorry (e : Expr) : MetaM Nat :=
  match e with
  | _ => return 0
  | `(expr| ?x) => let _ := x; return 1

/--
info: 'ExprQuotMatchTest.ignoreUnusedNonDepNoSorry' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ignoreUnusedNonDepNoSorry

set_option match.ignoreUnusedAlts true in
def ignoreUnusedDepNoSorry (n : Nat) (e : Expr) : MetaM (Fin (n + 1)) :=
  match h : n, e with
  | k, _ => let _ := h; return ⟨min k n, by omega⟩
  | 0, `(expr| ?x) => let _ := h; let _ := x; return ⟨0, by omega⟩

/--
info: 'ExprQuotMatchTest.ignoreUnusedDepNoSorry' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ignoreUnusedDepNoSorry

/-! ### Equality proof (`h :` / `eq :=`) restrictions -/

/--
error: `h:` equality proof is not supported on a discriminant matched with `expr` quotations
(the `Expr` values may only be related, not equal)
-/
#guard_msgs (whitespace := lax) in
def rejectEqProofOnQuot (e : Expr) : MetaM Nat :=
  match h : e with
  | `(expr| ?a) => let _ := (h, a); return 1
  | _ => return 0

/--
error: `h:` equality proof is not supported on a discriminant matched with `expr` quotations
(the `Expr` values may only be related, not equal)
-/
#guard_msgs (whitespace := lax) in
def rejectEqProofOnNestedQuot (o : Option Expr) : MetaM Nat :=
  match h : o with
  | some `(expr| ?a) => let _ := (h, a); return 1
  | _ => return 0

/--
error: `h:` equality proof is not supported on a discriminant matched with `expr` quotations
(the `Expr` values may only be related, not equal)
-/
#guard_msgs (whitespace := lax) in
def rejectEqProofOnCol1 (n : Nat) (e : Expr) : MetaM Nat :=
  match n, h : e with
  | 0, `(expr| ?a) => let _ := (h, a); return 1
  | _, _ => return 0

section AllowEqProofOnNonQuotCol0

def allowEqProofOnNonQuotCol0 (n : Nat) (e : Expr) : MetaM Nat :=
  match h : n, e with
  | 0, `(expr| ?a) =>
    let _ : n = 0 := h
    let _ := a
    return 1
  | _, _ => return n

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  let e1 := mkNatAdd x y
  check ((← allowEqProofOnNonQuotCol0 0 e1) == 1) "allowEqProofOnNonQuotCol0 0 failed"
  check ((← allowEqProofOnNonQuotCol0 7 e1) == 7) "allowEqProofOnNonQuotCol0 7 failed"

end AllowEqProofOnNonQuotCol0

/--
error: `h:` equality proof is not supported on a discriminant matched with `expr` quotations
(the `Expr` values may only be related, not equal)
-/
#guard_msgs (whitespace := lax) in
def rejectTermLetEq (e : Expr) : MetaM Nat :=
  let (eq := h) `(expr| ?a) := e
  let _ := (h, a)
  return 1

/--
error: `h:` equality proof is not supported on a discriminant matched with `expr` quotations
(the `Expr` values may only be related, not equal)
-/
#guard_msgs (whitespace := lax) in
def rejectDoLetEq (e : Expr) : MetaM Nat := do
  let (eq := h) `(expr| ?a) := e | return 0
  let _ := (h, a)
  return 1

/-! ### Pattern binders, pins, and mutable variable diagnostics -/

/--
error: repeated pattern variable `?x`; use `$x` to pin
-/
#guard_msgs in
def rejectRepeatedBinder (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| ?x + ?x) => let _ := x; return 1
  | _ => return 0

/--
error: repeated pattern variable `?x`; use `$x` to pin
-/
#guard_msgs in
def rejectRepeatedBinderInDoLetElse (e : Expr) : MetaM Nat := do
  let `(expr| ?x + ?x) := e | return 0
  let _ := x
  return 1

/--
error: repeated pattern variable `?x`; use `$x` to pin
-/
#guard_msgs in
def rejectRepeatedBinderInDoIfLet (e : Expr) : MetaM Nat := do
  if let `(expr| ?x + ?x) := e then
    let _ := x
    return 1
  else
    return 0

/-- error: unknown identifier `unknownPin` in `$`-pin (did you mean `?unknownPin`?) -/
#guard_msgs in
def rejectUnknownPin (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| $unknownPin + ?y) => let _ := y; return 1
  | _ => return 0

/-- error: expected `$e` pin; use `_` for a wildcard -/
#guard_msgs in
def rejectWildcardPin (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| $_ + ?y) => let _ := y; return 1
  | _ => return 0

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs in
def rejectMutVarShadowing (e : Expr) : MetaM Nat := do
  let mut x := mkNatLit 1
  if let `(expr| ?x + ?y) := e then
    let _ := y
    return 1
  else
    x := mkNatLit 2
    return 0

section AllowMutVarPin

def allowMutVarPin (e : Expr) : MetaM Bool := do
  let mut x := mkNatLit 1
  if let `(expr| $x + ?y) := e then
    let _ := y
    return true
  else
    x := mkNatLit 2
    return false

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  check (← allowMutVarPin (mkNatAdd (mkNatLit 1) y)) "allowMutVarPin hit failed"
  check (!(← allowMutVarPin (mkNatAdd (mkNatLit 2) y))) "allowMutVarPin miss failed"

end AllowMutVarPin

/-! ### Type, typeclass, monad, engine, and flag diagnostics -/

/--
error: type mismatch
  `(expr| ?x)
has type
  Expr
but is expected to have type
  Nat
-/
#guard_msgs in
def rejectTypeMismatch (n : Nat) : MetaM Nat :=
  match n with
  | `(expr| ?x) => let _ := x; return 1
  | _ => return 0

/--
error: type mismatch
  `(expr| ?x)
has type
  Expr
but is expected to have type
  Nat
-/
#guard_msgs in
def rejectNestedTypeMismatch (o : Option Nat) : MetaM Nat :=
  match o with
  | some `(expr| ?x) => let _ := x; return 1
  | _ => return 0

/--
error: invalid `expr` quotation pattern: quotation occurs in an inaccessible or parameter position
-/
#guard_msgs in
def rejectInaccessibleParam (h : Nat = Nat) : MetaM Nat :=
  match h with
  | @Eq.refl _ `(expr| ?x) => let _ := x; return 1

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.6

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
def rejectInvalidAddTC (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| 1 + "hello") => return 1
  | _ => return 0

/--
error: failed to synthesize instance of type class
  HAdd Bool Nat ?m.8

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
def rejectInvalidTypedBinderTC (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| (?x : Bool) + 1) => let _ := x; return 1
  | _ => return 0

/--
error: expr quotation matching requires a monad lifting `MetaM`, got result type
  Id Nat
-/
#guard_msgs in
def rejectNonMetaMonad (e : Expr) : Id Nat :=
  match e with
  | `(expr| ?a + ?b) => let _ := (a, b); 1
  | _ => 0

/--
error: expr quotation matching requires a monad with `[MonadSym]` (e.g. `SymM` or `GrindTacticM`),
got result type
  MetaM Nat
-/
#guard_msgs (whitespace := lax) in
def rejectUnsupportedSym (e : Expr) : MetaM Nat :=
  match e with
  | `(expr/sym| ?x) => let _ := x; return 1
  | _ => return 0

/--
error: unknown expr quotation engine `bogus`;
expected `structural`, `reducible`, `instances`, `defeq`, or `sym`
-/
#guard_msgs (whitespace := lax) in
def rejectBadEngine (e : Expr) : MetaM Nat :=
  match e with
  | `(expr/bogus| ?x) => let _ := x; return 1
  | _ => return 0

/--
error: unknown expr quotation flag `bogus`; expected `inst`, `beta`, `zeta`, `proj`, or `eta`
-/
#guard_msgs in
def rejectBadFlag (e : Expr) : MetaM Nat :=
  match e with
  | `(expr +bogus| ?x) => let _ := x; return 1
  | _ => return 0

/--
error: type mismatch
  `(expr| 1 + 2)
has type
  MetaM Expr
but is expected to have type
  Expr
-/
#guard_msgs in
def rejectTermBuildingQuot : MetaM Expr :=
  return `(expr| 1 + 2)

/-! ## 8. Dependent `h :`, proof irrelevance, sorts, modulo pins, and HO edge cases -/

section DepHBasic

def depH1 (n : Nat) (h : n = n) (e : Expr) : MetaM (Fin (n + 1)) :=
  match h1 : n, e with
  | 0, `(expr| Nat.zero) =>
    let _ := h; let _ := h1
    return ⟨0, by omega⟩
  | 0, `(expr| Nat.succ _) =>
    let _ := h1
    return ⟨0, by omega⟩
  | _, `(expr| ?a + ?b) =>
    let _ := a; let _ := b; let _ := h1
    return ⟨0, by omega⟩
  | k, _ =>
    let _ := h1
    return ⟨min k n, by omega⟩

#guard_msgs in
#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  let sz := mkApp (mkConst ``Nat.succ) z
  let addZ ← mkAppM ``HAdd.hAdd #[z, z]
  check ((← depH1 0 rfl z).val == 0) "depH1 0 zero failed"
  check ((← depH1 0 rfl sz).val == 0) "depH1 0 succ failed"
  check ((← depH1 1 rfl addZ).val == 0) "depH1 1 add failed"
  check ((← depH1 2 rfl z).val == 2) "depH1 2 zero failed"

end DepHBasic

section DepHAs

def depHAs (n : Nat) (e : Expr) : MetaM (Fin (n + 1)) :=
  match h1 : n, e with
  | x@0, `(expr| ?a) =>
    let _ := x; let _ := a; let _ := h1
    return ⟨0, by omega⟩
  | k, _ =>
    let _ := h1
    return ⟨min k n, by omega⟩

#guard_msgs in
#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  check ((← depHAs 0 z).val == 0) "depHAs 0 failed"
  check ((← depHAs 1 z).val == 1) "depHAs 1 failed"

end DepHAs

section DepVecH

inductive TestVec (α : Type) : Nat → Type where
  | nil  : TestVec α 0
  | cons : α → TestVec α n → TestVec α (n + 1)

def depVecH : {n : Nat} → TestVec Expr n → MetaM Nat
  | _, .nil => return 0
  | n + 1, v@(.cons e _) =>
    match h1 : n + 1, hv : v, e with
    | _ + 1, .cons _ _, `(expr| Nat.zero) =>
      let _ := h1; let _ := hv
      return 1
    | _ + 1, .cons _ _, `(expr| Nat.succ _) =>
      let _ := h1; let _ := hv
      return 2
    | _, _, _ =>
      let _ := h1; let _ := hv
      return 3

#guard_msgs in
#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  let sz := mkApp (mkConst ``Nat.succ) z
  check ((← depVecH (.cons z .nil)) == 1) "depVecH 1 failed"
  check ((← depVecH (.cons sz .nil)) == 2) "depVecH 2 failed"
  check ((← depVecH (.cons (mkApp2 (mkConst ``Nat.add) z z) .nil)) == 3) "depVecH 3 failed"

end DepVecH

section NonDepHFall

def nonDepHFall (n : Nat) (e : Expr) : MetaM Nat :=
  match h1 : n, e with
  | 0, `(expr| Nat.zero) => let _ := h1; return 10
  | 0, `(expr| Nat.succ _) => let _ := h1; return 20
  | k, _ => if k == n then return 30 else return 99

#guard_msgs in
#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  let sz := mkApp (mkConst ``Nat.succ) z
  let addZ ← mkAppM ``HAdd.hAdd #[z, z]
  check ((← nonDepHFall 0 z) == 10) "nonDepHFall 10 failed"
  check ((← nonDepHFall 0 sz) == 20) "nonDepHFall 20 failed"
  check ((← nonDepHFall 0 addZ) == 30) "nonDepHFall 30 failed"

end NonDepHFall

section DepTwoGroupsH

def testDepTwoGroupsH (n : Nat) (h : n = n) (e : Expr) : MetaM (Fin (n + 1)) :=
  match h1 : n, e with
  | 0, `(expr| Nat.zero) =>
    let _ := h; let _ := h1; return ⟨0, by omega⟩
  | _ + 1, `(expr| Nat.succ _) =>
    let _ := h; let _ := h1; return ⟨0, by omega⟩
  | k, _ =>
    let _ := h; let _ := h1; return ⟨min k n, by omega⟩

#guard_msgs in
#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  let sz := mkApp (mkConst ``Nat.succ) z
  let eAdd := mkNatAdd (mkNatLit 1) (mkNatLit 2)
  check ((← testDepTwoGroupsH 0 rfl z).val == 0) "testDepTwoGroupsH 0 failed"
  check ((← testDepTwoGroupsH 1 rfl sz).val == 0) "testDepTwoGroupsH 1 failed"
  check ((← testDepTwoGroupsH 2 rfl eAdd).val == 2) "testDepTwoGroupsH 2 failed"

end DepTwoGroupsH

section GenShadowName

def testGenShadowName (e : Expr) (a : e = e) : MetaM Bool :=
  match e with
  | `(expr| ?a + _) => return a.isApp
  | _ =>
    let _ := a
    return false

#guard_msgs in
#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  let eAdd := mkNatAdd (mkNatLit 1) (mkNatLit 2)
  check (← testGenShadowName eAdd rfl) "testGenShadowName hit failed"
  check (!(← testGenShadowName z rfl)) "testGenShadowName miss failed"

end GenShadowName

section ProofIrrelevance

def checkProofTrueIntro (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| True.intro) => return true
  | _ => return false

def checkProofRefl0 (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| @Eq.refl Nat 0) => return true
  | _ => return false

#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `hTrue (mkConst ``True) fun hTrue =>
  withLocalDeclD `hFalse
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)) fun hFalse =>
  withLocalDeclD `hRefl0
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 0) (mkNatLit 0)) fun hRefl0 => do
  check (← checkProofTrueIntro hTrue) "checkProofTrueIntro true failed"
  check (!(← checkProofTrueIntro hFalse)) "checkProofTrueIntro false unexpectedly matched"
  check (← checkProofRefl0 (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 0)))
    "checkProofRefl0 refl0 failed"
  check (← checkProofRefl0 hRefl0) "checkProofRefl0 hRefl0 failed"
  check (!(← checkProofRefl0 (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1))))
    "checkProofRefl0 refl1 unexpectedly matched"

end ProofIrrelevance

section SortPatterns

def checkSortProp (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| Prop) => return true
  | _ => return false

def checkSortType0 (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| Type) => return true
  | _ => return false

def checkSortTypeU (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| Type _) => return true
  | _ => return false

def checkSortAny (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| Sort _) => return true
  | _ => return false

#guard_msgs in
#eval show MetaM Unit from do
  check (← checkSortProp (mkSort 0)) "Prop check failed"
  check (!(← checkSortProp (mkSort 1))) "Prop matched Sort 1"
  check (!(← checkSortType0 (mkSort 0))) "Type matched Prop"
  check (← checkSortType0 (mkSort 1)) "Type check failed"
  check (!(← checkSortType0 (mkSort 2))) "Type matched Sort 2"
  check (!(← checkSortTypeU (mkSort 0))) "Type _ matched Prop"
  check (← checkSortTypeU (mkSort 1)) "Type _ Sort 1 failed"
  check (← checkSortTypeU (mkSort 2)) "Type _ Sort 2 failed"
  check (← checkSortAny (mkSort 0)) "Sort _ Sort 0 failed"
  check (← checkSortAny (mkSort 2)) "Sort _ Sort 2 failed"

end SortPatterns

section StructuralBetaNoUnfold

def checkStructBetaZero (e : Expr) : MetaM Bool :=
  match e with
  | `(expr/structural +beta| Nat.zero) => return true
  | _ => return false

def checkStructBetaLit (e : Expr) : MetaM Bool :=
  match e with
  | `(expr/structural +beta| 5) => return true
  | _ => return false

def checkStructBetaSucc (e : Expr) : MetaM Bool :=
  match e with
  | `(expr/structural +beta| Nat.succ) => return true
  | _ => return false

#guard_msgs in
#eval show MetaM Unit from do
  check (!(← checkStructBetaZero (mkNatLit 0))) "structural +beta unfolded OfNat"
  check (!(← checkStructBetaLit (mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 3))))
    "structural +beta unfolded Nat.add"
  check (!(← checkStructBetaSucc
    (mkLambda `x .default (mkConst ``Nat) (mkApp (mkConst ``Nat.succ) (mkBVar 0)))))
    "structural +beta applied eta"

end StructuralBetaNoUnfold

section StructuralZetaWrap

def checkStructZetaWrap (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr/structural +zeta| Nat.add ?y 0) => return some y
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  let tenPlusTwenty := mkApp2 (mkConst ``Nat.add) (mkNatLit 10) (mkNatLit 20)
  let eLet :=
    mkLet `x natTy tenPlusTwenty <|
    mkLet `u natTy (mkNatLit 99) <|
      mkApp2 (mkConst ``Nat.add)
        (mkApp2 (mkConst ``Nat.add) (mkBVar 1) (mkBVar 1))
        (mkNatLit 0)
  let expectedWrapped :=
    mkLet `x natTy tenPlusTwenty <|
      mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkBVar 0)
  let some wrapped ← checkStructZetaWrap eLet
    | throwError "expected zeta wrap"
  check (wrapped == expectedWrapped) "wrapped zeta mismatch"

  withLetDecl `cx natTy tenPlusTwenty fun cx => do
    let some cxRes ← checkStructZetaWrap (mkApp2 (mkConst ``Nat.add) cx (mkNatLit 0))
      | throwError "expected cx"
    check (cxRes == cx) "cx let-fvar should stay bare"

end StructuralZetaWrap

section StructuralZetaHO

def checkStructZetaHO (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr/structural +zeta| fun z => Nat.add (?P z) 0) => return some P
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  let eHO :=
    mkLambda `z .default natTy <|
    mkLet `x natTy (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkNatLit 1)) <|
      mkApp2 (mkConst ``Nat.add)
        (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkBVar 0))
        (mkNatLit 0)
  let expectedHO :=
    mkLambda `z .default natTy <|
    mkLet `x natTy (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkNatLit 1)) <|
      mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkBVar 0)
  let some hoWrapped ← checkStructZetaHO eHO
    | throwError "expected HO zeta wrap"
  check (hoWrapped == expectedHO) "HO wrapped zeta mismatch"

end StructuralZetaHO

section DefeqNoProjAndStructInst

def checkDefeqNoProj (e : Expr) : MetaM Bool :=
  match e with
  | `(expr/defeq -proj| Nat.zero) => return true
  | _ => return false

def checkStructInst (e : Expr) : MetaM Bool :=
  match e with
  | `(expr/structural +inst| @toString Nat _ ?x) =>
    let _ := x
    return true
  | _ => return false

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  let z := mkConst ``Nat.zero
  let projZero := mkProj ``Prod 0 (mkApp4 (mkConst ``Prod.mk [0, 0]) natTy natTy z z)
  check (!(← checkDefeqNoProj projZero)) "defeq -proj unexpectedly reduced proj"
  let instExpr ← mkAppM ``toString #[mkNatLit 7]
  check (← checkStructInst instExpr) "structural +inst toString failed"

end DefeqNoProjAndStructInst

section ModuloLocalPinNoCapture

def checkModuloNoCapture (v : Expr) (p : Expr × Expr) : MetaM Nat :=
  match (modulo := structural[+$v]) p with
  | (v, `(expr| Nat.add Nat.zero 0)) =>
    if v == mkConst ``Nat.succ then return 1 else return 2
  | _ => return 0

def testDoModPin (v : Expr) (xs : List (Expr × Expr)) : MetaM Nat := do
  let mut acc := 0
  for p in xs do
    match (modulo := structural[+$v]) p with
    | (v, `(expr| Nat.add Nat.zero 0)) =>
      if v == mkConst ``Nat.succ then
        acc := acc + 10
        continue
      else
        return 999
    | _ =>
      acc := acc + 1
  return acc

#guard_msgs in
#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  withLetDecl `v (mkConst ``Nat) z fun v => do
    let target := mkApp2 (mkConst ``Nat.add) v (mkNatLit 0)
    check ((← checkModuloNoCapture v (mkConst ``Nat.succ, target)) == 1)
      "checkModuloNoCapture failed"
    check ((← testDoModPin v [(mkConst ``Nat.succ, target), (z, z)]) == 11)
      "testDoModPin failed"

end ModuloLocalPinNoCapture

section MotiveBeforeModulo

def checkMotiveBeforeModulo (n : Nat) (e : Expr) : MetaM (Fin (n + 1)) :=
  match (motive := (k : Nat) → Expr → MetaM (Fin (k + 1))) (modulo := structural +beta) n, e with
  | 0, `(expr| (fun x => x) Nat.zero) => return ⟨0, by omega⟩
  | _, _ => return ⟨0, by omega⟩

#guard_msgs in
#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  let motiveBeta := mkApp (mkLambda `x .default (mkConst ``Expr) (mkBVar 0)) z
  check ((← checkMotiveBeforeModulo 0 motiveBeta).val == 0)
    "checkMotiveBeforeModulo failed"

end MotiveBeforeModulo

section ModuloOrAlt

def testModuloOrAlt (e : Expr) : MetaM (Option Expr) :=
  match (modulo := defeq) e with
  | `(expr| (?a, myDefId 0))
  | `(expr| (myDefId 0, ?a)) => return some a
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let idZero := mkApp (mkConst ``myDefId) (mkNatLit 0)
  check ((← testModuloOrAlt (← mkAppM ``Prod.mk #[mkNatLit 7, idZero])) == some (mkNatLit 7))
    "testModuloOrAlt 7 failed"
  check ((← testModuloOrAlt (← mkAppM ``Prod.mk #[idZero, mkNatLit 8])) == some (mkNatLit 8))
    "testModuloOrAlt 8 failed"

end ModuloOrAlt

section DoDepModulo

def testDoDepModulo (n : Nat) (e : Expr) : MetaM (Fin (n + 1)) := do
  match (dependent := true) (modulo := defeq) n, e with
  | 0, `(expr| myDefId 0) => return ⟨0, by omega⟩
  | k, _ => return ⟨k, by omega⟩

#guard_msgs in
#eval show MetaM Unit from do
  let idZero := mkApp (mkConst ``myDefId) (mkNatLit 0)
  check ((← testDoDepModulo 0 idZero).val == 0) "testDoDepModulo failed"

end DoDepModulo

section CacheIsolation

def testCacheIsolation (e v : Expr) : MetaM (Bool × Bool × Bool × Bool) := do
  let c1 ← match e with | `(expr/reducible| Nat.zero) => pure true | _ => pure false
  let c2 ← match e with | `(expr/reducible[+myDefId]| Nat.zero) => pure true | _ => pure false
  let l1 ← match v with | `(expr/defeq -zeta| Nat.zero) => pure true | _ => pure false
  let l2 ← match v with | `(expr/defeq[+$v] -zeta| Nat.zero) => pure true | _ => pure false
  return (c1, c2, l1, l2)

#guard_msgs in
#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  withLetDecl `v (mkConst ``Nat) z fun v => do
    check ((← testCacheIsolation (mkApp (mkConst ``myDefId) z) v) == (false, true, false, true))
      "testCacheIsolation failed"

end CacheIsolation

section TacticMLift

example (e : Expr) (_h : e = mkConst ``Nat.zero) : True := by
  have _checkTacticM : Lean.Elab.Tactic.TacticM Bool := do
    match e with
    | `(expr| Nat.zero) => return true
    | _ => return false
  trivial

end TacticMLift

section ModuloInvalidOptionErrors

/--
error: unknown expr quotation engine `bogus`;
expected `structural`, `reducible`, `instances`, `defeq`, or `sym`
-/
#guard_msgs (whitespace := lax) in
def rejectBadModNoQuot (e : Expr) : Nat :=
  match (modulo := bogus) e with
  | _ => 0

/--
error: unknown expr quotation flag `badflag`; expected `inst`, `beta`, `zeta`, `proj`, or `eta`
-/
#guard_msgs in
def rejectBadModFlagNoQuot (e : Expr) : MetaM Nat := do
  match (modulo := +badflag) e with
  | _ => return 0

/--
error: expr quotation matching requires a monad lifting `MetaM`, got result type
  Nat
-/
#guard_msgs (substring := true) in
def rejectPlainNonMonadic (e : Expr) : Nat :=
  match e with
  | `(expr| ?x) => let _ := x; 1
  | _ => 0

end ModuloInvalidOptionErrors

section TopAsH

def testTopAsH (e : Expr) : MetaM (Option (Expr × Expr)) :=
  match e with
  | x@h:`(expr| ?a + ?b) =>
    let _ := h; let _ := b
    return some (x, a)
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let one := mkNatLit 1
  let eAdd := mkNatAdd one (mkNatLit 2)
  check ((← testTopAsH eAdd) == some (eAdd, one)) "testTopAsH failed"

end TopAsH

section ReorderedStructVars

def testReorderedStructVars (p : Expr × Expr) : MetaM Nat :=
  match p with
  | { fst := x, snd := `(expr| $x + 1) } => return 1
  | { snd := `(expr| $y + 2), fst := y } => return 2
  | _ => return 3

#guard_msgs in
#eval show MetaM Unit from do
  let one := mkNatLit 1
  let two := mkNatLit 2
  check ((← testReorderedStructVars (mkNatLit 5, mkNatAdd (mkNatLit 5) one)) == 1)
    "testReorderedStructVars 1 failed"
  check ((← testReorderedStructVars (mkNatLit 5, mkNatAdd (mkNatLit 5) two)) == 2)
    "testReorderedStructVars 2 failed"
  check ((← testReorderedStructVars (mkNatLit 5, mkNatLit 9)) == 3)
    "testReorderedStructVars 3 failed"

end ReorderedStructVars

section MixedHOPinAndFirstOrder

def testMixedHOPinAndFirstOrder (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| (∀ x : Nat, ?P x) ∧ ($P 0)) => return some P
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  withLocalDeclD `P (← mkArrow natTy (mkSort 0)) fun P => do
    let forallPx := mkForall `x .default natTy (mkApp P (mkBVar 0))
    let p0 := mkApp P (mkNatLit 0)
    let conj := mkApp2 (mkConst ``And) forallPx p0
    check ((← testMixedHOPinAndFirstOrder conj) == some P)
      "testMixedHOPinAndFirstOrder failed"

end MixedHOPinAndFirstOrder

section DepHOForall

def testDepHOForall (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| ∀ (α : Type) (x : α), ?P α x) => return some P
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let depBody ← Lean.Elab.Term.TermElabM.run' do
    instantiateMVars (← Lean.Elab.Term.elabTermAndSynthesize
      (← `(fun (α : Type) (x : α) => x = x)) none)
  let some depForall := (
    match depBody with
    | .lam n1 t1 (.lam n2 t2 b bi2) bi1 => some (mkForall n1 bi1 t1 (mkForall n2 bi2 t2 b))
    | _ => none)
    | throwError "expected depBody lam"
  check ((← testDepHOForall depForall) == some depBody) "testDepHOForall failed"

end DepHOForall

section DepHOEq

def testDepHOEq (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| ∀ (α : Type) (x : α), ?P α x = x) => return some P
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let depEqBody ← Lean.Elab.Term.TermElabM.run' do
    instantiateMVars (← Lean.Elab.Term.elabTermAndSynthesize
      (← `(fun (α : Type) (x : α) => x)) none)
  let depEqForall ← Lean.Elab.Term.TermElabM.run' do
    instantiateMVars (← Lean.Elab.Term.elabTermAndSynthesize
      (← `(∀ (α : Type) (x : α), x = x)) none)
  check ((← testDepHOEq depEqForall) == some depEqBody) "testDepHOEq failed"

end DepHOEq

section DepHOPin

def testDepHOPin (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| (∀ (α : Type) (x : α), ?P α x) ∧ (∀ (β : Type) (y : β), $P β y)) => return some P
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let fTy ← Lean.Elab.Term.TermElabM.run' <|
    Lean.Elab.Term.elabTermAndSynthesize (← `((α : Type) → α → Prop)) none
  withLocalDeclD `F fTy fun F => do
    let lhs := mkForall `α .default (mkSort 1)
      (mkForall `x .default (mkBVar 0) (mkApp2 F (mkBVar 1) (mkBVar 0)))
    let rhs := mkForall `β .default (mkSort 1)
      (mkForall `y .default (mkBVar 0) (mkApp2 F (mkBVar 1) (mkBVar 0)))
    check ((← testDepHOPin (mkApp2 (mkConst ``And) lhs rhs)) == some F) "testDepHOPin failed"

end DepHOPin

section DepHOFinAndMissingArg

def testDepHOFin (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| ∀ (n : Nat) (v : Fin n), ?P n v) => return some P
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let finForall ← Lean.Elab.Term.TermElabM.run' do
    instantiateMVars (← Lean.Elab.Term.elabTermAndSynthesize
      (← `(∀ (n : Nat) (v : Fin n), v.val < n)) none)
  check (← testDepHOFin finForall).isSome "testDepHOFin failed"

/-- error: pattern hole cannot depend on bound variables not passed as arguments -/
#guard_msgs in
def rejectDepHOMissingArg (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| ∀ (α : Type) (x : α), ?P x) => return some P
  | _ => return none

end DepHOFinAndMissingArg

section LetHONested

def testLetHONested (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| fun (x : Nat) => let y := x + 1; ?P y) => return some P
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  let one := mkNatLit 1
  let two := mkNatLit 2
  let eLetNested :=
    mkLambda `x .default natTy
      (mkLet `y natTy (mkNatAdd (mkBVar 0) one) (mkNatAdd (mkBVar 0) two))
  check ((← testLetHONested eLetNested) ==
    some (mkLambda `y .default natTy (mkNatAdd (mkBVar 0) two))) "testLetHONested failed"

end LetHONested

section LetHOFlat

def testLetHOFlat (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| let y := 1; ?P y) => return some P
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  let one := mkNatLit 1
  let two := mkNatLit 2
  let eLetFlat := mkLet `y natTy one (mkNatAdd (mkBVar 0) two)
  check ((← testLetHOFlat eLetFlat) ==
    some (mkLambda `y .default natTy (mkNatAdd (mkBVar 0) two))) "testLetHOFlat failed"
  let eLetUnused := mkLet `y natTy one (mkNatLit 42)
  check ((← testLetHOFlat eLetUnused) ==
    some (mkLambda `y .default natTy (mkNatLit 42))) "testLetHOFlat unused failed"

end LetHOFlat

section TwoHOBetaEta

def testTwoHOBetaEta (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr/structural +beta +eta| (∀ x : Nat, ?P x) ∧ (∀ y : Nat, $P y)) => return some P
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let natTy := mkConst ``Nat
  withLocalDeclD `P (← mkArrow natTy (mkSort 0)) fun P => do
    let e2 := mkApp2 (mkConst ``And)
      (mkForall `x .default natTy (mkApp P (mkBVar 0)))
      (mkForall `y .default natTy
        (mkApp (mkLambda `z .default natTy (mkApp P (mkBVar 0))) (mkBVar 0)))
    check ((← testTwoHOBetaEta e2) == some P) "testTwoHOBetaEta failed"

end TwoHOBetaEta

section SelfPinLinterClean

def testSelfPinLinterClean (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| ?p + $p) => return true
  | _ => return false

#guard_msgs in
#eval show MetaM Unit from do
  let one := mkNatLit 1
  let eAdd := mkNatAdd one (mkNatLit 2)
  check (← testSelfPinLinterClean (mkNatAdd one one)) "testSelfPinLinterClean hit failed"
  check (!(← testSelfPinLinterClean eAdd)) "testSelfPinLinterClean miss failed"

end SelfPinLinterClean

section BoundedHOEta

def testBoundedHOLamStructural (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| fun (x : Nat) => ?P x) => return some P
  | _ => return none

def testBoundedHOLamEta (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr/structural +eta| fun (x : Nat) => ?P x) => return some P
  | _ => return none

def testBoundedHOLetStructural (e : Expr) : MetaM (Option (Expr × Expr)) :=
  match e with
  | `(expr| let y : Nat := ?v; ?P y) => return some (v, P)
  | _ => return none

#guard_msgs in
#eval show MetaM Unit from do
  let eLam ← `(expr| fun (x y : Nat) => x + y)
  let some pStruct ← testBoundedHOLamStructural eLam
    | throwError "testBoundedHOLamStructural did not match"
  check (pStruct == eLam) "testBoundedHOLamStructural collapsed inner lambda"
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let expectedBody ← `(expr| fun (y : Nat) => $x + y)
    check (pStruct.beta #[x] == expectedBody) "testBoundedHOLamStructural beta mismatch"
  let some pEta ← testBoundedHOLamEta eLam
    | throwError "testBoundedHOLamEta did not match"
  let expectedHAdd ← `(expr| (HAdd.hAdd : Nat → Nat → Nat))
  check (pEta == expectedHAdd) "testBoundedHOLamEta did not eta-reduce to HAdd.hAdd"
  let eLet ← `(expr| let y : Nat := 1; fun z : Nat => y + z)
  let some (v, pLet) ← testBoundedHOLetStructural eLet
    | throwError "testBoundedHOLetStructural did not match"
  check (v == (← `(expr| (1 : Nat)))) "testBoundedHOLetStructural value mismatch"
  withLocalDeclD `y (mkConst ``Nat) fun y => do
    let expectedLetBody ← `(expr| fun (z : Nat) => $y + z)
    check (pLet.beta #[y] == expectedLetBody) "testBoundedHOLetStructural beta mismatch"

end BoundedHOEta

end ExprQuotMatchTest
