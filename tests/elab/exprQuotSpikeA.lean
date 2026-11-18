import Lean

/-!
Spike A tests for quasi-quoted `Expr` pattern matching (`(expr[rel]| ...)`),
native `match`/`if let`/`let ... |`/`do` integration, `match (modulo := rel)`,
join-point fall-through without code duplication, and error diagnostics.
-/

open Lean Meta

namespace ExprQuotSpikeA

/-! ## 1. Syntax & tokenization coexistence -/

declare_syntax_cat expression
syntax ident : expression

def checkSyntaxQuotCoexist (x : TSyntax `term) (instVar : Term) : MacroM (Array Syntax) := do
  let a ← `(expr + 1)
  let b ← `(expr + $instVar)
  let c ← `(expr + inst)
  let d ← `(expr1 + 1)
  let e ← `(match $x:term with | `(expr + 1) => 1 | _ => 0)
  pure #[a.raw, b.raw, c.raw, d.raw, e.raw]

def checkExpressionCategoryNoSpace (x : Ident) : MacroM (TSyntax `expression) :=
  `(expression|$x:ident)

def checkExpressionCategorySpace (x : Ident) : MacroM (TSyntax `expression) :=
  `(expression| $x:ident)

def checkLeadingAntiquotNoSpace (a b : Expr) (e : Expr) : MetaM Bool := do
  match e with
  | `(expr|$a + $b) => return true
  | _ => return false

def checkLeadingAntiquotWithSpace (a b : Expr) (e : Expr) : MetaM Bool := do
  match e with
  | `(expr| $a + $b) => return true
  | _ => return false

/-! ## 2. Basic matching, non-linear, HO, wildcards, pins, relations -/

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

def matchHigherOrder (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| fun x => ?P x) => return some P
  | _ => return none

def matchConstBinder (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| fun (_ : Nat) => ?c) => return some c
  | _ => return none

abbrev myAbbrevId (n : Nat) : Nat := n
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
  if let `(expr/reducible[-myAbbrevId]| Nat.zero) := e then hits := hits.push "reducible_minus_item"
  if let `(expr/structural[+simp]| Nat.zero) := e then hits := hits.push "simp_set_0"
  if let `(expr/structural +beta| Nat.add ?a Nat.zero) := e then
    if a == mkNatLit 2 then hits := hits.push "beta"
  if let `(expr/structural +zeta| Nat.add ?a Nat.zero) := e then
    if a == mkLet `z (mkConst ``Nat) (mkNatLit 2) (mkBVar 0) then hits := hits.push "zeta"
  if let `(expr/structural +proj| Nat.zero) := e then hits := hits.push "proj"
  if let `(expr/structural +eta| Nat.succ) := e then hits := hits.push "eta"
  return hits

def testBlockedFlagInDefeq (e : Expr) : MetaM Bool :=
  match e with
  | `(expr/defeq -zeta| Nat.add 2 1) => return true
  | _ => return false

def testLocalLetPinItem (x : Expr) : MetaM Bool := do
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
        let structuralPlusVLeavesWBlocked ← match targetW with
          | `(expr/structural[+$v]| $z + Nat.zero) => pure true
          | _ => pure false
        let defeqDefaultUnfolds ← match targetV with
          | `(expr/defeq| $z + Nat.zero) => pure true
          | _ => pure false
        let defeqMinusVBlocked ← match targetV with
          | `(expr/defeq[-$v]| $z + Nat.zero) => pure true
          | _ => pure false
        let _ := x
        return !structuralDefaultBlocked && structuralPlusV &&
          !structuralPlusVLeavesWBlocked && defeqDefaultUnfolds && !defeqMinusVBlocked

/-! ## 3. Nested, multi-discriminant, as-pattern, or-pattern, cross-pattern pins -/

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

def matchPairOrdPin (p : Expr × Expr) : MetaM Bool :=
  match p with
  | (x, `(expr| $x + _)) => return true
  | _ => return false

def matchGeneralizeShadow (a : Nat) (h : a = a) (e : Expr) : MetaM (Nat × Nat) :=
  let _ := h
  match e with
  | `(expr| ?a + _) =>
    let _ := a
    return (1, 0)
  | _ => return (0, a)

/-! ## 4. Term `if let` & `let ... | fallback`, plus `do` integration & control flow -/

def termIfLet (e : Expr) : MetaM (Option Expr) :=
  if let `(expr| ?a + ?b) := e then
    let _ := b
    pure (some a)
  else
    pure none

def termAndDoLetElse (e : Expr) : MetaM Nat := do
  let x ← if let `(expr| ?a + ?b) := e then let _ := b; pure a else pure (mkNatLit 0)
  let `(expr| ?u * ?v) := x | return 99
  let _ := (u, v)
  return 1

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

def monadicDiscrInDo (mk : MetaM Expr) : MetaM Nat := do
  match ← mk with
  | `(expr| 1 + 1) => return 10
  | _ => return 20

def doLetArrowElse (mk : MetaM Expr) : MetaM Nat := do
  let `(expr| ?a + ?b) ← mk | return 42
  let _ := (a, b)
  return 7

def doLetMutBinders (e : Expr) : MetaM Nat := do
  let `(expr| ?a + ?b) := e | return 0
  let mut k := 1
  if a == b then
    k := k + 1
  return k

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

/-! ## 5. Zero code duplication & single discriminant evaluation verification -/

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

private def countConstOccs (target : Name) (e : Expr) : Nat :=
  e.foldConsts 0 fun n acc => if n == target then acc + 1 else acc

#eval show MetaM Unit from do
  let env ← getEnv
  for (declName, checks) in [
    (``dupCheckTerm, [(``markerA, 1), (``markerB, 1), (``markerElse, 1)]),
    (``dupCheckDo, [(``markerA, 1), (``markerB, 1), (``markerElse, 1), (``markerCont, 1)])
  ] do
    let info := env.find? declName |>.get!
    let val := info.value!
    for (mName, expected) in checks do
      let cnt := countConstOccs mName val
      if cnt != expected then
        throwError "expected {expected} occurrence(s) of {mName} in {declName}, got {cnt}"

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
  assert! res == 3
  assert! c == 1

#eval testSingleDiscrEval

/-! ## 6. `match (modulo := rel)` integration checks -/

def matchModuloSharedAndOverride (e : Expr) : MetaM String :=
  match (modulo := defeq) e with
  | `(expr/structural| myDefId 0) => return "exact_structural"
  | `(expr| myDefId 0) => return "modulo_defeq"
  | _ => return "other"

def matchModuloWithItemsAndFlags (e : Expr) : MetaM String :=
  match (modulo := structural[+myDefId] +beta) e with
  | `(expr[-myDefId]| myDefId 0) => return "wait"
  | `(expr| myDefId 0) => return "merged"
  | _ => return "other"

def matchModuloDoAndNested (mk : MetaM Expr) (n : Nat) : MetaM Nat := do
  match (dependent := false) (modulo := defeq) ← mk with
  | `(expr| myDefId 0) =>
    -- Nested ordinary match in RHS must remain completely untouched
    let p := (n, n + 1)
    match p with
    | (0, k) => return k
    | (a, b) => return a + b
  | _ => return 0

def matchModuloMultiDiscr (e : Expr) (n : Nat) : MetaM Nat :=
  match (modulo := defeq) e, n with
  | `(expr| myDefId 0), 0 => return 10
  | `(expr| myDefId 0), k => return k + 1
  | _, _ => return 0

def ordinaryTupleMatchAfterModulo (p : Nat × Nat) : Nat :=
  match (p.1, p.2) with
  | (0, b) => b
  | (a, b) => a + b

/-! ## 7. Runtime tests for positive semantic checks -/

#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  let e1 := mkNatAdd x y
  assert! (← checkLeadingAntiquotNoSpace x y e1)
  assert! (← checkLeadingAntiquotWithSpace x y e1)
  assert! !(← checkLeadingAntiquotNoSpace y x e1)
  assert! (← matchAddSplit e1).isSome
  assert! (← matchSameAdd (mkNatAdd x x)).isSome
  assert! (← matchSameAdd e1).isNone
  assert! (← matchWithWildcards (mkNatAdd (mkNatAdd x y) (mkNatLit 1))).isSome

  -- Higher-order pattern checks
  let natTy := mkConst ``Nat
  let lamApp := mkLambda `x .default natTy (mkNatAdd (mkBVar 0) (mkNatLit 1))
  let ho? ← matchHigherOrder lamApp
  assert! ho?.isSome
  assert! (← matchConstBinder lamApp).isNone
  let constLam := mkLambda `x .default natTy (mkNatLit 5)
  assert! (← matchConstBinder constLam) == some (mkNatLit 5)

  -- Relation tests
  let abbrevTarget := mkApp (mkConst ``myAbbrevId) (mkConst ``Nat.zero)
  let h1 ← testRelations abbrevTarget
  assert! h1.contains "structural_abbrev:false"
  assert! h1.contains "reducible_0"
  assert! !h1.contains "reducible_minus_item"
  assert! !h1.contains "structural_plus_item"

  let defTarget := mkApp (mkConst ``myDefId) (mkConst ``Nat.zero)
  let h2 ← testRelations defTarget
  assert! h2.contains "structural_def"
  assert! !h2.contains "reducible_0"
  assert! h2.contains "defeq_def_0"
  assert! h2.contains "structural_plus_item"

  let simpTarget := mkApp (mkConst ``mySimpId) (mkConst ``Nat.zero)
  assert! (← testRelations simpTarget).contains "simp_set_0"

  let betaTarget := mkApp (mkLambda `z .default natTy (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkConst ``Nat.zero))) (mkNatLit 2)
  assert! (← testRelations betaTarget).contains "beta"

  let zetaTarget := mkLet `z natTy (mkNatLit 2) (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkConst ``Nat.zero))
  assert! (← testRelations zetaTarget).contains "zeta"
  let zetaTargetLits := mkLet `z natTy (mkNatLit 2) (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkNatLit 1))
  assert! !(← testBlockedFlagInDefeq zetaTargetLits)

  let projTarget := mkProj ``Prod 0 (mkApp4 (mkConst ``Prod.mk [0, 0]) natTy natTy (mkConst ``Nat.zero) (mkConst ``Nat.zero))
  assert! (← testRelations projTarget).contains "proj"

  let etaTarget := mkLambda `z .default natTy (mkApp (mkConst ``Nat.succ) (mkBVar 0))
  assert! (← testRelations etaTarget).contains "eta"

  assert! (← testLocalLetPinItem x)

  -- Nested + cross-pattern pins + or-pattern + as-pattern
  let eMul := mkNatMul x (mkNatLit 3)
  let eTail := mkNatAdd y (mkNatLit 3)
  assert! (← matchNested (some (.pair e1 eMul, [eTail]))) == "matched1:true:true"
  assert! (← matchNested (some (.single e1, []))) == "as:true:true:true"
  assert! (← matchNested (some (.pair (mkNatAdd (mkNatLit 0) x) y, []))) == "or:true:true"
  assert! (← matchPairOrdPin (x, e1))

  -- Control flow
  let (s, outs) ← doControlFlowTest [mkNatAdd (mkNatLit 0) x, e1, mkNatMul (mkNatLit 5) (mkNatLit 6)]
  assert! s == 111
  assert! outs.length == 4

  -- match (modulo := ...)
#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  let e1 := mkNatAdd x y
  let defTarget := mkApp (mkConst ``myDefId) (mkConst ``Nat.zero)
  let defLitTarget := mkApp (mkConst ``myDefId) (mkNatLit 0)
  assert! (← matchModuloSharedAndOverride defLitTarget) == "exact_structural"
  assert! (← matchModuloSharedAndOverride defTarget) == "modulo_defeq"
  assert! (← matchModuloSharedAndOverride (mkNatLit 0)) == "modulo_defeq"
  assert! (← matchModuloWithItemsAndFlags (mkNatLit 0)) == "merged"
  assert! (← matchModuloDoAndNested (pure (mkNatLit 0)) 0) == 1
  assert! (← matchModuloMultiDiscr (mkNatLit 0) 0) == 10
  assert! (← matchModuloMultiDiscr (mkNatLit 0) 4) == 5

  -- Additional API runtime checks
  assert! (← termIfLet e1) == some x
  assert! (← termIfLet (mkNatLit 0)).isNone
  assert! (← termAndDoLetElse e1) == 99
  assert! (← termAndDoLetElse (mkNatAdd (mkNatMul x y) (mkNatLit 1))) == 1
  assert! (← monadicDiscrInDo (pure (mkNatAdd (mkNatLit 1) (mkNatLit 1)))) == 10
  assert! (← monadicDiscrInDo (pure e1)) == 20
  assert! (← doLetArrowElse (pure e1)) == 7
  assert! (← doLetArrowElse (pure (mkNatLit 0))) == 42
  assert! (← doLetMutBinders (mkNatAdd x x)) == 2
  assert! (← doLetMutBinders e1) == 1
  assert! (← matchGeneralizeShadow 42 rfl e1) == (1, 0)
  assert! (← matchGeneralizeShadow 42 rfl (mkNatLit 0)) == (0, 42)

def matchModuloGeneralizingFalse (e : Expr) (h : e = e) : MetaM Bool :=
  let _ := h
  match (generalizing := false) (modulo := defeq) e with
  | `(expr| myDefId 0) => return true
  | _ => return false

def matchNoSpacePipeWithEngine (a b e : Expr) : MetaM Bool :=
  match e with
  | `(expr/defeq|$a + $b) => return true
  | _ => return false

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  let e1 := mkNatAdd x y
  assert! (← matchInTermElabAndStateAndOption e1) == some 30
  assert! (← matchInTermElabAndStateAndOption (mkNatLit 0)) == some 6
  assert! (← matchModuloGeneralizingFalse (mkNatLit 0) rfl)
  assert! (← matchNoSpacePipeWithEngine (mkNatLit 0) (mkNatLit 1) (mkApp (mkConst ``myDefId) (mkNatLit 0) |> fun z => mkNatAdd z (mkNatLit 1)))
  let co ← Lean.Elab.liftMacroM <| checkSyntaxQuotCoexist (← `(1)) (← `(2))
  assert! co.size == 5
  let ex1 ← Lean.Elab.liftMacroM <| checkExpressionCategoryNoSpace (mkIdent `foo)
  let ex2 ← Lean.Elab.liftMacroM <| checkExpressionCategorySpace (mkIdent `foo)
  assert! ex1.raw == ex2.raw

/-! ## 8. Exhaustiveness, redundancy, `match h :`, and negative tests -/

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
  __eq_1_0✝
will match one of the preceding alternatives
-/
#guard_msgs in
def redundantAfterWildcard (e : Expr) : MetaM Nat :=
  match e with
  | _ => return 0
  | `(expr| ?x) => let _ := x; return 1

/--
error: Redundant alternative: Any expression matching
  some __eq_2_0✝
will match one of the preceding alternatives
-/
#guard_msgs in
def redundantNestedAfterSome (o : Option Expr) : MetaM Nat :=
  match o with
  | none => return 0
  | some _ => return 1
  | some `(expr| ?x) => let _ := x; return 2

/--
error: `h:` equality proof is not supported on a discriminant matched with `expr` quotations (the `Expr` values may only be related, not equal)
-/
#guard_msgs in
def rejectEqProofOnQuot (e : Expr) : MetaM Nat :=
  match h : e with
  | `(expr| ?a) => let _ := (h, a); return 1
  | _ => return 0

/--
error: `h:` equality proof is not supported on a discriminant matched with `expr` quotations (the `Expr` values may only be related, not equal)
-/
#guard_msgs in
def rejectEqProofOnNestedQuot (o : Option Expr) : MetaM Nat :=
  match h : o with
  | some `(expr| ?a) => let _ := (h, a); return 1
  | _ => return 0

/--
error: `h:` equality proof is not supported on a discriminant matched with `expr` quotations (the `Expr` values may only be related, not equal)
-/
#guard_msgs in
def rejectEqProofOnCol1 (n : Nat) (e : Expr) : MetaM Nat :=
  match n, h : e with
  | 0, `(expr| ?a) => let _ := (h, a); return 1
  | _, _ => return 0

def allowEqProofOnNonQuotCol0 (n : Nat) (e : Expr) : MetaM Nat :=
  match h : n, e with
  | 0, `(expr| ?a) =>
    let _ : n = 0 := h
    let _ := a
    return 1
  | _, _ => return n

/--
error: `h:` equality proof is not supported on a discriminant matched with `expr` quotations (the `Expr` values may only be related, not equal)
-/
#guard_msgs in
def rejectTermLetEq (e : Expr) : MetaM Nat :=
  let (eq := h) `(expr| ?a) := e
  let _ := (h, a)
  return 1

/--
error: `h:` equality proof is not supported on a discriminant matched with `expr` quotations (the `Expr` values may only be related, not equal)
-/
#guard_msgs in
def rejectDoLetEq (e : Expr) : MetaM Nat := do
  let (eq := h) `(expr| ?a) := e | return 0
  let _ := (h, a)
  return 1

/--
error: repeated pattern variable `?x`; use `$x` to pin
-/
#guard_msgs in
def rejectRepeatedBinder (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| ?x + ?x) => let _ := x; return 1
  | _ => return 0

/-- error: unknown identifier `unknownPin` in `$`-pin (did you mean `?unknownPin`?) -/
#guard_msgs in
def rejectUnknownPin (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| $unknownPin + ?y) => let _ := y; return 1
  | _ => return 0

/--
error: Type mismatch
  __eq_0_0✝
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
error: expr quotation matching requires a monad lifting `MetaM`, got result type
  Id Nat
failed to synthesize
  MonadLiftT MetaM Id

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def rejectNonMetaMonad (e : Expr) : Id Nat :=
  match e with
  | `(expr| ?a + ?b) => let _ := (a, b); 1
  | _ => 0

def rejectUnsupportedSym (e : Expr) : MetaM Nat :=
  match e with
  | `(expr/sym| ?x) => let _ := x; return 1
  | _ => return 0

/-- error: expr quotation `/sym` matching engine is not implemented yet (Spike B / B5) -/
#guard_msgs in
#eval rejectUnsupportedSym (mkNatLit 0)

/--
error: unknown expr quotation engine `bogus`; expected `structural`, `reducible`, `instances`, `defeq`, or `sym`
-/
#guard_msgs in
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

/-- error: expected `$e` pin; use `_` for a wildcard -/
#guard_msgs in
def rejectWildcardPin (e : Expr) : MetaM Nat :=
  match e with
  | `(expr| $_ + ?y) => let _ := y; return 1
  | _ => return 0

/--
error: expr quotation ``(expr| 1 + 2)` in term (building) position is not implemented yet (B3)
-/
#guard_msgs in
def rejectTermBuildingQuot : MetaM Expr :=
  return `(expr| 1 + 2)

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

def allowMutVarPin (e : Expr) : MetaM Bool := do
  let mut x := mkNatLit 1
  if let `(expr| $x + ?y) := e then
    let _ := y
    return true
  else
    x := mkNatLit 2
    return false

#eval show MetaM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  let e1 := mkNatAdd x y
  assert! (← allowEqProofOnNonQuotCol0 0 e1) == 1
  assert! (← allowEqProofOnNonQuotCol0 7 e1) == 7
  assert! (← allowMutVarPin (mkNatAdd (mkNatLit 1) y))
  assert! !(← allowMutVarPin (mkNatAdd (mkNatLit 2) y))

/-! ## 10. Adversarial regression tests (Spike A review) -/

inductive SpikeAVec (α : Type) : Nat → Type where
  | nil  : SpikeAVec α 0
  | cons : α → SpikeAVec α n → SpikeAVec α (n + 1)

def depH1 (n : Nat) (h : n = n) (e : Expr) : MetaM (Fin (n + 1)) :=
  match h1 : n, e with
  | 0, `(expr| Nat.zero) =>
    let _ := h
    let _ := h1
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

def depHAs (n : Nat) (e : Expr) : MetaM (Fin (n + 1)) :=
  match h1 : n, e with
  | x@0, `(expr| ?a) =>
    let _ := x; let _ := a; let _ := h1
    return ⟨0, by omega⟩
  | k, _ =>
    let _ := h1
    return ⟨min k n, by omega⟩

def depVecH : {n : Nat} → SpikeAVec Expr n → MetaM Nat
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

def nonDepHFall (n : Nat) (e : Expr) : MetaM Nat :=
  match h1 : n, e with
  | 0, `(expr| Nat.zero) => let _ := h1; return 10
  | 0, `(expr| Nat.succ _) => let _ := h1; return 20
  | k, _ => if k == n then return 30 else return 99

def checkProofTrueIntro (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| True.intro) => return true
  | _ => return false

def checkProofRefl0 (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| @Eq.refl Nat 0) => return true
  | _ => return false

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

def checkStructZetaWrap (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr/structural +zeta| Nat.add ?y 0) => return some y
  | _ => return none

def checkStructZetaHO (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr/structural +zeta| fun z => Nat.add (?P z) 0) => return some P
  | _ => return none

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

def checkMotiveBeforeModulo (n : Nat) (e : Expr) : MetaM (Fin (n + 1)) :=
  match (motive := (k : Nat) → Expr → MetaM (Fin (k + 1))) (modulo := structural +beta) n, e with
  | 0, `(expr| (fun x => x) Nat.zero) => return ⟨0, by omega⟩
  | _, _ => return ⟨0, by omega⟩

example (e : Expr) (_h : e = mkConst ``Nat.zero) : True := by
  have _checkTacticM : Lean.Elab.Tactic.TacticM Bool := do
    match e with
    | `(expr| Nat.zero) => return true
    | _ => return false
  trivial

/--
error: unknown expr quotation engine `bogus`; expected `structural`, `reducible`, `instances`, `defeq`, or `sym`
-/
#guard_msgs in
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

#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  let sz := mkApp (mkConst ``Nat.succ) z
  let addZ ← mkAppM ``HAdd.hAdd #[z, z]
  assert! (← depH1 0 rfl z).val == 0
  assert! (← depH1 0 rfl sz).val == 0
  assert! (← depH1 1 rfl addZ).val == 0
  assert! (← depH1 2 rfl z).val == 2
  assert! (← depHAs 0 z).val == 0
  assert! (← depHAs 1 z).val == 1
  assert! (← depVecH (.cons z .nil)) == 1
  assert! (← depVecH (.cons sz .nil)) == 2
  assert! (← depVecH (.cons (mkApp2 (mkConst ``Nat.add) z z) .nil)) == 3
  assert! (← nonDepHFall 0 z) == 10
  assert! (← nonDepHFall 0 sz) == 20
  assert! (← nonDepHFall 0 addZ) == 30

  withLocalDeclD `hTrue (mkConst ``True) fun hTrue =>
  withLocalDeclD `hFalse (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)) fun hFalse =>
  withLocalDeclD `hRefl0 (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 0) (mkNatLit 0)) fun hRefl0 => do
  assert! (← checkProofTrueIntro hTrue)
  assert! !(← checkProofTrueIntro hFalse)
  assert! (← checkProofRefl0 (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 0)))
  assert! (← checkProofRefl0 hRefl0)
  assert! !(← checkProofRefl0 (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1)))

  assert! (← checkSortProp (mkSort 0))
  assert! !(← checkSortProp (mkSort 1))
  assert! !(← checkSortType0 (mkSort 0))
  assert! (← checkSortType0 (mkSort 1))
  assert! !(← checkSortType0 (mkSort 2))
  assert! !(← checkSortTypeU (mkSort 0))
  assert! (← checkSortTypeU (mkSort 1))
  assert! (← checkSortTypeU (mkSort 2))
  assert! (← checkSortAny (mkSort 0))
  assert! (← checkSortAny (mkSort 2))

  assert! !(← checkStructBetaZero (mkNatLit 0))
  assert! !(← checkStructBetaLit (mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 3)))
  assert! !(← checkStructBetaSucc (mkLambda `x .default (mkConst ``Nat) (mkApp (mkConst ``Nat.succ) (mkBVar 0))))

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
  let some wrapped ← checkStructZetaWrap eLet | panic! "expected zeta wrap"
  assert! wrapped == expectedWrapped

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
  let some hoWrapped ← checkStructZetaHO eHO | panic! "expected HO zeta wrap"
  assert! hoWrapped == expectedHO

  withLetDecl `cx natTy tenPlusTwenty fun cx => do
    let some cxRes ← checkStructZetaWrap (mkApp2 (mkConst ``Nat.add) cx (mkNatLit 0)) | panic! "expected cx"
    assert! cxRes == cx

  let projZero := mkProj ``Prod 0 (mkApp4 (mkConst ``Prod.mk [0, 0]) natTy natTy z z)
  assert! !(← checkDefeqNoProj projZero)

  let instExpr ← mkAppM ``toString #[mkNatLit 7]
  assert! (← checkStructInst instExpr)

  withLetDecl `v natTy z fun v => do
    let target := mkApp2 (mkConst ``Nat.add) v (mkNatLit 0)
    assert! (← checkModuloNoCapture v (mkConst ``Nat.succ, target)) == 1
    assert! (← testDoModPin v [(mkConst ``Nat.succ, target), (z, z)]) == 11
  assert! (← checkMotiveBeforeModulo 0 (mkApp (mkLambda `x .default (mkConst ``Expr) (mkBVar 0)) z)).val == 0

def testMixedHOPinAndFirstOrder (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| (∀ x : Nat, ?P x) ∧ ($P 0)) => return some P
  | _ => return none

def testTopAsH (e : Expr) : MetaM (Option (Expr × Expr)) :=
  match e with
  | x@h:`(expr| ?a + ?b) =>
    let _ := h; let _ := b
    return some (x, a)
  | _ => return none

def testReorderedStructVars (p : Expr × Expr) : MetaM Nat :=
  match p with
  | { fst := x, snd := `(expr| $x + 1) } => return 1
  | { snd := `(expr| $y + 2), fst := y } => return 2
  | _ => return 3

def testModuloOrAlt (e : Expr) : MetaM (Option Expr) :=
  match (modulo := defeq) e with
  | `(expr| (?a, myDefId 0))
  | `(expr| (myDefId 0, ?a)) => return some a
  | _ => return none

def testGenShadowName (e : Expr) (a : e = e) : MetaM Bool :=
  match e with
  | `(expr| ?a + _) => return a.isApp
  | _ =>
    let _ := a
    return false

def testDepTwoGroupsH (n : Nat) (h : n = n) (e : Expr) : MetaM (Fin (n + 1)) :=
  match h1 : n, e with
  | 0, `(expr| Nat.zero) =>
    let _ := h; let _ := h1; return ⟨0, by omega⟩
  | _ + 1, `(expr| Nat.succ _) =>
    let _ := h; let _ := h1; return ⟨0, by omega⟩
  | k, _ =>
    let _ := h; let _ := h1; return ⟨min k n, by omega⟩

def testDoDepModulo (n : Nat) (e : Expr) : MetaM (Fin (n + 1)) := do
  match (dependent := true) (modulo := defeq) n, e with
  | 0, `(expr| myDefId 0) => return ⟨0, by omega⟩
  | k, _ => return ⟨k, by omega⟩

def testCacheIsolation (e v : Expr) : MetaM (Bool × Bool × Bool × Bool) := do
  let c1 ← match e with | `(expr/reducible| Nat.zero) => pure true | _ => pure false
  let c2 ← match e with | `(expr/reducible[+myDefId]| Nat.zero) => pure true | _ => pure false
  let l1 ← match v with | `(expr/defeq -zeta| Nat.zero) => pure true | _ => pure false
  let l2 ← match v with | `(expr/defeq[+$v] -zeta| Nat.zero) => pure true | _ => pure false
  return (c1, c2, l1, l2)

/--
error: expr quotation matching requires a monad lifting `MetaM`, got result type
  Nat
-/
#guard_msgs (substring := true) in
def rejectPlainNonMonadic (e : Expr) : Nat :=
  match e with
  | `(expr| ?x) => let _ := x; 1
  | _ => 0

def testDepHOForall (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| ∀ (α : Type) (x : α), ?P α x) => return some P
  | _ => return none

def testDepHOEq (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| ∀ (α : Type) (x : α), ?P α x = x) => return some P
  | _ => return none

def testDepHOPin (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| (∀ (α : Type) (x : α), ?P α x) ∧ (∀ (β : Type) (y : β), $P β y)) => return some P
  | _ => return none

def testDepHOFin (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| ∀ (n : Nat) (v : Fin n), ?P n v) => return some P
  | _ => return none

/-- error: pattern hole cannot depend on bound variables not passed as arguments -/
#guard_msgs in
def rejectDepHOMissingArg (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| ∀ (α : Type) (x : α), ?P x) => return some P
  | _ => return none

def testLetHONested (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| fun (x : Nat) => let y := x + 1; ?P y) => return some P
  | _ => return none

def testLetHOFlat (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr| let y := 1; ?P y) => return some P
  | _ => return none

def testTwoHOBetaEta (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr/structural +beta +eta| (∀ x : Nat, ?P x) ∧ (∀ y : Nat, $P y)) => return some P
  | _ => return none

def testSelfPinLinterClean (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| ?p + $p) => return true
  | _ => return false

#eval show MetaM Unit from do
  let z := mkConst ``Nat.zero
  let sz := mkApp (mkConst ``Nat.succ) z
  let one := mkNatLit 1
  let two := mkNatLit 2
  let eAdd := mkNatAdd one two
  let natTy := mkConst ``Nat
  withLocalDeclD `P (← mkArrow natTy (mkSort 0)) fun P => do
    let forallPx := mkForall `x .default natTy (mkApp P (mkBVar 0))
    let p0 := mkApp P (mkNatLit 0)
    let conj := mkApp2 (mkConst ``And) forallPx p0
    assert! (← testMixedHOPinAndFirstOrder conj) == some P
  assert! (← testTopAsH eAdd) == some (eAdd, one)
  assert! (← testReorderedStructVars (mkNatLit 5, mkNatAdd (mkNatLit 5) one)) == 1
  assert! (← testReorderedStructVars (mkNatLit 5, mkNatAdd (mkNatLit 5) two)) == 2
  assert! (← testReorderedStructVars (mkNatLit 5, mkNatLit 9)) == 3
  let idZero := mkApp (mkConst ``myDefId) (mkNatLit 0)
  assert! (← testModuloOrAlt (← mkAppM ``Prod.mk #[mkNatLit 7, idZero])) == some (mkNatLit 7)
  assert! (← testModuloOrAlt (← mkAppM ``Prod.mk #[idZero, mkNatLit 8])) == some (mkNatLit 8)
  assert! (← testGenShadowName eAdd rfl)
  assert! !(← testGenShadowName z rfl)
  assert! (← testDepTwoGroupsH 0 rfl z).val == 0
  assert! (← testDepTwoGroupsH 1 rfl sz).val == 0
  assert! (← testDepTwoGroupsH 2 rfl eAdd).val == 2
  assert! (← testDoDepModulo 0 idZero).val == 0
  withLetDecl `v natTy z fun v => do
    assert! (← testCacheIsolation (mkApp (mkConst ``myDefId) z) v) == (false, true, false, true)
  let depBody ← Lean.Elab.Term.TermElabM.run' do
    instantiateMVars (← Lean.Elab.Term.elabTermAndSynthesize (← `(fun (α : Type) (x : α) => x = x)) none)
  let depForall := match depBody with
    | .lam n1 t1 (.lam n2 t2 b bi2) bi1 => mkForall n1 bi1 t1 (mkForall n2 bi2 t2 b)
    | _ => unreachable!
  assert! (← testDepHOForall depForall) == some depBody
  let depEqBody ← Lean.Elab.Term.TermElabM.run' do
    instantiateMVars (← Lean.Elab.Term.elabTermAndSynthesize (← `(fun (α : Type) (x : α) => x)) none)
  let depEqForall ← Lean.Elab.Term.TermElabM.run' do
    instantiateMVars (← Lean.Elab.Term.elabTermAndSynthesize (← `(∀ (α : Type) (x : α), x = x)) none)
  assert! (← testDepHOEq depEqForall) == some depEqBody
  withLocalDeclD `F (← Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Term.elabTermAndSynthesize (← `((α : Type) → α → Prop)) none) fun F => do
    let lhs := mkForall `α .default (mkSort 1) (mkForall `x .default (mkBVar 0) (mkApp2 F (mkBVar 1) (mkBVar 0)))
    let rhs := mkForall `β .default (mkSort 1) (mkForall `y .default (mkBVar 0) (mkApp2 F (mkBVar 1) (mkBVar 0)))
    assert! (← testDepHOPin (mkApp2 (mkConst ``And) lhs rhs)) == some F
  let finForall ← Lean.Elab.Term.TermElabM.run' do
    instantiateMVars (← Lean.Elab.Term.elabTermAndSynthesize (← `(∀ (n : Nat) (v : Fin n), v.val < n)) none)
  assert! (← testDepHOFin finForall).isSome
  let eLetNested := mkLambda `x .default natTy (mkLet `y natTy (mkNatAdd (mkBVar 0) one) (mkNatAdd (mkBVar 0) two))
  assert! (← testLetHONested eLetNested) == some (mkLambda `y .default natTy (mkNatAdd (mkBVar 0) two))
  let eLetFlat := mkLet `y natTy one (mkNatAdd (mkBVar 0) two)
  assert! (← testLetHOFlat eLetFlat) == some (mkLambda `y .default natTy (mkNatAdd (mkBVar 0) two))
  let eLetUnused := mkLet `y natTy one (mkNatLit 42)
  assert! (← testLetHOFlat eLetUnused) == some (mkLambda `y .default natTy (mkNatLit 42))
  withLocalDeclD `P (← mkArrow natTy (mkSort 0)) fun P => do
    let e2 := mkApp2 (mkConst ``And)
      (mkForall `x .default natTy (mkApp P (mkBVar 0)))
      (mkForall `y .default natTy (mkApp (mkLambda `z .default natTy (mkApp P (mkBVar 0))) (mkBVar 0)))
    assert! (← testTwoHOBetaEta e2) == some P
  assert! (← testSelfPinLinterClean (mkNatAdd one one))
  assert! !(← testSelfPinLinterClean eAdd)

end ExprQuotSpikeA
