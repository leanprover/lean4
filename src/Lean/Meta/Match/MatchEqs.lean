/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Match.Match
public import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Tactic.CasesOnStuckLHS
import Lean.Meta.Match.SimpH
import Lean.Meta.Match.DiteTree
import Lean.Meta.Match.AltTelescopes
import Lean.Meta.Match.NamedPatterns
import Lean.Meta.SplitSparseCasesOn
import Lean.Meta.StringLitProof

public section

namespace Lean.Meta.Match

/--
Given an application of an matcher arm `alt` that is expecting the `numDiscrEqs`, and
an array of `discr = pattern` equalities (one for each discriminant), apply those that
are expected by the alternative.
-/
partial def mkAppDiscrEqs (alt : Expr) (heqs : Array Expr) (numDiscrEqs : Nat) : MetaM Expr := do
  go alt (← inferType alt) 0
where
  go e ty i := do
    if i < numDiscrEqs then
      let Expr.forallE n d b .. := ty
        | throwError "expecting {numDiscrEqs} equalities, but found type{indentExpr alt}"
      for heq in heqs do
        if (← isDefEq (← inferType heq) d) then
          return ← go (mkApp e heq) (b.instantiate1 heq) (i+1)
      throwError "Could not find equation {n} : {d} among {heqs}"
    else
      return e


private def substSomeVar (mvarId : MVarId) : MetaM (Array MVarId) := mvarId.withContext do
  for localDecl in (← getLCtx) do
    if let some (_, lhs, rhs) ← matchEq? localDecl.type then
      if lhs.isFVar then
        if !(← dependsOn rhs lhs.fvarId!) then
          match (← subst? mvarId lhs.fvarId!) with
          | some mvarId => return #[mvarId]
          | none => pure ()
  throwError "substSomeVar failed"

private def unfoldElimOffset (mvarId : MVarId) : MetaM MVarId := do
  if Option.isNone <| (← mvarId.getType).find? fun e => e.isConstOf ``Nat.Internal.elimOffset then
    throwError "goal's target does not contain `Nat.Internal.elimOffset`"
  mvarId.deltaTarget (· == ``Nat.Internal.elimOffset)

/--
The codes of the `String` literals of a matcher: a mapping from a literal `s` to the numeral `n`
such that `String.Internal.byteCode s = n`, and a proof of this equation. See `getStrLitCodes`.
-/
private abbrev StrLitCodes := Std.HashMap String (Expr × Expr)

/--
Returns `true` if `e` is a `String` literal that has a code in `StrLitCodes`.

A literal with more than `256` bytes does not have one: the kernel evaluates
`String.Internal.codeOfBytes` with one multiplication for each byte, on a number whose size
is proportional to the number of bytes already processed.
-/
private def hasStrLitCode (e : Expr) : Bool :=
  match e with
  | .lit (.strVal s) => s.utf8ByteSize ≤ 256
  | _ => false

/--
The minimum number of `String` literals of a matcher for which the auxiliary theorems
`strLitCodes` (see `getStrLitCodes`) and `strLitChain` are generated.

These theorems reduce the time the kernel takes to check the equations of a matcher with many
literals, but each equation has to request them, and this request has a cost. With less than `32`
literals, the equations are generated faster without them.
-/
private def minStrLits := 32

/-- Returns `true` if at least `minStrLits` different `String` literals with a code occur in `e`. -/
private def hasMinStrLits (e : Expr) : MetaM Bool := do
  let (_, lits) ← e.forEach' visit |>.run {}
  return lits.size ≥ minStrLits
where
  visit (e : Expr) : StateRefT (Std.HashSet String) MetaM Bool := do
    if (← get).size ≥ minStrLits then return false
    if hasStrLitCode e then
      let .lit (.strVal s) := e | unreachable!
      modify (·.insert s)
    return true

/-- Returns the `String` literals occurring in `e` that have a code, without duplicates. -/
private def collectStrLits (e : Expr) : MetaM (Array String) := do
  let (_, lits, _) ← e.forEach visit |>.run (#[], {})
  return lits
where
  visit (e : Expr) : StateRefT (Array String × Std.HashSet String) MetaM Unit := do
    unless hasStrLitCode e do return ()
    let .lit (.strVal s) := e | return ()
    modify fun (lits, visited) =>
      if visited.contains s then (lits, visited) else (lits.push s, visited.insert s)

/--
Returns the codes of the `String` literals occurring in the definition of the matcher
`matchDeclName`. Only literals with at most `256` bytes have a code (see `hasStrLitCode`),
and the result is empty if there are less than `minStrLits` different ones.

The proof of an equation of a matcher with `n` `String` literal patterns contains up to `n-1`
proofs that two of these literals are different, and there is one equation for each alternative.
With `String.Internal.ne_of_byteCode`, such a proof is a comparison between the codes of the two
literals. Computing the code of a literal is the expensive step: the kernel evaluates
`String.Internal.codeOfBytes` on its bytes. So, it is performed once for each literal, in
the auxiliary theorem
```
matchDeclName.strLitCodes : byteCode "a" = n₁ ∧ byteCode "b" = n₂ ∧ ...
```
and the proof for the literal `i` returned by this function is a projection of this theorem.
-/
private def getStrLitCodes (matchDeclName : Name) : MetaM StrLitCodes := do
  -- A matcher with less than `minStrLits` alternatives is not traversed.
  let some matchInfo ← getMatcherInfo? matchDeclName | return {}
  if matchInfo.numAlts < minStrLits then return {}
  let some value := (← getConstInfo matchDeclName).value? | return {}
  unless (← hasMinStrLits value) do return {}
  let thmName := mkPrivateName (← getEnv) matchDeclName ++ `strLitCodes
  realizeConst matchDeclName thmName do
    let mkFact (lit : String) : Expr × Expr :=
      let (n, h) := mkStringLitCodeProof lit
      let code := mkApp (mkConst ``String.Internal.byteCode) (mkStrLit lit)
      (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) code n, h)
    let lits ← collectStrLits value
    let (type, value) := lits.pop.foldr (init := mkFact lits.back!) fun lit (type, value) =>
      let (fact, h) := mkFact lit
      (mkAnd fact type, mkApp4 (mkConst ``And.intro) fact type h value)
    addDecl <| Declaration.thmDecl { name := thmName, levelParams := [], type, value }
  -- The literals and their codes are retrieved from the statement of the theorem.
  let getCode (fact : Expr) : String × Expr :=
    -- `fact` is `byteCode lit = n`
    match fact.appFn!.appArg! with
    | .app _ (.lit (.strVal lit)) => (lit, fact.appArg!)
    | _ => unreachable!
  let mut codes : StrLitCodes := {}
  let mut type := (← getConstInfo thmName).type
  let mut proof := mkConst thmName
  repeat
    let_expr And fact rest := type | break
    let (lit, n) := getCode fact
    codes := codes.insert lit (n, .proj ``And 0 proof)
    type := rest
    proof := .proj ``And 1 proof
  let (lit, n) := getCode type
  return codes.insert lit (n, proof)

/--
Returns a proof of `¬ a = b`, where `a` and `b` are the `String` literals `s₁` and `s₂`,
which must be different.

If both literals have a code in `codes`, the proof compares the codes. Otherwise, it compares the
bytes at the first position where the two literals differ (see `mkStringLitNeProof`).
-/
private def mkStrLitNeProof (codes : StrLitCodes) (a b : Expr) (s₁ s₂ : String) : MetaM Expr := do
  let some (n₁, h₁) := codes[s₁]? | mkByteNeProof
  let some (n₂, h₂) := codes[s₂]? | mkByteNeProof
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``false)
  return mkApp7 (mkConst ``String.Internal.ne_of_byteCode) a b n₁ n₂ h₁ h₂ h
where
  mkByteNeProof : MetaM Expr :=
    return mkExpectedPropHint (← mkStringLitNeProof s₁ s₂)
      (mkNot (mkApp3 (mkConst ``Eq [1]) (mkConst ``String) a b))

/--
If the left-hand side of the goal is `dite (a = b) t e` where `a` and `b` are `String` literals,
rewrites it to the selected branch. Distinct literals are proved distinct with `mkStrLitNeProof`;
reducing `String.decEq` instead compares them character by character.
`codes` are the codes of the literals of the matcher, see `getStrLitCodes`.
-/
private def rwStringLitDite? (codes : StrLitCodes) (mvarId : MVarId) : MetaM (Option MVarId) := mvarId.withContext do
  let some (_, lhs, rhs) := (← mvarId.getType).eq? | return none
  let_expr dite@dite α c h t e := lhs | return none
  let_expr Eq _ a b := c | return none
  let some s₁ := getStringValue? a | return none
  let some s₂ := getStringValue? b | return none
  let us := dite.constLevels!
  if s₁ == s₂ then
    let hc ← mkEqRefl a
    let proof := mkAppN (mkConst ``dite_eq_left us) #[c, h, hc, α, t, e]
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar (← mkEq (t.beta #[hc]) rhs) (← mvarId.getTag)
    mvarId.assign (← mkEqTrans proof mvarNew)
    return some mvarNew.mvarId!
  else
    let hc ← mkStrLitNeProof codes a b s₁ s₂
    -- The new goal is `e hc = rhs`, and `dite_eq_of_not` expects a proof of `∀ h, e h = rhs`.
    -- The proof of the new goal is put under the binder without abstracting `hc`:
    -- `e h` and `e hc` are definitionally equal by proof irrelevance.
    -- See `dite_eq_of_not` for why the binder matters.
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar (← mkEq (e.beta #[hc]) rhs) (← mvarId.getTag)
    let proof := mkLambda `h .default (mkNot c) mvarNew
    mvarId.assign (mkAppN (mkConst ``dite_eq_of_not us) #[c, h, α, t, e, rhs, hc, proof])
    return some mvarNew.mvarId!

/--
Removes the proofs of the discriminant equalities from the goal of `proveCondEqThm`.

If `n > 0` discriminants of the matcher are annotated with `h :`, the tests generated by the match
compiler have a function type that takes the `n` proofs, and the matcher applies them to
`Eq.refl d`. For example, for `match h : s with | "a" => .. | _ => ..`, the goal for the last
alternative is
```
(dite (x = "a") (Eq.ndrec_symm h_1) fun _ => h_2 x) (Eq.refl x) = h_2 x (Eq.refl x)
```
This function replaces it with
```
(dite (x = "a") (Eq.ndrec_symm h_1) fun _ => h_2 x) = h_2 x
```
This is important for performance: `rwStringLitDite?` and `splitDiteTree` only recognize a `dite`
that is not applied to extra arguments. If the proofs are not removed, the equations for `String`
literal patterns are proved by reducing `String.decEq`, and each test in the equation for a
catch-all alternative has a cost proportional to the number of alternatives.

The proofs can be removed because the new goal implies the original one. Given the original goal
`f p₁ ... pₙ = g q₁ ... qₙ`, where `pᵢ` and `qᵢ` are the last `n` arguments of each side, the new
goal is `?h : f = g`, and the original goal is assigned the term
```
congrFun (... (congrFun ?h p₁) ...) pₙ : f p₁ ... pₙ = g p₁ ... pₙ
```
Its type is definitionally equal to the original goal even when `pᵢ` and `qᵢ` are not syntactically
equal, because they are proofs of the same proposition. This function checks that the removed
arguments are proofs, and that `f` and `g` have the same type.
-/
private def stripDiscrEqProofs (matchDeclName : Name) (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let some info ← getMatcherInfo? matchDeclName | return mvarId
  let n := info.getNumDiscrEqs
  if n == 0 then return mvarId
  let mvarId ← mvarId.modifyTargetEqLHS whnfCore
  let_expr eq@Eq _ lhs rhs := (← mvarId.getType) | return mvarId
  let lhsArgs := lhs.getAppArgs
  let rhsArgs := rhs.getAppArgs
  unless lhsArgs.size ≥ n && rhsArgs.size ≥ n do return mvarId
  let ps := lhsArgs.extract (lhsArgs.size - n) lhsArgs.size
  let qs := rhsArgs.extract (rhsArgs.size - n) rhsArgs.size
  unless (← ps.allM isProof) && (← qs.allM isProof) do return mvarId
  let f := lhs.getAppPrefix (lhsArgs.size - n)
  let g := rhs.getAppPrefix (rhsArgs.size - n)
  let fType ← inferType f
  unless (← isDefEq fType (← inferType g)) do return mvarId
  -- `fType` is in the same universe as the type of `lhs` because the removed arguments are proofs.
  let us := eq.constLevels!
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar (mkApp3 eq fType f g) (← mvarId.getTag)
  let congrFun := mkConst ``congrFun (.zero :: us)
  let mut proof := mvarNew
  let mut f := f
  let mut g := g
  let mut fType := fType
  for p in ps do
    let .forallE x α β _ ← whnfCore fType | return mvarId
    proof := mkApp6 congrFun α (mkLambda x .default α β) f g proof p
    f := mkApp f p
    g := mkApp g p
    fType := β.instantiate1 p
  mvarId.assign proof
  return mvarNew.mvarId!

/--
A matcher whose definition starts with a chain of tests on `String` literals
```
dite (x = "a₁") (Eq.ndrec_symm (alt₁ ())) fun _ => dite (x = "a₂") (Eq.ndrec_symm (alt₂ ())) fun _ => ... e
```
where `x` is its only discriminant. See `getStrLitChain?`.
-/
private structure StrLitChain where
  /-- The number of arguments of the matcher. -/
  arity    : Nat
  /-- The position of the discriminant in the arguments of the matcher. -/
  discrPos : Nat
  /-- The literals tested by the chain. -/
  lits     : Array String
  /-- `altPos[i]` is the position, in the arguments of the matcher, of the alternative for `lits[i]`. -/
  altPos   : Array Nat
  /--
  The term `e` after the last test. Its loose bound variables are the arguments of the matcher:
  it is under `arity` binders.
  -/
  rest     : Expr

/-- Returns `true` if `e` has a loose bound variable with index smaller than `n`. -/
private partial def hasLooseBVarLt (e : Expr) (n : Nat) : Bool :=
  go e 0
where
  go (e : Expr) (offset : Nat) : Bool :=
    if e.looseBVarRange ≤ offset then false else
    match e with
    | .bvar idx => idx < offset + n
    | .app f a => go f offset || go a offset
    | .lam _ d b _ | .forallE _ d b _ => go d offset || go b (offset + 1)
    | .letE _ t v b _ => go t offset || go v offset || go b (offset + 1)
    | .mdata _ b | .proj _ _ b => go b offset
    | _ => false

/--
Returns the chain of tests on `String` literals at the beginning of the definition of the matcher
`matchDeclName`, if it has one with at least `minStrLits` tests. See `StrLitChain`.

The `else` branch of a test is `fun h : ¬ x = "aᵢ" => ..`. No hypothesis `h` is used in a chain.
`getStrLitChainThm` relies on this property.
-/
private def getStrLitChain? (matchDeclName : Name) : MetaM (Option StrLitChain) := do
  let some matchInfo ← getMatcherInfo? matchDeclName | return none
  unless matchInfo.numDiscrs == 1 && matchInfo.getNumDiscrEqs == 0 do return none
  let some value := (← getConstInfo matchDeclName).value? | return none
  let arity := matchInfo.arity
  let discrPos := matchInfo.numParams + 1
  let mut e := value
  for _ in *...arity do
    let .lam _ _ b _ := e | return none
    e := b
  -- `e` is under `arity + lits.size` binders: the arguments of the matcher, and one hypothesis for
  -- each test that failed.
  -- The hypotheses are the bound variables with index smaller than `lits.size`.
  let mut lits := #[]
  let mut altPos := #[]
  repeat
    let depth := arity + lits.size
    let_expr dite α c inst t e' := e | break
    let_expr Eq _ x v := c | break
    let_expr Eq.ndrec_symm _ _ motive m _ := t | break
    let .lit (.strVal lit) := v | break
    let .lam _ _ rest _ := e' | break
    let .app (.bvar altIdx) unit := m | break
    unless x == .bvar (depth - 1 - discrPos) && unit.isConstOf ``Unit.unit do break
    unless lits.size ≤ altIdx && altIdx < depth do break
    if hasLooseBVarLt α lits.size || hasLooseBVarLt inst lits.size || hasLooseBVarLt motive lits.size then break
    lits := lits.push lit
    altPos := altPos.push (depth - 1 - altIdx)
    e := rest
  if lits.size < minStrLits || hasLooseBVarLt e lits.size then return none
  return some { arity, discrPos, lits, altPos, rest := e.lowerLooseBVars lits.size lits.size }

/--
Returns the name of the auxiliary theorem for the matcher `matchDeclName`, which has the chain of
tests `chain`.
```
matchDeclName.strLitChain : ∀ params motive x alts (r : motive x),
  r = matchDeclName params motive x alts →
  (x = "a₁" → r ≍ alt₁ ()) ∧ (¬ x = "a₁" → (x = "a₂" → r ≍ alt₂ ()) ∧ (¬ x = "a₂" → ... r ≍ e))
```
It is proved with a single traversal of the chain, and has one case for each alternative.
The congruence equation for the literal `"aᵢ"` is the case `i` of this theorem: its proof
selects the case with `i-1` proofs that `"aᵢ"` is different from the preceding literals.
Proving each congruence equation directly traverses the chain up to the test `i`, and the
kernel processes the tests that follow at each step.

The variable `r` is used instead of the matcher application in the cases because the size of the
latter is proportional to the number of alternatives, and each case is under a different number
of binders.
-/
private def getStrLitChainThm (matchDeclName : Name) (chain : StrLitChain) : MetaM Name := do
  let thmName := mkPrivateName (← getEnv) matchDeclName ++ `strLitChain
  realizeConst matchDeclName thmName do
    let info ← getConstInfo matchDeclName
    let us := info.levelParams.map mkLevelParam
    forallBoundedTelescope info.type chain.arity fun xs _ => do
      let app := mkAppN (mkConst matchDeclName us) xs
      let tests := (info.instantiateValueLevelParams! us).beta xs
      withLocalDeclD `r (← inferType app) fun r => do
        let (stmt, proof) ← mkCases r tests chain.lits.size
        let type ← mkForallFVars (xs.push r) (.forallE `h (← mkEq r app) stmt .default)
        let value ← mkLambdaFVars (xs.push r) proof
        addDecl <| Declaration.thmDecl { name := thmName, levelParams := info.levelParams, type, value }
  return thmName
where
  /--
  Returns the statement of the cases of the first `n` tests of `tests`, and a proof for
  `r = tests → statement`.
  -/
  mkCases (r tests : Expr) : Nat → MetaM (Expr × Expr)
    | 0 => return (← mkHEq r tests, ← mkAppOptM ``heq_of_eq #[none, r, tests])
    | n+1 => do
      let_expr dite _ c inst t e := tests | unreachable!
      let_expr Eq α b a := c | unreachable!
      let_expr ndrec@Eq.ndrec_symm _ _ motive m _ := t | unreachable!
      let .lam _ _ rest _ := e | unreachable!
      let [u₁, u₂] := ndrec.constLevels! | unreachable!
      let (q, h) ← mkCases r rest n
      let heq := mkApp4 (mkConst ``HEq [u₁]) (motive.beta #[b]) r (motive.beta #[a]) m
      let stmt := mkAnd (.forallE `h c heq .default) (.forallE `h (mkNot c) q .default)
      let h := mkLambda `h .default (mkNot c) h
      let proof := mkAppN (mkConst ``dite_ndrec_symm_cases [u₂, u₁]) #[α, a, b, inst, motive, m, e, r, q, h]
      return (stmt, proof)

/--
Proves a goal `matchDeclName params motive a alts ≍ rhs` using the theorem
`matchDeclName.strLitChain`, if `matchDeclName` has a chain of tests on `String` literals, and
- `a` is one of the literals `"aᵢ"` of the chain and `rhs` is `altᵢ ()`. The case `i` of the
  theorem is selected with proofs that `"aᵢ"` is different from the preceding literals.
- `a` is a variable `x`, `rhs` is the term after the last test, and for each literal `"aᵢ"` of
  the chain there is a hypothesis `x = "aᵢ" → False`. The last case of the theorem is selected
  with these hypotheses.

Returns `false` otherwise. See `getStrLitChainThm`.
-/
private def proveUsingStrLitChain? (matchDeclName : Name) (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
  let some chain ← getStrLitChain? matchDeclName | return false
  let some (_, lhs, _, rhs) := (← mvarId.getType).heq? | return false
  unless lhs.isAppOfArity matchDeclName chain.arity do return false
  let args := lhs.getAppArgs
  let a := args[chain.discrPos]!
  let mkChainThm : MetaM Expr := do
    let thmName ← getStrLitChainThm matchDeclName chain
    return mkAppN (mkConst thmName lhs.getAppFn.constLevels!) (args ++ #[lhs, ← mkEqRefl lhs])
  match a with
  | .lit (.strVal lit) =>
    let some i := chain.lits.idxOf? lit | return false
    unless rhs == mkApp args[chain.altPos[i]!]! (mkConst ``Unit.unit) do return false
    let mut proof ← mkChainThm
    -- The first case does not need the codes of the literals.
    let codes ← if i == 0 then pure {} else getStrLitCodes matchDeclName
    for j in *...i do
      let lit' := chain.lits[j]!
      proof := mkApp (.proj ``And 1 proof) (← mkStrLitNeProof codes a (mkStrLit lit') lit lit')
    mvarId.assign (mkApp (.proj ``And 0 proof) (← mkEqRefl a))
    return true
  | .fvar _ =>
    unless rhs == chain.rest.instantiateRev args do return false
    -- The hypotheses `a = "aᵢ" → False`
    let mut hyps : Std.HashMap String Expr := {}
    for localDecl in (← getLCtx) do
      let .forallE _ d b _ := localDecl.type | continue
      let_expr Eq _ x v := d | continue
      let .lit (.strVal lit) := v | continue
      if x == a && b.isConstOf ``False then
        hyps := hyps.insert lit localDecl.toExpr
    let mut hs := #[]
    for lit in chain.lits do
      let some h := hyps[lit]? | return false
      hs := hs.push h
    let mut proof ← mkChainThm
    for h in hs do
      proof := mkApp (.proj ``And 1 proof) h
    mvarId.assign proof
    return true
  | _ => return false

/--
A `contradiction` variant for the goals of `proveCondEqThm`. It closes the goal if a hypothesis is
- a disequality `h : a ≠ b`, or `h : a = b → False`, where `a` and `b` are definitionally equal,
- a generalized disequality such as `h : ∀ ys, x = C ys → False` (see `processGenDiseq`), or
- an element of an empty inductive type.

Unlike `MVarId.contradiction`, it does not search for a pair of hypotheses `h₁ : p` and `h₂ : ¬ p`.
That search compares every `h₂` with every other hypothesis, and the goals of `proveCondEqThm` have
one hypothesis for each alternative of the `match`.
-/
private def contradictionForEqns (mvarId : MVarId) : MetaM Unit := mvarId.withContext do
  mvarId.checkNotAssigned `contradiction
  let fuel := ({} : Contradiction.Config).searchFuel
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      if let some (_, lhs, rhs) ← matchNe? localDecl.type then
        if (← isDefEq lhs rhs) then
          mvarId.assign (← mkAbsurd (← mvarId.getType) (← mkEqRefl lhs) localDecl.toExpr)
          return
      if Simp.isEqnThmHypothesis localDecl.type then
        if (← processGenDiseq mvarId localDecl) then
          return
      if (← matchEq? localDecl.type).isNone && (← matchHEq? localDecl.type).isNone then
        if (← elimEmptyInductive mvarId localDecl.fvarId fuel) then
          return
  throwTacticEx `contradiction mvarId

/--
Helper method for proving a conditional equational theorem associated with an alternative of
the `match`-eliminator `matchDeclName`. `type` contains the type of the theorem.

The `heqPos`/`heqNum` arguments indicate that these hypotheses are `Eq`/`HEq` hypotheses
to substitute first; this is used for the generalized match equations.
-/
partial def proveCondEqThm (matchDeclName : Name) (type : Expr)
  (heqPos : Nat := 0) (heqNum : Nat := 0) : MetaM Expr := withLCtx {} {} do
  let type ← instantiateMVars type
  let mvar0  ← mkFreshExprSyntheticOpaqueMVar type
  trace[Meta.Match.matchEqs] "proveCondEqThm {mvar0.mvarId!}"
  let mut mvarId := mvar0.mvarId!
  if heqNum > 0 then
    mvarId := (← mvarId.introN heqPos).2
    for _ in *...heqNum do
      (_, mvarId) ← introSubstEq mvarId
    trace[Meta.Match.matchEqs] "proveCondEqThm after subst{mvarId}"
  mvarId := (← mvarId.intros).2
  -- The target of a congruence equation is a `HEq`.
  let rfl := do if (← mvarId.getType).isHEq then mvarId.hrefl else mvarId.refl
  reflOrProve rfl (unfoldAndProve mvarId)
  instantiateMVars mvar0
where
  unfoldAndProve (mvarId : MVarId) : MetaM Unit := do
    if (← proveUsingStrLitChain? matchDeclName mvarId) then return
    let mvarId ← mvarId.deltaTarget (· == matchDeclName)
    let mvarId ← mvarId.heqOfEq
    go (← getStrLitCodes matchDeclName) (← stripDiscrEqProofs matchDeclName mvarId) 0

  go (codes : StrLitCodes) (mvarId : MVarId) (depth : Nat) : MetaM Unit := withIncRecDepth do
    trace[Meta.Match.matchEqs] "proveCondEqThm.go {mvarId}"
    let mvarId ← mvarId.modifyTargetEqLHS whnfCore
    let subgoals ←
      (do let some mvarId ← rwStringLitDite? codes mvarId | throwError "no `String` literal `dite`"
          return #[mvarId])
      <|>
      (do mvarId.refl; return #[])
      <|>
      (do contradictionForEqns mvarId; return #[])
      <|>
      (splitDiteTree mvarId)
      <|>
      (do let mvarId ← unfoldElimOffset mvarId; return #[mvarId])
      <|>
      (casesOnStuckLHS mvarId)
      <|>
      (reduceSparseCasesOn mvarId)
      <|>
      (splitSparseCasesOn mvarId)
      <|>
      (do let mvarId' ← simpIfTarget mvarId (useDecide := true) (useNewSemantics := true)
          if mvarId' == mvarId then throwError "simpIf failed"
          return #[mvarId'])
      <|>
      (do if let some (s₁, s₂) ← splitIfTarget? mvarId (useNewSemantics := true) then
            let mvarId₁ ← trySubst s₁.mvarId s₁.fvarId
            return #[mvarId₁, s₂.mvarId]
          else
            throwError "spliIf failed")
      <|>
      (substSomeVar mvarId)
      <|>
      (throwError "failed to generate equality theorems for `match` expression `{matchDeclName}`\n{MessageData.ofGoal mvarId}")
    subgoals.forM (go codes · (depth+1))

/--
  Create new alternatives (aka minor premises) by replacing `discrs` with `patterns` at `alts`.
  Recall that `alts` depends on `discrs` when `numDiscrEqs > 0`, where `numDiscrEqs` is the number of discriminants
  annotated with `h : discr`.
-/
private partial def withNewAlts (numDiscrEqs : Nat) (discrs : Array Expr) (patterns : Array Expr) (alts : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  if numDiscrEqs == 0 then
    k alts
  else
    go 0 #[]
where
  go (i : Nat) (altsNew : Array Expr) : MetaM α := do
   if h : i < alts.size then
     let altLocalDecl ← getFVarLocalDecl alts[i]
     let typeNew := altLocalDecl.type.replaceFVars discrs patterns
     withLocalDecl altLocalDecl.userName altLocalDecl.binderInfo typeNew fun altNew =>
       go (i+1) (altsNew.push altNew)
   else
     k altsNew

/--
Proves the match equation `type` of the alternative `altIdx` of `matchDeclName`:
```
∀ params motive ys alts, hs → matchDeclName params motive patterns alts = alt ys
```
where `hs` are the `numOverlaps` overlap hypotheses.

If `rfl` does not prove it, the proof is an instance of the congruence equation of the alternative
```
∀ params motive discrs alts ys, discrs = patterns → hs → matchDeclName params motive discrs alts ≍ alt ys
```
with `discrs := patterns`. The hypotheses `discrs = patterns` are proved by reflexivity, and the
result is `eq_of_heq (congr_eq params motive patterns alts ys rfl .. hs)`.
So, the two theorems share one proof. This matters for a `match` with many literal alternatives,
where the proof of each equation refutes every preceding alternative.

The arguments of the congruence equation after `alts` are split by position: the variables `ys`,
then `numDiscrs` hypotheses `discrs = patterns`, then `numOverlaps` overlap hypotheses.
Both theorems have the same overlap hypotheses in the same order: `getEquationsForImpl` and
`genMatchCongrEqnsImpl` build them with the same loop over `Overlaps.overlapping`, and both
simplify them with `simpH?`.
-/
private def proveEqThm (matchDeclName : Name) (altIdx : Nat) (numDiscrs numOverlaps : Nat) (type : Expr) : MetaM Expr := withLCtx {} {} do
  let mvar0 ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars type)
  let (fvarIds, mvarId) ← mvar0.mvarId!.intros
  reflOrProve mvarId.refl (useCongrEqn mvarId fvarIds[(fvarIds.size - numOverlaps)...*])
  instantiateMVars mvar0
where
  useCongrEqn (mvarId : MVarId) (overlapHyps : Subarray FVarId) : MetaM Unit := mvarId.withContext do
    let target ← mvarId.getType
    let some (_, lhs, _) := target.eq? | throwError "equality expected{indentExpr target}"
    let congrEqn ← genMatchCongrEqn matchDeclName altIdx
    let h := mkAppN (mkConst congrEqn lhs.getAppFn.constLevels!) lhs.getAppArgs
    -- `args` are metavariables for `ys`, the hypotheses `patterns = patterns[ys]`, and `hs`.
    let (args, _, _) ← forallMetaTelescope (← inferType h)
    let numAltVars := args.size - numDiscrs - numOverlaps
    -- Reflexivity assigns `ys`.
    for arg in args[numAltVars...(numAltVars + numDiscrs)] do
      if (← inferType arg).isHEq then arg.mvarId!.hrefl else arg.mvarId!.refl
    for arg in args[(numAltVars + numDiscrs)...*], overlapHyp in overlapHyps do
      unless (← isDefEq arg (mkFVar overlapHyp)) do
        throwError "failed to prove match equation using `{.ofConstName congrEqn}`, overlap hypothesis mismatch{indentExpr target}"
    let proof ← mkEqOfHEq (← instantiateMVars (mkAppN h args))
    unless (← isDefEq target (← inferType proof)) do
      throwError "failed to prove match equation using `{.ofConstName congrEqn}`{indentExpr target}"
    mvarId.assign proof

/-
Creates conditional equations and splitter for the given match auxiliary declaration.

See also `getEquationsFor`.
-/
set_option compiler.ignoreBorrowAnnotation true in
@[export lean_get_match_equations_for]
def getEquationsForImpl (matchDeclName : Name) : MetaM MatchEqns := do
  /-
  Remark: users have requested the `split` tactic to be available for writing code.
  Thus, the `splitter` declaration must be a definition instead of a theorem.
  Moreover, the `splitter` is generated on demand, and we currently
  can't import the same definition from different modules. Thus, we must
  keep `splitter` as a private declaration to prevent import failures.
  -/
  let baseName := mkPrivateName (← getEnv) matchDeclName
  let splitterName := baseName ++ `splitter
  -- NOTE: `go` will generate both splitter and equations but we use the splitter as the "key" for
  -- `realizeConst` as well as for looking up the resultant environment extension state via
  -- `getState`.
  realizeConst matchDeclName splitterName (go baseName splitterName)
  match matchEqnsExt.getState (asyncMode := .async .asyncEnv) (asyncDecl := splitterName) (← getEnv) |>.map.find? matchDeclName with
  | some eqns => return eqns
  | none      => throwError "failed to retrieve match equations for `{matchDeclName}` after realization"
where go baseName splitterName := withConfig (fun c => { c with etaStruct := .none }) do
  let constInfo ← getConstInfo matchDeclName
  let us := constInfo.levelParams.map mkLevelParam
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "`{matchDeclName}` is not a matcher function"
  let numDiscrEqs := getNumEqsFromDiscrInfos matchInfo.discrInfos
  forallTelescopeReducing constInfo.type fun xs _matchResultType => do
    let mut eqnNames := #[]
    let params := xs[*...matchInfo.numParams]
    let motive := xs[matchInfo.getMotivePos]!
    let alts   := xs[(xs.size - matchInfo.numAlts)...*]
    let firstDiscrIdx := matchInfo.numParams + 1
    let discrs := xs[firstDiscrIdx...(firstDiscrIdx + matchInfo.numDiscrs)]
    let mut notAlts := #[]
    let mut idx := 1
    let mut splitterAltInfos := #[]
    let mut altArgMasks := #[] -- masks produced by `forallAltTelescope`
    for i in *...alts.size do
      let altInfo := matchInfo.altInfos[i]!
      let thmName := Name.str baseName eqnThmSuffixBase |>.appendIndexAfter idx
      eqnNames := eqnNames.push thmName
      let (notAlt, splitterAltInfo, argMask) ←
          forallAltTelescope (← inferType alts[i]!) altInfo numDiscrEqs
          fun ys _eqs rhsArgs argMask altResultType => do
        let patterns := altResultType.getAppArgs
        let mut hs := #[]
        for overlappedBy in matchInfo.overlaps.overlapping i do
          let notAlt := notAlts[overlappedBy]!
          let h ← instantiateForall notAlt patterns
          if let some h ← simpH? h patterns.size then
            hs := hs.push h
        trace[Meta.Match.matchEqs] "hs: {hs}"
        let hasUnitThunk := ys.isEmpty && hs.isEmpty && numDiscrEqs = 0
        let splitterAltInfo := { numFields := ys.size, numOverlaps := hs.size, hasUnitThunk }
        -- Create a proposition for representing terms that do not match `patterns`
        let mut notAlt := mkConst ``False
        for discr in discrs.toArray.reverse, pattern in patterns.reverse do
          notAlt ← mkArrow (← mkEqHEq discr pattern) notAlt
        notAlt ← mkForallFVars (discrs ++ ys) notAlt
        /- Recall that when we use the `h : discr`, the alternative type depends on the discriminant.
           Thus, we need to create new `alts`. -/
        withNewAlts numDiscrEqs discrs patterns alts fun alts => do
          let alt := alts[i]!
          let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ patterns ++ alts)
          let rhs := mkAppN alt rhsArgs
          let thmType ← mkEq lhs rhs
          let thmType ← mkArrowN hs thmType
          let thmType ← mkForallFVars (params ++ #[motive] ++ ys ++ alts) thmType
          let thmType ← unfoldNamedPattern thmType
          let thmVal ← proveEqThm matchDeclName i discrs.size hs.size thmType
          addDecl <| Declaration.thmDecl {
            name        := thmName
            levelParams := constInfo.levelParams
            type        := thmType
            value       := thmVal
          }
          return (notAlt, splitterAltInfo, argMask)
      notAlts := notAlts.push notAlt
      splitterAltInfos := splitterAltInfos.push splitterAltInfo
      altArgMasks := altArgMasks.push argMask
      idx := idx + 1
    let splitterMatchInfo : MatcherInfo := { matchInfo with altInfos := splitterAltInfos }

    let needsSplitter := !matchInfo.overlaps.isEmpty || (constInfo.type.find? (isNamedPattern )).isSome

    if needsSplitter then
      withMkMatcherInput matchDeclName (unfoldNamed := true) fun matcherInput => do
        let matcherInput := { matcherInput with
          matcherName := splitterName
          isSplitter := some matchInfo.overlaps
        }
        let res ← Match.mkMatcher matcherInput
        res.addMatcher -- TODO: Do not set matcherinfo for the splitter!
    else
      assert! matchInfo.altInfos == splitterAltInfos
      -- This match statement does not need a splitter, we can use itself for that.
      -- (We still have to generate a declaration to satisfy the realizable constant)
      let decl := Declaration.defnDecl {
        name        := splitterName
        levelParams := constInfo.levelParams
        type        := constInfo.type
        value       := mkConst matchDeclName us
        hints       := .abbrev
        safety      := .safe
      }
      addDecl decl
      setInlineAttribute splitterName
      compileDecl (logErrors := false) decl
    let result := { eqnNames, splitterName, splitterMatchInfo }
    registerMatchEqns matchDeclName result

/--
Generates the congruence equation of the alternative `altIdx` of the given match auxiliary
declaration, and returns its name. It assumes `altIdx` is a valid alternative index.

The congruence equations have a completely unrestricted left-hand side (arbitrary discriminants),
and take propositional equations relating the discriminants to the patterns as arguments. In this
sense they combine a congruence lemma with the regular equation lemma.
Since the motive depends on the discriminants, they are `HEq` equations.

Each congruence equation is its own realization. So, a caller that needs the equation of one
alternative does not pay for the other ones. For example, in a `match` with many literal
alternatives and a catch-all, only the match equation of the catch-all needs its congruence
equation, see `proveEqThm`.
The statement of the equation uses the patterns of the alternatives that overlap `altIdx`, but
not their congruence equations.
-/
private def realizeMatchCongrEqn (matchDeclName : Name) (altIdx : Nat) : MetaM Name := do
  let thmName := (matchDeclName.str congrEqnThmSuffixBase).appendIndexAfter (altIdx + 1)
  realizeConst matchDeclName thmName (go thmName)
  return thmName
where go (thmName : Name) := withConfig (fun c => { c with etaStruct := .none }) do
  let constInfo ← getConstInfo matchDeclName
  let us := constInfo.levelParams.map mkLevelParam
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "`{matchDeclName}` is not a matcher function"
  let numDiscrEqs := matchInfo.getNumDiscrEqs
  forallTelescopeReducing constInfo.type fun xs _matchResultType => do
    let params := xs[*...matchInfo.numParams]
    let motive := xs[matchInfo.getMotivePos]!
    let alts   := xs[(xs.size - matchInfo.numAlts)...*]
    let firstDiscrIdx := matchInfo.numParams + 1
    let discrs := xs[firstDiscrIdx...(firstDiscrIdx + matchInfo.numDiscrs)]
    -- `∀ discrs altVars, discrs = patterns → False` for the alternative `i`
    let mkNotAlt (i : Nat) : MetaM Expr := do
      Match.forallAltVarsTelescope (← inferType alts[i]!) matchInfo.altInfos[i]! fun altVars _ _ altResultType => do
        let patterns ← forallTelescope altResultType fun _ t => pure t.getAppArgs
        let mut notAlt := mkConst ``False
        for discr in discrs.toArray.reverse, pattern in patterns.reverse do
          notAlt ← mkArrow (← mkEqHEq discr pattern) notAlt
        mkForallFVars (discrs ++ altVars) notAlt
    let alt := alts[altIdx]!
    Match.forallAltVarsTelescope (← inferType alt) matchInfo.altInfos[altIdx]! fun altVars args _mask altResultType => do
      let patterns ← forallTelescope altResultType fun _ t => pure t.getAppArgs
      let mut heqsTypes := #[]
      assert! patterns.size == discrs.size
      for discr in discrs, pattern in patterns do
        let heqType ← mkEqHEq discr pattern
        heqsTypes := heqsTypes.push ((`heq).appendIndexAfter (heqsTypes.size + 1), heqType)
      withLocalDeclsDND heqsTypes fun heqs => do
        let rhs ← Match.mkAppDiscrEqs (mkAppN alt args) heqs numDiscrEqs
        let mut hs := #[]
        for overlappedBy in matchInfo.overlaps.overlapping altIdx do
          let h ← instantiateForall (← mkNotAlt overlappedBy) patterns
          if let some h ← simpH? h patterns.size then
            hs := hs.push h
        trace[Meta.Match.matchEqs] "hs: {hs}"
        let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ discrs ++ alts)
        let thmType ← mkHEq lhs rhs
        let thmType ← mkArrowN hs thmType
        let thmType ← mkForallFVars (params ++ #[motive] ++ discrs ++ alts ++ altVars ++ heqs) thmType
        let thmType ← Match.unfoldNamedPattern thmType
        -- The match equations are instances of these theorems, see `proveEqThm`.
        -- The proof may create auxiliary definitions, such as a sparse `casesOn`. `thmName` is
        -- the same name in every module that realizes this equation, and the same definition
        -- cannot be imported from different modules. So, the auxiliary declarations must be
        -- private to the realizing module.
        let thmVal ← withDeclNameForAuxNaming (mkPrivateName (← getEnv) thmName) do
          Match.proveCondEqThm matchDeclName thmType
            (heqPos := params.size + 1 + discrs.size + alts.size + altVars.size) (heqNum := heqs.size)
        addDecl <| Declaration.thmDecl {
          name        := thmName
          levelParams := constInfo.levelParams
          type        := thmType
          value       := thmVal
        }

set_option compiler.ignoreBorrowAnnotation true in
/--
Generates the congruence equation of the alternative `altIdx` of the given match auxiliary
declaration, and returns its name. See `realizeMatchCongrEqn`.
-/
@[export lean_get_congr_match_equation_for]
def genMatchCongrEqnImpl (matchDeclName : Name) (altIdx : Nat) : MetaM Name := do
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "`{matchDeclName}` is not a matcher function"
  unless altIdx < matchInfo.numAlts do
    throwError "`{matchDeclName}` does not have alternative {altIdx + 1}"
  realizeMatchCongrEqn matchDeclName altIdx

set_option compiler.ignoreBorrowAnnotation true in
/--
Generates the congruence equations of all alternatives of the given match auxiliary declaration,
and returns their names. See `realizeMatchCongrEqn`.
-/
@[export lean_get_congr_match_equations_for]
def genMatchCongrEqnsImpl (matchDeclName : Name) : MetaM (Array Name) := do
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "`{matchDeclName}` is not a matcher function"
  (Array.range matchInfo.numAlts).mapM (realizeMatchCongrEqn matchDeclName)

builtin_initialize registerTraceClass `Meta.Match.matchEqs

private def isMatchEqName? (env : Environment) (n : Name) : Option Name := do
  let .str p s := n | failure
  guard <| isEqnReservedNameSuffix s || s == "splitter"
  let p ← privateToUserName? p
  guard <| isMatcherCore env p
  return p

builtin_initialize
  registerReservedNamePredicate (fun s => isEqnReservedNameSuffix s || s == "splitter")
    (isMatchEqName? · · |>.isSome)

builtin_initialize registerReservedNameAction fun name => do
  let some p := isMatchEqName? (← getEnv) name |
    return false
  let _ ← MetaM.run' <| getEquationsForImpl p
  return true

/--
If `n` is of the form `matchDeclName.congr_eq_<idx>`, returns `matchDeclName` and `idx`.
-/
private def isMatchCongrEqName? (env : Environment) (n : Name) : Option (Name × Nat) := do
  let .str p s := n | failure
  let idx ← (← s.dropPrefix? congrEqnThmSuffixBasePrefix).toNat?
  guard <| isMatcherCore env p
  return (p, idx)

builtin_initialize
  registerReservedNamePredicate isCongrEqnReservedNameSuffix (isMatchCongrEqName? · · |>.isSome)

builtin_initialize registerReservedNameAction fun name => do
  let some (p, idx) := isMatchCongrEqName? (← getEnv) name |
    return false
  let some matchInfo ← getMatcherInfo? p | return false
  unless 0 < idx && idx ≤ matchInfo.numAlts do
    return false
  let _ ← MetaM.run' <| realizeMatchCongrEqn p (idx - 1)
  return true

end Lean.Meta.Match
