/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.LitValues
import Lean.Meta.Check
import Lean.Meta.Closure
import Lean.Meta.CtorRecognizer
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.GeneralizeTelescope
import Lean.Meta.Match.Basic
import Lean.Meta.Match.MatcherApp.Basic

namespace Lean.Meta.Match

/-- The number of patterns in each AltLHS must be equal to the number of discriminants. -/
private def checkNumPatterns (numDiscrs : Nat) (lhss : List AltLHS) : MetaM Unit := do
  if lhss.any fun lhs => lhs.patterns.length != numDiscrs then
    throwError "incorrect number of patterns"

/--
  Execute `k hs` where `hs` contains new equalities `h : lhs[i] = rhs[i]` for each `discrInfos[i] = some h`.
  Assume `lhs.size == rhs.size == discrInfos.size`
-/
private partial def withEqs (lhs rhs : Array Expr) (discrInfos : Array DiscrInfo) (k : Array Expr → MetaM α) : MetaM α := do
  go 0 #[]
where
  go (i : Nat) (hs : Array Expr) : MetaM α := do
    if i < lhs.size then
      if let some hName := discrInfos[i]!.hName? then
        withLocalDeclD hName (← mkEqHEq lhs[i]! rhs[i]!) fun h =>
          go (i+1) (hs.push h)
      else
        go (i+1) hs
    else
      k hs

/-- Given a list of `AltLHS`, create a minor premise for each one, convert them into `Alt`, and then execute `k` -/
private def withAlts {α} (motive : Expr) (discrs : Array Expr) (discrInfos : Array DiscrInfo) (lhss : List AltLHS) (k : List Alt → Array (Expr × Nat) → MetaM α) : MetaM α :=
  loop lhss [] #[]
where
  mkMinorType (xs : Array Expr) (lhs : AltLHS) : MetaM Expr :=
    withExistingLocalDecls lhs.fvarDecls do
      let args ← lhs.patterns.toArray.mapM (Pattern.toExpr · (annotate := true))
      let minorType := mkAppN motive args
      withEqs discrs args discrInfos fun eqs => do
        mkForallFVars (xs ++ eqs) minorType

  loop (lhss : List AltLHS) (alts : List Alt) (minors : Array (Expr × Nat)) : MetaM α := do
    match lhss with
    | [] => k alts.reverse minors
    | lhs::lhss =>
      let xs := lhs.fvarDecls.toArray.map LocalDecl.toExpr
      let minorType ← mkMinorType xs lhs
      let hasParams := !xs.isEmpty || discrInfos.any fun info => info.hName?.isSome
      let (minorType, minorNumParams) := if hasParams then (minorType, xs.size) else (mkSimpleThunkType minorType, 1)
      let idx       := alts.length
      let minorName := (`h).appendIndexAfter (idx+1)
      trace[Meta.Match.debug] "minor premise {minorName} : {minorType}"
      withLocalDeclD minorName minorType fun minor => do
        let rhs    := if hasParams then mkAppN minor xs else mkApp minor (mkConst `Unit.unit)
        let minors := minors.push (minor, minorNumParams)
        let fvarDecls ← lhs.fvarDecls.mapM instantiateLocalDeclMVars
        let alts   := { ref := lhs.ref, idx := idx, rhs := rhs, fvarDecls := fvarDecls, patterns := lhs.patterns, cnstrs := [] } :: alts
        loop lhss alts minors

structure State where
  used            : Std.HashSet Nat := {} -- used alternatives
  counterExamples : List (List Example) := []

/-- Return true if the given (sub-)problem has been solved. -/
private def isDone (p : Problem) : Bool :=
  p.vars.isEmpty

/-- Return true if the next element on the `p.vars` list is a variable. -/
private def isNextVar (p : Problem) : Bool :=
  match p.vars with
  | .fvar _ :: _ => true
  | _            => false

private def hasAsPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | .as .. :: _ => true
    | _           => false

private def hasCtorPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | .ctor .. :: _ => true
    | _             => false

private def hasValPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | .val _ :: _ => true
    | _           => false

private def hasNatValPattern (p : Problem) : MetaM Bool :=
  p.alts.anyM fun alt => do
    match alt.patterns with
    | .val v :: _ => return (← getNatValue? v).isSome
    | _           => return false

private def hasIntValPattern (p : Problem) : MetaM Bool :=
  p.alts.anyM fun alt => do
    match alt.patterns with
    | .val v :: _ => return (← getIntValue? v).isSome
    | _           => return false

private def hasVarPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | .var _ :: _ => true
    | _           => false

private def hasArrayLitPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | .arrayLit .. :: _ => true
    | _                 => false

private def isVariableTransition (p : Problem) : Bool :=
  p.alts.all fun alt => match alt.patterns with
    | .inaccessible _ :: _ => true
    | .var _ :: _          => true
    | _                    => false

private def isConstructorTransition (p : Problem) : Bool :=
  (hasCtorPattern p || p.alts.isEmpty)
  && p.alts.all fun alt => match alt.patterns with
     | .ctor .. :: _        => true
     | .var _ :: _          => true
     | .inaccessible _ :: _ => true
     | _                    => false

private def isValueTransition (p : Problem) : Bool :=
  hasVarPattern p && hasValPattern p
  && p.alts.all fun alt => match alt.patterns with
     | .val _ :: _ => true
     | .var _ :: _ => true
     | _           => false

private def isValueOnlyTransitionCore (p : Problem) (isValue : Expr → MetaM Bool) : MetaM Bool := do
  if hasVarPattern p then return false
  if !hasValPattern p then return false
  p.alts.allM fun alt => do
     match alt.patterns with
     | .val v :: _   => isValue v
     | .ctor .. :: _ => return true
     | _             => return false

private def isFinValueTransition (p : Problem) : MetaM Bool :=
  isValueOnlyTransitionCore p fun e => return (← getFinValue? e).isSome

private def isBitVecValueTransition (p : Problem) : MetaM Bool :=
  isValueOnlyTransitionCore p fun e => return (← getBitVecValue? e).isSome

private def isArrayLitTransition (p : Problem) : Bool :=
  hasArrayLitPattern p && hasVarPattern p
  && p.alts.all fun alt => match alt.patterns with
     | .arrayLit .. :: _ => true
     | .var _ :: _       => true
     | _                 => false

private def hasCtorOrInaccessible (p : Problem) : Bool :=
  !isNextVar p ||
    p.alts.any fun alt => match alt.patterns with
    | .ctor .. :: _        => true
    | .inaccessible _ :: _ => true
    | _                    => false

private def isNatValueTransition (p : Problem) : MetaM Bool := do
  unless (← hasNatValPattern p) do return false
  return hasCtorOrInaccessible p

/--
Predicate for testing whether we need to expand `Int` value patterns into constructors.
There are two cases:
- We have constructor or inaccessible patterns. Example:
```
| 0, ...
| Int.toVal p, ...
...
```
- We don't have the `else`-case (i.e., variable pattern). This can happen
when the non-value cases are unreachable.
-/
private def isIntValueTransition (p : Problem) : MetaM Bool := do
  unless (← hasIntValPattern p) do return false
  return hasCtorOrInaccessible p || !hasVarPattern p

private def processSkipInaccessible (p : Problem) : Problem := Id.run do
  let x :: xs := p.vars | unreachable!
  let alts := p.alts.map fun alt => Id.run do
    let .inaccessible e :: ps := alt.patterns | unreachable!
    { alt with patterns := ps, cnstrs := (x, e) :: alt.cnstrs }
  { p with alts := alts, vars := xs }

/--
If constraint is of the form `e ≋ x` where `x` is a free variable, reorient it
as `x ≋ e` If
- `x` is an `alt`-local declaration
- `e` is not a free variable.
-/
private def reorientCnstrs (alt : Alt) : Alt :=
  let cnstrs := alt.cnstrs.map fun (lhs, rhs) =>
    if rhs.isFVar && alt.isLocalDecl rhs.fvarId! then
      (rhs, lhs)
    else if !lhs.isFVar && rhs.isFVar then
      (rhs, lhs)
    else
      (lhs, rhs)
  { alt with cnstrs }

/--
Remove constraints of the form `lhs ≋ rhs` where `lhs` and `rhs` are definitionally equal,
or `lhs` is a free variable.
-/
private def filterTrivialCnstrs (alt : Alt) : MetaM Alt := do
   let cnstrs ← withExistingLocalDecls alt.fvarDecls do
     alt.cnstrs.filterM fun (lhs, rhs) => do
       if (← isDefEqGuarded lhs rhs) then
         return false
       else if lhs.isFVar then
         return false
       else
         return true
   return { alt with cnstrs }

/--
Find an alternative constraint of the form `x ≋ e` where `x` is an alternative
local declarations, and `x` and `e` have definitionally equal types.
Then, replace `x` with `e` in the alternative, and return it.
Return `none` if the alternative does not contain a constraint of this form.
-/
private def solveSomeLocalFVarIdCnstr? (alt : Alt) : MetaM (Option Alt) :=
  withExistingLocalDecls alt.fvarDecls do
    let (some (fvarId, val), cnstrs) ← go alt.cnstrs | return none
    trace[Meta.Match.match] "found cnstr to solve {mkFVar fvarId} ↦ {val}"
    return some <| { alt with cnstrs }.replaceFVarId fvarId val
where
  go (cnstrs : List (Expr × Expr)) := do
    match cnstrs with
    | [] => return (none, [])
    | (lhs, rhs) :: cnstrs =>
      if lhs.isFVar && alt.isLocalDecl lhs.fvarId! then
        if !(← dependsOn rhs lhs.fvarId!) && (← isDefEqGuarded (← inferType lhs) (← inferType rhs)) then
          return (some (lhs.fvarId!, rhs), cnstrs)
      let (p, cnstrs) ← go cnstrs
      return (p, (lhs, rhs) :: cnstrs)

/--
Solve pending alternative constraints. If all constraints can be solved perform assignment
`mvarId := alt.rhs`, and return true.
-/
private partial def solveCnstrs (mvarId : MVarId) (alt : Alt) : StateRefT State MetaM Bool := do
  go (reorientCnstrs alt)
where
  go (alt : Alt) : StateRefT State MetaM Bool := do
    match (← solveSomeLocalFVarIdCnstr? alt) with
    | some alt => go alt
    | none =>
      let alt ← filterTrivialCnstrs alt
      if alt.cnstrs.isEmpty then
        let eType ← inferType alt.rhs
        let targetType ← mvarId.getType
        unless (← isDefEqGuarded targetType eType) do
          trace[Meta.Match.match] "assignGoalOf failed {eType} =?= {targetType}"
          throwError "dependent elimination failed, type mismatch when solving alternative with type{indentExpr eType}\nbut expected{indentExpr targetType}"
        mvarId.assign alt.rhs
        modify fun s => { s with used := s.used.insert alt.idx }
        return true
      else
        trace[Meta.Match.match] "alt has unsolved cnstrs:\n{← alt.toMessageData}"
        return false

/--
Try to solve the problem by using the first alternative whose pending constraints can be resolved.
-/
private def processLeaf (p : Problem) : StateRefT State MetaM Unit :=
  p.mvarId.withContext do
    trace[Meta.Match.match] "local context at processLeaf:\n{(← mkFreshTypeMVar).mvarId!}"
    go p.alts
where
  go (alts : List Alt) : StateRefT State MetaM Unit := do
    match alts with
    | [] =>
      /- TODO: allow users to configure which tactic is used to close leaves. -/
      unless (← p.mvarId.contradictionCore {}) do
        trace[Meta.Match.match] "missing alternative"
        p.mvarId.admit
        modify fun s => { s with counterExamples := p.examples :: s.counterExamples }
    | alt :: alts =>
      unless (← solveCnstrs p.mvarId alt) do
        go alts

private def processAsPattern (p : Problem) : MetaM Problem := withGoalOf p do
  let x :: _ := p.vars | unreachable!
  let alts ← p.alts.mapM fun alt => do
    match alt.patterns with
    | .as fvarId p h :: ps =>
      /- We used to use `checkAndReplaceFVarId` here, but `x` and `fvarId` may have different types
        when dependent types are being used. Let's consider the repro for issue #471
        ```
        inductive vec : Nat → Type
        | nil : vec 0
        | cons : Int → vec n → vec n.succ

        def vec_len : vec n → Nat
        | vec.nil => 0
        | x@(vec.cons h t) => vec_len t + 1

        ```
        we reach the state
        ```
          [Meta.Match.match] remaining variables: [x✝:(vec n✝)]
          alternatives:
            [n:(Nat), x:(vec (Nat.succ n)), h:(Int), t:(vec n)] |- [x@(vec.cons n h t)] => h_1 n x h t
            [x✝:(vec n✝)] |- [x✝] => h_2 n✝ x✝
        ```
        The variables `x✝:(vec n✝)` and `x:(vec (Nat.succ n))` have different types, but we perform the substitution anyway,
        because we claim the "discrepancy" will be corrected after we process the pattern `(vec.cons n h t)`.
        The right-hand-side is temporarily type incorrect, but we claim this is fine because it will be type correct again after
        we the pattern `(vec.cons n h t)`. TODO: try to find a cleaner solution.
       -/
      let r ← mkEqRefl x
      return { alt with patterns := p :: ps }.replaceFVarId fvarId x |>.replaceFVarId h r
    | _ => return alt
  return { p with alts := alts }

private def processVariable (p : Problem) : MetaM Problem := withGoalOf p do
  let x :: xs := p.vars | unreachable!
  let alts ← p.alts.mapM fun alt => do
    match alt.patterns with
    | .inaccessible e :: ps => return { alt with patterns := ps, cnstrs := (x, e) :: alt.cnstrs }
    | .var fvarId :: ps     =>
      withExistingLocalDecls alt.fvarDecls do
        if (← isDefEqGuarded (← fvarId.getType) (← inferType x)) then
          return { alt with patterns := ps }.replaceFVarId fvarId x
        else
          return { alt with patterns := ps, cnstrs := (mkFVar fvarId, x) :: alt.cnstrs }
    | _  => unreachable!
  return { p with alts := alts, vars := xs }

/-!
Note that we decided to store pending constraints to address issues exposed by #1279 and #1361.
Here is a simplified version of the example on this issue (see test: `1279_simplified.lean`)
```lean
inductive Arrow : Type → Type → Type 1
  | id   : Arrow a a
  | unit : Arrow Unit Unit
  | comp : Arrow β γ → Arrow α β → Arrow α γ
deriving Repr

def Arrow.compose (f : Arrow β γ) (g : Arrow α β) : Arrow α γ :=
  match f, g with
  | id, g => g
  | f, id => f
  | f, g => comp f g
```
The initial state for the `match`-expression above is
```lean
[Meta.Match.match] remaining variables: [β✝:(Type), γ✝:(Type), f✝:(Arrow β✝ γ✝), g✝:(Arrow α β✝)]
alternatives:
  [β:(Type), g:(Arrow α β)] |- [β, .(β), (Arrow.id .(β)), g] => h_1 β g
  [γ:(Type), f:(Arrow α γ)] |- [.(α), γ, f, (Arrow.id .(α))] => h_2 γ f
  [β:(Type), γ:(Type), f:(Arrow β γ), g:(Arrow α β)] |- [β, γ, f, g] => h_3 β γ f g
```
The first step is a variable-transition which replaces `β` with `β✝` in the first and third alternatives.
The constraint `β✝ ≋ α` in the second alternative used to be discarded. We now store it at the
alternative `cnstrs` field.
-/

private def inLocalDecls (localDecls : List LocalDecl) (fvarId : FVarId) : Bool :=
  localDecls.any fun d => d.fvarId == fvarId

private def expandVarIntoCtor? (alt : Alt) (fvarId : FVarId) (ctorName : Name) : MetaM (Option Alt) :=
  withExistingLocalDecls alt.fvarDecls do
    trace[Meta.Match.unify] "expandVarIntoCtor? fvarId: {mkFVar fvarId}, ctorName: {ctorName}, alt:\n{← alt.toMessageData}"
    let expectedType ← inferType (mkFVar fvarId)
    let expectedType ← whnfD expectedType
    let (ctorLevels, ctorParams) ← getInductiveUniverseAndParams expectedType
    let ctor := mkAppN (mkConst ctorName ctorLevels) ctorParams
    let ctorType ← inferType ctor
    forallTelescopeReducing ctorType fun ctorFields resultType => do
      let ctor := mkAppN ctor ctorFields
      let alt  := alt.replaceFVarId fvarId ctor
      let ctorFieldDecls ← ctorFields.mapM fun ctorField => ctorField.fvarId!.getDecl
      let newAltDecls := ctorFieldDecls.toList ++ alt.fvarDecls
      let mut cnstrs := alt.cnstrs
      unless (← isDefEqGuarded resultType expectedType) do
         cnstrs := (resultType, expectedType) :: cnstrs
      trace[Meta.Match.unify] "expandVarIntoCtor? {mkFVar fvarId} : {expectedType}, ctor: {ctor}"
      let ctorFieldPatterns := ctorFieldDecls.toList.map fun decl => Pattern.var decl.fvarId
      return some { alt with fvarDecls := newAltDecls, patterns := ctorFieldPatterns ++ alt.patterns, cnstrs }

private def getInductiveVal? (x : Expr) : MetaM (Option InductiveVal) := do
  let xType ← inferType x
  let xType ← whnfD xType
  match xType.getAppFn with
  | Expr.const constName _ =>
    let cinfo ← getConstInfo constName
    match cinfo with
    | ConstantInfo.inductInfo val => return some val
    | _ => return none
  | _ => return none

private def hasRecursiveType (x : Expr) : MetaM Bool := do
  match (← getInductiveVal? x) with
  | some val => return val.isRec
  | _        => return false

/-- Given `alt` s.t. the next pattern is an inaccessible pattern `e`,
   try to normalize `e` into a constructor application.
   If it is not a constructor, throw an error.
   Otherwise, if it is a constructor application of `ctorName`,
   update the next patterns with the fields of the constructor.
   Otherwise, return none. -/
def processInaccessibleAsCtor (alt : Alt) (ctorName : Name) : MetaM (Option Alt) := do
  match alt.patterns with
  | p@(.inaccessible e) :: ps =>
    trace[Meta.Match.match] "inaccessible in ctor step {e}"
    withExistingLocalDecls alt.fvarDecls do
      -- Try to push inaccessible annotations.
      let e ← whnfD e
      match (← constructorApp? e) with
      | some (ctorVal, ctorArgs) =>
        if ctorVal.name == ctorName then
          let fields := ctorArgs.extract ctorVal.numParams ctorArgs.size
          let fields := fields.toList.map .inaccessible
          return some { alt with patterns := fields ++ ps }
        else
          return none
      | _ => throwErrorAt alt.ref "dependent match elimination failed, inaccessible pattern found{indentD p.toMessageData}\nconstructor expected"
  | _ => unreachable!

private def hasNonTrivialExample (p : Problem) : Bool :=
  p.examples.any fun | Example.underscore => false | _ => true

private def throwCasesException (p : Problem) (ex : Exception) : MetaM α := do
  match ex with
  | .error ref msg =>
    let exampleMsg :=
      if hasNonTrivialExample p then m!" after processing{indentD <| examplesToMessageData p.examples}" else ""
    throw <| Exception.error ref <| m!"{msg}{exampleMsg}\n" ++
              "the dependent pattern matcher can solve the following kinds of equations\n" ++
              "- <var> = <term> and <term> = <var>\n" ++
              "- <term> = <term> where the terms are definitionally equal\n" ++
              "- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil"
  | _ => throw ex

private def processConstructor (p : Problem) : MetaM (Array Problem) := do
  trace[Meta.Match.match] "constructor step"
  let x :: xs := p.vars | unreachable!
  let subgoals? ← commitWhenSome? do
     let subgoals ←
       try
         p.mvarId.cases x.fvarId!
       catch ex =>
         if p.alts.isEmpty then
           /- If we have no alternatives and dependent pattern matching fails, then a "missing cases" error is better than a "stuck" error message. -/
           return none
         else
           throwCasesException p ex
     if subgoals.isEmpty then
       /- Easy case: we have solved problem `p` since there are no subgoals -/
       return some #[]
     else if !p.alts.isEmpty then
       return some subgoals
     else do
       let isRec ← withGoalOf p <| hasRecursiveType x
        /- If there are no alternatives and the type of the current variable is recursive, we do NOT consider
          a constructor-transition to avoid nontermination.
          TODO: implement a more general approach if this is not sufficient in practice -/
       if isRec then
         return none
       else
         return some subgoals
  let some subgoals := subgoals? | return #[{ p with vars := xs }]
  subgoals.mapM fun subgoal => subgoal.mvarId.withContext do
    let subst    := subgoal.subst
    let fields   := subgoal.fields.toList
    let newVars  := fields ++ xs
    let newVars  := newVars.map fun x => x.applyFVarSubst subst
    let subex    := Example.ctor subgoal.ctorName <| fields.map fun field => match field with
      | .fvar fvarId => Example.var fvarId
      | _            => Example.underscore -- This case can happen due to dependent elimination
    let examples := p.examples.map <| Example.replaceFVarId x.fvarId! subex
    let examples := examples.map <| Example.applyFVarSubst subst
    let newAlts  := p.alts.filter fun alt => match alt.patterns with
      | .ctor n .. :: _       => n == subgoal.ctorName
      | .var _ :: _           => true
      | .inaccessible _ :: _  => true
      | _                     => false
    let newAlts  := newAlts.map fun alt => alt.applyFVarSubst subst
    let newAlts ← newAlts.filterMapM fun alt => do
      match alt.patterns with
      | .ctor _ _ _ fields :: ps  => return some { alt with patterns := fields ++ ps }
      | .var fvarId :: ps         => expandVarIntoCtor? { alt with patterns := ps } fvarId subgoal.ctorName
      | .inaccessible _ :: _      => processInaccessibleAsCtor alt subgoal.ctorName
      | _                         => unreachable!
    return { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }

private def altsAreCtorLike (p : Problem) : MetaM Bool := withGoalOf p do
  p.alts.allM fun alt => do match alt.patterns with
    | .ctor .. :: _ => return true
    | .inaccessible e :: _ => isConstructorApp e
    | _ => return false

private def processNonVariable (p : Problem) : MetaM Problem := withGoalOf p do
  let x :: xs := p.vars | unreachable!
  if let some (ctorVal, xArgs) ← withTransparency .default <| constructorApp'? x then
    if (← altsAreCtorLike p) then
      let alts ← p.alts.filterMapM fun alt => do
        match alt.patterns with
        | .ctor ctorName _ _ fields :: ps   =>
          if ctorName != ctorVal.name then
            return none
          else
            return some { alt with patterns := fields ++ ps }
        | .inaccessible _ :: _ => processInaccessibleAsCtor alt ctorVal.name
        | _ => unreachable!
      let xFields := xArgs.extract ctorVal.numParams xArgs.size
      return { p with alts := alts, vars := xFields.toList ++ xs }
  let alts ← p.alts.mapM fun alt => do
    match alt.patterns with
    | p :: ps => return { alt with patterns := ps, cnstrs := (x, ← p.toExpr) :: alt.cnstrs }
    | _      => unreachable!
  return { p with alts := alts, vars := xs }

private def collectValues (p : Problem) : Array Expr :=
  p.alts.foldl (init := #[]) fun values alt =>
    match alt.patterns with
    | .val v :: _ => if values.contains v then values else values.push v
    | _           => values

private def isFirstPatternVar (alt : Alt) : Bool :=
  match alt.patterns with
  | .var _ :: _ => true
  | _           => false

private def processValue (p : Problem) : MetaM (Array Problem) := do
  trace[Meta.Match.match] "value step"
  let x :: xs := p.vars | unreachable!
  let values := collectValues p
  let subgoals ← caseValues p.mvarId x.fvarId! values (substNewEqs := true)
  subgoals.mapIdxM fun i subgoal => do
    trace[Meta.Match.match] "processValue subgoal\n{MessageData.ofGoal subgoal.mvarId}"
    if h : i < values.size then
      let value := values[i]
      -- (x = value) branch
      let subst := subgoal.subst
      trace[Meta.Match.match] "processValue subst: {subst.map.toList.map fun p => mkFVar p.1}, {subst.map.toList.map fun p => p.2}"
        let examples := p.examples.map <| Example.replaceFVarId x.fvarId! (Example.val value)
      let examples := examples.map <| Example.applyFVarSubst subst
      let newAlts  := p.alts.filter fun alt => match alt.patterns with
        | .val v :: _ => v == value
        | .var _ :: _ => true
        | _           => false
      let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst
      let newAlts := newAlts.map fun alt => match alt.patterns with
        | .val _ :: ps      => { alt with patterns := ps }
        | .var fvarId :: ps =>
          let alt := { alt with patterns := ps }
          alt.replaceFVarId fvarId value
        | _  => unreachable!
      let newVars := xs.map fun x => x.applyFVarSubst subst
      return { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }
    else
      -- else branch for value
      let newAlts := p.alts.filter isFirstPatternVar
      return { p with mvarId := subgoal.mvarId, alts := newAlts, vars := x::xs }

private def collectArraySizes (p : Problem) : Array Nat :=
  p.alts.foldl (init := #[]) fun sizes alt =>
    match alt.patterns with
    | .arrayLit _ ps :: _ => let sz := ps.length; if sizes.contains sz then sizes else sizes.push sz
    | _                   => sizes

private def expandVarIntoArrayLit (alt : Alt) (fvarId : FVarId) (arrayElemType : Expr) (arraySize : Nat) : MetaM Alt :=
  withExistingLocalDecls alt.fvarDecls do
    let fvarDecl ← fvarId.getDecl
    let varNamePrefix := fvarDecl.userName
    let rec loop (n : Nat) (newVars : Array Expr) := do
      match n with
      | n+1 =>
        withLocalDeclD (varNamePrefix.appendIndexAfter (n+1)) arrayElemType fun x =>
          loop n (newVars.push x)
      | 0 =>
        let arrayLit ← mkArrayLit arrayElemType newVars.toList
        let alt := alt.replaceFVarId fvarId arrayLit
        let newDecls ← newVars.toList.mapM fun newVar => newVar.fvarId!.getDecl
        let newPatterns := newVars.toList.map fun newVar => .var newVar.fvarId!
        return { alt with fvarDecls := newDecls ++ alt.fvarDecls, patterns := newPatterns ++ alt.patterns }
    loop arraySize #[]

private def processArrayLit (p : Problem) : MetaM (Array Problem) := do
  trace[Meta.Match.match] "array literal step"
  let x :: xs := p.vars | unreachable!
  let sizes := collectArraySizes p
  let subgoals ← caseArraySizes p.mvarId x.fvarId! sizes
  subgoals.mapIdxM fun i subgoal => do
    if i < sizes.size then
      let size     := sizes.get! i
      let subst    := subgoal.subst
      let elems    := subgoal.elems.toList
      let newVars  := elems.map mkFVar ++ xs
      let newVars  := newVars.map fun x => x.applyFVarSubst subst
      let subex    := Example.arrayLit <| elems.map Example.var
      let examples := p.examples.map <| Example.replaceFVarId x.fvarId! subex
      let examples := examples.map <| Example.applyFVarSubst subst
      let newAlts  := p.alts.filter fun alt => match alt.patterns with
        | .arrayLit _ ps :: _ => ps.length == size
        | .var _ :: _         => true
        | _                          => false
      let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst
      let newAlts ← newAlts.mapM fun alt => do
        match alt.patterns with
        | .arrayLit _ pats :: ps => return { alt with patterns := pats ++ ps }
        | .var fvarId :: ps      =>
          let α ← getArrayArgType <| subst.apply x
          expandVarIntoArrayLit { alt with patterns := ps } fvarId α size
        | _  => unreachable!
      return { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }
    else
      -- else branch
      let newAlts := p.alts.filter isFirstPatternVar
      return { p with mvarId := subgoal.mvarId, alts := newAlts, vars := x::xs }

private def expandNatValuePattern (p : Problem) : MetaM Problem := do
  let alts ← p.alts.mapM fun alt => do
    match alt.patterns with
    | .val n :: ps =>
      match (← getNatValue? n) with
      | some 0     => return { alt with patterns := .ctor ``Nat.zero [] [] [] :: ps }
      | some (n+1) => return { alt with patterns := .ctor ``Nat.succ [] [] [.val (toExpr n)] :: ps }
      | _ => return alt
    | _ => return alt
  return { p with alts := alts }

private def expandIntValuePattern (p : Problem) : MetaM Problem := do
  let alts ← p.alts.mapM fun alt => do
    match alt.patterns with
    | .val n :: ps =>
      match (← getIntValue? n) with
      | some i =>
        if i >= 0 then
        return { alt with patterns := .ctor ``Int.ofNat [] [] [.val (toExpr i.toNat)] :: ps }
        else
        return { alt with patterns := .ctor ``Int.negSucc [] [] [.val (toExpr (-(i + 1)).toNat)] :: ps }
      | _ => return alt
    | _ => return alt
  return { p with alts := alts }

private def expandFinValuePattern (p : Problem) : MetaM Problem := do
  let alts ← p.alts.mapM fun alt => do
    let .val n :: ps := alt.patterns | return alt
    let some ⟨n, v⟩ ← getFinValue? n | return alt
    let p ← mkLt (toExpr v.val) (toExpr n)
    let h ← mkDecideProof p
    return { alt with patterns := .ctor ``Fin.mk [] [toExpr n] [.val (toExpr v.val), .inaccessible h] :: ps }
  return { p with alts := alts }

private def expandBitVecValuePattern (p : Problem) : MetaM Problem := do
  let alts ← p.alts.mapM fun alt => do
    let .val n :: ps := alt.patterns | return alt
    let some ⟨_, v⟩ ← getBitVecValue? n | return alt
    return { alt with patterns := .ctor ``BitVec.ofFin [] [] [.val (toExpr v.toFin)] :: ps }
  return { p with alts := alts }

private def traceStep (msg : String) : StateRefT State MetaM Unit := do
  trace[Meta.Match.match] "{msg} step"

private def traceState (p : Problem) : MetaM Unit :=
  withGoalOf p (traceM `Meta.Match.match p.toMessageData)

private def throwNonSupported (p : Problem) : MetaM Unit :=
  withGoalOf p do
    let msg ← p.toMessageData
    throwError "failed to compile pattern matching, stuck at{indentD msg}"

def isCurrVarInductive (p : Problem) : MetaM Bool := do
  match p.vars with
  | []   => return false
  | x::_ => withGoalOf p do
    let val? ← getInductiveVal? x
    return val?.isSome

private def checkNextPatternTypes (p : Problem) : MetaM Unit := do
  match p.vars with
  | []   => return ()
  | x::_ => withGoalOf p do
    for alt in p.alts do
      withRef alt.ref do
        match alt.patterns with
        | []   => return ()
        | p::_ =>
          let e ← p.toExpr
          let xType ← inferType x
          let eType ← inferType e
          unless (← isDefEq xType eType) do
            throwError "pattern{indentExpr e}\n{← mkHasTypeButIsExpectedMsg eType xType}"

private partial def process (p : Problem) : StateRefT State MetaM Unit := do
  traceState p
  let isInductive ← isCurrVarInductive p
  if isDone p then
    traceStep ("leaf")
    processLeaf p
  else if hasAsPattern p then
    traceStep ("as-pattern")
    let p ← processAsPattern p
    process p
  else if (← isNatValueTransition p) then
    traceStep ("nat value to constructor")
    process (← expandNatValuePattern p)
  else if (← isIntValueTransition p) then
    traceStep ("int value to constructor")
    process (← expandIntValuePattern p)
  else if (← isFinValueTransition p) then
    traceStep ("fin value to constructor")
    process (← expandFinValuePattern p)
  else if (← isBitVecValueTransition p) then
    traceStep ("bitvec value to constructor")
    process (← expandBitVecValuePattern p)
  else if !isNextVar p then
    traceStep ("non variable")
    let p ← processNonVariable p
    process p
  else if isInductive && isConstructorTransition p then
    let ps ← processConstructor p
    ps.forM process
  else if isVariableTransition p then
    traceStep ("variable")
    let p ← processVariable p
    process p
  else if isValueTransition p then
    let ps ← processValue p
    ps.forM process
  else if isArrayLitTransition p then
    let ps ← processArrayLit p
    ps.forM process
  else if (← hasNatValPattern p) then
    -- This branch is reachable when `p`, for example, is just values without an else-alternative.
    -- We added it just to get better error messages.
    traceStep ("nat value to constructor")
    process (← expandNatValuePattern p)
  else
    checkNextPatternTypes p
    throwNonSupported p

private def getUElimPos? (matcherLevels : List Level) (uElim : Level) : MetaM (Option Nat) :=
  if uElim == levelZero then
    return none
  else match matcherLevels.toArray.indexOf? uElim with
    | none => throwError "dependent match elimination failed, universe level not found"
    | some pos => return some pos.val

/- See comment at `mkMatcher` before `mkAuxDefinition` -/
register_builtin_option bootstrap.genMatcherCode : Bool := {
  defValue := true
  group := "bootstrap"
  descr := "disable code generation for auxiliary matcher function"
}

builtin_initialize matcherExt : EnvExtension (PHashMap (Expr × Bool) Name) ← registerEnvExtension (pure {})

/-- Similar to `mkAuxDefinition`, but uses the cache `matcherExt`.
   It also returns an Boolean that indicates whether a new matcher function was added to the environment or not. -/
def mkMatcherAuxDefinition (name : Name) (type : Expr) (value : Expr) : MetaM (Expr × Option (MatcherInfo → MetaM Unit)) := do
  trace[Meta.Match.debug] "{name} : {type} := {value}"
  let compile := bootstrap.genMatcherCode.get (← getOptions)
  let result ← Closure.mkValueTypeClosure type value (zetaDelta := false)
  let env ← getEnv
  let mkMatcherConst name :=
    mkAppN (mkConst name result.levelArgs.toList) result.exprArgs
  match (matcherExt.getState env).find? (result.value, compile) with
  | some nameNew => return (mkMatcherConst nameNew, none)
  | none =>
    let decl := Declaration.defnDecl (← mkDefinitionValInferrringUnsafe name result.levelParams.toList
      result.type result.value .abbrev)
    trace[Meta.Match.debug] "{name} : {result.type} := {result.value}"
    let addMatcher : MatcherInfo → MetaM Unit := fun mi => do
      addDecl decl
      modifyEnv fun env => matcherExt.modifyState env fun s => s.insert (result.value, compile) name
      addMatcherInfo name mi
      setInlineAttribute name
      if compile then
        compileDecl decl
    return (mkMatcherConst name, some addMatcher)

structure MkMatcherInput where
  matcherName : Name
  matchType   : Expr
  discrInfos  : Array DiscrInfo
  lhss        : List AltLHS

def MkMatcherInput.numDiscrs (m : MkMatcherInput) :=
  m.discrInfos.size

def MkMatcherInput.collectFVars (m : MkMatcherInput) : StateRefT CollectFVars.State MetaM Unit := do
  m.matchType.collectFVars
  m.lhss.forM fun alt => alt.collectFVars

def MkMatcherInput.collectDependencies (m : MkMatcherInput) : MetaM FVarIdSet := do
  let (_, s) ← m.collectFVars |>.run {}
  let s ← s.addDependencies
  return s.fvarSet

/--
Auxiliary method used at `mkMatcher`. It executes `k` in a local context that contains only
the local declarations `m` depends on. This is important because otherwise dependent elimination
may "refine" the types of unnecessary declarations and accidentally introduce unnecessary dependencies
in the auto-generated auxiliary declaration. Note that this is not just an optimization because the
unnecessary dependencies may prevent the termination checker from succeeding. For an example,
see issue #1237.
-/
def withCleanLCtxFor (m : MkMatcherInput) (k : MetaM α) : MetaM α := do
  let s ← m.collectDependencies
  let lctx ← getLCtx
  let lctx := lctx.foldr (init := lctx) fun localDecl lctx =>
    if s.contains localDecl.fvarId then lctx else lctx.erase localDecl.fvarId
  let localInstances := (← getLocalInstances).filter fun localInst => s.contains localInst.fvar.fvarId!
  withLCtx lctx localInstances k

/--
Create a dependent matcher for `matchType` where `matchType` is of the form
`(a_1 : A_1) -> (a_2 : A_2[a_1]) -> ... -> (a_n : A_n[a_1, a_2, ... a_{n-1}]) -> B[a_1, ..., a_n]`
where `n = numDiscrs`, and the `lhss` are the left-hand-sides of the `match`-expression alternatives.
Each `AltLHS` has a list of local declarations and a list of patterns.
The number of patterns must be the same in each `AltLHS`.
The generated matcher has the structure described at `MatcherInfo`. The motive argument is of the form
`(motive : (a_1 : A_1) -> (a_2 : A_2[a_1]) -> ... -> (a_n : A_n[a_1, a_2, ... a_{n-1}]) -> Sort v)`
where `v` is a universe parameter or 0 if `B[a_1, ..., a_n]` is a proposition.

If `exceptionIfContainsSorry := true`, then `mkMatcher` throws an exception if the auxiliary
declarations contains a `sorry`. We use this argument to workaround a bug at `IndPredBelow.mkBelowMatcher`.
-/
def mkMatcher (input : MkMatcherInput) (exceptionIfContainsSorry := false) : MetaM MatcherResult := withCleanLCtxFor input do
  let ⟨matcherName, matchType, discrInfos, lhss⟩ := input
  let numDiscrs := discrInfos.size
  let numEqs := getNumEqsFromDiscrInfos discrInfos
  checkNumPatterns numDiscrs lhss
  forallBoundedTelescope matchType numDiscrs fun discrs matchTypeBody => do
  /- We generate an matcher that can eliminate using different motives with different universe levels.
     `uElim` is the universe level the caller wants to eliminate to.
     If it is not levelZero, we create a matcher that can eliminate in any universe level.
     This is useful for implementing `MatcherApp.addArg` because it may have to change the universe level. -/
  let uElim ← getLevel matchTypeBody
  let uElimGen ← if uElim == levelZero then pure levelZero else mkFreshLevelMVar
  let mkMatcher (type val : Expr) (minors : Array (Expr × Nat)) (s : State) : MetaM MatcherResult := do
    let val ← instantiateMVars val
    let type ← instantiateMVars type
    if exceptionIfContainsSorry then
      if type.hasSorry || val.hasSorry then
        throwError "failed to create auxiliary match declaration `{matcherName}`, it contains `sorry`"
    trace[Meta.Match.debug] "matcher value: {val}\ntype: {type}"
    trace[Meta.Match.debug] "minors num params: {minors.map (·.2)}"
    /- The option `bootstrap.gen_matcher_code` is a helper hack. It is useful, for example,
       for compiling `src/Init/Data/Int`. It is needed because the compiler uses `Int.decLt`
       for generating code for `Int.casesOn` applications, but `Int.casesOn` is used to
       give the reference implementation for
       ```
       @[extern "lean_int_neg"] def neg (n : @& Int) : Int :=
       match n with
       | ofNat n   => negOfNat n
       | negSucc n => succ n
       ```
       which is defined **before** `Int.decLt` -/
    let (matcher, addMatcher) ← mkMatcherAuxDefinition matcherName type val
    trace[Meta.Match.debug] "matcher levels: {matcher.getAppFn.constLevels!}, uElim: {uElimGen}"
    let uElimPos? ← getUElimPos? matcher.getAppFn.constLevels! uElimGen
    discard <| isLevelDefEq uElimGen uElim
    let addMatcher :=
      match addMatcher with
      | some addMatcher => addMatcher <|
        { numParams := matcher.getAppNumArgs
          altNumParams := minors.map fun minor => minor.2 + numEqs
          discrInfos
          numDiscrs
          uElimPos?
          }
      | none => pure ()

    trace[Meta.Match.debug] "matcher: {matcher}"
    let unusedAltIdxs := lhss.length.fold (init := []) fun i r =>
      if s.used.contains i then r else i::r
    return {
      matcher,
      counterExamples := s.counterExamples,
      unusedAltIdxs := unusedAltIdxs.reverse,
      addMatcher
    }

  let motiveType ← mkForallFVars discrs (mkSort uElimGen)
  trace[Meta.Match.debug] "motiveType: {motiveType}"
  withLocalDeclD `motive motiveType fun motive => do
  if discrInfos.any fun info => info.hName?.isSome then
    forallBoundedTelescope matchType numDiscrs fun discrs' _ => do
    let (mvarType, isEqMask) ← withEqs discrs discrs' discrInfos fun eqs => do
      let mvarType ← mkForallFVars eqs (mkAppN motive discrs')
      let isEqMask ← eqs.mapM fun eq => return (← inferType eq).isEq
      return (mvarType, isEqMask)
    trace[Meta.Match.debug] "target: {mvarType}"
    withAlts motive discrs discrInfos lhss fun alts minors => do
      let mvar ← mkFreshExprMVar mvarType
      trace[Meta.Match.debug] "goal\n{mvar.mvarId!}"
      let examples := discrs'.toList.map fun discr => Example.var discr.fvarId!
      let (_, s) ← (process { mvarId := mvar.mvarId!, vars := discrs'.toList, alts := alts, examples := examples }).run {}
      let val ← mkLambdaFVars discrs' mvar
      trace[Meta.Match.debug] "matcher\nvalue: {val}\ntype: {← inferType val}"
      let mut rfls := #[]
      let mut isEqMaskIdx := 0
      for discr in discrs, info in discrInfos do
        if info.hName?.isSome then
          if isEqMask[isEqMaskIdx]! then
            rfls := rfls.push (← mkEqRefl discr)
          else
            rfls := rfls.push (← mkHEqRefl discr)
          isEqMaskIdx := isEqMaskIdx + 1
      let val := mkAppN (mkAppN val discrs) rfls
      let args := #[motive] ++ discrs ++ minors.map Prod.fst
      let val ← mkLambdaFVars args val
      let type ← mkForallFVars args (mkAppN motive discrs)
      mkMatcher type val minors s
  else
    let mvarType  := mkAppN motive discrs
    trace[Meta.Match.debug] "target: {mvarType}"
    withAlts motive discrs discrInfos lhss fun alts minors => do
      let mvar ← mkFreshExprMVar mvarType
      let examples := discrs.toList.map fun discr => Example.var discr.fvarId!
      let (_, s) ← (process { mvarId := mvar.mvarId!, vars := discrs.toList, alts := alts, examples := examples }).run {}
      let args := #[motive] ++ discrs ++ minors.map Prod.fst
      let type ← mkForallFVars args mvarType
      let val  ← mkLambdaFVars args mvar
      mkMatcher type val minors s

def getMkMatcherInputInContext (matcherApp : MatcherApp) : MetaM MkMatcherInput := do
  let matcherName := matcherApp.matcherName
  let some matcherInfo ← getMatcherInfo? matcherName | throwError "not a matcher: {matcherName}"
  let matcherConst ← getConstInfo matcherName
  let matcherType ← instantiateForall matcherConst.type <| matcherApp.params ++ #[matcherApp.motive]
  let matchType ← do
    let u :=
      if let some idx := matcherInfo.uElimPos?
      then mkLevelParam matcherConst.levelParams.toArray[idx]!
      else levelZero
    forallBoundedTelescope matcherType (some matcherInfo.numDiscrs) fun discrs _ => do
    mkForallFVars discrs (mkConst ``PUnit [u])

  let matcherType ← instantiateForall matcherType matcherApp.discrs
  let lhss ← forallBoundedTelescope matcherType (some matcherApp.alts.size) fun alts _ =>
    alts.mapM fun alt => do
    let ty ← inferType alt
    forallTelescope ty fun xs body => do
    let xs ← xs.filterM fun x => dependsOn body x.fvarId!
    body.withApp fun _ args => do
    let ctx ← getLCtx
    let localDecls := xs.map ctx.getFVar!
    let patterns ← args.mapM Match.toPattern
    return {
      ref := Syntax.missing
      fvarDecls := localDecls.toList
      patterns := patterns.toList : Match.AltLHS }

  return { matcherName, matchType, discrInfos := matcherInfo.discrInfos, lhss := lhss.toList }

/-- This function is only used for testing purposes -/
def withMkMatcherInput (matcherName : Name) (k : MkMatcherInput → MetaM α) : MetaM α := do
  let some matcherInfo ← getMatcherInfo? matcherName | throwError "not a matcher: {matcherName}"
  let matcherConst ← getConstInfo matcherName
  forallBoundedTelescope matcherConst.type (some matcherInfo.arity) fun xs _ => do
  let matcherApp ← mkConstWithLevelParams matcherConst.name
  let matcherApp := mkAppN matcherApp xs
  let some matcherApp ← matchMatcherApp? matcherApp | throwError "not a matcher app: {matcherApp}"
  let mkMatcherInput ← getMkMatcherInputInContext matcherApp
  k mkMatcherInput

end Match


builtin_initialize
  registerTraceClass `Meta.Match.match
  registerTraceClass `Meta.Match.debug
  registerTraceClass `Meta.Match.unify

end Lean.Meta
