/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Closure
public import Lean.Meta.Tactic.Contradiction
public import Lean.Meta.GeneralizeTelescope
public import Lean.Meta.Match.Basic
public import Lean.Meta.Match.MatcherApp.Basic
public import Lean.Meta.Match.MVarRenaming
public import Lean.Meta.Match.MVarRenaming
import Lean.Meta.Match.SimpH
import Lean.Meta.Match.SolveOverlap
import Lean.Meta.HasNotBit
import Lean.Meta.Match.CaseArraySizes
import Lean.Meta.Match.CaseValues
import Lean.Meta.Match.NamedPatterns

/-!
This module implements the backend of match compilation. The elaborator has already elaborated
the patterns and the the expected type of the matcher is known.

The match compilation task is represented as a `Problem`, which is then processed interatively by
the `process` function. It has various “moves” which it tries in a particular order, to make progress
on the problem, possibly splitting it.

The high-level overview of moves are
* If no variables are left, process as leaf
  * If there is an alternative, solve its constraints
  * Else use `contradiction` to prove completeness of the match
* Process “independent prefixes” of patterns. These are patterns that can be processed without
  affecting the aother alternatives, and without side effects in the sense of updating the `mvarId`.
  These are
  - variable patterns; substitute
  - inaccessible patterns; add equality constraints
  - as-patterns: substitute value and equality
  After thes have been processed, we use `.inaccessible x` where `x` is the variable being matched
  to mark them as “done”.
* If all patterns start with “done”, drop the first variable
* The first alt has only “done” patterns, drop remaining alts (they're overlapped)
* If the first alternative has its first refutable pattern not at the front, move it to the front.
* If we have both constructor and value patterns, expand the values to constructors.
* If next pattern is not a variable, but an expression, then
  - if it is a constructor, behave a bit as if we just did a case split
  - else move it to constraints
* If we have constructor patterns, or no alternatives, split by constructor
  Use sparse splitting if not all constructors are present
* If match is empty (no alts), drop the variable
* If we have value patterns (e.g. strings), split by value
* If we have array literal patterns, split by array

If we reach this point, the match is not supported.
If only nat value patterns exist, we expand them for better error messages.
Throw error.
-/

public section

namespace Lean.Meta.Match

register_builtin_option backward.match.sparseCases : Bool := {
  defValue := true
  descr := "if true (the default), generate and use sparse case constructs when splitting inductive
    types. In some cases this will prevent Lean from noticing that a match statement is complete
    because it performs less case-splitting for the unreachable case. In this case, give explicit
    patterns to perform the deeper split with `by contradiction` as the right-hand side.
     ,"
}

register_builtin_option backward.match.rowMajor : Bool := {
  defValue := true
  descr := "If true (the default), match compilation will split the discrimnants based \
    on position of the first constructor pattern in the first alternative. If false, \
    it splits them from left to right, which can lead to unnecessary code bloat."
}

private def mkIncorrectNumberOfPatternsMsg [ToMessageData α]
    (discrepancyKind : String) (expected actual : Nat) (pats : List α) :=
  let patternsMsg := MessageData.joinSep (pats.map toMessageData) ", "
  m!"{discrepancyKind} patterns in match alternative: Expected {expected}, \
    but found {actual}:{indentD patternsMsg}"

/--
Throws an error indicating that the alternative at `ref` contains an unexpected number of patterns.
Remark: we allow `α` to be arbitrary because this error may be thrown before or after elaborating
pattern syntax.
-/
def throwIncorrectNumberOfPatternsAt [ToMessageData α]
    (ref : Syntax) (discrepancyKind : String) (expected actual : Nat) (pats : List α)
    : MetaM Unit := do
  throwErrorAt ref (mkIncorrectNumberOfPatternsMsg discrepancyKind expected actual pats)

/--
Logs an error indicating that the alternative at `ref` contains an unexpected number of patterns.
Remark: we allow `α` to be arbitrary because this error may be thrown before or after elaborating
pattern syntax.
-/
def logIncorrectNumberOfPatternsAt [ToMessageData α]
    (ref : Syntax) (discrepancyKind : String) (expected actual : Nat) (pats : List α)
    : MetaM Unit :=
  logErrorAt ref (mkIncorrectNumberOfPatternsMsg discrepancyKind expected actual pats)

/-- The number of patterns in each AltLHS must be equal to the number of discriminants. -/
private def checkNumPatterns (numDiscrs : Nat) (lhss : List AltLHS) : MetaM Unit := do
  for lhs in lhss do
    let doThrow (kind : String) := withExistingLocalDecls lhs.fvarDecls do
      throwIncorrectNumberOfPatternsAt lhs.ref kind numDiscrs lhs.patterns.length
        (lhs.patterns.map Pattern.toMessageData)
    if lhs.patterns.length < numDiscrs then
      doThrow "Not enough"
    else if lhs.patterns.length > numDiscrs then
      -- This case should be impossible, as an alternative with too many patterns will cause an
      -- error to be thrown in `Lean.Elab.Term.elabPatterns`
      doThrow "Too many"

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
private def withAlts {α} (motive : Expr) (discrs : Array Expr) (discrInfos : Array DiscrInfo)
    (lhss : List AltLHS) (isSplitter : Option Overlaps)
    (k : List Alt → Array Expr → Array AltParamInfo → MetaM α) : MetaM α :=
  loop lhss [] #[] #[] #[]
where
  mkSplitterHyps (idx : Nat) (lhs : AltLHS) (notAlts : Array Expr) : MetaM (Array Expr × Array Nat) := do
    withExistingLocalDecls lhs.fvarDecls do
      let patterns ← lhs.patterns.toArray.mapM (Pattern.toExpr · (annotate := true))
      let mut hs := #[]
      let mut notAltIdxs := #[]
      for overlappingIdx in isSplitter.get!.overlapping idx do
        let notAlt := notAlts[overlappingIdx]!
        let h ← instantiateForall notAlt patterns
        if let some h ← simpH? h patterns.size then
          notAltIdxs := notAltIdxs.push overlappingIdx
          hs := hs.push h
      trace[Meta.Match.debug] "hs for {lhs.ref}: {hs}"
      return (hs, notAltIdxs)

  mkMinorType (xs : Array Expr) (lhs : AltLHS) (notAltHs : Array Expr): MetaM Expr :=
    withExistingLocalDecls lhs.fvarDecls do
      let args ← lhs.patterns.toArray.mapM (Pattern.toExpr · (annotate := true))
      let minorType := mkAppN motive args
      withEqs discrs args discrInfos fun eqs => do
        let minorType ← mkForallFVars eqs minorType
        let minorType ← mkArrowN notAltHs minorType
        mkForallFVars xs minorType

  mkNotAlt (xs : Array Expr) (lhs : AltLHS) : MetaM Expr := do
    withExistingLocalDecls lhs.fvarDecls do
      let mut notAlt := mkConst ``False
      for discr in discrs.reverse, pattern in lhs.patterns.reverse do
        notAlt ← mkArrow (← mkEqHEq discr (← pattern.toExpr)) notAlt
      notAlt ← mkForallFVars (discrs ++ xs) notAlt
      return notAlt

  loop (lhss : List AltLHS) (alts : List Alt) (minors : Array Expr) (altInfos : Array AltParamInfo) (notAlts : Array Expr) : MetaM α := do
    match lhss with
    | [] => k alts.reverse minors altInfos
    | lhs::lhss =>
      let idx       := alts.length
      let xs := lhs.fvarDecls.toArray.map LocalDecl.toExpr
      let (notAltHs, notAltIdxs) ← if isSplitter.isSome then mkSplitterHyps idx lhs notAlts else pure (#[], #[])
      let minorType ← mkMinorType xs lhs notAltHs
      let notAlt ← mkNotAlt xs lhs
      let hasParams := !xs.isEmpty || !notAltHs.isEmpty || discrInfos.any fun info => info.hName?.isSome
      let minorType := if hasParams then minorType else mkSimpleThunkType minorType
      let minorName := (`h).appendIndexAfter (idx+1)
      trace[Meta.Match.debug] "minor premise {minorName} : {minorType}"
      withLocalDeclD minorName minorType fun minor => do
        let rhs    := if hasParams then mkAppN minor xs else mkApp minor (mkConst `Unit.unit)
        let minors := minors.push minor
        let altInfos := altInfos.push { numFields := xs.size, numOverlaps := notAltHs.size, hasUnitThunk := !hasParams }
        let fvarDecls ← lhs.fvarDecls.mapM instantiateLocalDeclMVars
        let alt    := { ref := lhs.ref, idx := idx, rhs := rhs, fvarDecls := fvarDecls, patterns := lhs.patterns, cnstrs := [], notAltIdxs := notAltIdxs }
        let alts   := alt :: alts
        loop lhss alts minors altInfos (notAlts.push notAlt)

structure State where
  /-- Used alternatives -/
  used            : Std.HashSet Nat := {} -- used alternatives
  /--
  Overlapped alternatives.
  Stored as ordered pairs `(overlapping,overlapped) ∈ overlaps`.
  Used during splitter generation to avoid going through all pairs of patterns.
  -/
  overlaps        : Overlaps := {}
  counterExamples : List (List Example) := []

/-- Return true if the given (sub-)problem has been solved. -/
private def isDone (p : Problem) : Bool :=
  p.vars.isEmpty

/-- Return true if the next element on the `p.vars` list is a variable. -/
private def isNextVar (p : Problem) : Bool :=
  match p.vars with
  | .fvar _ :: _ => true
  | _            => false

private def hasCtorPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | .ctor .. :: _ => true
    | _             => false

private def hasValPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | .val _ :: _ => true
    | _           => false

private def hasInaccessiblePattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | .inaccessible _ :: _ => true
    | _                    => false

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

def isCurrVarInductive (p : Problem) : MetaM Bool := do
  match p.vars with
  | []   => return false
  | x::_ => withGoalOf p do
    let val? ← getInductiveVal? x
    return val?.isSome

private def isConstructorTransition (p : Problem) : MetaM Bool := do
  return (← isCurrVarInductive p)
    && (hasCtorPattern p || p.alts.isEmpty)
    && p.alts.all fun alt => match alt.patterns with
      | .ctor .. :: _        => true
      | .inaccessible _ :: _ => true -- should be a done pattern by now
      | _                    => false

private def isValueTransition (p : Problem) : Bool :=
  hasValPattern p && hasInaccessiblePattern p &&
  p.alts.all fun alt => match alt.patterns with
     | .val _          :: _ => true
     | .inaccessible _ :: _ => true -- should be a done pattern by now
     | _                    => false

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
  hasArrayLitPattern p && hasInaccessiblePattern p &&
  p.alts.all fun alt => match alt.patterns with
     | .arrayLit .. :: _    => true
     | .inaccessible _ :: _ => true -- should be a done pattern by now
     | _                    => false

private def hasCtor (p : Problem) : Bool :=
  !isNextVar p ||
    p.alts.any fun alt => match alt.patterns with
    | .ctor .. :: _        => true
    | _                    => false

private def isNatValueTransition (p : Problem) : MetaM Bool := do
  return (← hasNatValPattern p) && hasCtor p

/--
Predicate for testing whether we need to expand `Int` value patterns into constructors.
There are two cases:
- We have constructor patterns. Example:
```
| 0, ...
| Int.toVal p, ...
...
```
- We don't have the `else`-case (i.e., inaccessible pattern). This can happen
when the non-value cases are unreachable.
-/
private def isIntValueTransition (p : Problem) : MetaM Bool := do
  unless (← hasIntValPattern p) do return false
  return hasCtor p || !hasInaccessiblePattern p

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

Dropping unsolved constraints where `lhs` is a free variable seems unsound, but simply leads to later
errors about the type of the alternative not matching the goal type, which is arguably a bit more
user-friendly than showing possibly match-compilation-internal variable names.
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
Solve pending alternative constraints and overlap assumptions.
If all constraints can be solved perform assignment `mvarId := alt.rhs`, else throw error.
-/
private partial def solveCnstrs (mvarId : MVarId) (alt : Alt) : StateRefT State MetaM Unit := do
  go (reorientCnstrs alt)
where
  go (alt : Alt) : StateRefT State MetaM Unit := do
    match (← solveSomeLocalFVarIdCnstr? alt) with
    | some alt => go alt
    | none =>
      let alt ← filterTrivialCnstrs alt
      if alt.cnstrs.isEmpty then
        mvarId.withContext do
          let eType ← inferType alt.rhs
          let (notAltsMVarIds, _, eType) ← forallMetaBoundedTelescope eType alt.notAltIdxs.size
          unless notAltsMVarIds.size = alt.notAltIdxs.size do
            throwErrorAt alt.ref "Incorrect number of overlap hypotheses in the right-hand-side, expected {alt.notAltIdxs.size}:{indentExpr eType}"
          let targetType ← mvarId.getType
          unless (← isDefEqGuarded targetType eType) do
            trace[Meta.Match.match] "assignGoalOf failed {eType} =?= {targetType}"
            throwErrorAt alt.ref "Dependent elimination failed: Type mismatch when solving this alternative: it {← mkHasTypeButIsExpectedMsg eType targetType}"
          for notAltMVarId in notAltsMVarIds do
            solveOverlap notAltMVarId.mvarId!
          mvarId.assign (mkAppN alt.rhs notAltsMVarIds)
          modify fun s => { s with used := s.used.insert alt.idx }
      else
        trace[Meta.Match.match] "alt has unsolved cnstrs:\n{← alt.toMessageData}"
        let mut msg := m!"Dependent match elimination failed: Could not solve constraints"
        for (lhs, rhs) in alt.cnstrs do
          msg := msg ++ m!"\n  {lhs} ≋ {rhs}"
        throwErrorAt alt.ref msg

private def isCtorIdxHasNotBit? (e : Expr) : Option FVarId := do
  let ctorIdxApp ← isHasNotBit? e
  guard ctorIdxApp.isApp
  guard ctorIdxApp.getAppFn.isConst
  guard <| (`ctorIdx).isSuffixOf ctorIdxApp.getAppFn.constName! -- This should be an env extension maybe
  guard ctorIdxApp.appArg!.isFVar
  return ctorIdxApp.appArg!.fvarId!

private partial def contradiction (mvarId : MVarId) : MetaM Bool := do
  mvarId.withContext do
    withTraceNode `Meta.Match.match (msg := (return m!"{exceptBoolEmoji ·} Match.contradiction")) do
    trace[Meta.Match.match] m!"Match.contradiction:\n{mvarId}"
    if (← mvarId.contradictionCore {}) then
      trace[Meta.Match.match] "Contradiction found!"
      return true
    else
      -- Try harder by splitting `ctorIdx x ≠ 23` assumptions
      for localDecl in (← getLCtx) do
        if let some fvarId := isCtorIdxHasNotBit? localDecl.type then
          trace[Meta.Match.match] "splitting ctorIdx assumption {localDecl.type}"
          let subgoals ← mvarId.cases fvarId
          -- NB: do not use `allM`, we want to process all cases to not leave
          -- unsolved metavariables behind.
          let allDone ← subgoals.mapM (contradiction ·.mvarId)
          return allDone.all id

      mvarId.admit
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
      let mvarId ← p.mvarId.exfalso
      /- TODO: allow users to configure which tactic is used to close leaves. -/
      if (← contradiction mvarId) then
        trace[Meta.Match.match] "contradiction succeeded"
      else
        trace[Meta.Match.match] "contradiction failed, missing alternative"
        modify fun s => { s with counterExamples := p.examples :: s.counterExamples }
    | alt :: overlapped =>
      solveCnstrs p.mvarId alt
      for otherAlt in overlapped do
        modify fun s => { s with overlaps := s.overlaps.insert alt.idx otherAlt.idx }
      trace[Meta.Match.match] "leaf closed"

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

private def hasRecursiveType (x : Expr) : MetaM Bool := do
  match (← getInductiveVal? x) with
  | some val => return val.isRec
  | _        => return false

private def hasNonTrivialExample (p : Problem) : Bool :=
  p.examples.any fun | Example.underscore => false | _ => true

private def throwCasesException (p : Problem) (ex : Exception) : MetaM α := do
  match ex with
  | .error ref msg =>
    let exampleMsg :=
      if hasNonTrivialExample p then m!" after processing{indentD <| examplesToMessageData p.examples}" else ""
    throw <| Exception.error ref <| msg.composePreservingKind <| m!"{exampleMsg}\n" ++
              "the dependent pattern matcher can solve the following kinds of equations\n" ++
              "- <var> = <term> and <term> = <var>\n" ++
              "- <term> = <term> where the terms are definitionally equal\n" ++
              "- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil"
  | _ => throw ex

private def collectCtors (p : Problem) : Array Name :=
  p.alts.foldl (init := #[]) fun ctors alt =>
    match alt.patterns with
    | .ctor n _ _ _ :: _ => if ctors.contains n then ctors else ctors.push n
    | _                  => ctors

private def processConstructor (p : Problem) : MetaM (Array Problem) := do
  trace[Meta.Match.match] "constructor step"
  let x :: xs := p.vars | unreachable!
  let interestingCtors? ←
    -- We use a sparse case analysis only if there is at least one non-constructor pattern,
    -- but not just because there are constructors missing (in that case we benefit from
    -- the eager split in ruling out constructors by type or by a more explicit error message)
    if backward.match.sparseCases.get (← getOptions) && hasInaccessiblePattern p then
      let ctors := collectCtors p
      trace[Meta.Match.match] "using sparse cases: {ctors}"
      pure (some ctors)
    else
      pure none
  let subgoals? ← commitWhenSome? do
     let subgoals ←
       try
         p.mvarId.cases x.fvarId! (interestingCtors? := interestingCtors?)
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
    -- withTraceNode `Meta.Match.match (msg := (return m!"{exceptEmoji ·} case {subgoal.ctorName}")) do
    if let some ctorName := subgoal.ctorName then
      -- A normal constructor case
      let subst    := subgoal.subst
      let fields   := subgoal.fields.toList
      let newVars  := fields ++ xs
      let newVars  := newVars.map fun x => x.applyFVarSubst subst
      let subex    := Example.ctor ctorName <| fields.map fun field => match field with
        | .fvar fvarId => Example.var fvarId
        | _            => Example.underscore -- This case can happen due to dependent elimination
      let examples := p.examples.map <| Example.replaceFVarId x.fvarId! subex
      let examples := examples.map <| Example.applyFVarSubst subst
      let newAlts  := p.alts.filter fun alt => match alt.patterns with
        | .ctor n .. :: _       => n == ctorName
        | .inaccessible _ :: _  => true
        | _                     => unreachable!
      let newAlts  := newAlts.map fun alt => alt.applyFVarSubst subst
      let newAlts ← newAlts.mapM fun alt => do
        match alt.patterns with
        | .ctor _ _ _ fieldPats :: ps  => return { alt with patterns := fieldPats ++ ps }
        | .inaccessible _ :: ps        => return { alt with patterns := fields.map .inaccessible ++ ps }
        | _                            => unreachable!
      return { p with mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }
    else
      -- A catch-all case
      let subst := subgoal.subst
      trace[Meta.Match.match] "constructor catch-all case"
      let examples := p.examples.map <| Example.applyFVarSubst subst
      let newVars := p.vars.map fun x => x.applyFVarSubst subst
      let newAlts := p.alts.filter fun alt => match alt.patterns with
        | .ctor .. :: _ => false
        | _             => true
      let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst
      return { p with mvarId := subgoal.mvarId, alts := newAlts, vars := newVars, examples := examples }

private def processNonVariable (p : Problem) : MetaM Problem := withGoalOf p do
  let x :: xs := p.vars | unreachable!
  if let some (ctorVal, xArgs) ← withTransparency .default <| constructorApp'? x then
    if hasCtorPattern p then
      let xFields := xArgs.extract ctorVal.numParams xArgs.size
      let alts ← p.alts.filterMapM fun alt => do
        match alt.patterns with
        | .ctor ctorName _ _ fields :: ps   =>
          if ctorName != ctorVal.name then
            return none
          else
            return some { alt with patterns := fields ++ ps }
        | .inaccessible _ :: ps =>
            return some { alt with patterns := xFields.toList.map .inaccessible ++ ps }
        | _ => unreachable!
      return { p with alts := alts, vars := xFields.toList ++ xs }
  let alts ← p.alts.mapM fun alt => do
    match alt.patterns with
    | .inaccessible _ :: ps => return { alt with patterns := ps }
    | p :: ps => return { alt with patterns := ps, cnstrs := (x, ← p.toExpr) :: alt.cnstrs }
    | _      => unreachable!
  return { p with alts := alts, vars := xs }

private def collectValues (p : Problem) : Array Expr :=
  p.alts.foldl (init := #[]) fun values alt =>
    match alt.patterns with
    | .val v :: _ => if values.contains v then values else values.push v
    | _           => values

private def isFirstPatternInaccessible (alt : Alt) : Bool :=
  match alt.patterns with
  | .inaccessible _ :: _ => true
  | _                    => false

private def Pattern.isRefutable : Pattern → Bool
  | .var _           => false
  | .inaccessible _  => false
  | .as _ p _        => p.isRefutable
  | .arrayLit ..     => true
  | .ctor ..         => true
  | .val ..          => true

private def triviallyComplete (p : Problem) : Bool :=
  !p.alts.isEmpty && p.alts.getLast!.patterns.all (!·.isRefutable)

private def processValue (p : Problem) : MetaM (Array Problem) := do
  trace[Meta.Match.match] "value step"
  let x :: xs := p.vars | unreachable!
  let values := collectValues p
  let needHyps := !triviallyComplete p || p.alts.any (!·.notAltIdxs.isEmpty)
  let subgoals ← caseValues p.mvarId x.fvarId! values (needHyps := needHyps)
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
        | .val v          :: _ => v == value
        | .inaccessible _ :: _ => true
        | _                    => unreachable!
      let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst
      let newAlts := newAlts.map fun alt => match alt.patterns with
        | .val _          :: ps => { alt with patterns := ps }
        | .inaccessible _ :: ps => { alt with patterns := ps }
        | _                     => unreachable!
      let newVars := xs.map fun x => x.applyFVarSubst subst
      return { p with mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }
    else
      -- else branch for value
      let newAlts := p.alts.filter isFirstPatternInaccessible
      return { p with mvarId := subgoal.mvarId, alts := newAlts, vars := x::xs }

private def collectArraySizes (p : Problem) : Array Nat :=
  p.alts.foldl (init := #[]) fun sizes alt =>
    match alt.patterns with
    | .arrayLit _ ps :: _ => let sz := ps.length; if sizes.contains sz then sizes else sizes.push sz
    | _                   => sizes

private def processArrayLit (p : Problem) : MetaM (Array Problem) := do
  trace[Meta.Match.match] "array literal step"
  let x :: xs := p.vars | unreachable!
  let sizes := collectArraySizes p
  let subgoals ← caseArraySizes p.mvarId x.fvarId! sizes
  subgoals.mapIdxM fun i subgoal => do
    if h : i < sizes.size then
      let size     := sizes[i]
      let subst    := subgoal.subst
      let elems    := subgoal.elems.toList
      let newVars  := elems.map mkFVar ++ xs
      let newVars  := newVars.map fun x => x.applyFVarSubst subst
      let subex    := Example.arrayLit <| elems.map Example.var
      let examples := p.examples.map <| Example.replaceFVarId x.fvarId! subex
      let examples := examples.map <| Example.applyFVarSubst subst
      let newAlts  := p.alts.filter fun alt => match alt.patterns with
        | .arrayLit _ ps :: _  => ps.length == size
        | .inaccessible _ :: _ => true
        | _                    => unreachable!
      let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst
      let newAlts := newAlts.map fun alt =>
        match alt.patterns with
        | .arrayLit _ pats :: ps => { alt with patterns := pats ++ ps }
        | .inaccessible _ :: ps  =>
          let patterns := elems.map (fun elem => .inaccessible (mkFVar elem)) ++ ps
          { alt with patterns }
        | _  => unreachable!
      return { p with mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }
    else
      -- else branch
      let newAlts := p.alts.filter isFirstPatternInaccessible
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
    throwError "Failed to compile pattern matching: Stuck at{indentD msg}"

private def checkNextPatternTypes (p : Problem) : MetaM Unit := do
  match p.vars with
  | []   => return ()
  | x::_ => withGoalOf p do
    for alt in p.alts do
      withRef alt.ref do
        withExistingLocalDecls alt.fvarDecls do
          match alt.patterns with
          | []   => return ()
          | p::_ =>
            let e ← p.toExpr
            let xType ← inferType x
            let eType ← inferType e
            unless (← isDefEq xType eType) do
              throwError "Type mismatch in pattern: Pattern{indentExpr e}\n{← mkHasTypeButIsExpectedMsg eType xType}"

private def List.moveToFront [Inhabited α] (as : List α) (i : Nat) : List α :=
  let rec loop : (as : List α) → (i : Nat) → α × List α
    | [],    _   => unreachable!
    | a::as, 0   => (a, as)
    | a::as, i+1 =>
      let (b, bs) := loop as i
      (b, a::bs)
  let (b, bs) := loop as i
  b :: bs

/-- Move variable `#i` to the beginning of the to-do list `p.vars`. -/
private def moveToFront (p : Problem) (i : Nat) : Problem :=
  if i == 0 then
    p
  else if i < p.vars.length then
    { p with
      vars := List.moveToFront p.vars i
      alts := p.alts.map fun alt => { alt with patterns := List.moveToFront alt.patterns i }
    }
  else
    p

/--
Returns the index of the first pattern in the first alternative that is refutable
(i.e. not a variable or inaccessible pattern). We want to handle these first
so that the generated code branches in the order suggested by the user's code.
-/
private def firstRefutablePattern (p : Problem) : Option Nat :=
  match p.alts with
  | alt:: _ => alt.patterns.findIdx? (·.isRefutable)
  | _ => none

def isExFalsoTransition (p : Problem) : MetaM Bool := do
  if p.alts.isEmpty then
    withGoalOf p do
      let targetType ← p.mvarId.getType
      return !targetType.isFalse
  else
    return false

def processExFalso (p : Problem) : MetaM Problem := do
  let mvarId' ← p.mvarId.exfalso
  return { p with mvarId := mvarId' }

/--
Does any alternative have a pattern that can be independently handled (variable, inaccessible,
as-pattern) before any refutable pattern?
-/
def hasIndependentPatterns (p : Problem) : Bool :=
  p.alts.any fun alt => Id.run do
    for v in p.vars, p in alt.patterns do
      match p with
      | .inaccessible e =>
        if e == v then
          -- Skip inaccessible pattern that's are equal to the variable, these are “done”
          continue
        else
          return true
      | .var .. | .as .. => return true
      | .ctor .. | .val .. | .arrayLit .. => return false
    return false

def processIndependentPatterns (p : Problem) : MetaM Problem := withGoalOf p do
  let alts' ← p.alts.mapM fun alt => do
    -- We process only one pattern at a time, for code simplicity and better tracing
    -- of the main loop
    let mut donePrefix := 0
    for var in p.vars, pat in alt.patterns do
      match pat with
      | .inaccessible e =>
        if e == var then
          donePrefix := donePrefix + 1
        else
          break
      | _ => break
    match alt.patterns.drop donePrefix with
    | [] =>
      -- All done here
      return alt
    | pat :: remainingPats =>
      let v := p.vars[donePrefix]!
      match pat with
      | .inaccessible e =>
        trace[Meta.Match.match] "processing inaccessible pattern"
        let patterns := (p.vars.take (donePrefix + 1)).map .inaccessible ++ remainingPats
        let cnstrs := (v, e) :: alt.cnstrs
        return { alt with patterns, cnstrs }
      | .var fvarId =>
        trace[Meta.Match.match] "processing variable pattern"
        let patterns := (p.vars.take (donePrefix + 1)).map .inaccessible ++ remainingPats
        let alt' ← withExistingLocalDecls alt.fvarDecls do
          if (← isDefEqGuarded (← fvarId.getType) (← inferType v)) then
            return { alt with patterns }.replaceFVarId fvarId v
          else
            let cnstrs := (mkFVar fvarId, v) :: alt.cnstrs
            return { alt with patterns, cnstrs }
        return alt'
      | .as fvarId pat h =>
        let patterns := (p.vars.take donePrefix).map .inaccessible ++ [pat] ++ remainingPats
        /- We used to use eagerly check the types here (using what was called `checkAndReplaceFVarId`),
          but `x` and `fvarId` can have different types when dependent types are being used.
          Let's consider the repro for issue #471
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
        let r ← mkEqRefl v
        return { alt with patterns }.replaceFVarId fvarId v |>.replaceFVarId h r
      | .ctor .. | .val .. | .arrayLit .. =>
        return alt
  return { p with alts := alts' }

private def isFirstVarDoneTransition (p : Problem) : Bool := Id.run do
  if p.alts.isEmpty then
    return false
  let x :: _ := p.vars | unreachable!
  return p.alts.all fun alt => Id.run do
    let p :: _ := alt.patterns | unreachable!
    return match p with
    | .inaccessible e    => e == x
    | _                  => false

private def processFirstVarDone (p : Problem) : Problem :=
  { p with
    vars := p.vars.tail!
    alts := p.alts.map fun alt => { alt with patterns := alt.patterns.tail! } }

private def tracedForM (xs : Array α) (process : α → StateRefT State MetaM Unit) : StateRefT State MetaM Unit :=
  if xs.size > 1 then
    for x in xs, i in [:xs.size] do
      withTraceNode `Meta.Match.match (msg := (return m!"{exceptEmoji ·} subgoal {i+1}/{xs.size}")) do
        process x
  else
    for x in xs do
      process x

private partial def process (p : Problem) : StateRefT State MetaM Unit := do
  traceState p
  if isDone p then
    traceStep ("leaf")
    processLeaf p
    return

  if (← isExFalsoTransition p) then
    traceStep ("ex falso")
    let p ← processExFalso p
    process p
    return

  if hasIndependentPatterns p then
    traceStep ("processing independent prefixes of patterns")
    let p ← processIndependentPatterns p
    process p
    return

  if isFirstVarDoneTransition p then
    traceStep ("first var done")
    let p := processFirstVarDone p
    process p
    return

  if backward.match.rowMajor.get (← getOptions) then
    match firstRefutablePattern p with
    | some i =>
      if i > 0 then
        traceStep ("move var to front")
        process (moveToFront p i)
        return
    | none =>
      if let alt::(overlapped@(_::_)) := p.alts then
        traceStep ("drop all but first alt")
        -- all patterns in first alternative are irrefutable, we can drop all other alts
        let p := { p with alts := [alt] }
        for otherAlt in overlapped do
          modify fun s => { s with overlaps := s.overlaps.insert alt.idx otherAlt.idx }
        process p
        return

  if (← isNatValueTransition p) then
    traceStep ("nat value to constructor")
    process (← expandNatValuePattern p)
    return

  if (← isIntValueTransition p) then
    traceStep ("int value to constructor")
    process (← expandIntValuePattern p)
    return

  if (← isFinValueTransition p) then
    traceStep ("fin value to constructor")
    process (← expandFinValuePattern p)
    return

  if (← isBitVecValueTransition p) then
    traceStep ("bitvec value to constructor")
    process (← expandBitVecValuePattern p)
    return

  if !isNextVar p then
    traceStep ("non variable")
    let p ← processNonVariable p
    process p
    return

  if (← isConstructorTransition p) then
    let ps ← processConstructor p
    tracedForM ps process
    return

  if p.alts.isEmpty then
    -- Note that for inductive types, `isConstructorTransition` does something on empty matches
    -- For all others, drop the variable here
    traceStep ("empty match transition")
    let p := { p with vars := p.vars.tail! }
    process p
    return

  if isValueTransition p then
    let ps ← processValue p
    tracedForM ps process
    return

  if isArrayLitTransition p then
    let ps ← processArrayLit p
    tracedForM ps process
    return

  if (← hasNatValPattern p) then
    -- This branch is reachable when `p`, for example, is just values without an else-alternative.
    -- We added it just to get better error messages.
    traceStep ("nat value to constructor")
    process (← expandNatValuePattern p)
    return

  checkNextPatternTypes p
  throwNonSupported p

private def getUElimPos? (matcherLevels : List Level) (uElim : Level) : MetaM (Option Nat) :=
  if uElim == levelZero then
    return none
  else match matcherLevels.idxOf? uElim with
    | none => throwError "Dependent match elimination failed: Universe level not found"
    | some pos => return some pos

/- See comment at `mkMatcher` before `mkAuxDefinition` -/
register_builtin_option bootstrap.genMatcherCode : Bool := {
  defValue := true
  descr := "disable code generation for auxiliary matcher function"
}

private structure MatcherKey where
  value     : Expr
  compile   : Bool
  -- When a matcher is created in a private context and thus may contain private references, we must
  -- not reuse it in an exported context.
  isPrivate : Bool
deriving BEq, Hashable

private builtin_initialize matcherExt : EnvExtension (PHashMap MatcherKey Name) ←
  registerEnvExtension (pure {}) (asyncMode := .local)  -- mere cache, keep it local

/-- Similar to `mkAuxDefinition`, but uses the cache `matcherExt`.
   It also returns an Boolean that indicates whether a new matcher function was added to the environment or not. -/
def mkMatcherAuxDefinition (name : Name) (type : Expr) (value : Expr) (isSplitter : Bool) : MetaM (Expr × Option (MatcherInfo → MetaM Unit)) := do
  trace[Meta.Match.debug] "{name} : {type} := {value}"
  let compile := bootstrap.genMatcherCode.get (← getOptions)
  let result ← Closure.mkValueTypeClosure type value (zetaDelta := false)
  let env ← getEnv
  let mkMatcherConst name :=
    mkAppN (mkConst name result.levelArgs.toList) result.exprArgs
  let key := { value := result.value, compile, isPrivate := env.header.isModule && isPrivateName name }
  let mut nameNew? := none
  unless isSplitter do
    nameNew? := (matcherExt.getState env).find? key
    if nameNew?.isNone && key.isPrivate then
      -- private contexts may reuse public matchers
      nameNew? := (matcherExt.getState env).find? { key with isPrivate := false }
  match nameNew? with
  | some nameNew => return (mkMatcherConst nameNew, none)
  | none =>
    let decl := Declaration.defnDecl (← mkDefinitionValInferringUnsafe name result.levelParams.toList
      result.type result.value .abbrev)
    trace[Meta.Match.debug] "{name} : {result.type} := {result.value}"
    let addMatcher : MatcherInfo → MetaM Unit := fun mi => do
      -- matcher bodies should always be exported, if not private anyway
      withExporting do
        addDecl decl
      unless isSplitter do
        modifyEnv fun env => matcherExt.modifyState env fun s => s.insert key name
        addMatcherInfo name mi
      setInlineAttribute name
      enableRealizationsForConst name
      if compile then
        compileDecl decl
    return (mkMatcherConst name, some addMatcher)

structure MkMatcherInput where
  matcherName : Name
  matchType   : Expr
  discrInfos  : Array DiscrInfo
  lhss        : List AltLHS
  isSplitter  : Option Overlaps := none

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
-/
def mkMatcher (input : MkMatcherInput) : MetaM MatcherResult := withCleanLCtxFor input do
  let {matcherName, matchType, discrInfos, lhss, isSplitter} := input
  let numDiscrs := discrInfos.size
  checkNumPatterns numDiscrs lhss
  forallBoundedTelescope matchType numDiscrs fun discrs matchTypeBody => do
  /- We generate an matcher that can eliminate using different motives with different universe levels.
     `uElim` is the universe level the caller wants to eliminate to.
     If it is not levelZero, we create a matcher that can eliminate in any universe level.
     This is useful for implementing `MatcherApp.addArg` because it may have to change the universe level. -/
  let uElim ← getLevel matchTypeBody
  let uElimGen ← if uElim == levelZero then pure levelZero else mkFreshLevelMVar
  let mkMatcher (type val : Expr) (altInfos : Array AltParamInfo) (s : State) : MetaM MatcherResult := do
    trace[Meta.Match.debug] "matcher value: {val}\ntype: {type}"
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
    let (matcher, addMatcher) ← mkMatcherAuxDefinition matcherName type val (isSplitter := input.isSplitter.isSome)
    trace[Meta.Match.debug] "matcher levels: {matcher.getAppFn.constLevels!}, uElim: {uElimGen}"
    let uElimPos? ← getUElimPos? matcher.getAppFn.constLevels! uElimGen
    discard <| isLevelDefEq uElimGen uElim
    let addMatcher :=
      match addMatcher with
      | some addMatcher => addMatcher <|
        { numParams := matcher.getAppNumArgs
          altInfos
          discrInfos
          numDiscrs
          uElimPos?
          overlaps := s.overlaps
          }
      | none => pure ()

    trace[Meta.Match.debug] "matcher: {matcher}"
    let unusedAltIdxs := lhss.length.fold (init := []) fun i _ r =>
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
    withAlts motive discrs discrInfos lhss isSplitter fun alts minors altInfos => do
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
      let args := #[motive] ++ discrs ++ minors
      let val ← mkLambdaFVars args val
      let type ← mkForallFVars args (mkAppN motive discrs)
      mkMatcher type val altInfos s
  else
    let mvarType  := mkAppN motive discrs
    trace[Meta.Match.debug] "target: {mvarType}"
    withAlts motive discrs discrInfos lhss isSplitter fun alts minors altInfos => do
      let mvar ← mkFreshExprMVar mvarType
      let examples := discrs.toList.map fun discr => Example.var discr.fvarId!
      let (_, s) ← (process { mvarId := mvar.mvarId!, vars := discrs.toList, alts := alts, examples := examples }).run {}
      let args := #[motive] ++ discrs ++ minors
      let type ← mkForallFVars args mvarType
      let val  ← mkLambdaFVars args mvar
      mkMatcher type val altInfos s

def getMkMatcherInputInContext (matcherApp : MatcherApp) (unfoldNamed : Bool) : MetaM MkMatcherInput := do
  let matcherName := matcherApp.matcherName
  let some matcherInfo ← getMatcherInfo? matcherName
    | throwError "Internal error during match expression elaboration: Could not find a matcher named `{matcherName}`"
  let matcherConst ← getConstVal matcherName
  let matcherType ← instantiateTypeLevelParams matcherConst matcherApp.matcherLevels.toList
  let matcherType ← instantiateForall matcherType <| matcherApp.params ++ #[matcherApp.motive]
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
    let ty ← if unfoldNamed then unfoldNamedPattern ty else pure ty
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

def withMkMatcherInput (matcherName : Name) (unfoldNamed : Bool) (k : MkMatcherInput → MetaM α) : MetaM α := do
  let some matcherInfo ← getMatcherInfo? matcherName
    | throwError "withMkMatcherInput: {.ofConstName matcherName} is not a matcher"
  let matcherConst ← getConstInfo matcherName
  forallBoundedTelescope matcherConst.type matcherInfo.arity fun xs _ => do
    let matcherApp ← mkConstWithLevelParams matcherConst.name
    let matcherApp := mkAppN matcherApp xs
    let some matcherApp ← matchMatcherApp? matcherApp
      | throwError "withMkMatcherInput: {.ofConstName matcherName} does not produce a matcher application"
    let mkMatcherInput ← getMkMatcherInputInContext matcherApp unfoldNamed
    k mkMatcherInput

end Match


builtin_initialize
  registerTraceClass `Meta.Match.match
  registerTraceClass `Meta.Match.debug
  registerTraceClass `Meta.Match.unify

end Lean.Meta
