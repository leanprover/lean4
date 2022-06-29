/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.CollectLevelParams
import Lean.Util.CollectFVars
import Lean.Util.Recognizers
import Lean.Compiler.ExternAttr
import Lean.Meta.Check
import Lean.Meta.Closure
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.GeneralizeTelescope
import Lean.Meta.Match.Basic
import Lean.Meta.Match.MVarRenaming
import Lean.Meta.Match.CaseValues

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
      if let some hName := discrInfos[i].hName? then
        withLocalDeclD hName (← mkEqHEq lhs[i] rhs[i]) fun h =>
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
        let alts   := { ref := lhs.ref, idx := idx, rhs := rhs, fvarDecls := fvarDecls, patterns := lhs.patterns : Alt } :: alts
        loop lhss alts minors

def assignGoalOf (p : Problem) (e : Expr) : MetaM Unit :=
  withGoalOf p do
    let mvar := mkMVar p.mvarId
    let mvarType ← inferType mvar
    let eType ← inferType e
    unless (← isDefEq mvarType eType) do
      throwError "dependent elimination failed, type mismatch when solving alternative with type{indentExpr eType}\nbut expected{indentExpr mvarType}"
    assignExprMVar p.mvarId e

structure State where
  used            : Std.HashSet Nat := {} -- used alternatives
  counterExamples : List (List Example) := []

/-- Return true if the given (sub-)problem has been solved. -/
private def isDone (p : Problem) : Bool :=
  p.vars.isEmpty

/-- Return true if the next element on the `p.vars` list is a variable. -/
private def isNextVar (p : Problem) : Bool :=
  match p.vars with
  | Expr.fvar _ _ :: _ => true
  | _                  => false

private def hasAsPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | Pattern.as _ _ _ :: _ => true
    | _                     => false

private def hasCtorPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | Pattern.ctor _ _ _ _ :: _ => true
    | _                         => false

private def hasValPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | Pattern.val _ :: _ => true
    | _                  => false

private def hasNatValPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | Pattern.val v :: _ => v.isNatLit
    | _                  => false

private def hasVarPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | Pattern.var _ :: _ => true
    | _                  => false

private def hasArrayLitPattern (p : Problem) : Bool :=
  p.alts.any fun alt => match alt.patterns with
    | Pattern.arrayLit _ _ :: _ => true
    | _                         => false

private def isVariableTransition (p : Problem) : Bool :=
  p.alts.all fun alt => match alt.patterns with
    | Pattern.inaccessible _ :: _ => true
    | Pattern.var _ :: _          => true
    | _                           => false

private def isConstructorTransition (p : Problem) : Bool :=
  (hasCtorPattern p || p.alts.isEmpty)
  && p.alts.all fun alt => match alt.patterns with
     | Pattern.ctor _ _ _ _ :: _   => true
     | Pattern.var _ :: _          => true
     | Pattern.inaccessible _ :: _ => true
     | _                           => false

private def isValueTransition (p : Problem) : Bool :=
  hasVarPattern p && hasValPattern p
  && p.alts.all fun alt => match alt.patterns with
     | Pattern.val _ :: _ => true
     | Pattern.var _ :: _ => true
     | _                  => false

private def isArrayLitTransition (p : Problem) : Bool :=
  hasArrayLitPattern p && hasVarPattern p
  && p.alts.all fun alt => match alt.patterns with
     | Pattern.arrayLit _ _ :: _ => true
     | Pattern.var _ :: _        => true
     | _                         => false

private def isNatValueTransition (p : Problem) : Bool :=
  hasNatValPattern p
  && (!isNextVar p ||
      p.alts.any fun alt => match alt.patterns with
      | Pattern.ctor _ _ _ _ :: _   => true
      | Pattern.inaccessible _ :: _ => true
      | _                           => false)

private def processSkipInaccessible (p : Problem) : Problem :=
  match p.vars with
  | []      => unreachable!
  | _ :: xs =>
    let alts := p.alts.map fun alt => match alt.patterns with
      | Pattern.inaccessible _ :: ps => { alt with patterns := ps }
      | _       => unreachable!
    { p with alts := alts, vars := xs }

private def processLeaf (p : Problem) : StateRefT State MetaM Unit := do
  match p.alts with
  | []       =>
    /- TODO: allow users to configure which tactic is used to close leaves. -/
    unless (← contradictionCore p.mvarId {}) do
      trace[Meta.Match.match] "missing alternative"
      admit p.mvarId
      modify fun s => { s with counterExamples := p.examples :: s.counterExamples }
  | alt :: _ =>
    -- TODO: check whether we have unassigned metavars in rhs
    liftM <| assignGoalOf p alt.rhs
    modify fun s => { s with used := s.used.insert alt.idx }

private def processAsPattern (p : Problem) : MetaM Problem :=
  match p.vars with
  | []      => unreachable!
  | x :: _  => withGoalOf p do
    let alts ← p.alts.mapM fun alt => do
      match alt.patterns with
      | Pattern.as fvarId p h :: ps =>
        /- We used to use `checkAndReplaceFVarId` here, but `x` and `fvarId` may have different types
           when dependent types are beind used. Let's consider the repro for issue #471
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

private def processVariable (p : Problem) : MetaM Problem :=
  match p.vars with
  | []      => unreachable!
  | x :: xs => withGoalOf p do
    let alts ← p.alts.mapM fun alt => do
      match alt.patterns with
      | Pattern.inaccessible _ :: ps => return { alt with patterns := ps }
      | Pattern.var fvarId :: ps     => ({ alt with patterns := ps }).checkAndReplaceFVarId fvarId x
      | _                            => unreachable!
    return { p with alts := alts, vars := xs }

private def throwInductiveTypeExpected {α} (e : Expr) : MetaM α := do
  let t ← inferType e
  throwError "failed to compile pattern matching, inductive type expected{indentExpr e}\nhas type{indentExpr t}"

private def inLocalDecls (localDecls : List LocalDecl) (fvarId : FVarId) : Bool :=
  localDecls.any fun d => d.fvarId == fvarId

namespace Unify

structure Context where
  altFVarDecls : List LocalDecl

structure State where
  fvarSubst : FVarSubst := {}

abbrev M := ReaderT Context $ StateRefT State MetaM

def isAltVar (fvarId : FVarId) : M Bool := do
  return inLocalDecls (← read).altFVarDecls fvarId

def expandIfVar (e : Expr) : M Expr := do
  match e with
  | Expr.fvar _ _ => return (← get).fvarSubst.apply e
  | _             => return e

def occurs (fvarId : FVarId) (v : Expr) : Bool :=
  Option.isSome <| v.find? fun e => match e with
     | Expr.fvar fvarId' _ => fvarId == fvarId'
     | _=> false

def assign (fvarId : FVarId) (v : Expr) : M Bool := do
  if occurs fvarId v then
    trace[Meta.Match.unify] "assign occurs check failed, {mkFVar fvarId} := {v}"
    return false
  else
    if (← isAltVar fvarId) then
      trace[Meta.Match.unify] "{mkFVar fvarId} := {v}"
      modify fun s => { s with fvarSubst := s.fvarSubst.insert fvarId v }
      return true
    else
      trace[Meta.Match.unify] "assign failed variable is not local, {mkFVar fvarId} := {v}"
      return false

partial def unify (a : Expr) (b : Expr) : M Bool := do
  trace[Meta.Match.unify] "{a} =?= {b}"
  if (← isDefEq a b) then
    return true
  else
    let a' ← whnfD (← expandIfVar a)
    let b' ← whnfD (← expandIfVar b)
    if a != a' || b != b' then
      unify a' b'
    else match a, b with
      | Expr.fvar aFvarId _, Expr.fvar bFVarId _ => assign aFvarId b <||> assign bFVarId a
      | Expr.fvar aFvarId _, b => assign aFvarId b
      | a, Expr.fvar bFVarId _ => assign bFVarId a
      | Expr.app aFn aArg _, Expr.app bFn bArg _ => unify aFn bFn <&&> unify aArg bArg
      | _, _ => return false

end Unify

private def unify? (altFVarDecls : List LocalDecl) (a b : Expr) : MetaM (Option FVarSubst) := do
  let a ← instantiateMVars a
    let b ← instantiateMVars b
    let (r, s) ← Unify.unify a b { altFVarDecls := altFVarDecls} |>.run {}
    if r then
      return s.fvarSubst
    else
      trace[Meta.Match.unify] "failed to unify{indentExpr a}\nwith{indentExpr b}"
      return none

private def expandVarIntoCtor? (alt : Alt) (fvarId : FVarId) (ctorName : Name) : MetaM (Option Alt) :=
  withExistingLocalDecls alt.fvarDecls do
    let expectedType ← inferType (mkFVar fvarId)
    let expectedType ← whnfD expectedType
    let (ctorLevels, ctorParams) ← getInductiveUniverseAndParams expectedType
    let ctor := mkAppN (mkConst ctorName ctorLevels) ctorParams
    let ctorType ← inferType ctor
    forallTelescopeReducing ctorType fun ctorFields resultType => do
      let ctor := mkAppN ctor ctorFields
      let alt  := alt.replaceFVarId fvarId ctor
      let ctorFieldDecls ← ctorFields.mapM fun ctorField => getLocalDecl ctorField.fvarId!
      let newAltDecls := ctorFieldDecls.toList ++ alt.fvarDecls
      let subst? ← unify? newAltDecls resultType expectedType
      match subst? with
      | none       => return none
      | some subst =>
        let newAltDecls := newAltDecls.filter fun d => !subst.contains d.fvarId -- remove declarations that were assigned
        let newAltDecls := newAltDecls.map fun d => d.applyFVarSubst subst -- apply substitution to remaining declaration types
        let patterns    := alt.patterns.map fun p => p.applyFVarSubst subst
        let rhs         := subst.apply alt.rhs
        let ctorFieldPatterns := ctorFields.toList.map fun ctorField => match subst.get ctorField.fvarId! with
          | e@(Expr.fvar fvarId _) => if inLocalDecls newAltDecls fvarId then Pattern.var fvarId else Pattern.inaccessible e
          | e                      => Pattern.inaccessible e
        return some { alt with fvarDecls := newAltDecls, rhs := rhs, patterns := ctorFieldPatterns ++ patterns }

private def getInductiveVal? (x : Expr) : MetaM (Option InductiveVal) := do
  let xType ← inferType x
  let xType ← whnfD xType
  match xType.getAppFn with
  | Expr.const constName _ _ =>
    let cinfo ← getConstInfo constName
    match cinfo with
    | ConstantInfo.inductInfo val => return some val
    | _ => return none
  | _ => return none

private def hasRecursiveType (x : Expr) : MetaM Bool := do
  match (← getInductiveVal? x) with
  | some val => return val.isRec
  | _        => return false

/- Given `alt` s.t. the next pattern is an inaccessible pattern `e`,
   try to normalize `e` into a constructor application.
   If it is not a constructor, throw an error.
   Otherwise, if it is a constructor application of `ctorName`,
   update the next patterns with the fields of the constructor.
   Otherwise, return none. -/
def processInaccessibleAsCtor (alt : Alt) (ctorName : Name) : MetaM (Option Alt) := do
  let env ← getEnv
  match alt.patterns with
  | p@(Pattern.inaccessible e) :: ps =>
    trace[Meta.Match.match] "inaccessible in ctor step {e}"
    withExistingLocalDecls alt.fvarDecls do
      -- Try to push inaccessible annotations.
      let e ← whnfD e
      match e.constructorApp? env with
      | some (ctorVal, ctorArgs) =>
        if ctorVal.name == ctorName then
          let fields := ctorArgs.extract ctorVal.numParams ctorArgs.size
          let fields := fields.toList.map Pattern.inaccessible
          return some { alt with patterns := fields ++ ps }
        else
          return none
      | _ => throwErrorAt alt.ref "dependent match elimination failed, inaccessible pattern found{indentD p.toMessageData}\nconstructor expected"
  | _ => unreachable!

private def hasNonTrivialExample (p : Problem) : Bool :=
  p.examples.any fun | Example.underscore => false | _ => true

private def throwCasesException (p : Problem) (ex : Exception) : MetaM α := do
  match ex with
  | Exception.error ref msg =>
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
  match p.vars with
  | []      => unreachable!
  | x :: xs => do
    let subgoals? ← commitWhenSome? do
       let subgoals ←
         try
           cases p.mvarId x.fvarId!
         catch ex =>
           if p.alts.isEmpty then
             /- If we have no alternatives and dependent pattern matching fails, then a "missing cases" error is bettern than a "stuck" error message. -/
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

    match subgoals? with
    | none          => return #[{ p with vars := xs }]
    | some subgoals =>
      subgoals.mapM fun subgoal => withMVarContext subgoal.mvarId do
        let subst    := subgoal.subst
        let fields   := subgoal.fields.toList
        let newVars  := fields ++ xs
        let newVars  := newVars.map fun x => x.applyFVarSubst subst
        let subex    := Example.ctor subgoal.ctorName <| fields.map fun field => match field with
          | Expr.fvar fvarId _ => Example.var fvarId
          | _                  => Example.underscore -- This case can happen due to dependent elimination
        let examples := p.examples.map <| Example.replaceFVarId x.fvarId! subex
        let examples := examples.map <| Example.applyFVarSubst subst
        let newAlts  := p.alts.filter fun alt => match alt.patterns with
          | Pattern.ctor n _ _ _ :: _    => n == subgoal.ctorName
          | Pattern.var _ :: _           => true
          | Pattern.inaccessible _ :: _  => true
          | _                            => false
        let newAlts  := newAlts.map fun alt => alt.applyFVarSubst subst
        let newAlts ← newAlts.filterMapM fun alt => do
          match alt.patterns with
          | Pattern.ctor _ _ _ fields :: ps  => return some { alt with patterns := fields ++ ps }
          | Pattern.var fvarId :: ps         => expandVarIntoCtor? { alt with patterns := ps } fvarId subgoal.ctorName
          | Pattern.inaccessible _ :: _      => processInaccessibleAsCtor alt subgoal.ctorName
          | _                                => unreachable!
        return { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }

private def processNonVariable (p : Problem) : MetaM Problem :=
  match p.vars with
  | []      => unreachable!
  | x :: xs => withGoalOf p do
    let x ← whnfD x
    let env ← getEnv
    match x.constructorApp? env with
    | some (ctorVal, xArgs) =>
      let alts ← p.alts.filterMapM fun alt => do
        match alt.patterns with
        | Pattern.ctor n _ _ fields :: ps   =>
          if n != ctorVal.name then
            return none
          else
            return some { alt with patterns := fields ++ ps }
        | Pattern.inaccessible _ :: _ => processInaccessibleAsCtor alt ctorVal.name
        | p :: _  => throwError "failed to compile pattern matching, inaccessible pattern or constructor expected{indentD p.toMessageData}"
        | _       => unreachable!
      let xFields := xArgs.extract ctorVal.numParams xArgs.size
      return { p with alts := alts, vars := xFields.toList ++ xs }
    | none =>
      let alts ← p.alts.filterMapM fun alt => match alt.patterns with
        | Pattern.inaccessible e :: ps => do
          if (← isDefEq x e) then
            return some { alt with patterns := ps }
          else
            return none
        | p :: _ => throwError "failed to compile pattern matching, unexpected pattern{indentD p.toMessageData}\ndiscriminant{indentExpr x}"
        | _      => unreachable!
      return { p with alts := alts, vars := xs }

private def collectValues (p : Problem) : Array Expr :=
  p.alts.foldl (init := #[]) fun values alt =>
    match alt.patterns with
    | Pattern.val v :: _ => if values.contains v then values else values.push v
    | _                  => values

private def isFirstPatternVar (alt : Alt) : Bool :=
  match alt.patterns with
  | Pattern.var _ :: _ => true
  | _                  => false

private def processValue (p : Problem) : MetaM (Array Problem) := do
  trace[Meta.Match.match] "value step"
  match p.vars with
  | []      => unreachable!
  | x :: xs =>
    let values := collectValues p
    let subgoals ← caseValues p.mvarId x.fvarId! values (substNewEqs := true)
    subgoals.mapIdxM fun i subgoal => do
      trace[Meta.Match.match] "processValue subgoal\n{MessageData.ofGoal subgoal.mvarId}"
      if h : i.val < values.size then
        let value := values.get ⟨i, h⟩
        -- (x = value) branch
        let subst := subgoal.subst
        trace[Meta.Match.match] "processValue subst: {subst.map.toList.map fun p => mkFVar p.1}, {subst.map.toList.map fun p => p.2}"
          let examples := p.examples.map <| Example.replaceFVarId x.fvarId! (Example.val value)
        let examples := examples.map <| Example.applyFVarSubst subst
        let newAlts  := p.alts.filter fun alt => match alt.patterns with
          | Pattern.val v :: _ => v == value
          | Pattern.var _ :: _ => true
          | _                  => false
        let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst
        let newAlts := newAlts.map fun alt => match alt.patterns with
          | Pattern.val _ :: ps      => { alt with patterns := ps }
          | Pattern.var fvarId :: ps =>
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
    | Pattern.arrayLit _ ps :: _ => let sz := ps.length; if sizes.contains sz then sizes else sizes.push sz
    | _                          => sizes

private def expandVarIntoArrayLit (alt : Alt) (fvarId : FVarId) (arrayElemType : Expr) (arraySize : Nat) : MetaM Alt :=
  withExistingLocalDecls alt.fvarDecls do
    let fvarDecl ← getLocalDecl fvarId
    let varNamePrefix := fvarDecl.userName
    let rec loop (n : Nat) (newVars : Array Expr) := do
      match n with
      | n+1 =>
        withLocalDeclD (varNamePrefix.appendIndexAfter (n+1)) arrayElemType fun x =>
          loop n (newVars.push x)
      | 0 =>
        let arrayLit ← mkArrayLit arrayElemType newVars.toList
        let alt := alt.replaceFVarId fvarId arrayLit
        let newDecls ← newVars.toList.mapM fun newVar => getLocalDecl newVar.fvarId!
        let newPatterns := newVars.toList.map fun newVar => Pattern.var newVar.fvarId!
        return { alt with fvarDecls := newDecls ++ alt.fvarDecls, patterns := newPatterns ++ alt.patterns }
    loop arraySize #[]

private def processArrayLit (p : Problem) : MetaM (Array Problem) := do
  trace[Meta.Match.match] "array literal step"
  match p.vars with
  | []      => unreachable!
  | x :: xs => do
    let sizes := collectArraySizes p
    let subgoals ← caseArraySizes p.mvarId x.fvarId! sizes
    subgoals.mapIdxM fun i subgoal => do
      if i.val < sizes.size then
        let size     := sizes.get! i
        let subst    := subgoal.subst
        let elems    := subgoal.elems.toList
        let newVars  := elems.map mkFVar ++ xs
        let newVars  := newVars.map fun x => x.applyFVarSubst subst
        let subex    := Example.arrayLit <| elems.map Example.var
        let examples := p.examples.map <| Example.replaceFVarId x.fvarId! subex
        let examples := examples.map <| Example.applyFVarSubst subst
        let newAlts  := p.alts.filter fun alt => match alt.patterns with
          | Pattern.arrayLit _ ps :: _ => ps.length == size
          | Pattern.var _ :: _         => true
          | _                          => false
        let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst
        let newAlts ← newAlts.mapM fun alt => do
          match alt.patterns with
          | Pattern.arrayLit _ pats :: ps => return { alt with patterns := pats ++ ps }
          | Pattern.var fvarId :: ps      =>
            let α ← getArrayArgType <| subst.apply x
            expandVarIntoArrayLit { alt with patterns := ps } fvarId α size
          | _  => unreachable!
        return { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }
      else
        -- else branch
        let newAlts := p.alts.filter isFirstPatternVar
        return { p with mvarId := subgoal.mvarId, alts := newAlts, vars := x::xs }

private def expandNatValuePattern (p : Problem) : Problem :=
  let alts := p.alts.map fun alt => match alt.patterns with
    | Pattern.val (Expr.lit (Literal.natVal 0) _) :: ps     => { alt with patterns := Pattern.ctor `Nat.zero [] [] [] :: ps }
    | Pattern.val (Expr.lit (Literal.natVal (n+1)) _) :: ps => { alt with patterns := Pattern.ctor `Nat.succ [] [] [Pattern.val (mkRawNatLit n)] :: ps }
    | _                                                     => alt
  { p with alts := alts }

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

private partial def process (p : Problem) : StateRefT State MetaM Unit :=
  search 0
where
  /- If `p.vars` is empty, then we are done. Otherwise, we process `p.vars[0]`. -/
  tryToProcess (p : Problem) : StateRefT State MetaM Unit := withIncRecDepth do
    traceState p
    let isInductive ← isCurrVarInductive p
    if isDone p then
      processLeaf p
    else if hasAsPattern p then
      traceStep ("as-pattern")
      let p ← processAsPattern p
      process p
    else if isNatValueTransition p then
      traceStep ("nat value to constructor")
      process (expandNatValuePattern p)
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
    else if hasNatValPattern p then
      -- This branch is reachable when `p`, for example, is just values without an else-alternative.
      -- We added it just to get better error messages.
      traceStep ("nat value to constructor")
      process (expandNatValuePattern p)
    else
      checkNextPatternTypes p
      throwNonSupported p

  /- Return `true` if `type` does not depend on the first `i` elements in `xs` -/
  checkVarDeps (xs : List Expr) (i : Nat) (type : Expr) : MetaM Bool := do
    match i, xs with
    | 0,   _     => return true
    | _,   []    => unreachable!
    | i+1, x::xs =>
      if x.isFVar then
        if (← dependsOn type x.fvarId!) then
          return false
      checkVarDeps xs i type

  /--
    Auxiliary method for `search`. Find next variable to "try".
    `i` is the position of the variable s.t. `tryToProcess` failed.
    We only consider variables that do not depend on other variables at `p.vars`. -/
  findNext (i : Nat) : MetaM (Option Nat) := do
    if h : i < p.vars.length then
      let x := p.vars.get ⟨i, h⟩
      if (← checkVarDeps p.vars i (← inferType x)) then
        return i
      else
        findNext (i+1)
    else
      return none

  /--
    Auxiliary method for trying the next variable to process.
    It moves variable `#i` to the front of the to-do list and invokes `tryToProcess`.
    Note that for non-dependent elimination, variable `#0` always work.
    If variable `#i` fails, we use `findNext` to select the next variable to try.
    Remark: the "missing cases" error is not considered a failure. -/
  search (i : Nat) : StateRefT State MetaM Unit := do
    let s₁ ← getThe Meta.State
    let s₂ ← get
    let p' := moveToFront p i
    try
      tryToProcess p'
    catch ex =>
      match (← withGoalOf p <| findNext (i+1)) with
      | none   => throw ex
      | some j =>
        trace[Meta.Match.match] "failed with #{i}, trying #{j}{indentD ex.toMessageData}"
        set s₁; set s₂; search j

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

builtin_initialize matcherExt : EnvExtension (Std.PHashMap (Expr × Bool) Name) ← registerEnvExtension (pure {})

/- Similar to `mkAuxDefinition`, but uses the cache `matcherExt`.
   It also returns an Boolean that indicates whether a new matcher function was added to the environment or not. -/
def mkMatcherAuxDefinition (name : Name) (type : Expr) (value : Expr) : MetaM (Expr × Option (MatcherInfo → MetaM Unit)) := do
  trace[Meta.Match.debug] "{name} : {type} := {value}"
  let compile := bootstrap.genMatcherCode.get (← getOptions)
  let result ← Closure.mkValueTypeClosure type value (zeta := false)
  let env ← getEnv
  let mkMatcherConst name :=
    mkAppN (mkConst name result.levelArgs.toList) result.exprArgs
  match (matcherExt.getState env).find? (result.value, compile) with
  | some nameNew => return (mkMatcherConst nameNew, none)
  | none =>
    let decl := Declaration.defnDecl {
      name
      levelParams := result.levelParams.toList
      type        := result.type
      value       := result.value
      hints       := ReducibilityHints.abbrev
      safety      := if env.hasUnsafe result.type || env.hasUnsafe result.value then DefinitionSafety.unsafe else DefinitionSafety.safe
    }
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
where `v` is a universe parameter or 0 if `B[a_1, ..., a_n]` is a proposition. -/
def mkMatcher (input : MkMatcherInput) : MetaM MatcherResult := withCleanLCtxFor input do
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
          if isEqMask[isEqMaskIdx] then
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
      then mkLevelParam matcherConst.levelParams.toArray[idx]
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

/- This function is only used for testing purposes -/
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

/- Auxiliary function for MatcherApp.addArg -/
private partial def updateAlts (typeNew : Expr) (altNumParams : Array Nat) (alts : Array Expr) (i : Nat) : MetaM (Array Nat × Array Expr) := do
  if h : i < alts.size then
    let alt       := alts.get ⟨i, h⟩
    let numParams := altNumParams[i]
    let typeNew ← whnfD typeNew
    match typeNew with
    | Expr.forallE _ d b _ =>
      let alt ← forallBoundedTelescope d (some numParams) fun xs d => do
        let alt ← try instantiateLambda alt xs catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"
        forallBoundedTelescope d (some 1) fun x _ => do
          let alt ← mkLambdaFVars x alt -- x is the new argument we are adding to the alternative
          mkLambdaFVars xs alt
      updateAlts (b.instantiate1 alt) (altNumParams.set! i (numParams+1)) (alts.set ⟨i, h⟩ alt) (i+1)
    | _ => throwError "unexpected type at MatcherApp.addArg"
  else
    return (altNumParams, alts)

/- Given
  - matcherApp `match_i As (fun xs => motive[xs]) discrs (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining`, and
  - expression `e : B[discrs]`,
  Construct the term
  `match_i As (fun xs => B[xs] -> motive[xs]) discrs (fun ys_1 (y : B[C_1[ys_1]]) => alt_1) ... (fun ys_n (y : B[C_n[ys_n]]) => alt_n) e remaining`, and
  We use `kabstract` to abstract the discriminants from `B[discrs]`.
  This method assumes
  - the `matcherApp.motive` is a lambda abstraction where `xs.size == discrs.size`
  - each alternative is a lambda abstraction where `ys_i.size == matcherApp.altNumParams[i]`
-/
def MatcherApp.addArg (matcherApp : MatcherApp) (e : Expr) : MetaM MatcherApp :=
  lambdaTelescope matcherApp.motive fun motiveArgs motiveBody => do
    unless motiveArgs.size == matcherApp.discrs.size do
      -- This error can only happen if someone implemented a transformation that rewrites the motive created by `mkMatcher`.
      throwError "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"
    let eType ← inferType e
    let eTypeAbst ← matcherApp.discrs.size.foldRevM (init := eType) fun i eTypeAbst => do
      let motiveArg := motiveArgs[i]
      let discr     := matcherApp.discrs[i]
      let eTypeAbst ← kabstract eTypeAbst discr
      return eTypeAbst.instantiate1 motiveArg
    let motiveBody ← mkArrow eTypeAbst motiveBody
    let matcherLevels ← match matcherApp.uElimPos? with
      | none     => pure matcherApp.matcherLevels
      | some pos =>
        let uElim ← getLevel motiveBody
        pure <| matcherApp.matcherLevels.set! pos uElim
    let motive ← mkLambdaFVars motiveArgs motiveBody
    -- Construct `aux` `match_i As (fun xs => B[xs] → motive[xs]) discrs`, and infer its type `auxType`.
    -- We use `auxType` to infer the type `B[C_i[ys_i]]` of the new argument in each alternative.
    let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) matcherApp.params
    let aux := mkApp aux motive
    let aux := mkAppN aux matcherApp.discrs
    unless (← isTypeCorrect aux) do
      throwError "failed to add argument to matcher application, type error when constructing the new motive"
    let auxType ← inferType aux
    let (altNumParams, alts) ← updateAlts auxType matcherApp.altNumParams matcherApp.alts 0
    return { matcherApp with
      matcherLevels := matcherLevels,
      motive        := motive,
      alts          := alts,
      altNumParams  := altNumParams,
      remaining     := #[e] ++ matcherApp.remaining
    }

/-- Similar `MatcherApp.addArg?`, but returns `none` on failure. -/
def MatcherApp.addArg? (matcherApp : MatcherApp) (e : Expr) : MetaM (Option MatcherApp) :=
  try
    return some (← matcherApp.addArg e)
  catch _ =>
    return none

builtin_initialize
  registerTraceClass `Meta.Match.match
  registerTraceClass `Meta.Match.debug
  registerTraceClass `Meta.Match.unify

end Lean.Meta
