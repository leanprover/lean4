/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.CollectLevelParams
import Lean.Util.Recognizers
import Lean.Compiler.ExternAttr
import Lean.Meta.Check
import Lean.Meta.Closure
import Lean.Meta.Tactic.Cases
import Lean.Meta.GeneralizeTelescope
import Lean.Meta.Match.MVarRenaming
import Lean.Meta.Match.CaseValues
import Lean.Meta.Match.CaseArraySizes

namespace Lean.Meta.Match

inductive Pattern : Type
  | inaccessible (e : Expr) : Pattern
  | var          (fvarId : FVarId) : Pattern
  | ctor         (ctorName : Name) (us : List Level) (params : List Expr) (fields : List Pattern) : Pattern
  | val          (e : Expr) : Pattern
  | arrayLit     (type : Expr) (xs : List Pattern) : Pattern
  | as           (varId : FVarId) (p : Pattern) : Pattern

namespace Pattern

instance : Inhabited Pattern := ⟨Pattern.inaccessible (arbitrary _)⟩

partial def toMessageData : Pattern → MessageData
  | inaccessible e         => msg!".({e})"
  | var varId              => mkFVar varId
  | ctor ctorName _ _ []   => ctorName
  | ctor ctorName _ _ pats => msg!"({ctorName}{pats.foldl (fun (msg : MessageData) pat => msg ++ " " ++ toMessageData pat) Format.nil})"
  | val e                  => e
  | arrayLit _ pats        => msg!"#[{MessageData.joinSep (pats.map toMessageData) ", "}]"
  | as varId p             => msg!"{mkFVar varId}@{toMessageData p}"

partial def toExpr : Pattern → MetaM Expr
  | inaccessible e                 => pure e
  | var fvarId                     => pure $ mkFVar fvarId
  | val e                          => pure e
  | as _ p                         => toExpr p
  | arrayLit type xs               => do
    let xs ← xs.mapM toExpr;
    mkArrayLit type xs
  | ctor ctorName us params fields => do
    let fields ← fields.mapM toExpr;
    pure $ mkAppN (mkConst ctorName us) (params ++ fields).toArray

/- Apply the free variable substitution `s` to the given pattern -/
partial def applyFVarSubst (s : FVarSubst) : Pattern → Pattern
  | inaccessible e  => inaccessible $ s.apply e
  | ctor n us ps fs => ctor n us (ps.map s.apply) $ fs.map (applyFVarSubst s)
  | val e           => val $ s.apply e
  | arrayLit t xs   => arrayLit (s.apply t) $ xs.map (applyFVarSubst s)
  | var fvarId      => match s.find? fvarId with
    | some e => inaccessible e
    | none   => var fvarId
  | as fvarId p     => match s.find? fvarId with
    | none   => as fvarId $ applyFVarSubst s p
    | some _ => applyFVarSubst s p

def replaceFVarId (fvarId : FVarId) (v : Expr) (p : Pattern) : Pattern :=
  let s : FVarSubst := {}
  p.applyFVarSubst (s.insert fvarId v)

end Pattern

structure AltLHS :=
  (ref        : Syntax)
  (fvarDecls  : List LocalDecl) -- Free variables used in the patterns.
  (patterns   : List Pattern)   -- We use `List Pattern` since we have nary match-expressions.

structure Alt :=
  (ref       : Syntax)
  (idx       : Nat) -- for generating error messages
  (rhs       : Expr)
  (fvarDecls : List LocalDecl)
  (patterns  : List Pattern)

namespace Alt

instance : Inhabited Alt := ⟨⟨arbitrary _, 0, arbitrary _, [], []⟩⟩

partial def toMessageData (alt : Alt) : MetaM MessageData := do
  withExistingLocalDecls alt.fvarDecls do
    let msg : List MessageData := alt.fvarDecls.map fun d => d.toExpr ++ ":(" ++ d.type ++ ")"
    let msg : MessageData := msg ++ " |- " ++ (alt.patterns.map Pattern.toMessageData) ++ " => " ++ alt.rhs
    addMessageContext msg

def applyFVarSubst (s : FVarSubst) (alt : Alt) : Alt :=
  { alt with
    patterns  := alt.patterns.map fun p => p.applyFVarSubst s,
    fvarDecls := alt.fvarDecls.map fun d => d.applyFVarSubst s,
    rhs       := alt.rhs.applyFVarSubst s }

def replaceFVarId (fvarId : FVarId) (v : Expr) (alt : Alt) : Alt :=
  { alt with
    patterns  := alt.patterns.map fun p => p.replaceFVarId fvarId v,
    fvarDecls :=
      let decls := alt.fvarDecls.filter fun d => d.fvarId != fvarId
      decls.map $ replaceFVarIdAtLocalDecl fvarId v,
    rhs       := alt.rhs.replaceFVarId fvarId v }

/-
  Similar to `checkAndReplaceFVarId`, but ensures type of `v` is definitionally equal to type of `fvarId`.
  This extra check is necessary when performing dependent elimination and inaccessible terms have been used.
  For example, consider the following code fragment:

```
inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n} (head : α) (tail : Vec α n) : Vec α (n+1)

inductive VecPred {α : Type u} (P : α → Prop) : {n : Nat} → Vec α n → Prop
  | nil   : VecPred P Vec.nil
  | cons  {n : Nat} {head : α} {tail : Vec α n} : P head → VecPred P tail → VecPred P (Vec.cons head tail)

theorem ex {α : Type u} (P : α → Prop) : {n : Nat} → (v : Vec α (n+1)) → VecPred P v → Exists P
  | _, Vec.cons head _, VecPred.cons h (w : VecPred P Vec.nil) => ⟨head, h⟩
```
Recall that `_` in a pattern can be elaborated into pattern variable or an inaccessible term.
The elaborator uses an inaccessible term when typing constraints restrict its value.
Thus, in the example above, the `_` at `Vec.cons head _` becomes the inaccessible pattern `.(Vec.nil)`
because the type ascription `(w : VecPred P Vec.nil)` propagates typing constraints that restrict its value to be `Vec.nil`.
After elaboration the alternative becomes:
```
  | .(0), @Vec.cons .(α) .(0) head .(Vec.nil), @VecPred.cons .(α) .(P) .(0) .(head) .(Vec.nil) h w => ⟨head, h⟩
```
where
```
(head : α), (h: P head), (w : VecPred P Vec.nil)
```
Then, when we process this alternative in this module, the following check will detect that
`w` has type `VecPred P Vec.nil`, when it is supposed to have type `VecPred P tail`.
Note that if we had written
```
theorem ex {α : Type u} (P : α → Prop) : {n : Nat} → (v : Vec α (n+1)) → VecPred P v → Exists P
  | _, Vec.cons head Vec.nil, VecPred.cons h (w : VecPred P Vec.nil) => ⟨head, h⟩
```
we would get the easier to digest error message
```
missing cases:
_, (Vec.cons _ _ (Vec.cons _ _ _)), _
```
-/
def checkAndReplaceFVarId (fvarId : FVarId) (v : Expr) (alt : Alt) : MetaM Alt := do
  match alt.fvarDecls.find? fun (fvarDecl : LocalDecl) => fvarDecl.fvarId == fvarId with
  | none          => throwErrorAt alt.ref "unknown free pattern variable"
  | some fvarDecl => do
    let vType ← inferType v
    unless (← isDefEqGuarded fvarDecl.type vType) do
      withExistingLocalDecls alt.fvarDecls do
        throwErrorAt alt.ref $
          msg!"type mismatch during dependent match-elimination at pattern variable '{mkFVar fvarDecl.fvarId}' with type{indentExpr fvarDecl.type}\nexpected type{indentExpr vType}"
    pure $ replaceFVarId fvarId v alt

end Alt

inductive Example
  | var        : FVarId → Example
  | underscore : Example
  | ctor       : Name → List Example → Example
  | val        : Expr → Example
  | arrayLit   : List Example → Example

namespace Example

partial def replaceFVarId (fvarId : FVarId) (ex : Example) : Example → Example
  | var x        => if x == fvarId then ex else var x
  | ctor n exs   => ctor n $ exs.map (replaceFVarId fvarId ex)
  | arrayLit exs => arrayLit $ exs.map (replaceFVarId fvarId ex)
  | ex           => ex

partial def applyFVarSubst (s : FVarSubst) : Example → Example
  | var fvarId =>
    match s.get fvarId with
    | Expr.fvar fvarId' _ => var fvarId'
    | _                   => underscore
  | ctor n exs   => ctor n $ exs.map (applyFVarSubst s)
  | arrayLit exs => arrayLit $ exs.map (applyFVarSubst s)
  | ex           => ex

partial def varsToUnderscore : Example → Example
  | var x        => underscore
  | ctor n exs   => ctor n $ exs.map varsToUnderscore
  | arrayLit exs => arrayLit $ exs.map varsToUnderscore
  | ex           => ex

partial def toMessageData : Example → MessageData
  | var fvarId        => mkFVar fvarId
  | ctor ctorName []  => mkConst ctorName
  | ctor ctorName exs => "(" ++ mkConst ctorName ++ exs.foldl (fun (msg : MessageData) pat => msg ++ " " ++ toMessageData pat) Format.nil ++ ")"
  | arrayLit exs      => "#" ++ MessageData.ofList (exs.map toMessageData)
  | val e             => e
  | underscore        => "_"

end Example

def examplesToMessageData (cex : List Example) : MessageData :=
  MessageData.joinSep (cex.map (Example.toMessageData ∘ Example.varsToUnderscore)) ", "

structure Problem :=
  (mvarId        : MVarId)
  (vars          : List Expr)
  (alts          : List Alt)
  (examples      : List Example)

def withGoalOf {α} (p : Problem) (x : MetaM α) : MetaM α :=
  withMVarContext p.mvarId x

instance : Inhabited Problem := ⟨{ mvarId := arbitrary _, vars := [], alts := [], examples := []}⟩

def Problem.toMessageData (p : Problem) : MetaM MessageData :=
  withGoalOf p do
    let alts ← p.alts.mapM Alt.toMessageData
    let vars ← p.vars.mapM fun x => do let xType ← inferType x; pure (x ++ ":(" ++ xType ++ ")" : MessageData)
    return "remaining variables: " ++ vars
      ++ Format.line ++ "alternatives:" ++ indentD (MessageData.joinSep alts Format.line)
      ++ Format.line ++ "examples: " ++ examplesToMessageData p.examples
      ++ Format.line

abbrev CounterExample := List Example

def counterExampleToMessageData (cex : CounterExample) : MessageData :=
  examplesToMessageData cex

def counterExamplesToMessageData (cexs : List CounterExample) : MessageData :=
  MessageData.joinSep (cexs.map counterExampleToMessageData) Format.line

structure MatcherResult :=
  (matcher         : Expr) -- The matcher. It is not just `Expr.const matcherName` because the type of the major premises may contain free variables.
  (counterExamples : List CounterExample)
  (unusedAltIdxs   : List Nat)

/- The number of patterns in each AltLHS must be equal to majors.length -/
private def checkNumPatterns (majors : Array Expr) (lhss : List AltLHS) : MetaM Unit := do
  let num := majors.size
  if lhss.any fun lhs => lhs.patterns.length != num then
    throwError "incorrect number of patterns"

private partial def withAltsAux {α} (motive : Expr) : List AltLHS → List Alt → Array (Expr × Nat) → (List Alt → Array (Expr × Nat) → MetaM α) → MetaM α
  | [],        alts, minors, k => k alts.reverse minors
  | lhs::lhss, alts, minors, k => do
    let xs := lhs.fvarDecls.toArray.map LocalDecl.toExpr
    let minorType ← withExistingLocalDecls lhs.fvarDecls do
      let args ← lhs.patterns.toArray.mapM Pattern.toExpr
      let minorType := mkAppN motive args
      mkForallFVars xs minorType
    let (minorType, minorNumParams) := if !xs.isEmpty then (minorType, xs.size) else (mkSimpleThunkType minorType, 1)
    let idx       := alts.length
    let minorName := (`h).appendIndexAfter (idx+1)
    trace[Meta.Match.debug]! "minor premise {minorName} : {minorType}"
    withLocalDeclD minorName minorType fun minor => do
      let rhs    := if xs.isEmpty then mkApp minor (mkConst `Unit.unit) else mkAppN minor xs
      let minors := minors.push (minor, minorNumParams)
      let fvarDecls ← lhs.fvarDecls.mapM instantiateLocalDeclMVars
      let alts   := { ref := lhs.ref, idx := idx, rhs := rhs, fvarDecls := fvarDecls, patterns := lhs.patterns : Alt } :: alts
      withAltsAux motive lhss alts minors k

/- Given a list of `AltLHS`, create a minor premise for each one, convert them into `Alt`, and then execute `k` -/
private partial def withAlts {α} (motive : Expr) (lhss : List AltLHS) (k : List Alt → Array (Expr × Nat) → MetaM α) : MetaM α :=
  withAltsAux motive lhss [] #[] k

def assignGoalOf (p : Problem) (e : Expr) : MetaM Unit :=
  withGoalOf p (assignExprMVar p.mvarId e)

structure State :=
  (used            : Std.HashSet Nat := {}) -- used alternatives
  (counterExamples : List (List Example) := [])

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
    | Pattern.as _ _ :: _ => true
    | _                   => false

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
  | x :: xs => do
    let alts := p.alts.map fun alt => match alt.patterns with
      | Pattern.inaccessible _ :: ps => { alt with patterns := ps }
      | _       => unreachable!
    { p with alts := alts, vars := xs }

private def processLeaf (p : Problem) : StateRefT State MetaM Unit :=
  match p.alts with
  | []       => do
    liftM $ admit p.mvarId
    modify fun s => { s with counterExamples := p.examples :: s.counterExamples }
  | alt :: _ => do
    -- TODO: check whether we have unassigned metavars in rhs
    liftM $ assignGoalOf p alt.rhs
    modify fun s => { s with used := s.used.insert alt.idx }

private def processAsPattern (p : Problem) : MetaM Problem :=
  match p.vars with
  | []      => unreachable!
  | x :: xs => withGoalOf p do
    let alts ← p.alts.mapM fun alt => match alt.patterns with
      | Pattern.as fvarId p :: ps => { alt with patterns := p :: ps }.checkAndReplaceFVarId fvarId x
      | _                         => pure alt
    pure { p with alts := alts }

private def processVariable (p : Problem) : MetaM Problem :=
  match p.vars with
  | []      => unreachable!
  | x :: xs => withGoalOf p do
    let alts ← p.alts.mapM fun alt => match alt.patterns with
      | Pattern.inaccessible _ :: ps => pure { alt with patterns := ps }
      | Pattern.var fvarId :: ps     => { alt with patterns := ps }.checkAndReplaceFVarId fvarId x
      | _                            => unreachable!
    pure { p with alts := alts, vars := xs }

private def throwInductiveTypeExpected {α} (e : Expr) : MetaM α := do
  let t ← inferType e
  throwError! "failed to compile pattern matching, inductive type expected{indentExpr e}\nhas type{indentExpr t}"

private def inLocalDecls (localDecls : List LocalDecl) (fvarId : FVarId) : Bool :=
  localDecls.any fun d => d.fvarId == fvarId

namespace Unify

structure Context :=
  (altFVarDecls : List LocalDecl)

structure State :=
  (fvarSubst : FVarSubst := {})

abbrev M := ReaderT Context $ StateRefT State MetaM

def isAltVar (fvarId : FVarId) : M Bool := do
  return inLocalDecls (← read).altFVarDecls fvarId

def expandIfVar (e : Expr) : M Expr := do
  match e with
  | Expr.fvar _ _ => return (← get).fvarSubst.apply e
  | _             => return e

def occurs (fvarId : FVarId) (v : Expr) : Bool :=
  Option.isSome $ v.find? fun e => match e with
     | Expr.fvar fvarId' _ => fvarId == fvarId'
     | _=> false

def assign (fvarId : FVarId) (v : Expr) : M Bool := do
  if occurs fvarId v then
    trace[Meta.Match.unify]! "assign occurs check failed, {mkFVar fvarId} := {v}"
    pure false
  else
    let ctx ← read
    if (← isAltVar fvarId) then
      trace[Meta.Match.unify]! "{mkFVar fvarId} := {v}"
      modify fun s => { s with fvarSubst := s.fvarSubst.insert fvarId v }
      pure true
    else
      trace[Meta.Match.unify]! "assign failed variable is not local, {mkFVar fvarId} := {v}"
      pure false

partial def unify (a : Expr) (b : Expr) : M Bool := do
  trace[Meta.Match.unify]! "{a} =?= {b}"
  if (← isDefEq a b) then
    pure true
  else
    let a' ← expandIfVar a
    let b' ← expandIfVar b
    if a != a' || b != b' then unify a' b'
    else match a, b with
      | Expr.mdata _ a _, b                      => unify a b
      | a, Expr.mdata _ b _                      => unify a b
      | Expr.fvar aFvarId _, Expr.fvar bFVarId _ => assign aFvarId b <||> assign bFVarId a
      | Expr.fvar aFvarId _, b => assign aFvarId b
      | a, Expr.fvar bFVarId _ => assign bFVarId a
      | Expr.app aFn aArg _, Expr.app bFn bArg _ => unify aFn bFn <&&> unify aArg bArg
      | _, _ =>
        trace[Meta.Match.unify]! "unify failed @ {a} =?= {b}"
        pure false

end Unify

private def unify? (altFVarDecls : List LocalDecl) (a b : Expr) : MetaM (Option FVarSubst) := do
  let a ← instantiateMVars a
    let b ← instantiateMVars b
    let (b, s) ← Unify.unify a b { altFVarDecls := altFVarDecls} $.run {}
    if b then pure s.fvarSubst else pure none

private def expandVarIntoCtor? (alt : Alt) (fvarId : FVarId) (ctorName : Name) : MetaM (Option Alt) :=
  withExistingLocalDecls alt.fvarDecls do
    let env ← getEnv
    let ldecl ← getLocalDecl fvarId
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
      | none       => pure none
      | some subst =>
        let newAltDecls := newAltDecls.filter fun d => !subst.contains d.fvarId -- remove declarations that were assigned
        let newAltDecls := newAltDecls.map fun d => d.applyFVarSubst subst -- apply substitution to remaining declaration types
        let patterns    := alt.patterns.map fun p => p.applyFVarSubst subst
        let rhs         := subst.apply alt.rhs
        let ctorFieldPatterns := ctorFields.toList.map fun ctorField => match subst.get ctorField.fvarId! with
          | e@(Expr.fvar fvarId _) => if inLocalDecls newAltDecls fvarId then Pattern.var fvarId else Pattern.inaccessible e
          | e                      => Pattern.inaccessible e
        pure $ some { alt with fvarDecls := newAltDecls, rhs := rhs, patterns := ctorFieldPatterns ++ patterns }

private def getInductiveVal? (x : Expr) : MetaM (Option InductiveVal) := do
  let xType ← inferType x
  let xType ← whnfD xType
  match xType.getAppFn with
  | Expr.const constName _ _ =>
    let cinfo ← getConstInfo constName
    match cinfo with
    | ConstantInfo.inductInfo val => pure (some val)
    | _ => pure none
  | _ => pure none

private def hasRecursiveType (x : Expr) : MetaM Bool := do
  match (← getInductiveVal? x) with
  | some val => pure val.isRec
  | _        => pure false

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
    trace[Meta.Match.match]! "inaccessible in ctor step {e}"
    withExistingLocalDecls alt.fvarDecls do
      -- Try to push inaccessible annotations.
      let e ← whnfD e
      match e.constructorApp? env with
      | some (ctorVal, ctorArgs) =>
        if ctorVal.name == ctorName then
          let fields := ctorArgs.extract ctorVal.nparams ctorArgs.size
          let fields := fields.toList.map Pattern.inaccessible
          pure $ some { alt with patterns := fields ++ ps }
        else
          pure none
      | _ => throwErrorAt! alt.ref "dependent match elimination failed, inaccessible pattern found{indentD p.toMessageData}\nconstructor expected"
  | _ => unreachable!

private def processConstructor (p : Problem) : MetaM (Array Problem) := do
  trace[Meta.Match.match]! "constructor step"
  let env ← getEnv
  match p.vars with
  | []      => unreachable!
  | x :: xs => do
    let subgoals? ← commitWhenSome? do
       let subgoals ← cases p.mvarId x.fvarId!
       if subgoals.isEmpty then
         /- Easy case: we have solved problem `p` since there are no subgoals -/
         pure (some #[])
       else if !p.alts.isEmpty then
         pure (some subgoals)
       else do
         let isRec ← withGoalOf p $ hasRecursiveType x
          /- If there are no alternatives and the type of the current variable is recursive, we do NOT consider
            a constructor-transition to avoid nontermination.
            TODO: implement a more general approach if this is not sufficient in practice -/
         if isRec then pure none
         else pure (some subgoals)
    match subgoals? with
    | none          => pure #[{ p with vars := xs }]
    | some subgoals =>
      subgoals.mapM fun subgoal => withMVarContext subgoal.mvarId do
        let subst    := subgoal.subst
        let fields   := subgoal.fields.toList
        let newVars  := fields ++ xs
        let newVars  := newVars.map fun x => x.applyFVarSubst subst
        let subex    := Example.ctor subgoal.ctorName $ fields.map fun field => match field with
          | Expr.fvar fvarId _ => Example.var fvarId
          | _                  => Example.underscore -- This case can happen due to dependent elimination
        let examples := p.examples.map $ Example.replaceFVarId x.fvarId! subex
        let examples := examples.map $ Example.applyFVarSubst subst
        let newAlts  := p.alts.filter fun alt => match alt.patterns with
          | Pattern.ctor n _ _ _ :: _    => n == subgoal.ctorName
          | Pattern.var _ :: _           => true
          | Pattern.inaccessible _ :: _  => true
          | _                            => false
        let newAlts  := newAlts.map fun alt => alt.applyFVarSubst subst
        let newAlts ← newAlts.filterMapM fun alt => match alt.patterns with
          | Pattern.ctor _ _ _ fields :: ps  => pure $ some { alt with patterns := fields ++ ps }
          | Pattern.var fvarId :: ps         => expandVarIntoCtor? { alt with patterns := ps } fvarId subgoal.ctorName
          | Pattern.inaccessible _ :: _      => processInaccessibleAsCtor alt subgoal.ctorName
          | _                                => unreachable!
        pure { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }

private def processNonVariable (p : Problem) : MetaM Problem :=
  match p.vars with
  | []      => unreachable!
  | x :: xs => withGoalOf p do
    let x ← whnfD x
    let env ← getEnv
    match x.constructorApp? env with
    | some (ctorVal, xArgs) =>
      let alts ← p.alts.filterMapM fun alt => match alt.patterns with
        | Pattern.ctor n _ _ fields :: ps   =>
          if n != ctorVal.name then
            pure none
          else
            pure $ some { alt with patterns := fields ++ ps }
        | Pattern.inaccessible _ :: _ => processInaccessibleAsCtor alt ctorVal.name
        | p :: _  => throwError! "failed to compile pattern matching, inaccessible pattern or constructor expected{indentD p.toMessageData}"
        | _       => unreachable!
      let xFields := xArgs.extract ctorVal.nparams xArgs.size
      pure { p with alts := alts, vars := xFields.toList ++ xs }
    | none => throwError! "failed to compile pattern matching, constructor expected{indentExpr x}"

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
  trace[Meta.Match.match]! "value step"
  match p.vars with
  | []      => unreachable!
  | x :: xs => do
    let values := collectValues p
    let subgoals ← caseValues p.mvarId x.fvarId! values
    subgoals.mapIdxM fun i subgoal => do
      if h : i.val < values.size then
        let value := values.get ⟨i, h⟩
        -- (x = value) branch
        let subst := subgoal.subst
        let examples := p.examples.map $ Example.replaceFVarId x.fvarId! (Example.val value)
        let examples := examples.map $ Example.applyFVarSubst subst
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
        pure { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }
      else
        -- else branch for value
        let newAlts := p.alts.filter isFirstPatternVar
        pure { p with mvarId := subgoal.mvarId, alts := newAlts, vars := x::xs }

private def collectArraySizes (p : Problem) : Array Nat :=
  p.alts.foldl (init := #[]) fun sizes alt =>
    match alt.patterns with
    | Pattern.arrayLit _ ps :: _ => let sz := ps.length; if sizes.contains sz then sizes else sizes.push sz
    | _                          => sizes

private def expandVarIntoArrayLit (alt : Alt) (fvarId : FVarId) (arrayElemType : Expr) (arraySize : Nat) : MetaM Alt :=
  withExistingLocalDecls alt.fvarDecls do
    let fvarDecl ← getLocalDecl fvarId
    let varNamePrefix := fvarDecl.userName
    let rec loop
    | n+1, newVars =>
      withLocalDeclD (varNamePrefix.appendIndexAfter (n+1)) arrayElemType fun x =>
        loop n (newVars.push x)
    | 0, newVars => do
      let arrayLit ← mkArrayLit arrayElemType newVars.toList
      let alt := alt.replaceFVarId fvarId arrayLit
      let newDecls ← newVars.toList.mapM fun newVar => getLocalDecl newVar.fvarId!
      let newPatterns := newVars.toList.map fun newVar => Pattern.var newVar.fvarId!
      pure { alt with fvarDecls := newDecls ++ alt.fvarDecls, patterns := newPatterns ++ alt.patterns }
    loop arraySize #[]

private def processArrayLit (p : Problem) : MetaM (Array Problem) := do
  trace[Meta.Match.match]! "array literal step"
  match p.vars with
  | []      => unreachable!
  | x :: xs => do
    let sizes := collectArraySizes p
    let subgoals ← caseArraySizes p.mvarId x.fvarId! sizes
    subgoals.mapIdxM fun i subgoal => do
      if h : i.val < sizes.size then
        let size     := sizes.get! i
        let subst    := subgoal.subst
        let elems    := subgoal.elems.toList
        let newVars  := elems.map mkFVar ++ xs
        let newVars  := newVars.map fun x => x.applyFVarSubst subst
        let subex    := Example.arrayLit $ elems.map Example.var
        let examples := p.examples.map $ Example.replaceFVarId x.fvarId! subex
        let examples := examples.map $ Example.applyFVarSubst subst
        let newAlts  := p.alts.filter fun alt => match alt.patterns with
          | Pattern.arrayLit _ ps :: _ => ps.length == size
          | Pattern.var _ :: _         => true
          | _                          => false
        let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst
        newAlts ← newAlts.mapM fun alt => match alt.patterns with
          | Pattern.arrayLit _ pats :: ps => pure { alt with patterns := pats ++ ps }
          | Pattern.var fvarId :: ps      => do let α ← getArrayArgType x; expandVarIntoArrayLit { alt with patterns := ps } fvarId α size
          | _  => unreachable!
        pure { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }
      else do
        -- else branch
        let newAlts := p.alts.filter isFirstPatternVar
        pure { p with mvarId := subgoal.mvarId, alts := newAlts, vars := x::xs }

private def expandNatValuePattern (p : Problem) : Problem := do
  let alts := p.alts.map fun alt => match alt.patterns with
    | Pattern.val (Expr.lit (Literal.natVal 0) _) :: ps     => { alt with patterns := Pattern.ctor `Nat.zero [] [] [] :: ps }
    | Pattern.val (Expr.lit (Literal.natVal (n+1)) _) :: ps => { alt with patterns := Pattern.ctor `Nat.succ [] [] [Pattern.val (mkNatLit n)] :: ps }
    | _                                                     => alt
  { p with alts := alts }

private def traceStep (msg : String) : StateRefT State MetaM Unit :=
  trace[Meta.Match.match]! "{msg} step"

private def traceState (p : Problem) : MetaM Unit :=
  withGoalOf p (traceM `Meta.Match.match p.toMessageData)

private def throwNonSupported (p : Problem) : MetaM Unit :=
  withGoalOf p do
    let msg ← p.toMessageData
    throwError! "failed to compile pattern matching, stuck at{indentD msg}"

def isCurrVarInductive (p : Problem) : MetaM Bool := do
  match p.vars with
  | []   => pure false
  | x::_ => withGoalOf p do
    let val? ← getInductiveVal? x
    pure val?.isSome

private partial def process (p : Problem) : StateRefT State MetaM Unit := withIncRecDepth do
  traceState p
  let isInductive ← liftM $ isCurrVarInductive p
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
  else
    liftM $ throwNonSupported p

/--
A "matcher" auxiliary declaration has the following structure:
- `numParams` parameters
- motive
- `numDiscrs` discriminators (aka major premises)
- `altNumParams.size` alternatives (aka minor premises) where alternative `i` has `altNumParams[i]` alternatives
- `uElimPos?` is `some pos` when the matcher can eliminate in different universe levels, and
   `pos` is the position of the universe level parameter that specifies the elimination universe.
   It is `none` if the matcher only eliminates into `Prop`. -/
structure MatcherInfo :=
  (numParams : Nat)
  (numDiscrs : Nat)
  (altNumParams : Array Nat)
  (uElimPos? : Option Nat)

def MatcherInfo.numAlts (matcherInfo : MatcherInfo) : Nat :=
  matcherInfo.altNumParams.size

namespace Extension

structure Entry :=
  (name : Name)
  (info : MatcherInfo)

structure State :=
  (map : SMap Name MatcherInfo := {})

instance : Inhabited State := ⟨{}⟩

def State.addEntry (s : State) (e : Entry) : State := { s with map  := s.map.insert e.name e.info }
def State.switch (s : State) : State :=  { s with map := s.map.switch }

builtin_initialize extension : SimplePersistentEnvExtension Entry State ←
  registerSimplePersistentEnvExtension {
    name          := `matcher,
    addEntryFn    := State.addEntry,
    addImportedFn := fun es => (mkStateFromImportedEntries State.addEntry {} es).switch
  }

def addMatcherInfo (env : Environment) (matcherName : Name) (info : MatcherInfo) : Environment :=
  extension.addEntry env { name := matcherName, info := info }

def getMatcherInfo? (env : Environment) (declName : Name) : Option MatcherInfo :=
  (extension.getState env).map.find? declName

end Extension

def addMatcherInfo (matcherName : Name) (info : MatcherInfo) : MetaM Unit :=
  modifyEnv fun env => Extension.addMatcherInfo env matcherName info

private def getUElimPos? (matcherLevels : List Level) (uElim : Level) : MetaM (Option Nat) :=
  if uElim == levelZero then
    pure none
  else match matcherLevels.toArray.indexOf? uElim with
    | none => throwError "dependent match elimination failed, universe level not found"
    | some pos => pure $ some pos.val

/- See comment at `mkMatcher` before `mkAuxDefinition` -/
builtin_initialize
  registerOption `bootstrap.gen_matcher_code { defValue := true, group := "bootstrap", descr := "disable code generation for auxiliary matcher function" }

def generateMatcherCode (opts : Options) : Bool :=
  opts.get `bootstrap.gen_matcher_code true

/-
Create a dependent matcher for `matchType` where `matchType` is of the form
`(a_1 : A_1) -> (a_2 : A_2[a_1]) -> ... -> (a_n : A_n[a_1, a_2, ... a_{n-1}]) -> B[a_1, ..., a_n]`
where `n = numDiscrs`, and the `lhss` are the left-hand-sides of the `match`-expression alternatives.
Each `AltLHS` has a list of local declarations and a list of patterns.
The number of patterns must be the same in each `AltLHS`.
The generated matcher has the structure described at `MatcherInfo`. The motive argument is of the form
`(motive : (a_1 : A_1) -> (a_2 : A_2[a_1]) -> ... -> (a_n : A_n[a_1, a_2, ... a_{n-1}]) -> Sort v)`
where `v` is a universe parameter or 0 if `B[a_1, ..., a_n]` is a proposition. -/
def mkMatcher (matcherName : Name) (matchType : Expr) (numDiscrs : Nat) (lhss : List AltLHS) : MetaM MatcherResult :=
  forallBoundedTelescope matchType numDiscrs fun majors matchTypeBody => do
  checkNumPatterns majors lhss
  /- We generate an matcher that can eliminate using different motives with different universe levels.
     `uElim` is the universe level the caller wants to eliminate to.
     If it is not levelZero, we create a matcher that can eliminate in any universe level.
     This is useful for implementing `MatcherApp.addArg` because it may have to change the universe level. -/
  let uElim ← getLevel matchTypeBody
  let uElimGen ← if uElim == levelZero then pure levelZero else mkFreshLevelMVar
  let motiveType ← mkForallFVars majors (mkSort uElimGen)
  withLocalDeclD `motive motiveType fun motive => do
  trace! `Meta.Match.debug ("motiveType: " ++ motiveType)
  let mvarType  := mkAppN motive majors
  trace! `Meta.Match.debug ("target: " ++ mvarType)
  withAlts motive lhss fun alts minors => do
    let mvar ← mkFreshExprMVar mvarType
    let examples := majors.toList.map fun major => Example.var major.fvarId!
    let (_, s) ← (process { mvarId := mvar.mvarId!, vars := majors.toList, alts := alts, examples := examples }).run {}
    let args := #[motive] ++ majors ++ minors.map Prod.fst
    let type ← mkForallFVars args mvarType
    let val  ← mkLambdaFVars args mvar
    trace! `Meta.Match.debug ("matcher value: " ++ val ++ "\ntype: " ++ type)
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
    let matcher ← mkAuxDefinition matcherName type val (compile := generateMatcherCode (← getOptions))
    trace! `Meta.Match.debug ("matcher levels: " ++ toString matcher.getAppFn.constLevels! ++ ", uElim: " ++ toString uElimGen)
    let uElimPos? ← getUElimPos? matcher.getAppFn.constLevels! uElimGen
    isLevelDefEq uElimGen uElim
    addMatcherInfo matcherName { numParams := matcher.getAppNumArgs, numDiscrs := numDiscrs, altNumParams := minors.map Prod.snd, uElimPos? := uElimPos? }
    setInlineAttribute matcherName
    trace[Meta.Match.debug]! "matcher: {matcher}"
    let unusedAltIdxs : List Nat := lhss.length.fold
      (fun i r => if s.used.contains i then r else i::r)
      []
    pure { matcher := matcher, counterExamples := s.counterExamples, unusedAltIdxs := unusedAltIdxs.reverse }

end Match

export Match (MatcherInfo)

def getMatcherInfo? (declName : Name) : MetaM (Option MatcherInfo) := do
  let env ← getEnv
  pure $ Match.Extension.getMatcherInfo? env declName

def isMatcher (declName : Name) : MetaM Bool := do
  let info? ← getMatcherInfo? declName
  pure info?.isSome

structure MatcherApp :=
  (matcherName   : Name)
  (matcherLevels : Array Level)
  (uElimPos?     : Option Nat)
  (params        : Array Expr)
  (motive        : Expr)
  (discrs        : Array Expr)
  (altNumParams  : Array Nat)
  (alts          : Array Expr)
  (remaining     : Array Expr)

def matchMatcherApp? (e : Expr) : MetaM (Option MatcherApp) :=
  match e.getAppFn with
  | Expr.const declName declLevels _ => do
    let some info ← getMatcherInfo? declName | pure none
    let args := e.getAppArgs
    if args.size < info.numParams + 1 + info.numDiscrs + info.numAlts then pure none
    else
      pure $ some {
        matcherName   := declName,
        matcherLevels := declLevels.toArray,
        uElimPos?     := info.uElimPos?,
        params        := args.extract 0 info.numParams,
        motive        := args.get! info.numParams,
        discrs        := args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs),
        altNumParams  := info.altNumParams,
        alts          := args.extract (info.numParams + 1 + info.numDiscrs) (info.numParams + 1 + info.numDiscrs + info.numAlts),
        remaining     := args.extract (info.numParams + 1 + info.numDiscrs + info.numAlts) args.size
      }
  | _ => pure none

def MatcherApp.toExpr (matcherApp : MatcherApp) : Expr :=
  let result := mkAppN (mkConst matcherApp.matcherName matcherApp.matcherLevels.toList) matcherApp.params
  let result := mkApp result matcherApp.motive
  let result := mkAppN result matcherApp.discrs
  let result := mkAppN result matcherApp.alts
  mkAppN result matcherApp.remaining

/- Auxiliary function for MatcherApp.addArg -/
private partial def updateAlts (typeNew : Expr) (altNumParams : Array Nat) (alts : Array Expr) (i : Nat) : MetaM (Array Nat × Array Expr) := do
  if h : i < alts.size then
    let alt       := alts.get ⟨i, h⟩
    let numParams := altNumParams[i]
    let typeNew ← whnfD typeNew
    match typeNew with
    | Expr.forallE n d b _ =>
      let alt ← forallBoundedTelescope d (some numParams) fun xs d => do
        let alt ← try instantiateLambda alt xs catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"
        forallBoundedTelescope d (some 1) fun x d => do
          let alt ← mkLambdaFVars x alt -- x is the new argument we are adding to the alternative
          let alt ← mkLambdaFVars xs alt
          pure alt
      updateAlts (b.instantiate1 alt) (altNumParams.set! i (numParams+1)) (alts.set ⟨i, h⟩ alt) (i+1)
    | _ => throwError "unexpected type at MatcherApp.addArg"
  else
    pure (altNumParams, alts)

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
      throwError! "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"
    let eType ← inferType e
    let eTypeAbst ← matcherApp.discrs.size.foldRevM (init := eType) fun i eTypeAbst => do
      let motiveArg := motiveArgs[i]
      let discr     := matcherApp.discrs[i]
      let eTypeAbst ← kabstract eTypeAbst discr
      pure $ eTypeAbst.instantiate1 motiveArg
    let motiveBody ← mkArrow eTypeAbst motiveBody
    let matcherLevels ← match matcherApp.uElimPos? with
      | none     => pure matcherApp.matcherLevels
      | some pos =>
        let uElim ← getLevel motiveBody
        pure $ matcherApp.matcherLevels.set! pos uElim
    let motive ← mkLambdaFVars motiveArgs motiveBody
    -- Construct `aux` `match_i As (fun xs => B[xs] → motive[xs]) discrs`, and infer its type `auxType`.
    -- We use `auxType` to infer the type `B[C_i[ys_i]]` of the new argument in each alternative.
    let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) matcherApp.params
    let aux := mkApp aux motive
    let aux := mkAppN aux matcherApp.discrs
    trace! `Meta.debug aux
    check aux
    unless (← isTypeCorrect aux) do
      throwError "failed to add argument to matcher application, type error when constructing the new motive"
    let auxType ← inferType aux
    let (altNumParams, alts) ← updateAlts auxType matcherApp.altNumParams matcherApp.alts 0
    pure { matcherApp with
      matcherLevels := matcherLevels,
      motive        := motive,
      alts          := alts,
      altNumParams  := altNumParams,
      remaining     := #[e] ++ matcherApp.remaining
    }

builtin_initialize
  registerTraceClass `Meta.Match.match
  registerTraceClass `Meta.Match.debug
  registerTraceClass `Meta.Match.unify

end Lean.Meta
