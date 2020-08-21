/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.CollectLevelParams
import Lean.Meta.Check
import Lean.Meta.Tactic.Cases
import Lean.Meta.GeneralizeTelescope
import Lean.Meta.EqnCompiler.MVarRenaming
import Lean.Meta.EqnCompiler.CaseValues
import Lean.Meta.EqnCompiler.CaseArraySizes

namespace Lean
namespace Meta
namespace Match

def replaceFVarIdAtLocalDecl (fvarId : FVarId) (e : Expr) (d : LocalDecl) : LocalDecl :=
if d.fvarId == fvarId then d
else match d with
  | LocalDecl.cdecl idx id n type bi  => LocalDecl.cdecl idx id n (type.replaceFVarId fvarId e) bi
  | LocalDecl.ldecl idx id n type val => LocalDecl.ldecl idx id n (type.replaceFVarId fvarId e) (val.replaceFVarId fvarId e)

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
| inaccessible e         => ".(" ++ e ++ ")"
| var varId              => mkFVar varId
| ctor ctorName _ _ []   => ctorName
| ctor ctorName _ _ pats => "(" ++ ctorName ++ pats.foldl (fun (msg : MessageData) pat => msg ++ " " ++ toMessageData pat) Format.nil ++ ")"
| val e                  => e
| arrayLit _ pats        => "#[" ++ MessageData.joinSep (pats.map toMessageData) ", " ++ "]"
| as varId p             => mkFVar varId ++ "@" ++toMessageData p

partial def toExpr : Pattern → MetaM Expr
| inaccessible e                 => pure e
| var fvarId                     => pure $ mkFVar fvarId
| val e                          => pure e
| as _ p                         => toExpr p
| arrayLit type xs               => do
  xs ← xs.mapM toExpr;
  mkArrayLit type xs
| ctor ctorName us params fields => do
  fields ← fields.mapM toExpr;
  pure $ mkAppN (mkConst ctorName us) (params ++ fields).toArray

/- Apply the free variable substitution `s` to the given pattern -/
partial def applyFVarSubst (s : FVarSubst) : Pattern → Pattern
| inaccessible e  => inaccessible $ s.apply e
| ctor n us ps fs => ctor n us (ps.map s.apply) $ fs.map applyFVarSubst
| val e           => val $ s.apply e
| arrayLit t xs   => arrayLit (s.apply t) $ xs.map applyFVarSubst
| var fvarId      => match s.find? fvarId with
  | some e => inaccessible e
  | none   => var fvarId
| as fvarId p     => match s.find? fvarId with
  | none   => as fvarId $ applyFVarSubst p
  | some _ => applyFVarSubst p

def replaceFVarId (fvarId : FVarId) (v : Expr) (p : Pattern) : Pattern :=
let s : FVarSubst := {};
p.applyFVarSubst (s.insert fvarId v)

end Pattern

structure AltLHS :=
(fvarDecls  : List LocalDecl) -- Free variables used in the patterns.
(patterns   : List Pattern)   -- We use `List Pattern` since we have nary match-expressions.

structure Alt :=
(idx       : Nat) -- for generating error messages
(rhs       : Expr)
(fvarDecls : List LocalDecl)
(patterns  : List Pattern)

namespace Alt

instance : Inhabited Alt := ⟨⟨0, arbitrary _, [], []⟩⟩

partial def toMessageData (alt : Alt) : MetaM MessageData := do
withExistingLocalDecls alt.fvarDecls do
  let msg : List MessageData := alt.fvarDecls.map fun d => d.toExpr ++ ":(" ++ d.type ++ ")";
  let msg : MessageData := msg ++ " |- " ++ (alt.patterns.map Pattern.toMessageData) ++ " => " ++ alt.rhs;
  addContext msg

def applyFVarSubst (s : FVarSubst) (alt : Alt) : Alt :=
{ alt with
  patterns  := alt.patterns.map fun p => p.applyFVarSubst s,
  fvarDecls := alt.fvarDecls.map fun d => d.applyFVarSubst s,
  rhs       := alt.rhs.applyFVarSubst s }

def replaceFVarId (fvarId : FVarId) (v : Expr) (alt : Alt) : Alt :=
{ alt with
  patterns  := alt.patterns.map fun p => p.replaceFVarId fvarId v,
  fvarDecls :=
    let decls := alt.fvarDecls.filter fun d => d.fvarId != fvarId;
    decls.map $ replaceFVarIdAtLocalDecl fvarId v,
  rhs       := alt.rhs.replaceFVarId fvarId v }

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
| ctor n exs   => ctor n $ exs.map replaceFVarId
| arrayLit exs => arrayLit $ exs.map replaceFVarId
| ex           => ex

partial def applyFVarSubst (s : FVarSubst) : Example → Example
| var fvarId =>
  match s.get fvarId with
  | Expr.fvar fvarId' _ => var fvarId'
  | _                   => underscore
| ctor n exs   => ctor n $ exs.map applyFVarSubst
| arrayLit exs => arrayLit $ exs.map applyFVarSubst
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

namespace Problem

instance : Inhabited Problem := ⟨{ mvarId := arbitrary _, vars := [], alts := [], examples := []}⟩

def toMessageData (p : Problem) : MetaM MessageData :=
withGoalOf p do
  alts ← p.alts.mapM Alt.toMessageData;
  vars : List MessageData ← p.vars.mapM fun x => do { xType ← inferType x; pure (x ++ ":(" ++ xType ++ ")" : MessageData) };
  pure $ "vars " ++ vars
    -- ++ Format.line ++ "var ids " ++ toString (p.vars.map (fun x => match x with | Expr.fvar id _ => toString id | _ => "[nonvar]"))
    ++ Format.line ++ MessageData.joinSep alts Format.line
    ++ Format.line ++ "examples: " ++ examplesToMessageData p.examples
    ++ Format.line
end Problem

abbrev CounterExample := List Example

def counterExampleToMessageData (cex : CounterExample) : MessageData :=
examplesToMessageData cex

def counterExamplesToMessageData (cexs : List CounterExample) : MessageData :=
MessageData.joinSep (cexs.map counterExampleToMessageData) Format.line

structure ElimResult :=
(elim            : Expr) -- The eliminator. It is not just `Expr.const elimName` because the type of the major premises may contain free variables.
(counterExamples : List CounterExample)
(unusedAltIdxs   : List Nat)

/- The number of patterns in each AltLHS must be equal to majors.length -/
private def checkNumPatterns (majors : Array Expr) (lhss : List AltLHS) : MetaM Unit :=
let num := majors.size;
when (lhss.any (fun lhs => lhs.patterns.length != num)) $
  throwError "incorrect number of patterns"

private partial def withAltsAux {α} (motive : Expr) : List AltLHS → List Alt → Array Expr → (List Alt → Array Expr → MetaM α) → MetaM α
| [],        alts, minors, k => k alts.reverse minors
| lhs::lhss, alts, minors, k => do
  let xs := lhs.fvarDecls.toArray.map LocalDecl.toExpr;
  minorType ← withExistingLocalDecls lhs.fvarDecls do {
    args ← lhs.patterns.toArray.mapM Pattern.toExpr;
    let minorType := mkAppN motive args;
    mkForall xs minorType
  };
  let minorType := if minorType.isForall then minorType else mkThunkType minorType;
  let idx       := alts.length;
  let minorName := (`h).appendIndexAfter (idx+1);
  trace! `Meta.EqnCompiler.matchDebug ("minor premise " ++ minorName ++ " : " ++ minorType);
  withLocalDecl minorName minorType BinderInfo.default fun minor => do
    let rhs    := if xs.isEmpty then mkApp minor (mkConst `Unit.unit) else mkAppN minor xs;
    let minors := minors.push minor;
    fvarDecls ← lhs.fvarDecls.mapM instantiateLocalDeclMVars;
    let alts   := { idx := idx, rhs := rhs, fvarDecls := fvarDecls, patterns := lhs.patterns : Alt } :: alts;
    withAltsAux lhss alts minors k

/- Given a list of `AltLHS`, create a minor premise for each one, convert them into `Alt`, and then execute `k` -/
private partial def withAlts {α} (motive : Expr) (lhss : List AltLHS) (k : List Alt → Array Expr → MetaM α) : MetaM α :=
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
&& p.alts.any fun alt => match alt.patterns with
   | Pattern.ctor _ _ _ _ :: _   => true
   | Pattern.inaccessible _ :: _ => true
   | _                           => false

private def processNonVariable (p : Problem) : Problem :=
match p.vars with
| []      => unreachable!
| x :: xs =>
  let alts := p.alts.map fun alt => match alt.patterns with
    | _ :: ps => { alt with patterns := ps }
    | _       => unreachable!;
  { p with alts := alts, vars := xs }

private def processLeaf (p : Problem) : StateT State MetaM Unit :=
match p.alts with
| []       => do
  liftM $ admit p.mvarId;
  modify fun s => { s with counterExamples := p.examples :: s.counterExamples }
| alt :: _ => do
  -- TODO: check whether we have unassigned metavars in rhs
  liftM $ assignGoalOf p alt.rhs;
  modify fun s => { s with used := s.used.insert alt.idx }

private def processAsPattern (p : Problem) : Problem :=
match p.vars with
| []      => unreachable!
| x :: xs => do
  let alts := p.alts.map fun alt => match alt.patterns with
    | Pattern.as fvarId p :: ps => { alt with patterns := p :: ps }.replaceFVarId fvarId x
    | _                         => alt;
  { p with alts := alts }

private def processVariable (p : Problem) : Problem :=
match p.vars with
| []      => unreachable!
| x :: xs => do
  let alts := p.alts.map fun alt => match alt.patterns with
    | Pattern.inaccessible _ :: ps => { alt with patterns := ps }
    | Pattern.var fvarId :: ps     => { alt with patterns := ps }.replaceFVarId fvarId x
    | _                            => unreachable!;
  { p with alts := alts, vars := xs }

private def throwInductiveTypeExpected {α} (e : Expr) : MetaM α := do
t ← inferType e;
throwError ("failed to compile pattern matching, inductive type expected" ++ indentExpr e ++ Format.line ++ "has type" ++ indentExpr t)

private def inLocalDecls (localDecls : List LocalDecl) (fvarId : FVarId) : Bool :=
localDecls.any fun d => d.fvarId == fvarId

namespace Unify

structure Context :=
(altFVarDecls : List LocalDecl)

structure State :=
(fvarSubst : FVarSubst := {})

abbrev M := ReaderT Context $ StateT State MetaM

def isAltVar (fvarId : FVarId) : M Bool := do
ctx ← read;
pure $ inLocalDecls ctx.altFVarDecls fvarId

def expandIfVar (e : Expr) : M Expr := do
match e with
| Expr.fvar _ _ => do s ← get; pure $ s.fvarSubst.apply e
| _             => pure e

def occurs (fvarId : FVarId) (v : Expr) : Bool :=
(v.find? fun e => match e with
   | Expr.fvar fvarId' _ => fvarId == fvarId'
   | _=> false).isSome

def assign (fvarId : FVarId) (v : Expr) : M Bool :=
if occurs fvarId v then do
  trace! `Meta.EqnCompiler.matchUnify ("assign occurs check failed, " ++ mkFVar fvarId ++ " := " ++ v);
  pure false
else do
  ctx ← read;
  condM (isAltVar fvarId)
    (do
      trace! `Meta.EqnCompiler.matchUnify (mkFVar fvarId ++ " := " ++ v);
      modify fun s => { s with fvarSubst := s.fvarSubst.insert fvarId v }; pure true)
    (do
      trace! `Meta.EqnCompiler.matchUnify ("assign failed variable is not local, " ++ mkFVar fvarId ++ " := " ++ v);
      pure false)

partial def unify : Expr → Expr → M Bool
| a, b => do
  trace! `Meta.EqnCompiler.matchUnify (a ++ " =?= " ++ b);
  condM (liftM $ isDefEq a b) (pure true) do
  a' ← expandIfVar a;
  b' ← expandIfVar b;
  if a != a' || b != b' then unify a' b'
  else match a, b with
    | Expr.mdata _ a _, b                      => unify a b
    | a, Expr.mdata _ b _                      => unify a b
    | Expr.fvar aFvarId _, Expr.fvar bFVarId _ => assign aFvarId b <||> assign bFVarId a
    | Expr.fvar aFvarId _, b => assign aFvarId b
    | a, Expr.fvar bFVarId _ => assign bFVarId a
    | Expr.app aFn aArg _, Expr.app bFn bArg _ => unify aFn bFn <&&> unify aArg bArg
    | _, _ => do
      trace! `Meta.EqnCompiler.matchUnify ("unify failed @" ++ a ++ " =?= " ++ b);
      pure false

end Unify

private def unify? (altFVarDecls : List LocalDecl) (a b : Expr) : MetaM (Option FVarSubst) := do
a ← instantiateMVars a;
b ← instantiateMVars b;
(b, s) ← (Unify.unify a b { altFVarDecls := altFVarDecls}).run {};
if b then pure s.fvarSubst else pure none

private def expandVarIntoCtor? (alt : Alt) (fvarId : FVarId) (ctorName : Name) : MetaM (Option Alt) :=
withExistingLocalDecls alt.fvarDecls do
  env ← getEnv;
  ldecl ← getLocalDecl fvarId;
  expectedType ← inferType (mkFVar fvarId);
  expectedType ← whnfD expectedType;
  (ctorLevels, ctorParams) ← getInductiveUniverseAndParams expectedType;
  let ctor := mkAppN (mkConst ctorName ctorLevels) ctorParams;
  ctorType ← inferType ctor;
  forallTelescopeReducing ctorType fun ctorFields resultType => do
    let ctor := mkAppN ctor ctorFields;
    let alt := alt.replaceFVarId fvarId ctor;
    ctorFieldDecls ← ctorFields.mapM fun ctorField => getLocalDecl ctorField.fvarId!;
    let newAltDecls := ctorFieldDecls.toList ++ alt.fvarDecls;
    subst? ← unify? newAltDecls resultType expectedType;
    match subst? with
    | none       => pure none
    | some subst => do
      let newAltDecls := newAltDecls.filter fun d => !subst.contains d.fvarId; -- remove declarations that were assigned
      let newAltDecls := newAltDecls.map fun d => d.applyFVarSubst subst; -- apply substitution to remaining declaration types
      let patterns    := alt.patterns.map fun p => p.applyFVarSubst subst;
      let rhs         := subst.apply alt.rhs;
      let ctorFieldPatterns := ctorFields.toList.map fun ctorField => match subst.get ctorField.fvarId! with
        | e@(Expr.fvar fvarId _) => if inLocalDecls newAltDecls fvarId then Pattern.var fvarId else Pattern.inaccessible e
        | e                      => Pattern.inaccessible e;
      pure $ some { alt with fvarDecls := newAltDecls, rhs := rhs, patterns := ctorFieldPatterns ++ patterns }

private def getInductiveVal? (x : Expr) : MetaM (Option InductiveVal) := do
xType ← inferType x;
xType ← whnfD xType;
match xType.getAppFn with
| Expr.const constName _ _ => do
  cinfo ← getConstInfo constName;
  match cinfo with
  | ConstantInfo.inductInfo val => pure (some val)
  | _ => pure none
| _ => pure none

private def hasRecursiveType (x : Expr) : MetaM Bool := do
val? ← getInductiveVal? x;
match val? with
| some val => pure val.isRec
| _        => pure false

private def processConstructor (p : Problem) : MetaM (Array Problem) := do
trace! `Meta.EqnCompiler.match ("constructor step");
env ← getEnv;
match p.vars with
| []      => unreachable!
| x :: xs => do
  subgoals? ← commitWhenSome? do {
     subgoals ← cases p.mvarId x.fvarId!;
     if subgoals.isEmpty then
       /- Easy case: we have solved problem `p` since there are no subgoals -/
       pure (some #[])
     else if !p.alts.isEmpty then
       pure (some subgoals)
     else do
       isRec ← withGoalOf p $ hasRecursiveType x;
        /- If there are no alternatives and the type of the current variable is recursive, we do NOT consider
          a constructor-transition to avoid nontermination.
          TODO: implement a more general approach if this is not sufficient in practice -/
       if isRec then pure none
       else pure (some subgoals)
  };
  match subgoals? with
  | none          => pure #[{ p with vars := xs }]
  | some subgoals =>
    subgoals.mapM fun subgoal => withMVarContext subgoal.mvarId do
      let subst    := subgoal.subst;
      let fields   := subgoal.fields.toList;
      let newVars  := fields ++ xs;
      let newVars  := newVars.map fun x => x.applyFVarSubst subst;
      let subex    := Example.ctor subgoal.ctorName $ fields.map fun field => match field with
        | Expr.fvar fvarId _ => Example.var fvarId
        | _                  => Example.underscore; -- This case can happen due to dependent elimination
      let examples := p.examples.map $ Example.replaceFVarId x.fvarId! subex;
      let examples := examples.map $ Example.applyFVarSubst subst;
      let newAlts  := p.alts.filter fun alt => match alt.patterns with
        | Pattern.ctor n _ _ _ :: _   => n == subgoal.ctorName
        | Pattern.var _ :: _          => true
        | Pattern.inaccessible _ :: _ => true
        | _                           => false;
      let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst;
      newAlts ← newAlts.filterMapM fun alt => match alt.patterns with
        | Pattern.ctor _ _ _ fields :: ps  => pure $ some { alt with patterns := fields ++ ps }
        | Pattern.var fvarId :: ps         => expandVarIntoCtor? { alt with patterns := ps } fvarId subgoal.ctorName
        | Pattern.inaccessible e :: ps     => do
          trace! `Meta.EqnCompiler.match ("inaccessible in ctor step " ++ e);
          e ← whnfD e;
          match e.constructorApp? env with
          | some (ctorVal, ctorArgs) => do
            if ctorVal.name == subgoal.ctorName then
              let fields := ctorArgs.extract ctorVal.nparams ctorArgs.size;
              let fields := fields.toList.map Pattern.inaccessible;
              pure $ some { alt with patterns := fields ++ ps }
            else
              pure none
          | _ => pure none
        | _                                => unreachable!;
      pure { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }

private def collectValues (p : Problem) : Array Expr :=
p.alts.foldl
  (fun (values : Array Expr) alt =>
    match alt.patterns with
    | Pattern.val v :: _ => if values.contains v then values else values.push v
    | _                  => values)
  #[]

private def isFirstPatternVar (alt : Alt) : Bool :=
match alt.patterns with
| Pattern.var _ :: _ => true
| _                  => false

private def processValue (p : Problem) : MetaM (Array Problem) := do
trace! `Meta.EqnCompiler.match ("value step");
match p.vars with
| []      => unreachable!
| x :: xs => do
  let values := collectValues p;
  subgoals ← caseValues p.mvarId x.fvarId! values;
  subgoals.mapIdxM fun i subgoal =>
    if h : i < values.size then do
      let value := values.get ⟨i, h⟩;
      -- (x = value) branch
      let subst := subgoal.subst;
      let examples := p.examples.map $ Example.replaceFVarId x.fvarId! (Example.val value);
      let examples := examples.map $ Example.applyFVarSubst subst;
      let newAlts  := p.alts.filter fun alt => match alt.patterns with
        | Pattern.val v :: _ => v == value
        | Pattern.var _ :: _ => true
        | _                  => false;
      let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst;
      let newAlts := newAlts.map fun alt => match alt.patterns with
        | Pattern.val _ :: ps      => { alt with patterns := ps }
        | Pattern.var fvarId :: ps =>
          let alt := { alt with patterns := ps };
          alt.replaceFVarId fvarId value
        | _  => unreachable!;
      let newVars := xs.map fun x => x.applyFVarSubst subst;
      pure { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }
    else do
      -- else branch
      let newAlts := p.alts.filter isFirstPatternVar;
      pure { p with mvarId := subgoal.mvarId, alts := newAlts, vars := x::xs }

private def collectArraySizes (p : Problem) : Array Nat :=
p.alts.foldl
  (fun (sizes : Array Nat) alt =>
    match alt.patterns with
    | Pattern.arrayLit _ ps :: _ => let sz := ps.length; if sizes.contains sz then sizes else sizes.push sz
    | _                          => sizes)
  #[]

private def expandVarIntoArrayLitAux (alt : Alt) (fvarId : FVarId) (arrayElemType : Expr) (varNamePrefix : Name) : Nat → Array Expr → MetaM Alt
| n+1, newVars =>
  withLocalDecl (varNamePrefix.appendIndexAfter (n+1)) arrayElemType BinderInfo.default fun x =>
    expandVarIntoArrayLitAux n (newVars.push x)
| 0, newVars => do
  arrayLit ← mkArrayLit arrayElemType newVars.toList;
  let alt := alt.replaceFVarId fvarId arrayLit;
  newDecls ← newVars.toList.mapM fun newVar => getLocalDecl newVar.fvarId!;
  let newPatterns := newVars.toList.map fun newVar => Pattern.var newVar.fvarId!;
  pure { alt with fvarDecls := newDecls ++ alt.fvarDecls, patterns := newPatterns ++ alt.patterns }

private def expandVarIntoArrayLit (alt : Alt) (fvarId : FVarId) (arrayElemType : Expr) (arraySize : Nat) : MetaM Alt :=
withExistingLocalDecls alt.fvarDecls do
  fvarDecl ← getLocalDecl fvarId;
  expandVarIntoArrayLitAux alt fvarId arrayElemType fvarDecl.userName arraySize #[]

private def processArrayLit (p : Problem) : MetaM (Array Problem) := do
trace! `Meta.EqnCompiler.match ("array literal step");
match p.vars with
| []      => unreachable!
| x :: xs => do
  let sizes := collectArraySizes p;
  subgoals ← caseArraySizes p.mvarId x.fvarId! sizes;
  subgoals.mapIdxM fun i subgoal =>
    if h : i < sizes.size then do
      let size     := sizes.get! i;
      let subst    := subgoal.subst;
      let elems    := subgoal.elems.toList;
      let newVars  := elems.map mkFVar ++ xs;
      let newVars  := newVars.map fun x => x.applyFVarSubst subst;
      let subex    := Example.arrayLit $ elems.map Example.var;
      let examples := p.examples.map $ Example.replaceFVarId x.fvarId! subex;
      let examples := examples.map $ Example.applyFVarSubst subst;
      let newAlts  := p.alts.filter fun alt => match alt.patterns with
        | Pattern.arrayLit _ ps :: _ => ps.length == size
        | Pattern.var _ :: _         => true
        | _                          => false;
      let newAlts := newAlts.map fun alt => alt.applyFVarSubst subst;
      newAlts ← newAlts.mapM fun alt => match alt.patterns with
        | Pattern.arrayLit _ pats :: ps => pure { alt with patterns := pats ++ ps }
        | Pattern.var fvarId :: ps      => do α ← getArrayArgType x; expandVarIntoArrayLit { alt with patterns := ps } fvarId α size
        | _  => unreachable!;
      pure { mvarId := subgoal.mvarId, vars := newVars, alts := newAlts, examples := examples }
    else do
      -- else branch
      let newAlts := p.alts.filter isFirstPatternVar;
      pure { p with mvarId := subgoal.mvarId, alts := newAlts, vars := x::xs }

private def expandNatValuePattern (p : Problem) : Problem := do
let alts := p.alts.map fun alt => match alt.patterns with
  | Pattern.val (Expr.lit (Literal.natVal 0) _) :: ps     => { alt with patterns := Pattern.ctor `Nat.zero [] [] [] :: ps }
  | Pattern.val (Expr.lit (Literal.natVal (n+1)) _) :: ps => { alt with patterns := Pattern.ctor `Nat.succ [] [] [Pattern.val (mkNatLit n)] :: ps }
  | _                                                     => alt;
{ p with alts := alts }

private def traceStep (msg : String) : StateT State MetaM Unit :=
liftM (trace! `Meta.EqnCompiler.match (msg ++ " step") : MetaM Unit)

private def traceState (p : Problem) : MetaM Unit :=
withGoalOf p (traceM `Meta.EqnCompiler.match p.toMessageData)

private def throwNonSupported (p : Problem) : MetaM Unit := do
msg ← p.toMessageData;
throwError ("not implement yet " ++ msg)

@[inline] def withIncRecDepth {α} (x : StateT State MetaM α) : StateT State MetaM α := do
liftM $ checkRecDepth;
adaptTheReader Core.Context Core.Context.incCurrRecDepth x

def isCurrVarInductive (p : Problem) : MetaM Bool := do
match p.vars with
| []   => pure false
| x::_ => withGoalOf p do
  val? ← getInductiveVal? x;
  pure val?.isSome

private partial def process : Problem → StateT State MetaM Unit
| p => withIncRecDepth do
  liftM $ traceState p;
  isInductive ← liftM $ isCurrVarInductive p;
  if isDone p then
    processLeaf p
  else if hasAsPattern p then do
    traceStep ("as-pattern");
    process (processAsPattern p)
  else if !isNextVar p then do
    traceStep ("non variable");
    process (processNonVariable p)
  else if isInductive && isConstructorTransition p then do
    ps ← liftM $ processConstructor p;
    ps.forM process
  else if isVariableTransition p then do
    traceStep ("variable");
    process (processVariable p)
  else if isValueTransition p then do
    ps ← liftM $ processValue p;
    ps.forM process
  else if isArrayLitTransition p then do
    ps ← liftM $ processArrayLit p;
    ps.forM process
  else if isNatValueTransition p then do
    traceStep ("nat value to constructor");
    process (expandNatValuePattern p)
  else
    liftM $ throwNonSupported p

def mkElim (elimName : Name) (motiveType : Expr) (lhss : List AltLHS) : MetaM ElimResult :=
withLocalDecl `motive motiveType BinderInfo.default fun motive => do
forallTelescopeReducing motiveType fun majors _ => do
checkNumPatterns majors lhss;
let mvarType  := mkAppN motive majors;
trace! `Meta.EqnCompiler.matchDebug ("target: " ++ mvarType);
withAlts motive lhss fun alts minors => do
  mvar ← mkFreshExprMVar mvarType;
  let examples := majors.toList.map fun major => Example.var major.fvarId!;
  (_, s) ← (process { mvarId := mvar.mvarId!, vars := majors.toList, alts := alts, examples := examples }).run {};
  let args := #[motive] ++ majors ++ minors;
  type ← mkForall args mvarType;
  val  ← mkLambda args mvar;
  trace! `Meta.EqnCompiler.matchDebug ("eliminator value: " ++ val ++ "\ntype: " ++ type);
  elim ← mkAuxDefinition elimName type val;
  setInlineAttribute elimName;
  trace! `Meta.EqnCompiler.matchDebug ("eliminator: " ++ elim);
  let unusedAltIdxs : List Nat := lhss.length.fold
    (fun i r => if s.used.contains i then r else i::r)
    [];
  pure { elim := elim, counterExamples := s.counterExamples, unusedAltIdxs := unusedAltIdxs.reverse }


/- Helper methods for testins mkElim -/

private def getUnusedLevelParam (majors : List Expr) (lhss : List AltLHS) : MetaM Level := do
let s : CollectLevelParams.State := {};
s ← majors.foldlM
  (fun s major => do
    major ← instantiateMVars major;
    majorType ← inferType major;
    majorType ← instantiateMVars majorType;
    let s := collectLevelParams s major;
    pure $ collectLevelParams s majorType)
  s;
pure s.getUnusedLevelParam

/- Return `Prop` if `inProf == true` and `Sort u` otherwise, where `u` is a fresh universe level parameter. -/
private def mkElimSort (majors : List Expr) (lhss : List AltLHS) (inProp : Bool) : MetaM Expr :=
if inProp then
  pure $ mkSort $ levelZero
else do
  v ← getUnusedLevelParam majors lhss;
  pure $ mkSort $ v

def mkElimTester (elimName : Name) (majors : List Expr) (lhss : List AltLHS) (inProp : Bool := false) : MetaM ElimResult := do
sortv ← mkElimSort majors lhss inProp;
generalizeTelescope majors.toArray `_d fun majors => do
  motiveType ← mkForall majors sortv;
  mkElim elimName motiveType lhss

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Meta.EqnCompiler.match;
registerTraceClass `Meta.EqnCompiler.matchDebug;
registerTraceClass `Meta.EqnCompiler.matchUnify;
pure ()

end Match
end Meta
end Lean
