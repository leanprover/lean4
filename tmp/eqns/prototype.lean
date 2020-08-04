import Lean.Util.CollectLevelParams
import Lean.Meta.Check
import Lean.Meta.Tactic.Cases
import Lean.Meta.GeneralizeTelescope

namespace Lean
namespace Meta
namespace DepElim

inductive Pattern
| inaccessible (ref : Syntax) (e : Expr)
| var          (ref : Syntax) (fvarId : FVarId)
| ctor         (ref : Syntax) (ctorName : Name) (us : List Level) (params : List Expr) (fields : List Pattern)
| val          (ref : Syntax) (e : Expr)
| arrayLit     (ref : Syntax) (type : Expr) (xs : List Pattern)

namespace Pattern

instance : Inhabited Pattern := ⟨Pattern.inaccessible Syntax.missing (arbitrary _)⟩

def ref : Pattern → Syntax
| inaccessible r _ => r
| var r _          => r
| ctor r _ _ _ _   => r
| val r _          => r
| arrayLit r _ _   => r

partial def toMessageData : Pattern → MessageData
| inaccessible _ e        => ".(" ++ e ++ ")"
| var _ fvarId             => mkFVar fvarId
| ctor _ ctorName _ _ []   => ctorName
| ctor _ ctorName _ _ pats => "(" ++ ctorName ++ pats.foldl (fun (msg : MessageData) pat => msg ++ " " ++ toMessageData pat) Format.nil ++ ")"
| val _ e                  => "val!(" ++ e ++ ")"
| arrayLit _ _ pats        => "#[" ++ MessageData.joinSep (pats.map toMessageData) ", " ++ "]"

partial def toExpr : Pattern → MetaM Expr
| inaccessible _ e                 => pure e
| var _ fvarId                     => pure (mkFVar fvarId)
| val _ e                          => pure e
| arrayLit _ type xs               => do
  xs ← xs.mapM toExpr;
  mkArrayLit type xs
| ctor _ ctorName us params fields => do
  fields ← fields.mapM toExpr;
  pure $ mkAppN (mkConst ctorName us) (params ++ fields).toArray

/- Apply the free variable substitution `s` to the given pattern -/
partial def applyFVarSubst (s : FVarSubst) : Pattern → Pattern
| inaccessible r e  => inaccessible r $ e.applyFVarSubst s
| ctor r n us ps fs => ctor r n us (ps.map fun p => p.applyFVarSubst s) (fs.map applyFVarSubst)
| val r e           => val r $ e.applyFVarSubst s
| arrayLit r t xs   => arrayLit r (t.applyFVarSubst s) (xs.map applyFVarSubst)
| var r fvarId      =>
  match s.get fvarId with
  | Expr.fvar newFVarId _ => var r newFVarId
  | e                     => inaccessible r e

def replaceFVarId (fvarId : FVarId) (e : Expr) (p : Pattern) : Pattern :=
let s := FVarSubst.empty.insert fvarId e;
applyFVarSubst s p

end Pattern

structure AltLHS :=
(fvarDecls : List LocalDecl) -- Free variables used in the patterns.
(patterns  : List Pattern)   -- We use `List Pattern` since we have nary match-expressions.

structure Alt :=
(idx       : Nat) -- for generating error messages
(rhs       : Expr)
(fvarDecls : List LocalDecl)
(patterns  : List Pattern)

namespace Alt

instance : Inhabited Alt := ⟨⟨0, arbitrary _, [], []⟩⟩

partial def toMessageData (alt : Alt) : MetaM MessageData := do
lctx ← getLCtx;
localInsts ← getLocalInstances;
let lctx := alt.fvarDecls.foldl (fun (lctx : LocalContext) decl => lctx.addDecl decl) lctx;
withLocalContext lctx localInsts do
  let msg : MessageData := "⟦" ++ MessageData.joinSep (alt.patterns.map Pattern.toMessageData) ", " ++ "⟧ := " ++ alt.rhs;
  addContext msg

def applyFVarSubst (s : FVarSubst) (alt : Alt) : Alt :=
{ alt with
  patterns  := alt.patterns.map fun p => p.applyFVarSubst s,
  fvarDecls := alt.fvarDecls.map fun d => d.applyFVarSubst s,
  rhs       := alt.rhs.applyFVarSubst s }

end Alt

structure Problem :=
(goal          : Expr)
(vars          : List Expr)
(alts          : List Alt)

def withGoalOf {α} (p : Problem) (x : MetaM α) : MetaM α :=
withMVarContext p.goal.mvarId! x

namespace Problem

instance : Inhabited Problem := ⟨{ goal := arbitrary _, vars := [], alts := []}⟩

def toMessageData (p : Problem) : MetaM MessageData :=
withGoalOf p do
  alts ← p.alts.mapM Alt.toMessageData;
  pure $ "vars " ++ p.vars.toArray
    -- ++ Format.line ++ "var ids " ++ toString (p.vars.map (fun x => match x with | Expr.fvar id _ => toString id | _ => "[nonvar]"))
    ++ Format.line ++ MessageData.joinSep alts Format.line

end Problem

structure ElimResult :=
(elim      : Expr) -- The eliminator. It is not just `Expr.const elimName` because the type of the major premises may contain free variables.

/- The number of patterns in each AltLHS must be equal to majors.length -/
private def checkNumPatterns (majors : List Expr) (lhss : List AltLHS) : MetaM Unit :=
let num := majors.length;
when (lhss.any (fun lhs => lhs.patterns.length != num)) $
  throw $ Exception.other "incorrect number of patterns"

/-
 Given major premises `(x_1 : A_1) (x_2 : A_2[x_1]) ... (x_n : A_n[x_1, x_2, ...])`, return
 `forall (x_1 : A_1) (x_2 : A_2[x_1]) ... (x_n : A_n[x_1, x_2, ...]), sortv` -/
private def withMotive {α} (majors : Array Expr) (sortv : Expr) (k : Expr → MetaM α) : MetaM α := do
type ← mkForall majors sortv;
trace! `Meta.debug ("motive: " ++ type);
withLocalDecl `motive type BinderInfo.default k

private partial def withAltsAux {α} (motive : Expr) : List AltLHS → List Alt → Array Expr → (List Alt → Array Expr → MetaM α) → MetaM α
| [],        alts, minors, k => k alts.reverse minors
| lhs::lhss, alts, minors, k => do
  let xs := lhs.fvarDecls.toArray.map LocalDecl.toExpr;
  minorType ← withExistingLocalDecls lhs.fvarDecls do {
    args ← lhs.patterns.toArray.mapM Pattern.toExpr;
    let minorType := mkAppN motive args;
    mkForall xs minorType
  };
  let idx       := alts.length;
  let minorName := (`h).appendIndexAfter (idx+1);
  trace! `Meta.debug ("minor premise " ++ minorName ++ " : " ++ minorType);
  withLocalDecl minorName minorType BinderInfo.default fun minor =>
    let rhs    := mkAppN minor xs;
    let minors := minors.push minor;
    let alts   := { idx := idx, rhs := rhs, fvarDecls := lhs.fvarDecls, patterns := lhs.patterns : Alt } :: alts;
    withAltsAux lhss alts minors k

/- Given a list of `AltLHS`, create a minor premise for each one, convert them into `Alt`, and then execute `k` -/
private partial def withAlts {α} (motive : Expr) (lhss : List AltLHS) (k : List Alt → Array Expr → MetaM α) : MetaM α :=
withAltsAux motive lhss [] #[] k

def assignGoalOf (p : Problem) (e : Expr) : MetaM Unit :=
withGoalOf p (assignExprMVar p.goal.mvarId! e)

structure State :=
(used   : Std.HashSet Nat := {}) -- used alternatives

/-- Return true if the given (sub-)problem has been solved. -/
private def isDone (p : Problem) : Bool :=
p.vars.isEmpty

/- Return true if the next pattern of each remaining alternative is an inaccessible term or a variable -/
private def isVariableTransition (p : Problem) : Bool :=
p.alts.all fun alt => match alt.patterns with
  | Pattern.inaccessible _ _ :: _ => true
  | Pattern.var _ _ :: _          => true
  | _                             => false

/- Return true if the next pattern of each remaining alternative is a constructor application -/
private def isConstructorTransition (p : Problem) : Bool :=
p.alts.all fun alt => match alt.patterns with
  | Pattern.ctor _ _ _ _ _ :: _ => true
  | _                           => false

/- Return true if the next pattern of the remaining alternatives contain variables AND constructors. -/
private def isCompleteTransition (p : Problem) : Bool :=
let (ok, hasVar, hasCtor) := p.alts.foldl
  (fun (acc : Bool × Bool × Bool) (alt : Alt) =>
    let (ok, hasVar, hasCtor) := acc;
    match alt.patterns with
    | Pattern.ctor _ _ _ _ _ :: _ => (ok, hasVar, true)
    | Pattern.var _ _ :: _        => (ok, true, hasCtor)
    | _                           => (false, hasVar, hasCtor))
  (true, false, false);
ok && hasVar && hasCtor

private def processLeaf (p : Problem) (s : State) : MetaM State := do
let alt := p.alts.head!;
assignGoalOf p alt.rhs;
pure { s with used := s.used.insert alt.idx }

private def replaceFVarIdAtLocalDecl (fvarId : FVarId) (e : Expr) (d : LocalDecl) : LocalDecl :=
if d.fvarId == fvarId then d
else match d with
  | LocalDecl.cdecl idx id n type bi  => LocalDecl.cdecl idx id n (type.replaceFVarId fvarId e) bi
  | LocalDecl.ldecl idx id n type val => LocalDecl.ldecl idx id n (type.replaceFVarId fvarId e) (val.replaceFVarId fvarId e)

private def isAltDecl (alt : Alt) (fvarId : FVarId) : Bool :=
alt.fvarDecls.any fun d => d.fvarId == fvarId

private def processVariable (process : Problem → State → MetaM State) (p : Problem) (s : State) : MetaM State := do
match p.vars with
| x :: xs =>
  let alts := p.alts.map fun alt => match alt.patterns with
    | Pattern.inaccessible _ _ :: ps => { alt with patterns := ps }
    | Pattern.var _ fvarId :: ps     =>
      if isAltDecl alt fvarId then
        let patterns  := ps.map (fun p => p.replaceFVarId fvarId x);
        let rhs       := alt.rhs.replaceFVarId fvarId x;
        /- We eliminate the LocalDecl for fvarId since it was substituted. -/
        let fvarDecls := alt.fvarDecls.filter fun d => d.fvarId != fvarId;
        let fvarDecls := fvarDecls.map $ replaceFVarIdAtLocalDecl fvarId x;
        { alt with patterns := patterns, rhs := rhs, fvarDecls := fvarDecls }
      else
        { alt with patterns := ps }
    | _                              => unreachable!;
  process { p with alts := alts, vars := xs } s
| _ => unreachable!

private def isFirstPatternCtor (ctorName : Name) (alt : Alt) : Bool :=
match alt.patterns with
| Pattern.ctor _ n _ _ _ :: _ => n == ctorName
| _                           => false

private def expandCtorPattern (alt : Alt) : Alt :=
match alt.patterns with
| Pattern.ctor _ _ _ _ fields :: ps => { alt with patterns := fields ++ ps }
| _                                 => alt

private def processConstructor (process : Problem → State → MetaM State) (p : Problem) (s : State) : MetaM State :=
match p.vars with
| x :: xs => do
  subgoals ← cases p.goal.mvarId! x.fvarId!;
  subgoals.foldlM
    (fun (s : State) subgoal =>
      let newVars := subgoal.fields.toList.map mkFVar ++ xs;
      let newVars := newVars.map fun x => x.applyFVarSubst subgoal.subst;
      let newAlts := p.alts.filter $ isFirstPatternCtor subgoal.ctorName;
      let newAlts := newAlts.map fun alt => match alt.patterns with
        | Pattern.ctor _ _ _ _ fields :: ps => { alt with patterns := fields ++ ps }
        | _                                 => unreachable!;
      let newAlts := newAlts.map fun alt => alt.applyFVarSubst subgoal.subst;
      process { goal := mkMVar subgoal.mvarId, vars := newVars, alts := newAlts } s)
    s
| _ => unreachable!

private def throwInductiveTypeExpected {α} (e : Expr) : MetaM α := do
t ← inferType e;
throwOther ("failed to compile pattern matching, inductive type expected" ++ indentExpr e ++ Format.line ++ "has type" ++ indentExpr t)

/- Auxiliary method for `processComplete` -/
private partial def mkCompatibleCtorPattern (ref : Syntax) (ctorName : Name) (us : List Level) (params : Array Expr)
    (mvars : Array Expr) (varNamePrefix : Name) : Nat → Array LocalDecl → Array Pattern → MetaM (List LocalDecl × Pattern)
| i, newDecls, fields =>
  if h : i < mvars.size then do
    let mvar := mvars.get ⟨i, h⟩;
    e ← instantiateMVars mvar;
    match e with
    | Expr.mvar _ _ => do
      type ← inferType e;
      withLocalDecl (varNamePrefix.appendIndexAfter i) type BinderInfo.default fun x => do
        decl ← getLocalDecl x.fvarId!;
        mkCompatibleCtorPattern (i+1) (newDecls.push decl) (fields.push (Pattern.var ref decl.fvarId))
    | Expr.fvar fvarId _ => mkCompatibleCtorPattern (i+1) newDecls (fields.push (Pattern.var ref fvarId))
    | _ => mkCompatibleCtorPattern (i+1) newDecls (fields.push (Pattern.inaccessible ref e))
  else
    pure (newDecls.toList, Pattern.ctor ref ctorName us params.toList fields.toList)

/- Auxiliary method for `processComplete` -/
private partial def compatibleConstructor? (ref : Syntax) (ctorName : Name) (us : List Level) (params : Array Expr) (expectedType : Expr)
    (varNamePrefix : Name) : MetaM (Option (List LocalDecl × Pattern)) := do
let ctor := mkAppN (mkConst ctorName us) params;
ctorType ← inferType ctor;
(mvars, _, resultType) ← forallMetaTelescopeReducing ctorType;
trace! `Meta.debug ("ctorName: " ++ ctorName ++ ", resultType: " ++ resultType ++ ", expectedType: " ++ expectedType);
condM (isDefEq resultType expectedType)
  (Option.some <$> mkCompatibleCtorPattern ref ctorName us params mvars varNamePrefix 0 #[] #[])
  (pure none)

/- Auxiliary method for `processComplete` -/
private def getCompatibleConstructors (ref : Syntax) (e : Expr) (varNamePrefix : Name) : MetaM (List (List LocalDecl × Pattern)) := do
env ← getEnv;
expectedType ← inferType e;
expectedType ← whnfD expectedType;
let I     := expectedType.getAppFn;
let Iargs := expectedType.getAppArgs;
matchConst env I (fun _ => throwInductiveTypeExpected e) fun info us =>
match info with
| ConstantInfo.inductInfo val =>
  let params := Iargs.extract 0 val.nparams;
  val.ctors.foldlM
    (fun (result : List (List LocalDecl × Pattern)) ctor => do
      entry? ← withNewMCtxDepth $ compatibleConstructor? ref ctor us params expectedType varNamePrefix;
      match entry? with
      | none       => pure result
      | some entry => pure (entry :: result))
    []
| _ => throwInductiveTypeExpected e

/- Auxiliary method for `processComplete` -/
private def processComplete (process : Problem → State → MetaM State) (p : Problem) (s : State) : MetaM State :=
withGoalOf p do
env ← getEnv;
newAlts ← p.alts.foldlM
  (fun (newAlts : List Alt) alt =>
    match alt.patterns with
    | Pattern.ctor _ _ _ _ _ :: ps => pure (alt :: newAlts)
    | p@(Pattern.var ref fvarId) :: ps =>
      withExistingLocalDecls alt.fvarDecls do
        ldecl ← getLocalDecl fvarId;
        dps ← getCompatibleConstructors p.ref (mkFVar fvarId) ldecl.userName;
        expandedAlts ← dps.mapM fun ⟨newLocalDecls, p⟩ => do {
          e ← p.toExpr;
          let ps  := ps.map fun p => p.replaceFVarId fvarId e;
          let rhs := alt.rhs.replaceFVarId fvarId e;
          let fvarDecls := alt.fvarDecls.map (replaceFVarIdAtLocalDecl fvarId e);
          pure { alt with patterns := p :: ps, fvarDecls := fvarDecls ++ newLocalDecls, rhs := rhs }
        };
        pure (expandedAlts ++ newAlts)
    | _ => unreachable!)
  [];
process { p with alts := newAlts.reverse } s

private partial def process : Problem → State → MetaM State
| p, s => withIncRecDepth do
  withGoalOf p (traceM `Meta.debug p.toMessageData);
  if isDone p then
    processLeaf p s
  else if isVariableTransition p then
    processVariable process p s
  else if isConstructorTransition p then
    processConstructor process p s
  else if isCompleteTransition p then
    processComplete process p s
  else do
    msg ← p.toMessageData;
    -- TODO: remaining cases
    throwOther ("not implement yet " ++ msg)

def getUnusedLevelParam (majors : List Expr) (lhss : List AltLHS) : MetaM Level := do
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

def mkElim (elimName : Name) (majors : List Expr) (lhss : List AltLHS) (inProp : Bool := false) : MetaM ElimResult := do
checkNumPatterns majors lhss;
sortv ← mkElimSort majors lhss inProp;
generalizeTelescope majors.toArray `_d fun majors => do
withMotive majors sortv fun motive => do
let target  := mkAppN motive majors;
trace! `Meta.debug ("target: " ++ target);
withAlts motive lhss fun alts minors => do
  goal ← mkFreshExprMVar target;
  s    ← process { goal := goal, vars := majors.toList, alts := alts } {};
  let args := #[motive] ++ majors ++ minors;
  type ← mkForall args target;
  val  ← mkLambda args goal;
  trace! `Meta.debug ("eliminator value: " ++ val ++ "\ntype: " ++ type);
  elim ← mkAuxDefinition elimName type val;
  trace! `Meta.debug ("eliminator: " ++ elim);
  pure { elim := elim }

end DepElim
end Meta
end Lean

open Lean
open Lean.Meta
open Lean.Meta.DepElim

/- Infrastructure for testing -/

universes u v

def inaccessible {α : Sort u} (a : α) : α := a
def val {α : Sort u} (a : α) : α := a

/- Convert expression using auxiliary hints `inaccessible` and `val` into a pattern -/
partial def mkPattern : Expr → MetaM Pattern
| e =>
  if e.isAppOfArity `val 2 then
    pure $ Pattern.val Syntax.missing e.appArg!
  else if e.isAppOfArity `inaccessible 2 then
    pure $ Pattern.inaccessible Syntax.missing e.appArg!
  else if e.isFVar then
    pure $ Pattern.var Syntax.missing e.fvarId!
  else match e.arrayLit? with
    | some es => do
      pats ← es.mapM mkPattern;
      type ← inferType e;
      type ← whnfD type;
      let elemType := type.appArg!;
      pure $ Pattern.arrayLit Syntax.missing elemType pats
    | none => do
      cval? ← constructorApp? e;
      match cval? with
      | none      => throw $ Exception.other "unexpected pattern"
      | some cval => do
        let fn     := e.getAppFn;
        let args   := e.getAppArgs;
        let params := args.extract 0 cval.nparams;
        let fields := args.extract cval.nparams args.size;
        pats ← fields.toList.mapM mkPattern;
        pure $ Pattern.ctor Syntax.missing cval.name fn.constLevels! params.toList pats

partial def decodePats : Expr → MetaM (List Pattern)
| e =>
  match e.app2? `Pat with
  | some (_, pat) => do pat ← mkPattern pat; pure [pat]
  | none =>
    match e.prod? with
    | none => throw $ Exception.other "unexpected pattern"
    | some (pat, pats) => do
      pat  ← decodePats pat;
      pats ← decodePats pats;
      pure (pat ++ pats)

partial def decodeAltLHS (e : Expr) : MetaM AltLHS :=
forallTelescopeReducing e fun args body => do
  decls ← args.toList.mapM (fun arg => getLocalDecl arg.fvarId!);
  pats  ← decodePats body;
  pure { fvarDecls := decls, patterns := pats }

partial def decodeAltLHSs : Expr → MetaM (List AltLHS)
| e =>
  match e.app2? `LHS with
  | some (_, lhs) => do lhs ← decodeAltLHS lhs; pure [lhs]
  | none =>
    match e.prod? with
    | none => throw $ Exception.other "unexpected LHS"
    | some (lhs, lhss) => do
      lhs  ← decodeAltLHSs lhs;
      lhss ← decodeAltLHSs lhss;
      pure (lhs ++ lhss)

def withDepElimFrom {α} (declName : Name) (numPats : Nat) (k : List FVarId → List AltLHS → MetaM α) : MetaM α := do
cinfo ← getConstInfo declName;
forallTelescopeReducing cinfo.type fun args body =>
  if args.size < numPats then
    throw $ Exception.other "insufficient number of parameters"
  else do
    let xs := (args.extract (args.size - numPats) args.size).toList.map $ Expr.fvarId!;
    alts ← decodeAltLHSs body;
    k xs alts

inductive Pat {α : Sort u} (a : α) : Type u
| mk : Pat

inductive LHS {α : Sort u} (a : α) : Type u
| mk : LHS

instance LHS.inhabited {α} (a : α) : Inhabited (LHS a) := ⟨LHS.mk⟩

-- set_option trace.Meta.debug true
-- set_option trace.Meta.Tactic.cases true
-- set_option trace.Meta.Tactic.subst true

@[init] def register : IO Unit :=
registerTraceClass `Meta.mkElim

def test (ex : Name) (numPats : Nat) (elimName : Name) : MetaM Unit :=
withDepElimFrom ex numPats fun majors alts => do
  let majors := majors.map mkFVar;
  trace! `Meta.debug ("majors: " ++ majors.toArray);
  _ ← mkElim elimName majors alts;
  pure ()

def ex0 (x : Nat) : LHS (forall (y : Nat), Pat y)
:= arbitrary _

#eval test `ex0 1 `elimTest0
#print elimTest0

def ex1 (α : Type u) (β : Type v) (n : Nat) (x : List α) (y : List β) :
  LHS (Pat ([] : List α) × Pat ([] : List β))
× LHS (forall (a : α) (as : List α) (b : β) (bs : List β), Pat (a::as) × Pat (b::bs))
× LHS (forall (a : α) (as : List α), Pat (a::as) × Pat ([] : List β))
× LHS (forall (b : β) (bs : List β), Pat ([] : List α) × Pat (b::bs))
:= arbitrary _

#eval test `ex1 2 `elimTest1
#print elimTest1

inductive Vec (α : Type u) : Nat → Type u
| nil            : Vec 0
| cons {n : Nat} : α → Vec n → Vec (n+1)

def ex2 (α : Type u) (n : Nat) (xs : Vec α n) (ys : Vec α n) :
  LHS (Pat (inaccessible 0) × Pat (Vec.nil : Vec α 0) × Pat (Vec.nil : Vec α 0))
× LHS (forall (n : Nat) (x : α) (xs : Vec α n) (y : α) (ys : Vec α n), Pat (inaccessible (n+1)) × Pat (Vec.cons x xs) × Pat (Vec.cons y ys)) :=
arbitrary _

#eval test `ex2 3 `elimTest2
#print elimTest2

def ex3 (α : Type u) (β : Type v) (n : Nat) (x : List α) (y : List β) :
  LHS (Pat ([] : List α) × Pat ([] : List β))
× LHS (forall (a : α) (b : β), Pat [a] × Pat [b])
× LHS (forall (a₁ a₂ : α) (as : List α) (b₁ b₂ : β) (bs : List β), Pat (a₁::a₂::as) × Pat (b₁::b₂::bs))
× LHS (forall (as : List α) (bs : List β), Pat as × Pat bs)
:= arbitrary _

#eval test `ex3 2 `elimTest3
#print elimTest3

def ex4 (α : Type u) (n : Nat) (xs : Vec α n) :
  LHS (Pat (inaccessible 0) × Pat (Vec.nil : Vec α 0))
× LHS (forall (n : Nat) (xs : Vec α (n+1)), Pat (inaccessible (n+1)) × Pat xs) :=
arbitrary _

#eval test `ex4 2 `elimTest4
#check elimTest4
#print elimTest4

def ex5 (α : Type u) (n : Nat) (xs : Vec α n) :
  LHS (Pat Nat.zero × Pat (Vec.nil : Vec α 0))
× LHS (forall (n : Nat) (xs : Vec α (n+1)), Pat (Nat.succ n) × Pat xs) :=
arbitrary _

#eval test `ex5 2 `elimTest5
#print elimTest5
