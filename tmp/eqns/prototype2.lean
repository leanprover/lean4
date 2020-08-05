import Lean.Util.CollectLevelParams
import Lean.Meta.Check
import Lean.Meta.Tactic.Cases
import Lean.Meta.GeneralizeTelescope

namespace Lean
namespace Meta
namespace DepElim

structure MVarSubst :=
(map : NameMap MVarId := {})

def MVarSubst.isEmpty (s : MVarSubst) : Bool :=
s.map.isEmpty

def MVarSubst.find? (s : MVarSubst) (mvarId : MVarId) : Option MVarId :=
s.map.find? mvarId

def MVarSubst.find! (s : MVarSubst) (mvarId : MVarId) : MVarId :=
(s.find? mvarId).get!

def MVarSubst.insert (s : MVarSubst) (mvarId mvarId' : MVarId) : MVarSubst :=
{ s with map := s.map.insert mvarId mvarId' }

def MVarSubst.apply (s : MVarSubst) (e : Expr) : Expr :=
if !e.hasMVar then e
else if s.map.isEmpty then e
else e.replace $ fun e => match e with
  | Expr.mvar mvarId _ => match s.map.find? mvarId with
    | none           => e
    | some newMVarId => mkMVar newMVarId
  | _ => none

abbrev VarId := Name

inductive Pattern (internal : Bool := false) : Type
| inaccessible (ref : Syntax) (e : Expr) : Pattern
| var          (ref : Syntax) (varId : VarId) : Pattern
| ctor         (ref : Syntax) (ctorName : Name) (us : List Level) (params : List Expr) (fields : List Pattern) : Pattern
| val          (ref : Syntax) (e : Expr) : Pattern
| arrayLit     (ref : Syntax) (type : Expr) (xs : List Pattern) : Pattern

abbrev IPattern := Pattern true

namespace Pattern

instance {b} : Inhabited (Pattern b) := ⟨Pattern.inaccessible Syntax.missing (arbitrary _)⟩

def ref {b : Bool} : Pattern b → Syntax
| inaccessible r _ => r
| var r _          => r
| ctor r _ _ _ _   => r
| val r _          => r
| arrayLit r _ _   => r

partial def toMessageData {b : Bool} : Pattern b → MessageData
| inaccessible _ e         => ".(" ++ e ++ ")"
| var _ varId              => if b then mkMVar varId else mkFVar varId
| ctor _ ctorName _ _ []   => ctorName
| ctor _ ctorName _ _ pats => "(" ++ ctorName ++ pats.foldl (fun (msg : MessageData) pat => msg ++ " " ++ toMessageData pat) Format.nil ++ ")"
| val _ e                  => "val!(" ++ e ++ ")"
| arrayLit _ _ pats        => "#[" ++ MessageData.joinSep (pats.map toMessageData) ", " ++ "]"

partial def toExpr {b} : Pattern b → MetaM Expr
| inaccessible _ e                 => pure e
| var _ varId                      => if b then pure (mkMVar varId) else pure (mkFVar varId)
| val _ e                          => pure e
| arrayLit _ type xs               => do
  xs ← xs.mapM toExpr;
  mkArrayLit type xs
| ctor _ ctorName us params fields => do
  fields ← fields.mapM toExpr;
  pure $ mkAppN (mkConst ctorName us) (params ++ fields).toArray

@[specialize] partial def visitM {b₁ b₂} {m : Type → Type} [Monad m] (f : Expr → m Expr) (g : Syntax → VarId → m (Pattern b₂)) : Pattern b₁ → m (Pattern b₂)
| inaccessible r e  => inaccessible r <$> f e
| ctor r n us ps fs => ctor r n us <$> ps.mapM f <*> fs.mapM visitM
| val r e           => val r <$> f e
| arrayLit r t xs   => arrayLit r <$> f t <*> xs.mapM visitM
| var r id          => g r id

@[inline] def visit {b₁ b₂} (f : Expr → Expr) (g : Syntax → VarId → Pattern b₂) (p : Pattern b₁) : Pattern b₂ :=
Id.run $ visitM f g p

/- Apply the free variable substitution `s` to the given (internal) pattern -/
def applyFVarSubst (s : FVarSubst) (p : Pattern true) : IPattern :=
p.visit s.apply Pattern.var

def instantiateMVars (p : IPattern) : MetaM IPattern :=
p.visitM Meta.instantiateMVars fun ref mvarId => do
  mctx ← getMCtx;
  match mctx.getExprAssignment? mvarId with
  | some v => inaccessible ref <$> Meta.instantiateMVars v
  | none   => pure (var ref mvarId)

def applyMVarSubst (m : MVarSubst) (p : Pattern true) : IPattern :=
p.visit m.apply fun ref mvarId =>
  match m.find? mvarId with
  | some newMVarId => var ref newMVarId
  | none           => var ref mvarId

end Pattern

structure AltLHS :=
(fvarDecls : List LocalDecl) -- Free variables used in the patterns.
(patterns  : List Pattern)   -- We use `List Pattern` since we have nary match-expressions.

structure Alt :=
(idx       : Nat) -- for generating error messages
(rhs       : Expr)
(mvars     : List MVarId)
(patterns  : List IPattern)

namespace Alt

instance : Inhabited Alt := ⟨⟨0, arbitrary _, [], []⟩⟩

partial def toMessageData (alt : Alt) : MetaM MessageData := do
let msg : MessageData := alt.mvars.toArray.map mkMVar ++ " ⟦" ++ MessageData.joinSep (alt.patterns.map Pattern.toMessageData) ", " ++ "⟧ := " ++ alt.rhs;
addContext msg

private def convertMVar (s : FVarSubst) (m : MVarSubst) (mvarId : MVarId) : MetaM (MVarSubst × MVarId) :=
if s.isEmpty && m.isEmpty then pure (m, mvarId)
else do
  mvarDecl ← getMVarDecl mvarId;
  let mvarType0 := mvarDecl.type;
  mvarType0 ← instantiateMVars mvarType0;
  let mvarType := s.apply mvarType0;
  let mvarType := m.apply mvarType;
  let lctx := mvarDecl.lctx;
  if (s.any fun fvarId _ => lctx.contains fvarId) || mvarType != mvarType0 then do
    newMVar ← mkFreshExprMVar mvarType;
    let m := m.insert mvarId newMVar.mvarId!;
    pure (m, newMVar.mvarId!)
  else
    pure (m, mvarId)

private def convertMVars (s : FVarSubst) (mvars : List MVarId) : MetaM (MVarSubst × List MVarId) := do
(m, mvars) ← mvars.foldlM
  (fun (acc : MVarSubst × List MVarId) mvarId => do
    let (m, mvarIds) := acc;
    (m, mvarId') ← convertMVar s m mvarId;
    let m := if mvarId == mvarId' then m else m.insert mvarId mvarId';
    pure (m, mvarId'::mvarIds))
  ({}, []);
pure (m, mvars.reverse)

def applyFVarSubst (s : FVarSubst) (alt : Alt) : MetaM Alt := do
(m, mvars) ← convertMVars s alt.mvars;
let patterns := alt.patterns.map fun p => (p.applyFVarSubst s).applyMVarSubst m;
let rhs      := m.apply $ s.apply alt.rhs;
pure { alt with patterns := patterns, mvars := mvars, rhs := rhs }

private def copyMVar (m : MVarSubst) (mvarId : MVarId) : MetaM (MVarSubst × MVarId) := do
mvarDecl ← getMVarDecl mvarId;
let mvarType := mvarDecl.type;
mvarType ← instantiateMVars mvarType;
let mvarType := m.apply mvarType;
newMVar ← mkFreshExprMVar mvarType;
let m := m.insert mvarId newMVar.mvarId!;
pure (m, newMVar.mvarId!)

private def copyMVars (mvars : List MVarId) : MetaM (MVarSubst × List MVarId) := do
(m, mvars) ← mvars.foldlM
  (fun (acc : MVarSubst × List MVarId) mvarId => do
    let (m, mvarIds) := acc;
    (m, mvarId) ← copyMVar m mvarId;
    pure (m, mvarId::mvarIds))
  ({}, []);
pure (m, mvars.reverse)

def copyCore (alt : Alt) : MetaM (MVarSubst × Alt) := do
(m, mvars) ← copyMVars alt.mvars;
let patterns := alt.patterns.map fun p => p.applyMVarSubst m;
let rhs      := m.apply alt.rhs;
pure (m, { alt with patterns := patterns, mvars := mvars, rhs := rhs })

/- Create a copy of the given alternative with fresh metavariables. -/
def copy (alt : Alt) : MetaM Alt := do
(m, alt) ← copyCore alt;
pure alt

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

private def localDeclsToMVarsAux : List LocalDecl → List MVarId → FVarSubst → MetaM (List MVarId × FVarSubst)
| [],    mvars, s => pure (mvars.reverse, s)
| d::ds, mvars, s => do
  let type := s.apply d.type;
  mvar ← mkFreshExprMVar type;
  let s := s.insert d.fvarId mvar;
  localDeclsToMVarsAux ds (mvar.mvarId! :: mvars) s

private def localDeclsToMVars (fvarDecls : List LocalDecl) : MetaM (List MVarId × FVarSubst) :=
localDeclsToMVarsAux fvarDecls [] {}

private partial def toIPattern (s : FVarSubst) (p : Pattern) : IPattern :=
p.visit s.apply fun ref fvarId =>
  match s.get fvarId with
  | Expr.mvar mvarId _ => Pattern.var ref mvarId
  | _                  => unreachable!

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
  withLocalDecl minorName minorType BinderInfo.default fun minor => do
    let rhs    := mkAppN minor xs;
    let minors := minors.push minor;
    (mvars, s) ← localDeclsToMVars lhs.fvarDecls;
    let patterns := lhs.patterns.map (toIPattern s);
    let rhs      := s.apply rhs;
    let alts   := { idx := idx, rhs := rhs, mvars := mvars, patterns := patterns : Alt } :: alts;
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

/-- Return true if the next element on the `p.vars` list is a variable. -/
private def isNextVar (p : Problem) : Bool :=
match p.vars with
| Expr.fvar _ _ :: _ => true
| _                  => false

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

private def processNonVariable (process : Problem → State → MetaM State) (p : Problem) (s : State) : MetaM State := do
trace! `Meta.debug ("process non variable");
match p.vars with
| x :: xs =>
  let alts := p.alts.map fun alt => match alt.patterns with
    | _ :: ps => { alt with patterns := ps }
    | _       => unreachable!;
  process { p with alts := alts, vars := xs } s
| _ => unreachable!

private def processLeaf (p : Problem) (s : State) : MetaM State :=
match p.alts with
| [] => throwOther "missing case" -- TODO improve error message
| alt :: _ => do
  -- TODO: check whether we have unassigned metavars in rhs
  assignGoalOf p alt.rhs;
  pure { s with used := s.used.insert alt.idx }

private def processVariable (process : Problem → State → MetaM State) (p : Problem) (s : State) : MetaM State := do
trace! `Meta.debug ("process variable");
match p.vars with
| x :: xs => do
  alts ← p.alts.mapM fun alt => match alt.patterns with
    | Pattern.inaccessible _ _ :: ps => pure { alt with patterns := ps }
    | Pattern.var _ mvarId :: ps     => do
      -- trace! `Meta.debug (">> assign " ++ mkMVar mvarId ++ " := " ++ x);
      assignExprMVar mvarId x;
      rhs ← instantiateMVars alt.rhs;
      let mvars := alt.mvars.erase mvarId;
      -- trace! `Meta.debug (">> patterns before assignment: " ++ MessageData.ofList (ps.map Pattern.toMessageData));
      patterns ← ps.mapM fun p => p.instantiateMVars;
      -- trace! `Meta.debug (">> patterns after assignment: " ++ MessageData.ofList (patterns.map Pattern.toMessageData));
      pure { alt with patterns := patterns, rhs := rhs, mvars := mvars }
    | _                              => unreachable!;
  process { p with alts := alts, vars := xs } s
| _ => unreachable!

private def isFirstPatternCtor (ctorName : Name) (alt : Alt) : Bool :=
match alt.patterns with
| Pattern.ctor _ n _ _ _ :: _ => n == ctorName
| _                           => false

private def processConstructor (process : Problem → State → MetaM State) (p : Problem) (s : State) : MetaM State := do
trace! `Meta.debug ("process constructor");
match p.vars with
| x :: xs => do
  subgoals ← cases p.goal.mvarId! x.fvarId!;
  subgoals.foldlM
    (fun (s : State) subgoal => do
      let subst   := subgoal.subst;
      let newVars := subgoal.fields.toList ++ xs;
      let newVars := newVars.map fun x => x.applyFVarSubst subst;
      let newAlts := p.alts.filter $ isFirstPatternCtor subgoal.ctorName;
      let newAlts := newAlts.map fun alt => match alt.patterns with
        | Pattern.ctor _ _ _ _ fields :: ps => { alt with patterns := fields ++ ps }
        | _                                 => unreachable!;
      newAlts ← newAlts.mapM fun alt => alt.applyFVarSubst subst;
      newAlts ← newAlts.mapM fun alt => alt.copy;
      process { goal := mkMVar subgoal.mvarId, vars := newVars, alts := newAlts } s)
    s
| _ => unreachable!

private def throwInductiveTypeExpected {α} (type : Expr) : MetaM α := do
throwOther ("failed to compile pattern matching, inductive type expected" ++ indentExpr type)

private partial def tryConstructorAux (alt : Alt) (ref : Syntax) (mvarId : MVarId) (ctorName : Name) (us : List Level) (params : Array Expr) (mvars : Array Expr)
    : Nat → Array MVarId → Array IPattern → MetaM Alt
| i, newMVars, fields => do
  if h : i < mvars.size then do
    let mvar := mvars.get ⟨i, h⟩;
    e ← instantiateMVars mvar;
    match e with
    | Expr.mvar mvarId _ => tryConstructorAux (i+1) (newMVars.push mvarId) (fields.push (Pattern.var ref mvarId))
    | _                  => tryConstructorAux (i+1) newMVars (fields.push (Pattern.inaccessible ref e))
  else do
    let p := Pattern.ctor ref ctorName us params.toList fields.toList;
    e ← p.toExpr;
    assignExprMVar mvarId e;
    ps ← alt.patterns.mapM Pattern.instantiateMVars;
    let ps := p :: ps;
    rhs ← instantiateMVars alt.rhs;
    unless (alt.mvars.contains mvarId) $
      throwOther "ill-format alternative"; -- TODO: improve error message
    let mvars := (alt.mvars.map fun mvarId' => if mvarId' == mvarId then newMVars.toList else [mvarId']).join;
    mvars ← mvars.filterM fun mvarId => not <$> isExprMVarAssigned mvarId;
    pure { alt with rhs := rhs, mvars := mvars, patterns := ps }

private def tryConstructor? (alt : Alt) (ref : Syntax) (mvarId : MVarId) (ctorName : Name) (us : List Level) (params : Array Expr) (expectedType : Expr)
    : MetaM (Option Alt) := do
let ctor := mkAppN (mkConst ctorName us) params;
ctorType ← inferType ctor;
(mvars, _, resultType) ← forallMetaTelescopeReducing ctorType;
trace! `Meta.debug ("ctorName: " ++ ctorName ++ ", resultType: " ++ resultType ++ ", expectedType: " ++ expectedType);
condM (isDefEq resultType expectedType)
  (Option.some <$> tryConstructorAux alt ref mvarId ctorName us params mvars 0 #[] #[])
  (pure none)

private def expandAlt (alt : Alt) (ref : Syntax) (mvarId : MVarId) : MetaM (List Alt) := do
env ← getEnv;
mvarDecl ← getMVarDecl mvarId;
let expectedType := mvarDecl.type;
expectedType ← whnfD expectedType;
matchConst env expectedType.getAppFn (fun _ => throwInductiveTypeExpected expectedType) fun info us =>
  match info with
  | ConstantInfo.inductInfo val =>
    val.ctors.foldlM
      (fun (result : List Alt) ctor => do
        (mvarSubst, alt) ← alt.copyCore;
        let mvarId := mvarSubst.find! mvarId;
        mvarDecl ← getMVarDecl mvarId;
        let expectedType := mvarDecl.type;
        expectedType ← whnfD expectedType;
        let I     := expectedType.getAppFn;
        let Iargs := expectedType.getAppArgs;
        let params := Iargs.extract 0 val.nparams;
        alt? ← tryConstructor? alt ref mvarId ctor us params expectedType;
        match alt? with
        | none     => pure result
        | some alt => pure (alt :: result))
      []
  | _ => throwInductiveTypeExpected expectedType

/- Auxiliary method for `processComplete` -/
private def processComplete (process : Problem → State → MetaM State) (p : Problem) (s : State) : MetaM State := do
trace! `Meta.debug ("process complete");
withGoalOf p do
env ← getEnv;
newAlts ← p.alts.foldlM
  (fun (newAlts : List Alt) alt =>
    match alt.patterns with
    | Pattern.ctor _ _ _ _ _ :: ps     => pure (alt :: newAlts)
    | p@(Pattern.var ref mvarId) :: ps => do
        let alt := { alt with patterns := ps };
        alts ← expandAlt alt ref mvarId;
        pure (alts ++ newAlts)
    | _ => unreachable!)
  [];
process { p with alts := newAlts.reverse } s

private partial def process : Problem → State → MetaM State
| p, s => withIncRecDepth do
  withGoalOf p (traceM `Meta.debug p.toMessageData);
  if isDone p then
    processLeaf p s
  else if !isNextVar p then
    processNonVariable process p s
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

private def getConstructorVal (ctorName : Name) (fn : Expr) (args : Array Expr) : MetaM (Option (ConstructorVal × Expr × Array Expr)) := do
env ← getEnv;
match env.find? ctorName with
| some (ConstantInfo.ctorInfo v) => if args.size == v.nparams + v.nfields then pure $ some (v, fn, args) else pure none
| _                              => pure none

private def constructorApp? (e : Expr) : MetaM (Option (ConstructorVal × Expr × Array Expr)) := do
env ← getEnv;
match e with
| Expr.lit (Literal.natVal n) _ =>
   if n == 0 then getConstructorVal `Nat.zero (mkConst `Nat.zero) #[] else getConstructorVal `Nat.succ (mkConst `Nat.succ) #[mkNatLit (n-1)]
| _ =>
  let fn := e.getAppFn;
  match fn with
  | Expr.const n _ _ => getConstructorVal n fn e.getAppArgs
  | _                => pure none

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
      e ← whnfD e;
      r? ← constructorApp? e;
      match r? with
      | none      => throw $ Exception.other "unexpected pattern"
      | some (cval, fn, args) => do
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

def test (ex : Name) (numPats : Nat) (elimName : Name) (inProp : Bool := false) : MetaM Unit :=
withDepElimFrom ex numPats fun majors alts => do
  let majors := majors.map mkFVar;
  trace! `Meta.debug ("majors: " ++ majors.toArray);
  _ ← mkElim elimName majors alts inProp;
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
#print elimTest4

def ex5 (α : Type u) (n : Nat) (xs : Vec α n) :
  LHS (Pat Nat.zero × Pat (Vec.nil : Vec α 0))
× LHS (forall (n : Nat) (xs : Vec α (n+1)), Pat (Nat.succ n) × Pat xs) :=
arbitrary _

#eval test `ex5 2 `elimTest5
#print elimTest5

def ex6 (α : Type u) (n : Nat) (xs : Vec α n) :
  LHS (Pat (inaccessible Nat.zero) × Pat (Vec.nil : Vec α 0))
× LHS (forall (N : Nat) (XS : Vec α N), Pat (inaccessible N) × Pat XS) :=
arbitrary _

-- set_option trace.Meta.debug true

#eval test `ex6 2 `elimTest6
#print elimTest6

def ex7 (α : Type u) (n : Nat) (xs : Vec α n) :
  LHS (forall (a : α), Pat (inaccessible 1) × Pat (Vec.cons a Vec.nil))
× LHS (forall (N : Nat) (XS : Vec α N), Pat (inaccessible N) × Pat XS) :=
arbitrary _

#eval test `ex7 2 `elimTest7
#check elimTest7

def isSizeOne {n : Nat} (xs : Vec Nat n) : Bool :=
elimTest7 _ (fun _ _ => Bool) n xs (fun _ => true) (fun _ _ => false)

#eval isSizeOne Vec.nil
#eval isSizeOne (Vec.cons 1 Vec.nil)
#eval isSizeOne (Vec.cons 2 (Vec.cons 1 Vec.nil))

def singleton? {n : Nat} (xs : Vec Nat n) : Option Nat :=
elimTest7 _ (fun _ _ => Option Nat) n xs (fun a => some a) (fun _ _ => none)

#eval singleton? Vec.nil
#eval singleton? (Vec.cons 10 Vec.nil)
#eval singleton? (Vec.cons 20 (Vec.cons 10 Vec.nil))

def ex8 (α : Type u) (n : Nat) (xs : Vec α n) :
  LHS (forall (a b : α), Pat (inaccessible 2) × Pat (Vec.cons a (Vec.cons b Vec.nil)))
× LHS (forall (N : Nat) (XS : Vec α N), Pat (inaccessible N) × Pat XS) :=
arbitrary _

#eval test `ex8 2 `elimTest8
#print elimTest8

def pair? {n : Nat} (xs : Vec Nat n) : Option (Nat × Nat) :=
elimTest8 _ (fun _ _ => Option (Nat × Nat)) n xs (fun a b => some (a, b)) (fun _ _ => none)

#eval pair? Vec.nil
#eval pair? (Vec.cons 10 Vec.nil)
#eval pair? (Vec.cons 20 (Vec.cons 10 Vec.nil))

inductive Op : Nat → Nat → Type
| mk : ∀ n, Op n n

structure Node : Type :=
(id₁ id₂ : Nat)
(o : Op id₁ id₂)

def ex9 (xs : List Node) :
  LHS (forall (h : Node) (t : List Node), Pat (h :: Node.mk 1 1 (Op.mk 1) :: t))
× LHS (forall (ys : List Node), Pat ys) :=
arbitrary _

#eval test `ex9 1 `elimTest9
#print elimTest9

def f (xs : List Node) : Bool :=
elimTest9 (fun _ => Bool) xs
  (fun _ _ => true)
  (fun _   => false)

#eval f []
#eval f [⟨0, 0, Op.mk 0⟩]
#eval f [⟨0, 0, Op.mk 0⟩, ⟨1, 1, Op.mk 1⟩]
#eval f [⟨0, 0, Op.mk 0⟩, ⟨2, 2, Op.mk 2⟩]

inductive Foo : Bool → Prop
| bar : Foo false
| baz : Foo false

def ex10 (x : Bool) (y : Foo x) :
  LHS (Pat (inaccessible false) × Pat Foo.bar)
× LHS (forall (x : Bool) (y : Foo x), Pat (inaccessible x) × Pat y) :=
arbitrary _

#eval test `ex10 2 `elimTest10 true
#check elimTest10
