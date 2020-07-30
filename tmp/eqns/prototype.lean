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

end Pattern

structure AltLHS :=
(fvarDecls : List LocalDecl) -- Free variables used in the patterns.
(patterns  : List Pattern)   -- We use `List Pattern` since we have nary match-expressions.

structure MinorsRange :=
(firstMinorPos : Nat)
(numMinors     : Nat)

abbrev AltToMinorsMap := Std.PersistentHashMap Nat MinorsRange

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

end Alt

structure Problem :=
(goal          : Expr)
(vars          : List Expr)
(alts          : List Alt)
(processedVars : Array Expr := #[])

namespace Problem

instance : Inhabited Problem := ⟨{ goal := arbitrary _, vars := [], alts := []}⟩

def toMessageData (p : Problem) : MetaM MessageData := do
alts ← p.alts.mapM Alt.toMessageData;
pure $ "vars " ++ p.vars.toArray ++ Format.line ++ MessageData.joinSep alts Format.line

end Problem

structure ElimResult :=
(numMinors : Nat)  -- It is the number of alternatives (Reason: support for overlapping equations)
(numEqs    : Nat)  -- It is the number of minors (Reason: users may want equations that hold definitionally)
(elim      : Expr) -- The eliminator. It is not just `Expr.const elimName` because the type of the major premises may contain free variables.
(altMap    : AltToMinorsMap) -- each alternative may be "expanded" into multiple minor premise

/- The number of patterns in each AltLHS must be equal to majors.length -/
private def checkNumPatterns (majors : List Expr) (lhss : List AltLHS) : MetaM Unit :=
let num := majors.length;
when (lhss.any (fun lhs => lhs.patterns.length != num)) $
  throw $ Exception.other "incorrect number of patterns"

/- Return `Prop` if `inProf == true` and `Sort u` otherwise, where `u` is a fresh universe level parameter. -/
private def mkElimSort (inProp : Bool) : MetaM Expr :=
if inProp then
  pure $ mkSort $ levelZero
else do
  vId ← mkFreshId;
  pure $ mkSort $ mkLevelParam vId

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

structure State :=
(minors : Array Expr := #[])
(used   : Std.HashSet Nat := {}) -- used alternatives

private def processLeaf {α} (p : Problem) (s : State) (k : State → MetaM α) : MetaM α := do
type ← inferType p.goal;
k s

private partial def process {α} : Problem → State → (State → MetaM α) → MetaM α
| p, s, k => withIncRecDepth do
  traceM `Meta.debug p.toMessageData;
  if p.vars.isEmpty then
    processLeaf p s k
  else
    k s

def mkElim (elimName : Name) (majors : List Expr) (lhss : List AltLHS) (inProp : Bool := false) : MetaM ElimResult := do
checkNumPatterns majors lhss;
generalizeTelescope majors.toArray `_d fun majors => do
sortv ← mkElimSort inProp;
withMotive majors sortv fun motive => do
let target  := mkAppN motive majors;
trace! `Meta.debug ("target: " ++ target);
goal ← mkFreshExprMVar target;
withAlts motive lhss fun alts minors => do
process { goal := goal, vars := majors.toList, alts := alts } {} fun s =>
pure { numMinors := 0, numEqs := 0, elim := arbitrary _, altMap := {} } -- TODO

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

set_option trace.Meta.debug true

@[init] def register : IO Unit :=
registerTraceClass `Meta.mkElim

def ex0 (x : Nat) : LHS (forall (y : Nat), Pat y)
:= arbitrary _

def tst0 : MetaM Unit :=
withDepElimFrom `ex0 1 fun majors alts => do
  let majors := majors.map mkFVar;
  trace! `Meta.debug ("majors: " ++ majors.toArray);
  _ ← mkElim `test majors alts;
  pure ()

#eval tst0

def ex1 (α : Type u) (β : Type v) (n : Nat) (x : List α) (y : List β) :
  LHS (Pat ([] : List α) × Pat ([] : List α))
× LHS (forall (a : α) (b : α), Pat [a] × Pat [b])
× LHS (forall (a₁ a₂ : α) (as : List α) (b₁ b₂ : β) (bs : List β), Pat (a₁::a₂::as) × Pat (b₁::b₂::bs))
× LHS (forall (as : List α) (bs : List β), Pat as × Pat bs)
:= arbitrary _

def tst1 : MetaM Unit :=
withDepElimFrom `ex1 2 fun majors alts => do
  let majors := majors.map mkFVar;
  trace! `Meta.debug ("majors: " ++ majors.toArray);
  _ ← mkElim `test majors alts;
  pure ()

#eval tst1
