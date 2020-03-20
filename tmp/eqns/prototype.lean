prelude
import Init.Lean.Meta.Tactic.Cases

namespace Lean
namespace Meta
namespace DepElim

inductive Pattern
| inaccessible (ref : Syntax) (e : Expr)
| var          (ref : Syntax) (fvarId : FVarId)
| ctor         (ref : Syntax) (ctorName : Name) (fields : List Pattern)
| val          (ref : Syntax) (e : Expr)
| arrayLit     (ref : Syntax) (xs : List Pattern)

namespace Pattern

instance : Inhabited Pattern := ⟨Pattern.arrayLit Syntax.missing []⟩

partial def toMessageData : Pattern → MessageData
| inaccessible _ e     => ".(" ++ e ++ ")"
| var _ fvarId         => mkFVar fvarId
| ctor _ ctorName []   => ctorName
| ctor _ ctorName pats => "(" ++ ctorName ++ pats.foldl (fun (msg : MessageData) pat => msg ++ " " ++ toMessageData pat) Format.nil ++ ")"
| val _ e              => "val!(" ++ e ++ ")"
| arrayLit _ pats      => "#[" ++ MessageData.joinSep (pats.map toMessageData) ", " ++ "]"

end Pattern

structure AltLHS :=
(fvarDecls : List LocalDecl) -- Free variables used in the patterns.
(patterns  : List Pattern)   -- We use `List Pattern` since we have nary match-expressions.

namespace AltLHS

instance : Inhabited AltLHS := ⟨⟨[], []⟩⟩

partial def toMessageData (alt : AltLHS) : MetaM MessageData := do
lctx ← getLCtx;
localInsts ← getLocalInstances;
let lctx := alt.fvarDecls.foldl (fun (lctx : LocalContext) decl => lctx.addDecl decl) lctx;
withLocalContext lctx localInsts $ do
  let msg : MessageData := "⟦" ++ MessageData.joinSep (alt.patterns.map Pattern.toMessageData) ", " ++ "⟧";
  addContext msg

end AltLHS

structure MinorsRange :=
(firstMinorPos : Nat)
(numMinors     : Nat)

abbrev AltToMinorsMap := PersistentHashMap Nat MinorsRange

structure ElimResult :=
(numMinors : Nat)  -- It is the number of alternatives (Reason: support for overlapping equations)
(numEqs    : Nat)  -- It is the number of minors (Reason: users may want equations that hold definitionally)
(elim      : Expr) -- The eliminator. It is not just `Expr.const elimName` because the type of the major premises may contain free variables.
(altMap    : AltToMinorsMap) -- each alternative may be "expanded" into multiple minor premise

private def checkNumPatterns (majors : List Expr) (lhss : List AltLHS) : MetaM Unit :=
let num := majors.length;
when (lhss.any (fun lhs => lhs.patterns.length != num)) $
  throw $ Exception.other "incorrect number of patterns"

def mkElim (elimName : Name) (majors : List Expr) (lhss : List AltLHS) : MetaM ElimResult := do
checkNumPatterns majors lhss;
pure { numMinors := 0, numEqs := 0, elim := arbitrary _, altMap := {} } -- TODO

end DepElim
end Meta
end Lean

open Lean
open Lean.Meta
open Lean.Meta.DepElim

/- Infrastructure for testing -/

def printAltLHS (alts : List AltLHS) : MetaM Unit := do
msgs ← alts.mapM AltLHS.toMessageData;
trace! `Meta.debug (Format.line ++ (MessageData.joinSep msgs Format.line))

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
      pure $ Pattern.arrayLit Syntax.missing pats
    | none => do
      cval? ← constructorApp? e;
      match cval? with
      | none      => throw $ Exception.other "unexpected pattern"
      | some cval => do
        let args   := e.getAppArgs;
        let fields := args.extract cval.nparams args.size;
        pats ← fields.toList.mapM mkPattern;
        pure $ Pattern.ctor Syntax.missing cval.name pats

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
forallTelescopeReducing e $ fun args body => do
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

def mkDepElimFrom (declName : Name) (numPats : Nat) : MetaM (List Expr × List AltLHS) := do
cinfo ← getConstInfo declName;
forallTelescopeReducing cinfo.type $ fun args body =>
  if args.size < numPats then
    throw $ Exception.other "insufficient number of parameters"
  else do
    let xs := (args.extract (args.size - numPats) args.size).toList;
    alts ← decodeAltLHSs body;
    pure (xs, alts)

inductive Pat {α : Sort u} (a : α) : Type u
| mk {} : Pat

inductive LHS {α : Sort u} (a : α) : Type u
| mk {} : LHS

instance LHS.inhabited {α} (a : α) : Inhabited (LHS a) := ⟨LHS.mk⟩

def ex1 (α : Type u) (β : Type v) (n : Nat) (x : List α) (y : List β) :
  LHS (Pat ([] : List α) × Pat ([] : List α))
× LHS (forall (a : α) (b : α), Pat [a] × Pat [b])
× LHS (forall (a₁ a₂ : α) (as : List α) (b₁ b₂ : β) (bs : List β), Pat (a₁::a₂::as) × Pat (b₁::b₂::bs))
× LHS (forall (as : List α) (bs : List β), Pat as × Pat bs)
:= arbitrary _

set_option trace.Meta.debug true

def tst1 : MetaM Unit := do
(majors, alts) ← mkDepElimFrom `ex1 2;
printAltLHS alts;
mkElim `test majors alts;
pure ()

#eval tst1
