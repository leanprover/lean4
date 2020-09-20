/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Meta.RecursorInfo
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.Induction
import Lean.Meta.Tactic.Cases
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Generalize

namespace Lean
namespace Elab
namespace Tactic

open Meta

-- Recall that
-- majorPremise := parser! optional (try (ident >> " : ")) >> termParser

private def getAuxHypothesisName (stx : Syntax) : Option Name :=
if ((stx.getArg 1).getArg 0).isNone then none
else some (((stx.getArg 1).getArg 0).getIdAt 0)

private def getMajor (stx : Syntax) : Syntax :=
(stx.getArg 1).getArg 1

private def elabMajor (h? : Option Name) (major : Syntax) : TacticM Expr := do
match h? with
| none   => withMainMVarContext $ elabTerm major none
| some h => withMainMVarContext do
  lctx ← getLCtx;
  let x := lctx.getUnusedName `x;
  major ← elabTerm major none;
  evalGeneralizeAux h? major x;
  withMainMVarContext do
    lctx ← getLCtx;
    match lctx.findFromUserName? x with
    | some decl => pure decl.toExpr
    | none      => throwError "failed to generalize"

private def generalizeMajor (major : Expr) : TacticM Expr := do
match major with
| Expr.fvar _ _ => pure major
| _ => do
  liftMetaTacticAux fun mvarId => do
    mvarId ← Meta.generalize mvarId major `x false;
    (fvarId, mvarId) ← Meta.intro1 mvarId;
    pure (mkFVar fvarId, [mvarId])

/-
  Recall that
  ```
  generalizingVars := optional (" generalizing " >> many1 ident)
  «induction»  := parser! nonReservedSymbol "induction " >> majorPremise >> usingRec >> generalizingVars >> withAlts
  ```
  `stx` is syntax for `induction`. -/
private def getGeneralizingFVarIds (stx : Syntax) : TacticM (Array FVarId) :=
withRef stx $
let generalizingStx := stx.getArg 3;
if generalizingStx.isNone then pure #[]
else withMainMVarContext do
  trace `Elab.induction fun _ => generalizingStx;
  let vars := (generalizingStx.getArg 1).getArgs;
  getFVarIds vars

-- process `generalizingVars` subterm of induction Syntax `stx`.
private def generalizeVars (stx : Syntax) (major : Expr) : TacticM Nat := do
fvarIds ← getGeneralizingFVarIds stx;
liftMetaTacticAux fun mvarId => do
  (fvarIds, mvarId') ← Meta.revert mvarId fvarIds;
  when (fvarIds.contains major.fvarId!) $
    Meta.throwTacticEx `induction mvarId "major premise depends on variable being generalized";
  pure (fvarIds.size, [mvarId'])

private def getAlts (withAlts : Syntax) : Array Syntax :=
(withAlts.getArg 2).getArgs.getSepElems

/-
  Given an `inductionAlt` of the form
  ```
  nodeWithAntiquot "inductionAlt" `Lean.Parser.Tactic.inductionAlt $ ident' >> many ident' >> darrow >> termParser
  ``` -/
private def getAltName (alt : Syntax) : Name := (alt.getArg 0).getId.eraseMacroScopes
private def getAltVarNames (alt : Syntax) : Array Name := (alt.getArg 1).getArgs.map Syntax.getId
private def getAltRHS (alt : Syntax) : Syntax := alt.getArg 3

/-
  Given alts of the form
  ```
  nodeWithAntiquot "inductionAlt" `Lean.Parser.Tactic.inductionAlt $ ident' >> many ident' >> darrow >> termParser
  ```
  esnure the first `ident'` is `_` or a constructor name.
-/
private def checkAltCtorNames (alts : Array Syntax) (ctorNames : List Name) : TacticM Unit :=
alts.forM $ fun alt => do
  let n := getAltName alt;
  withRef alt $ trace `Elab.checkAlt $ fun _ => n ++ ", " ++ alt;
  unless (n == `_ || ctorNames.any (fun ctorName => n.isSuffixOf ctorName)) $
    throwErrorAt (alt.getArg 0) ("invalid constructor name '" ++ toString n ++ "'")

structure RecInfo :=
(recName : Name)
(altVars : Array (List Name) := #[]) -- new variable names for each minor premise
(altRHSs : Array Syntax := #[])      -- RHS for each minor premise

def getInductiveValFromMajor (major : Expr) : TacticM InductiveVal :=
liftMetaMAtMain $ fun mvarId => do
  majorType ← inferType major;
  majorType ← whnf majorType;
  matchConstInduct majorType.getAppFn
    (fun _ => Meta.throwTacticEx `induction mvarId ("major premise type is not an inductive type " ++ indentExpr majorType))
    (fun val _ => pure val)

private partial def getRecFromUsingLoop (baseRecName : Name) : Expr → TacticM (Option Meta.RecursorInfo)
| majorType => do
  let continue (majorType : Expr) : TacticM (Option Meta.RecursorInfo) := do {
    majorType? ← unfoldDefinition? majorType;
    match majorType? with
    | some majorType => withIncRecDepth $ getRecFromUsingLoop majorType
    | none           => pure none
  };
  majorType ← whnfCore majorType;
  match majorType.getAppFn with
  | Expr.const name _ _ => do
    let candidate := name ++ baseRecName;
    env ← getEnv;
    match env.find? candidate with
    | some _ =>
      catch
        (liftMetaMAtMain fun _ => do info ← Meta.mkRecursorInfo candidate; pure (some info))
        (fun _ => continue majorType)
    | none   => continue majorType
  | _ => continue majorType

def getRecFromUsing (major : Expr) (baseRecName : Name) : TacticM Meta.RecursorInfo := do
majorType ← inferType major;
recInfo? ← getRecFromUsingLoop baseRecName majorType;
match recInfo? with
| some recInfo => pure recInfo
| none => do
  recName ← liftM $ Term.resolveGlobalConstNoOverload baseRecName;
  catch
    (liftMetaMAtMain fun _ => Meta.mkRecursorInfo recName)
    (fun _ => throwError ("invalid recursor name '" ++ baseRecName ++ "'"))

/- Create `RecInfo` assuming builtin recursor -/
private def getRecInfoDefault (major : Expr) (withAlts : Syntax) (allowMissingAlts : Bool) : TacticM (RecInfo × Array Name) := do
indVal ← getInductiveValFromMajor major;
let recName := mkRecFor indVal.name;
if withAlts.isNone then pure ({ recName := recName }, #[])
else do
  let ctorNames := indVal.ctors;
  let alts      := getAlts withAlts;
  checkAltCtorNames alts ctorNames;
  (altVars, altRHSs, remainingAlts, _) ← ctorNames.foldlM
    (fun (result : Array (List Name) × Array Syntax × Array Syntax × Option Syntax) (ctorName : Name) => do
      let (altVars, altRHSs, remainingAlts, prevAnonymousAlt?) := result;
      match remainingAlts.findIdx? (fun alt => (getAltName alt).isSuffixOf ctorName) with
      | some idx =>
        let newAlt := remainingAlts.get! idx;
        pure (altVars.push (getAltVarNames newAlt).toList, altRHSs.push (getAltRHS newAlt), remainingAlts.eraseIdx idx, prevAnonymousAlt?)
      | none => match remainingAlts.findIdx? (fun alt => getAltName alt == `_) with
        | some idx =>
          let newAlt     := remainingAlts.get! idx;
          pure (altVars.push (getAltVarNames newAlt).toList, altRHSs.push (getAltRHS newAlt), remainingAlts.eraseIdx idx, some newAlt)
        | none => match prevAnonymousAlt? with
          | some alt =>
            pure (altVars.push (getAltVarNames alt).toList, altRHSs.push (getAltRHS alt), remainingAlts, prevAnonymousAlt?)
          | none     =>
            if allowMissingAlts then
              pure (altVars.push [], altRHSs.push Syntax.missing, remainingAlts, prevAnonymousAlt?)
            else
              throwError ("alternative for constructor '" ++ toString ctorName ++ "' is missing"))
    (#[], #[], alts, none);
  unless remainingAlts.isEmpty $
    throwErrorAt (remainingAlts.get! 0) "unused alternative";
  pure ({ recName := recName, altVars := altVars, altRHSs := altRHSs }, ctorNames.toArray)

/-
  Recall that
  ```
  inductionAlt  : Parser :=
    nodeWithAntiquot "inductionAlt" `Lean.Parser.Tactic.inductionAlt $ ident' >> many ident' >> darrow >> (hole <|> syntheticHole <|> tacticParser)
  inductionAlts : Parser := withPosition $ fun pos => "|" >> sepBy1 inductionAlt (checkColGe pos.column "alternatives must be indented" >> "|")
  withAlts : Parser := optional (" with " >> inductionAlts)
  usingRec : Parser := optional (" using " >> ident)
  ``` -/
private def getRecInfo (stx : Syntax) (major : Expr) : TacticM RecInfo :=
withRef stx $
let usingRecStx := stx.getArg 2;
let withAlts    := stx.getArg 4;
if usingRecStx.isNone then do
  (rinfo, _) ← getRecInfoDefault major withAlts false;
  pure rinfo
else do
  let baseRecName := (usingRecStx.getIdAt 1).eraseMacroScopes;
  recInfo ← getRecFromUsing major baseRecName;
  let recName := recInfo.recursorName;
  if withAlts.isNone then pure { recName := recName }
  else do
    let alts := getAlts withAlts;
    paramNames ← liftMetaMAtMain $ fun _ => getParamNames recInfo.recursorName;
    (altVars, altRHSs, remainingAlts, _) ← paramNames.size.foldM
      (fun (i : Nat) (result : Array (List Name) × Array Syntax × Array Syntax × Option Syntax) =>
        if recInfo.isMinor i then
          let paramName := paramNames.get! i;
          let (altVars, altRHSs, remainingAlts, prevAnonymousAlt?) := result;
          match remainingAlts.findIdx? (fun alt => getAltName alt == paramName) with
          | some idx =>
            let newAlt := remainingAlts.get! idx;
            pure (altVars.push (getAltVarNames newAlt).toList, altRHSs.push (getAltRHS newAlt), remainingAlts.eraseIdx idx, prevAnonymousAlt?)
          | none => match remainingAlts.findIdx? (fun alt => getAltName alt == `_) with
            | some idx =>
              let newAlt     := remainingAlts.get! idx;
              pure (altVars.push (getAltVarNames newAlt).toList, altRHSs.push (getAltRHS newAlt), remainingAlts.eraseIdx idx, some newAlt)
            | none => match prevAnonymousAlt? with
              | some alt =>
                pure (altVars.push (getAltVarNames alt).toList, altRHSs.push (getAltRHS alt), remainingAlts, prevAnonymousAlt?)
              | none     => throwError ("alternative for minor premise '" ++ toString paramName ++ "' is missing")
        else
          pure result)
      (#[], #[], alts, none);
    unless remainingAlts.isEmpty $
      throwErrorAt (remainingAlts.get! 0) "unused alternative";
    pure { recName := recName, altVars := altVars, altRHSs := altRHSs }

-- Return true if `stx` is a term occurring in the RHS of the induction/cases tactic
def isHoleRHS (rhs : Syntax) : Bool :=
rhs.isOfKind `Lean.Parser.Term.syntheticHole || rhs.isOfKind `Lean.Parser.Term.hole

private def processResult (altRHSs : Array Syntax) (result : Array Meta.InductionSubgoal) : TacticM Unit := do
if altRHSs.isEmpty then
  setGoals $ result.toList.map $ fun s => s.mvarId
else do
  unless (altRHSs.size == result.size) $
    throwError ("mistmatch on the number of subgoals produced (" ++ toString result.size ++ ") and " ++
                "alternatives provided (" ++ toString altRHSs.size ++ ")");
  gs ← result.size.foldM
    (fun i gs => do
      let subgoal := result.get! i;
      let rhs     := altRHSs.get! i;
      let ref     := rhs;
      let mvarId  := subgoal.mvarId;
      if isHoleRHS rhs then withMVarContext mvarId $ withRef rhs do
        mvarDecl ← getMVarDecl mvarId;
        val ← elabTermEnsuringType rhs mvarDecl.type;
        assignExprMVar mvarId val;
        gs' ← getMVarsNoDelayed val;
        let gs' := gs'.toList;
        tagUntaggedGoals mvarDecl.userName `induction gs';
        pure (gs ++ gs')
      else do
        setGoals [mvarId];
        evalTactic rhs;
        done;
        pure gs)
    [];
  setGoals gs

@[builtinTactic Lean.Parser.Tactic.induction] def evalInduction : Tactic :=
fun stx => focusAux $ do
  let h? := getAuxHypothesisName stx;
  major ← elabMajor h? (getMajor stx);
  major ← generalizeMajor major;
  n ← generalizeVars stx major;
  recInfo ← getRecInfo stx major;
  (mvarId, _) ← getMainGoal;
  result ← liftMetaM $ Meta.induction mvarId major.fvarId! recInfo.recName recInfo.altVars;
  processResult recInfo.altRHSs result

private partial def checkCasesResultAux (casesResult : Array Meta.CasesSubgoal) (ctorNames : Array Name) (altRHSs : Array Syntax)
    : Nat → Nat → TacticM Unit
| i, j =>
  if h : j < altRHSs.size then do
    let altRHS   := altRHSs.get ⟨j, h⟩;
    if altRHS.isMissing then
      checkCasesResultAux i (j+1)
    else
      let ctorName := ctorNames.get! j;
      if h : i < casesResult.size then
        let subgoal := casesResult.get ⟨i, h⟩;
        if ctorName == subgoal.ctorName then
          checkCasesResultAux (i+1) (j+1)
        else
          throwError ("alternative for '" ++ subgoal.ctorName ++ "' has not been provided")
      else
        throwError ("alternative for '" ++ ctorName ++ "' is not needed")
  else if h : i < casesResult.size then
    let subgoal := casesResult.get ⟨i, h⟩;
    throwError ("alternative for '" ++ subgoal.ctorName ++ "' has not been provided")
  else
    pure ()

private def checkCasesResult (casesResult : Array Meta.CasesSubgoal) (ctorNames : Array Name) (altRHSs : Array Syntax) : TacticM Unit :=
unless altRHSs.isEmpty $ checkCasesResultAux casesResult ctorNames altRHSs 0 0

@[builtinTactic Lean.Parser.Tactic.cases] def evalCases : Tactic :=
fun stx => focusAux $ do
  -- parser! nonReservedSymbol "cases " >> majorPremise >> withAlts
  let h? := getAuxHypothesisName stx;
  major ← elabMajor h? (getMajor stx);
  major ← generalizeMajor major;
  (mvarId, _) ← getMainGoal;
  let withAlts := stx.getArg 2;
  (recInfo, ctorNames) ← getRecInfoDefault major withAlts true;
  result ← liftMetaM $ Meta.cases mvarId major.fvarId! recInfo.altVars;
  checkCasesResult result ctorNames recInfo.altRHSs;
  let result  := result.map (fun s => s.toInductionSubgoal);
  let altRHSs := recInfo.altRHSs.filter $ fun stx => !stx.isMissing;
  processResult altRHSs result

end Tactic
end Elab
end Lean
