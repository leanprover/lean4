/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Meta.RecursorInfo
import Init.Lean.Meta.Tactic.Induction
import Init.Lean.Meta.Tactic.Cases
import Init.Lean.Elab.Tactic.ElabTerm
import Init.Lean.Elab.Tactic.Generalize

namespace Lean
namespace Elab
namespace Tactic

-- Recall that
-- majorPremise := parser! optional (try (ident >> " : ")) >> termParser

private def getAuxHypothesisName (stx : Syntax) : Option Name :=
if ((stx.getArg 1).getArg 0).isNone then none
else some (((stx.getArg 1).getArg 0).getIdAt 0)

private def getMajor (stx : Syntax) : Syntax :=
(stx.getArg 1).getArg 1

private def elabMajor (ref : Syntax) (h? : Option Name) (major : Syntax) : TacticM Expr := do
match h? with
| none   => withMainMVarContext ref $ elabTerm major none
| some h => withMainMVarContext ref $ do
  lctx ← getLCtx;
  let x := lctx.getUnusedName `x;
  major ← elabTerm major none;
  evalGeneralizeAux ref h? major x;
  withMainMVarContext ref $ do
    lctx ← getLCtx;
    match lctx.findFromUserName? x with
    | some decl => pure decl.toExpr
    | none      => throwError ref "failed to generalize"

private def generalizeMajor (ref : Syntax) (major : Expr) : TacticM Expr := do
match major with
| Expr.fvar _ _ => pure major
| _ => do
  liftMetaTacticAux ref $ fun mvarId => do
    mvarId ← Meta.generalize mvarId major `x;
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
let generalizingStx := stx.getArg 3;
if generalizingStx.isNone then pure #[]
else withMainMVarContext stx $ do
  trace `Elab.induction stx $ fun _ => generalizingStx;
  let vars := (generalizingStx.getArg 1).getArgs;
  getFVarIds vars

-- process `generalizingVars` subterm of induction Syntax `stx`.
private def generalizeVars (stx : Syntax) (major : Expr) : TacticM Nat := do
fvarIds ← getGeneralizingFVarIds stx;
liftMetaTacticAux stx $ fun mvarId => do
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
  trace `Elab.checkAlt alt $ fun _ => n ++ ", " ++ alt;
  unless (n == `_ || ctorNames.any (fun ctorName => n.isSuffixOf ctorName)) $
    throwError (alt.getArg 0) ("invalid constructor name '" ++ toString n ++ "'")

structure RecInfo :=
(recName : Name)
(altVars : Array (List Name) := #[]) -- new variable names for each minor premise
(altRHSs : Array Syntax := #[])      -- RHS for each minor premise

def getInductiveValFromMajor (ref : Syntax) (major : Expr) : TacticM InductiveVal :=
liftMetaMAtMain ref $ fun mvarId => do
  majorType ← Meta.inferType major;
  majorType ← Meta.whnf majorType;
  match majorType.getAppFn with
  | Expr.const n _ _ => do
    env ← Meta.getEnv;
    match env.find? n with
    | ConstantInfo.inductInfo val => pure val
    | _ => Meta.throwTacticEx `induction mvarId ("major premise type is not an inductive type " ++ indentExpr majorType)
  | _ => Meta.throwTacticEx `induction mvarId ("major premise type is not an inductive type " ++ indentExpr majorType)

private partial def getRecFromUsingLoop (ref : Syntax) (baseRecName : Name) : Expr → TacticM (Option Meta.RecursorInfo)
| majorType => do
  let continue (majorType : Expr) : TacticM (Option Meta.RecursorInfo) := do {
    majorType? ← unfoldDefinition? ref majorType;
    match majorType? with
    | some majorType => withIncRecDepth ref $ getRecFromUsingLoop majorType
    | none           => pure none
  };
  majorType ← whnfCore ref majorType;
  match majorType.getAppFn with
  | Expr.const name _ _ => do
    let candidate := name ++ baseRecName;
    env ← getEnv;
    match env.find? candidate with
    | some _ =>
      catch
        (liftMetaMAtMain ref $ fun _ => do info ← Meta.mkRecursorInfo candidate; pure (some info))
        (fun _ => continue majorType)
    | none   => continue majorType
  | _ => continue majorType

def getRecFromUsing (ref : Syntax) (major : Expr) (baseRecName : Name) : TacticM Meta.RecursorInfo := do
majorType ← inferType ref major;
recInfo? ← getRecFromUsingLoop ref baseRecName majorType;
match recInfo? with
| some recInfo => pure recInfo
| none => do
  result ← resolveGlobalName baseRecName;
  match result with
  | _::_::_         => throwError ref ("ambiguous recursor name '" ++ baseRecName ++ "', " ++ toString (result.map Prod.fst))
  | [(recName, [])] => do
    catch
      (liftMetaMAtMain ref $ fun _ => Meta.mkRecursorInfo recName)
      (fun _ => throwError ref ("invalid recursor name '" ++ baseRecName ++ "'"))
  | _ => throwError ref ("invalid recursor name '" ++ baseRecName ++ "'")

/- Create `RecInfo` assuming builtin recursor -/
private def getRecInfoDefault (ref : Syntax) (major : Expr) (withAlts : Syntax) (allowMissingAlts : Bool) : TacticM RecInfo := do
indVal ← getInductiveValFromMajor ref major;
let recName := mkRecFor indVal.name;
if withAlts.isNone then pure { recName := recName }
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
              throwError ref ("alternative for constructor '" ++ toString ctorName ++ "' is missing"))
    (#[], #[], alts, none);
  unless remainingAlts.isEmpty $
    throwError (remainingAlts.get! 0) "unused alternative";
  pure { recName := recName, altVars := altVars, altRHSs := altRHSs }

/-
  Recall that
  ```
  inductionAlt  : Parser := nodeWithAntiquot "inductionAlt" `Lean.Parser.Tactic.inductionAlt $ ident' >> many ident' >> darrow >> termParser
  inductionAlts : Parser := withPosition $ fun pos => "|" >> sepBy1 inductionAlt (checkColGe pos.column "alternatives must be indented" >> "|")
  withAlts : Parser := optional (" with " >> inductionAlts)
  usingRec : Parser := optional (" using " >> ident)
  ``` -/
private def getRecInfo (stx : Syntax) (major : Expr) : TacticM RecInfo :=
let ref         := stx;
let usingRecStx := stx.getArg 2;
let withAlts    := stx.getArg 4;
if usingRecStx.isNone then do
  getRecInfoDefault ref major withAlts false
else do
  let baseRecName := (usingRecStx.getIdAt 1).eraseMacroScopes;
  recInfo ← getRecFromUsing ref major baseRecName;
  let recName := recInfo.recursorName;
  if withAlts.isNone then pure { recName := recName }
  else do
    let alts := getAlts withAlts;
    paramNames ← liftMetaMAtMain ref $ fun _ => Meta.getParamNames recInfo.recursorName;
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
              | none     => throwError ref ("alternative for minor premise '" ++ toString paramName ++ "' is missing")
        else
          pure result)
      (#[], #[], alts, none);
    unless remainingAlts.isEmpty $
      throwError (remainingAlts.get! 0) "unused alternative";
    pure { recName := recName, altVars := altVars, altRHSs := altRHSs }

private def processResult (ref : Syntax) (altRHSs : Array Syntax) (result : Array Meta.InductionSubgoal) : TacticM Unit := do
if altRHSs.isEmpty then
  setGoals $ result.toList.map $ fun s => s.mvarId
else do
  unless (altRHSs.size == result.size) $
    throwError ref ("mistmatch on the number of subgoals produced (" ++ toString result.size ++ ") and " ++
                    "alternatives provided (" ++ toString altRHSs.size ++ ")");
  result.size.forM $ fun i => do
    let subgoal := result.get! i;
    let rhs     := altRHSs.get! i;
    let mvarId  := subgoal.mvarId;
    withMVarContext mvarId $ do
      mvarDecl ← getMVarDecl mvarId;
      val ← elabTerm rhs mvarDecl.type;
      val ← ensureHasType rhs mvarDecl.type val;
      assignExprMVar mvarId val;
      gs'  ← collectMVars rhs val;
      tagUntaggedGoals mvarDecl.userName `induction gs';
      appendGoals gs'

@[builtinTactic «induction»] def evalInduction : Tactic :=
fun stx => focusAux stx $ do
  let h? := getAuxHypothesisName stx;
  major ← elabMajor stx h? (getMajor stx);
  major ← generalizeMajor stx major;
  n ← generalizeVars stx major;
  recInfo ← getRecInfo stx major;
  (mvarId, _) ← getMainGoal stx;
  result ← liftMetaM stx $ Meta.induction mvarId major.fvarId! recInfo.recName recInfo.altVars;
  processResult stx recInfo.altRHSs result

@[builtinTactic «cases»] def evalCases : Tactic :=
fun stx => focusAux stx $ do
  -- parser! nonReservedSymbol "cases " >> majorPremise >> withAlts
  let h? := getAuxHypothesisName stx;
  major ← elabMajor stx h? (getMajor stx);
  major ← generalizeMajor stx major;
  (mvarId, _) ← getMainGoal stx;
  let withAlts := stx.getArg 2;
  recInfo ← getRecInfoDefault stx major withAlts true;
  result ← liftMetaM stx $ Meta.cases mvarId major.fvarId! recInfo.altVars;
  let result  := result.map (fun s => s.toInductionSubgoal);
  let altRHSs := recInfo.altRHSs.filter $ fun stx => !stx.isMissing;
  processResult stx altRHSs result

end Tactic
end Elab
end Lean
