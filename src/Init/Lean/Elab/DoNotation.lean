/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Term
import Init.Lean.Elab.Quotation

namespace Lean
namespace Elab
namespace Term

private def mkIdMonadFor (ref : Syntax) (type : Expr) : TermElabM (Expr × Expr) := do
u ← getLevel ref type;
let id      := (Lean.mkConst `Id [u]);
let idType  := Lean.mkApp (Lean.mkConst `Id [u]) type;
let idMonad := Lean.mkConst `Id.monad [u];
pure (idType, idMonad)

private def extractMonad (ref : Syntax) (expectedType? : Option Expr) : TermElabM (Expr × Expr) := do
match expectedType? with
| none => throwError ref "invalid do notation, expected type is not available"
| some expectedType => do
  type ← withReducible $ whnf ref expectedType;
  when type.getAppFn.isMVar $ throwError ref "invalid do notation, expected type is not available";
  match type with
  | Expr.app m _ _ =>
    catch
      (do
        monadInst ← mkAppM ref `Monad #[m];
        monad     ← synthesizeInst ref monadInst;
        pure (m, monad))
      (fun ex => mkIdMonadFor ref type)
  | _ => mkIdMonadFor ref type

private def getDoElems (stx : Syntax) : Array Syntax :=
--parser! "do " >> (bracketedDoSeq <|> doSeq)
let arg := stx.getArg 1;
if arg.getKind == `Lean.Parser.Term.bracketedDoSeq then
  -- parser! "{" >> doSeq >> "}"
  (arg.getArg 1).getArgs
else
  arg.getArgs

/- Expand `doLet`, `doPat`, and nonterminal `doExpr` -/
private partial def expandDoElems : Array Syntax → Nat → TermElabM (Option Syntax)
| doElems, i =>
  let mkRest : Unit → TermElabM Syntax := fun _ => do {
    let restElems := doElems.extract (i+2) doElems.size;
    if restElems.size == 1 then
      pure (restElems.get! 0)
    else
      `(do { $restElems* })
  };
  let addPrefix (rest : Syntax) : TermElabM (Option Syntax) := do {
    if i == 0 then
      pure rest
    else
      let newElems := doElems.extract 0 (i-1);
      let newElems := newElems.push $ Syntax.node `Lean.Parser.Term.doExpr #[rest];
      `(do { $newElems* })
  };
  if h : i < doElems.size then
    let doElem := doElems.get ⟨i, h⟩;
    if doElem.getKind == `Lean.Parser.Term.doLet then do
      let letDecl := doElem.getArg 1;
      rest ← mkRest ();
      newBody ← `(let $letDecl:letDecl; $rest);
      addPrefix newBody
    else if doElem.getKind == `Lean.Parser.Term.doPat then withFreshMacroScope $ do
      -- (termParser >> leftArrow) >> termParser >> optional (" | " >> termParser)
      let pat      := doElem.getArg 0;
      let discr    := doElem.getArg 2;
      let optElse  := doElem.getArg 3;
      rest ← mkRest ();
      newBody ←
        if optElse.isNone then do
          `(do x ← $discr; match x with | $pat => $rest)
        else
          let elseBody := optElse.getArg 1;
          `(do x ← $discr; match x with | $pat => $rest | _ => $elseBody);
      addPrefix newBody
    else if i < doElems.size - 2 && doElem.getKind == `Lean.Parser.Term.doExpr then do
      -- def doExpr := parser! termParser
      let term := doElem.getArg 0;
      auxDo ← `(do x ← $term; $(Syntax.missing));
      let doElemNew := (getDoElems auxDo).get! 0;
      let doElems := doElems.set! i doElemNew;
      expandDoElems doElems (i+2)
    else
      expandDoElems doElems (i+2)
  else
    pure none

@[builtinTermElab «do»] def elabDo : TermElab :=
fun stx expectedType? => do
  let ref := stx;
  tryPostponeIfNoneOrMVar expectedType?;
  let doElems := getDoElems stx;
  stxNew? ← expandDoElems doElems 0;
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  | none => do
    let doElems := doElems.getSepElems;
    (m, monad) ← extractMonad ref expectedType?;
    throwError stx ("WIP " ++ toString doElems ++ Format.line ++ monad)

end Term
end Elab
end Lean
