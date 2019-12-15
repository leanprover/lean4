/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.Lean.Syntax
import Init.Lean.Elab.ResolveName
import Init.Lean.Elab.Term
import Init.Lean.Parser -- TODO: remove after removing old elaborator

namespace Lean

/-- Reflect a runtime datum back to surface syntax (best-effort). -/
class HasQuote (α : Type) :=
(quote : α → Syntax)

export HasQuote (quote)

instance Syntax.HasQuote : HasQuote Syntax := ⟨id⟩
instance String.HasQuote : HasQuote String := ⟨mkStxStrLit⟩
instance Nat.HasQuote : HasQuote Nat := ⟨fun n => mkStxNumLit $ toString n⟩

private def quoteName : Name → Syntax
| Name.anonymous => Unhygienic.run `(_root_.Lean.Name.anonymous)
| Name.str n s _ => Unhygienic.run `(_root_.Lean.mkNameStr %%(quoteName n) %%(Lean.HasQuote.quote s))
| Name.num n i _ => Unhygienic.run `(_root_.Lean.mkNameNum %%(quoteName n) %%(Lean.HasQuote.quote i))

instance Name.HasQuote : HasQuote Name := ⟨quoteName⟩

private def appN (fn : Syntax) (args : Array Syntax) : Syntax :=
args.foldl (fun fn arg => Unhygienic.run `(%%fn %%arg)) fn

instance Prod.HasQuote {α β : Type} [HasQuote α] [HasQuote β] : HasQuote (α × β) :=
⟨fun ⟨a, b⟩ => Unhygienic.run `(_root_.Prod.mk %%(Lean.HasQuote.quote a) %%(Lean.HasQuote.quote b))⟩

private def quoteList {α : Type} [HasQuote α] : List α → Syntax
| [] =>      Unhygienic.run `(_root_.List.nil)
| (x::xs) => Unhygienic.run `(_root_.List.cons %%(Lean.HasQuote.quote x) %%(quoteList xs))

instance List.HasQuote {α : Type} [HasQuote α] : HasQuote (List α) := ⟨quoteList⟩

instance Array.HasQuote {α : Type} [HasQuote α] : HasQuote (Array α) :=
⟨fun xs => let stx := quote xs.toList; Unhygienic.run `(_root_.List.toArray %%stx)⟩

namespace Elab
namespace Term

private partial def quoteSyntax (env : Environment) : Nat → Syntax → TermElabM Syntax
| _, Syntax.ident info rawVal val preresolved => do
  -- TODO: pass scope information
  let ns := Name.anonymous;
  let openDecls := [];
  let preresolved := resolveGlobalName env ns openDecls val <|> preresolved;
  let val := quote val;
  -- `scp` is bound in stxQuot.expand
  val ← `(Lean.addMacroScope %%val scp);
  let args := quote preresolved;
  `(Lean.Syntax.ident Option.none (String.toSubstring %%(Lean.mkStxStrLit (HasToString.toString rawVal))) %%val %%args)
| 0, Syntax.node `Lean.Parser.Term.antiquot args => pure $ args.get! 1
| lvl, Syntax.node k args => do
  let lvl := match k with
    | `Lean.Parser.Term.stxQuot => lvl + 1
    | `Lean.Parser.Term.antiquot => lvl - 1
    | _ => lvl;
  let k := quote k;
  args ← quote <$> args.mapM (quoteSyntax lvl);
  `(Lean.Syntax.node %%k %%args)
| _, Syntax.atom info val =>
  `(Lean.Syntax.atom Option.none %%(Lean.mkStxStrLit val))
| _, Syntax.missing => unreachable!

def stxQuot.expand (env : Environment) (stx : Syntax) : TermElabM Syntax := do
let quoted := stx.getArg 1;
-- `(do msc ← getCurrMacroScope; pure %(quoteSyntax env 0 quoted))
stx ← quoteSyntax env 0 quoted;
`(HasBind.bind Lean.MonadQuotation.getCurrMacroScope (fun scp => HasPure.pure %%stx))

@[builtinTermElab stxQuot] def elabStxQuot : TermElab :=
fun stx expectedType? => do
  env ← getEnv;
  stx ← stxQuot.expand env (stx.getArg 1);
  elabTerm stx expectedType?

private abbrev Alt := List Syntax × Syntax

private def isVarPat? (pat : Syntax) : Option (Syntax → TermElabM Syntax) :=
if pat.isOfKind `Lean.Parser.Term.id then some $ fun rhs => `(%%rhs discr)
else if pat.isOfKind `Lean.Parser.Term.hole then some pure
else if pat.isOfKind `Lean.Parser.Term.stxQuot then
  let quoted := pat.getArg 1;
  if quoted.isAtom then some pure
  else if quoted.isOfKind `Lean.Parser.Term.antiquot then
    let anti := quoted.getArg 1;
    if anti.isOfKind `Lean.Parser.Term.id then some $ fun rhs => `(%%rhs discr)
    -- TODO: *, ?
    else unreachable!
  else none
else none

private def altNextNode? : Alt → Option SyntaxNode
| (pat::_, _) =>
  if (isVarPat? pat).isNone && pat.isOfKind `Lean.Parser.Term.stxQuot then
    let quoted := pat.getArg 1;
    some quoted.asNode
  else none
| _ => none

private def explodeHeadPat (numArgs : Nat) : Alt → TermElabM Alt
| (pat::pats, rhs) => match isVarPat? pat with
  | some fnRhs => do
    newPat ← `(_);
    let newPats := List.replicate numArgs newPat;
    rhs ← fnRhs rhs;
    pure (newPats ++ pats, rhs)
  | none =>
    if pat.isOfKind `Lean.Parser.Term.stxQuot then do
      let quoted := pat.getArg 1;
      let newPats := quoted.getArgs.toList.map $ fun arg => Syntax.node `Lean.Parser.Term.stxQuot #[mkAtom "`(", arg, mkAtom ")"];
      pure (newPats ++ pats, rhs)
    else throwError pat $ "unsupported `syntax_match` pattern kind " ++ toString pat.getKind
| _ => unreachable!

private def nodeShape (n : SyntaxNode) : SyntaxNodeKind × Nat :=
(n.getKind, n.getArgs.size)

private partial def compileStxMatch (ref : Syntax) : List Syntax → List Alt → TermElabM Syntax
| [],            ([], rhs)::_ => pure rhs
| _,             []           => throwError ref "non-exhaustive 'match_syntax'"
| discr::discrs, alts         =>
  match alts.findSome? altNextNode? with
  | some node => do
    let shape := nodeShape node;
    newDiscrs ← (List.range node.getArgs.size).mapM $ fun i => `(Lean.Syntax.getArg discr %%(Lean.HasQuote.quote i));
    let yesAlts := alts.filter $ fun alt => match altNextNode? alt with some n => nodeShape n == shape | none => true;
    yesAlts ← yesAlts.mapM $ explodeHeadPat node.getArgs.size;
    let noAlts  := alts.filter $ fun alt => match altNextNode? alt with some n => nodeShape n != shape | none => true;
    yes ← withFreshMacroScope $ compileStxMatch (newDiscrs ++ discrs) yesAlts;
    no ← withFreshMacroScope $ compileStxMatch (discr::discrs) noAlts;
    `(let discr := %%discr; if Lean.Syntax.isOfKind discr %%(Lean.HasQuote.quote (Prod.fst shape)) then %%yes else %%no)
  | none => do
    alts ← alts.mapM $ explodeHeadPat 0;
    res ← withFreshMacroScope $ compileStxMatch discrs alts;
    `(let discr := %%discr; %%res)
--| _, _ => unreachable!
| discrs, alts => throwError ref $ toString (discrs, alts)

private partial def getAntiquotVarsAux : Syntax → TermElabM (List Syntax)
| Syntax.node `Lean.Parser.Term.antiquot args =>
  let anti := args.get! 1;
  if anti.isOfKind `Lean.Parser.Term.id then pure [anti]
  else throwError anti "syntax_match: antiquotation must be variable"
| Syntax.node k args => do
  List.join <$> args.toList.mapM getAntiquotVarsAux
| _ => pure []

private partial def getAntiquotVars (stx : Syntax) : TermElabM (List Syntax) :=
if stx.isOfKind `Lean.Parser.Term.stxQuot then do
  let quoted := stx.getArg 1;
  getAntiquotVarsAux stx
else pure []

private def letBindRhss (cont : List Alt → TermElabM Syntax) : List Alt → List Alt → TermElabM Syntax
| [],                altsRev' => cont altsRev'.reverse
| (pats, rhs)::alts, altsRev' => do
  vars ← List.join <$> pats.mapM getAntiquotVars;
  match vars with
  | [] => do
    rhs' ← `(rhs ());
    cont ← withFreshMacroScope $ letBindRhss alts ((pats, rhs')::altsRev');
    `(let rhs := fun _ => %%rhs; %%cont)
  | _ => do
    -- rhs ← `(fun %%vars... => %%rhs)
    let rhs := Syntax.node `Lean.Parser.Term.fun #[mkAtom "fun", Syntax.node `null vars.toArray, mkAtom "=>", rhs];
    -- rhs' ← `(rhs %%vars...);
    rhs' ← `(rhs);
    cont ← withFreshMacroScope $ letBindRhss alts ((pats, rhs')::altsRev');
    `(let rhs := %%rhs; %%cont)

def match_syntax.expand (stx : SyntaxNode) : TermElabM Syntax := do
let discr := stx.getArg 1;
let alts := stx.getArg 3;
alts ← alts.getArgs.mapM $ fun alt => do {
  let pats := alt.getArg 1;
  pat ← if pats.getArgs.size == 1 then pure $ pats.getArg 0
    else throwError stx.val "syntax_match: expected exactly one pattern per alternative";
  let rhs := alt.getArg 3;
  pure ([pat], rhs)
};
letBindRhss (compileStxMatch stx.val [discr]) alts.toList []

@[builtinTermElab «match_syntax»] def elabMatchSyntax : TermElab :=
fun stx expectedType? => do
  stx ← match_syntax.expand stx;
  elabTerm stx expectedType?

-- REMOVE with old frontend
private def exprPlaceholder := mkMVar Name.anonymous

private unsafe partial def toPreterm (env : Environment) : Syntax → Except String Expr
| stx =>
  let args := stx.getArgs;
  match stx.getKind with
  | `Lean.Parser.Term.id =>
    match args.get! 0 with
    | Syntax.ident _ _ val preresolved =>
      -- TODO: pass scope information
      let ns := Name.anonymous;
      let openDecls := [];
      let resolved := resolveGlobalName env ns openDecls val <|> preresolved;
      match resolved with
      | (pre,[])::_ => pure $ Lean.mkConst pre
      | [] => pure $ mkFVar val
      | _ => throw "stxQuot: unimplemented: projection notation"
    | _ => unreachable!
  | `Lean.Parser.Term.fun => do
    let params := (args.get! 1).getArgs;
    body ← toPreterm $ args.get! 3;
    params.foldrM (fun param e => do
      (n, ty) ← if param.isOfKind `Lean.Parser.Term.id then
          pure (param.getIdAt 0, exprPlaceholder)
        else if param.isOfKind `Lean.Parser.Term.hole then
          pure (`_a, exprPlaceholder)
        else do {
          let n := ((param.getArg 1).getArg 0).getIdAt 0;
          ty ← toPreterm $ (((param.getArg 1).getArg 1).getArg 0).getArg 1;
          pure (n, ty)
        };
      pure $ Lean.mkLambda n BinderInfo.default ty (Expr.abstract e #[mkFVar n]))
      body
  | `Lean.Parser.Term.let => do
    let n := (args.get! 1).getIdAt 0;
    val ← toPreterm $ (args.get! 1).getArg 4;
    body ← toPreterm $ args.get! 3;
    pure $ mkLet n exprPlaceholder val (Expr.abstract body #[mkFVar n])
  | `Lean.Parser.Term.app => do
    fn ← toPreterm $ args.get! 0;
    arg ← toPreterm $ args.get! 1;
    pure $ mkApp fn arg
  | `Lean.Parser.Term.if => do
    let con := args.get! 2;
    let yes := args.get! 4;
    let no := args.get! 6;
    toPreterm $ Unhygienic.run `(ite %%con %%yes %%no)
  | `Lean.Parser.Term.paren =>
    let inner := (args.get! 1).getArgs;
    if inner.size == 0 then pure $ Lean.mkConst `Unit.unit
    else toPreterm $ inner.get! 0
  | `Lean.Parser.Term.band =>
    let lhs := args.get! 0; let rhs := args.get! 2;
    toPreterm $ Unhygienic.run `(and %%lhs %%rhs)
  | `Lean.Parser.Term.beq =>
    let lhs := args.get! 0; let rhs := args.get! 2;
    toPreterm $ Unhygienic.run `(HasBeq.beq %%lhs %%rhs)
  | `strLit => pure $ mkStrLit $ stx.isStrLit?.getD ""
  | `numLit => pure $ mkNatLit $ stx.isNatLit?.getD 0
  | `expr => pure $ unsafeCast $ stx.getArg 0  -- HACK: see below
  | k => throw $ "stxQuot: unimplemented kind " ++ toString k

@[export lean_parse_expr]
def oldParseExpr (env : Environment) (input : String) (pos : String.Pos) : Except String (Syntax × String.Pos) := do
let c := Parser.mkParserContextCore env input "<foo>";
let c := c.toParserContext env;
let s := Parser.mkParserState c.input;
let s := s.setPos pos;
let s := (Parser.termParser : Parser.Parser).fn (0 : Nat) c s;
let stx := s.stxStack.back;
match s.errorMsg with
| some errorMsg =>
  Except.error $ toString errorMsg
| none =>
  Except.ok (stx, s.pos)

private def oldRunTermElabM {α} (env : Environment) (x : TermElabM α) : Except String α := do
match x {fileName := "foo", fileMap := FileMap.ofString "", cmdPos := 0, currNamespace := `foo} {env := env} with
| EStateM.Result.ok a _    => Except.ok a
| EStateM.Result.error msg _ => Except.error $ toString msg

@[export lean_expand_stx_quot]
unsafe def oldExpandStxQuot (env : Environment) (stx : Syntax) : Except String Expr := do
stx ← oldRunTermElabM env $ stxQuot.expand env stx;
toPreterm env stx

@[export lean_get_antiquot_vars]
def oldGetAntiquotVars (env : Environment) (pats : List Syntax) : Except String (List Name) := oldRunTermElabM env $ do
vars ← List.join <$> pats.mapM getAntiquotVars;
pure $ vars.map $ fun var => var.getIdAt 0

@[export lean_expand_match_syntax]
unsafe def oldExpandMatchSyntax (env : Environment) (discr : Syntax) (alts : List (List Syntax × Syntax)) : Except String Expr := do
stx ← oldRunTermElabM env $ do {
  -- HACK: discr and the RHSs are actually `Expr`
  let discr := Syntax.node `expr #[discr];
  let alts := alts.map $ fun alt => (alt.1, Syntax.node `expr #[alt.2]);
  letBindRhss (compileStxMatch Syntax.missing [discr]) alts []
};
toPreterm env stx

end Term
end Elab
end Lean
