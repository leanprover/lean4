/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Elaboration of syntax quotations as terms and patterns (in `match_syntax`). See also `./Hygiene.lean` for the basic
hygiene workings and data types.
-/
prelude
import Init.Lean.Syntax
import Init.Lean.Elab.ResolveName
import Init.Lean.Elab.Term
import Init.Lean.Parser -- TODO: remove after removing old elaborator

/- TODO

Quotations are currently integrated hackily into the old frontend. This implies the following restrictions:
* quotations have to fit in a single line, because that's how the old scanner works :)
* `open` commands are not respected (but `export`, `namespace` are)
* antiquotation terms have to be trivial (locals, consts (w/ projections), and apps, basically)

After removing the old frontend, quotations in this and other files should be cleaned up.
-/

namespace Lean

/-- Reflect a runtime datum back to surface syntax (best-effort). -/
class HasQuote (α : Type) :=
(quote : α → Syntax)

export HasQuote (quote)

instance Syntax.HasQuote : HasQuote Syntax := ⟨id⟩
instance String.HasQuote : HasQuote String := ⟨fun s => Syntax.node `Lean.Parser.Term.str #[mkStxStrLit s]⟩
instance Nat.HasQuote : HasQuote Nat := ⟨fun n => Syntax.node `Lean.Parser.Term.num #[mkStxNumLit $ toString n]⟩

private def quoteName : Name → Syntax
| Name.anonymous => Unhygienic.run `(_root_.Lean.Name.anonymous)
| Name.str n s _ => Unhygienic.run `(_root_.Lean.mkNameStr $(quoteName n) $(quote s))
| Name.num n i _ => Unhygienic.run `(_root_.Lean.mkNameNum $(quoteName n) $(quote i))

instance Name.hasQuote : HasQuote Name := ⟨quoteName⟩

private def appN (fn : Syntax) (args : Array Syntax) : Syntax :=
args.foldl (fun fn arg => Unhygienic.run `($fn $arg)) fn

instance Prod.hasQuote {α β : Type} [HasQuote α] [HasQuote β] : HasQuote (α × β) :=
⟨fun ⟨a, b⟩ => Unhygienic.run `(_root_.Prod.mk $(quote a) $(quote b))⟩

private def quoteList {α : Type} [HasQuote α] : List α → Syntax
| [] =>      Unhygienic.run `(_root_.List.nil)
| (x::xs) => Unhygienic.run `(_root_.List.cons $(quote x) $(quoteList xs))

instance List.hasQuote {α : Type} [HasQuote α] : HasQuote (List α) := ⟨quoteList⟩

instance Array.hasQuote {α : Type} [HasQuote α] : HasQuote (Array α) :=
⟨fun xs => let stx := quote xs.toList; Unhygienic.run `(_root_.List.toArray $stx)⟩

private def quoteOption {α : Type} [HasQuote α] : Option α → Syntax
| none     => Unhygienic.run `(_root_.Option.none)
| (some x) => Unhygienic.run `(_root_.Option.some $(quote x))

instance Option.hasQuote {α : Type} [HasQuote α] : HasQuote (Option α) := ⟨quoteOption⟩

namespace Elab
namespace Term

-- antiquotation node kinds are formed from the original node kind (if any) plus "antiquot"
def isAntiquot : Syntax → Bool
| Syntax.node (Name.str _ "antiquot" _) _ => true
| _                                       => false

def antiquotKind? : Syntax → Option SyntaxNodeKind
| Syntax.node (Name.str k "antiquot" _) args =>
  -- we treat all antiquotations where the kind was left implicit (`$e`) the same (see `elimAntiquotChoices`)
  if (args.get! 2).isNone then some Name.anonymous
  else some k
| _                                          => none

-- `$e*` is an antiquotation "splice" matching an arbitrary number of syntax nodes
def isAntiquotSplice (stx : Syntax) : Bool :=
isAntiquot stx && (stx.getArg 3).getOptional?.isSome

-- If any item of a `many` node is an antiquotation splice, its result should
-- be substituted into the `many` node's children
def isAntiquotSplicePat (stx : Syntax) : Bool :=
stx.isOfKind nullKind && stx.getArgs.any isAntiquotSplice

/-- A term like `($e) is actually ambiguous: the antiquotation could be of kind `term`,
    or `ident`, or ... . But it shouldn't really matter because antiquotations without
    explicit kinds behave the same at runtime. So we replace `choice` nodes that contain
    at least one implicit antiquotation with that antiquotation. -/
private partial def elimAntiquotChoices : Syntax → Syntax
| Syntax.node `choice args => match args.find? (fun arg => if antiquotKind? arg == Name.anonymous then some arg else none) with
  | some anti => anti
  | none      => Syntax.node `choice $ args.map elimAntiquotChoices
| Syntax.node k args       => Syntax.node k $ args.map elimAntiquotChoices
| stx                      => stx

-- Elaborate the content of a syntax quotation term
private partial def quoteSyntax : Syntax → TermElabM Syntax
| Syntax.ident info rawVal val preresolved => do
  -- Add global scopes at compilation time (now), add macro scope at runtime (in the quotation).
  -- See the paper for details.
  env           ← getEnv;
  currNamespace ← getCurrNamespace;
  openDecls     ← getOpenDecls;
  let preresolved := resolveGlobalName env currNamespace openDecls val ++ preresolved;
  let val := quote val;
  -- `scp` is bound in stxQuot.expand
  `(Syntax.ident none (String.toSubstring $(quote (toString rawVal))) (addMacroScope $val scp) $(quote preresolved))
-- if antiquotation, insert contents as-is, else recurse
| stx@(Syntax.node k args) =>
  if isAntiquot stx then
    -- splices must occur in a `many` node
    if isAntiquotSplice stx then throwError stx "unexpected antiquotation splice"
    else pure $ stx.getArg 1
  else do
    empty ← `(Array.empty);
    args ← args.foldlM (fun args arg =>
      if k == nullKind && isAntiquotSplice arg then
        -- antiquotation splice pattern: inject args array
        let arg := arg.getArg 1;
        `(Array.append $args $arg)
      else do
        arg ← quoteSyntax arg;
        `(Array.push $args $arg)) empty;
    `(Syntax.node $(quote k) $args)
| Syntax.atom info val =>
  `(Syntax.atom none $(quote val))
| Syntax.missing => unreachable!

def stxQuot.expand (stx : Syntax) : TermElabM Syntax := do
let quoted := stx.getArg 1;
/- Syntax quotations are monadic values depending on the current macro scope. For efficiency, we bind
   the macro scope once for each quotation, then build the syntax tree in a completely pure computation
   depending on this binding. Note that regular function calls do not introduce a new macro scope (i.e.
   we preserve referential transparency), so we can refer to this same `scp` inside `quoteSyntax` by
   including it literally in a syntax quotation. -/
-- TODO: simplify to `(do scp ← getCurrMacroScope; pure $(quoteSyntax quoted))
stx ← quoteSyntax (elimAntiquotChoices quoted);
`(bind getCurrMacroScope (fun scp => pure $stx))
/- NOTE: It may seem like the newly introduced binding `scp` may accidentally
   capture identifiers in an antiquotation introduced by `quoteSyntax`. However,
   note that the syntax quotation above enjoys the same hygiene guarantees as
   anywhere else in Lean; that is, we implement hygienic quotations by making
   use of the hygienic quotation support of the bootstrapped Lean compiler!

   Aside: While this might sound "dangerous", it is in fact less reliant on a
   "chain of trust" than other bootstrapping parts of Lean: because this
   implementation itself never uses `scp` (or any other identifier) both inside
   and outside quotations, it can actually correctly be compiled by an
   unhygienic (but otherwise correct) implementation of syntax quotations. As
   long as it is then compiled again with the resulting executable (i.e. up to
   stage 2), the result is a correct hygienic implementation. In this sense the
   implementation is "self-stabilizing". It was in fact originally compiled
   by an unhygienic prototype implementation. -/

@[builtinTermElab stxQuot] def elabStxQuot : TermElab :=
adaptExpander stxQuot.expand

/- match_syntax -/

-- an "alternative" of patterns plus right-hand side
private abbrev Alt := List Syntax × Syntax

/-- Information on a pattern's head that influences the compilation of a single
    match step. -/
structure HeadInfo :=
-- Node kind to match, if any
(kind    : Option SyntaxNodeKind     := none)
-- Nested patterns for each argument, if any. In a single match step, we only
-- check that the arity matches. The arity is usually implied by the node kind,
-- but not in the case of `many` nodes.
(argPats : Option (Array Syntax)     := none)
-- Function to apply to the right-hand side in case the match succeeds. Used to
-- bind pattern variables.
(rhsFn   : Syntax → TermElabM Syntax := pure)

instance HeadInfo.Inhabited : Inhabited HeadInfo := ⟨{}⟩

/-- `h1.generalizes h2` iff h1 is equal to or more general than h2, i.e. it matches all nodes
    h2 matches. This induces a partial ordering. -/
def HeadInfo.generalizes : HeadInfo → HeadInfo → Bool
| { kind := none, .. }, _                      => true
| { kind := some k1, argPats := none, .. },
  { kind := some k2, .. }                      => k1 == k2
| { kind := some k1, argPats := some ps1, .. },
  { kind := some k2, argPats := some ps2, .. } => k1 == k2 && ps1.size == ps2.size
| _, _                                         => false

private def getHeadInfo (alt : Alt) : HeadInfo :=
let pat := alt.fst.head!;
let unconditional (rhsFn) := { HeadInfo . rhsFn := rhsFn };
-- variable pattern
if pat.isOfKind `Lean.Parser.Term.id then unconditional $ fun rhs => `(let $pat:id := discr; $rhs)
-- wildcard pattern
else if pat.isOfKind `Lean.Parser.Term.hole then unconditional pure
-- quotation pattern
else if pat.isOfKind `Lean.Parser.Term.stxQuot then
  let quoted := pat.getArg 1;
  if quoted.isAtom then
    -- We assume that atoms are uniquely determined by the node kind and never have to be checked
    unconditional pure
  else match antiquotKind? quoted with
  -- quotation is a single antiquotation
  | some k =>
    -- Antiquotation kinds like `$id:id` influence the parser, but also need to be considered by
    -- match_syntax (but not by quotation terms). For example, `($id:id) and `($e) are not
    -- distinguishable without checking the kind of the node to be captured. Note that some
    -- antiquotations like the latter one for terms do not correspond to any actual node kind
    -- (signified by `k == Name.anonymous`), so we would only check for `Term.id` here.
    --
    -- if stx.isOfKind `Lean.Parser.Term.id then
    --   let id := stx; ...
    -- else
    --   let e := stx; ...
    let kind := if k == Name.anonymous then none else some k;
    let anti := quoted.getArg 1;
    let anti := match_syntax anti with
    | `(($e)) => e
    | _       => anti;
    -- Splices should only appear inside a nullKind node, see next case
    if isAntiquotSplice quoted then unconditional $ fun _ => throwError quoted "unexpected antiquotation splice"
    else if anti.isOfKind `Lean.Parser.Term.id then { kind := kind, rhsFn :=  fun rhs => `(let $anti:id := discr; $rhs) }
    else unconditional $ fun _ => throwError anti ("match_syntax: antiquotation must be variable " ++ toString anti)
  | _ =>
    if isAntiquotSplicePat quoted && quoted.getArgs.size == 1 then
      -- quotation is a single antiquotation splice => bind args array
      let anti := (quoted.getArg 0).getArg 1;
      unconditional $ fun rhs => `(let $anti:term := Syntax.getArgs discr; $rhs)
      -- TODO: support for more complex antiquotation splices
    else
      -- not an antiquotation: match head shape
      let argPats := quoted.getArgs.map $ fun arg => Syntax.node `Lean.Parser.Term.stxQuot #[mkAtom "`(", arg, mkAtom ")"];
      { kind := quoted.getKind, argPats := argPats }
else
  unconditional $ fun _ => throwError pat ("match_syntax: unexpected pattern kind " ++ toString pat)

-- Assuming that the first pattern of the alternative is taken, replace it with patterns (if any) for its
-- child nodes.
-- Ex: `($a + (- $b)) => `($a), `(+), `(- $b)
-- Note: The atom pattern `(+) will be discarded in a later step
private def explodeHeadPat (numArgs : Nat) : HeadInfo × Alt → TermElabM Alt
| (info, (pat::pats, rhs)) => do
    let newPats := match info.argPats with
      | some argPats => argPats.toList
      | none         => List.replicate numArgs $ Unhygienic.run `(_);
    rhs ← info.rhsFn rhs;
    pure (newPats ++ pats, rhs)
| _ => unreachable!

private partial def compileStxMatch (ref : Syntax) : List Syntax → List Alt → TermElabM Syntax
| [],            ([], rhs)::_ => pure rhs  -- nothing left to match
| _,             []           => throwError ref "non-exhaustive 'match_syntax'"
| discr::discrs, alts         => do
  let alts := (alts.map getHeadInfo).zip alts;
  -- Choose a most specific pattern, ie. a minimal element according to `generalizes`.
  -- If there are multiple minimal elements, the choice does not matter.
  let (info, alt) := alts.tail!.foldl (fun (min : HeadInfo × Alt) (alt : HeadInfo × Alt) => if min.1.generalizes alt.1 then alt else min) alts.head!;
  -- introduce pattern matches on the discriminant's children if there are any nested patterns
  newDiscrs ← match info.argPats with
    | some pats => (List.range pats.size).mapM $ fun i => `(Syntax.getArg discr $(quote i))
    | none      => pure [];
  -- collect matching alternatives and explode them
  let yesAlts := alts.filter $ fun (alt : HeadInfo × Alt) => alt.1.generalizes info;
  yesAlts ← yesAlts.mapM $ explodeHeadPat newDiscrs.length;
  -- NOTE: use fresh macro scopes for recursive call so that different `discr`s introduced by the quotations below do not collide
  yes ← withFreshMacroScope $ compileStxMatch (newDiscrs ++ discrs) yesAlts;
  some kind ← pure info.kind
    -- unconditional match step
    | `(let discr := $discr; $yes);
  -- conditional match step
  let noAlts  := (alts.filter $ fun (alt : HeadInfo × Alt) => !info.generalizes alt.1).map Prod.snd;
  no ← withFreshMacroScope $ compileStxMatch (discr::discrs) noAlts;
  cond ← match info.argPats with
  | some pats => `(Syntax.isOfKind discr $(quote kind) && Array.size (Syntax.getArgs discr) == $(quote pats.size))
  | none      => `(Syntax.isOfKind discr $(quote kind));
  `(let discr := $discr; if coe $cond then $yes else $no)
| _, _ => unreachable!

private partial def getPatternVarsAux : Syntax → TermElabM (List Syntax)
| stx@(Syntax.node k args) => do
  if isAntiquot stx then
    let anti := args.get! 1;
    let anti := match_syntax anti with
    | `(($e)) => e
    | _       => anti;
    if anti.isOfKind `Lean.Parser.Term.id then pure [anti]
    else throwError anti ("match_syntax: antiquotation must be variable " ++ toString anti)
  else
    List.join <$> args.toList.mapM getPatternVarsAux
| _ => pure []

-- Get all pattern vars (as Term.id nodes) in `stx`
private partial def getPatternVars (stx : Syntax) : TermElabM (List Syntax) :=
if stx.isOfKind `Lean.Parser.Term.stxQuot then do
  let quoted := stx.getArg 1;
  getPatternVarsAux stx
else if stx.isOfKind `Lean.Parser.Term.id then
  pure [stx]
else pure []

-- Transform alternatives by binding all right-hand sides to outside the match_syntax in order to prevent
-- code duplication during match_syntax compilation
private def letBindRhss (cont : List Alt → TermElabM Syntax) : List Alt → List Alt → TermElabM Syntax
| [],                altsRev' => cont altsRev'.reverse
| (pats, rhs)::alts, altsRev' => do
  vars ← List.join <$> pats.mapM getPatternVars;
  match vars with
  -- no antiquotations => introduce Unit parameter to preserve evaluation order
  | [] => do
    -- NOTE: references binding below
    rhs' ← `(rhs ());
    -- NOTE: new macro scope so that introduced bindings do not collide
    stx ← withFreshMacroScope $ letBindRhss alts ((pats, rhs')::altsRev');
    `(let rhs := fun _ => $rhs; $stx)
  | _ => do
    -- rhs ← `(fun $vars* => $rhs)
    let rhs := Syntax.node `Lean.Parser.Term.fun #[mkAtom "fun", Syntax.node `null vars.toArray, mkAtom "=>", rhs];
    rhs' ← `(rhs);
    stx ← withFreshMacroScope $ letBindRhss alts ((pats, rhs')::altsRev');
    `(let rhs := $rhs; $stx)

def match_syntax.expand (stx : Syntax) : TermElabM Syntax := do
let discr := stx.getArg 1;
let alts := stx.getArg 3;
alts ← alts.getArgs.mapM $ fun alt => do {
  let pats := alt.getArg 1;
  pat ← if pats.getArgs.size == 1 then pure $ pats.getArg 0
    else throwError stx "match_syntax: expected exactly one pattern per alternative";
  let pat := if pat.isOfKind `Lean.Parser.Term.stxQuot then pat.setArg 1 $ elimAntiquotChoices $ pat.getArg 1 else pat;
  let rhs := alt.getArg 3;
  pure ([pat], rhs)
};
-- letBindRhss (compileStxMatch stx [discr]) alts.toList []
compileStxMatch stx [discr] alts.toList

@[builtinTermElab «match_syntax»] def elabMatchSyntax : TermElab :=
adaptExpander match_syntax.expand

-- REMOVE with old frontend
private def exprPlaceholder := mkMVar Name.anonymous

private unsafe partial def toPreterm : Syntax → TermElabM Expr
| stx =>
  let args := stx.getArgs;
  match stx.getKind with
  | `Lean.Parser.Term.id =>
    match args.get! 0 with
    | Syntax.ident _ _ val preresolved => do
      resolved ← resolveName stx val preresolved [];
      match resolved with
      | (pre,projs)::_ =>
        let pre := match pre with
        | Expr.const c _ _ => Lean.mkConst c  -- remove universes confusing the old frontend
        | _ => pre;
        pure $ projs.foldl (fun e proj => mkMData (MData.empty.setName `fieldNotation proj) e) pre
      | [] => unreachable!
    | _ => unreachable!
  | `Lean.Parser.Term.fun => do
    let params := (args.get! 1).getArgs;
    let body := args.get! 3;
    if params.size == 0 then toPreterm body
    else do
      let param := params.get! 0;
      (n, ty) ← if param.isOfKind `Lean.Parser.Term.id then
          pure (param.getIdAt 0, exprPlaceholder)
        else if param.isOfKind `Lean.Parser.Term.hole then
          pure (`_a, exprPlaceholder)
        else do {
          let n := ((param.getArg 1).getArg 0).getIdAt 0;
          ty ← toPreterm $ (((param.getArg 1).getArg 1).getArg 0).getArg 1;
          pure (n, ty)
        };
      lctx ← getLCtx;
      let lctx := lctx.mkLocalDecl n n ty;
      let params := params.eraseIdx 0;
      stx ← `(fun $params* => $body);
      adaptReader (fun (ctx : Context) => { lctx := lctx, .. ctx }) $ do
        e ← toPreterm stx;
        pure $ lctx.mkLambda #[mkFVar n] e
  | `Lean.Parser.Term.let => do
    let ⟨n, val⟩ := show Name × Syntax from match (args.get! 1).getKind with
      | `Lean.Parser.Term.letIdDecl  => ((args.get! 1).getIdAt 0, (args.get! 1).getArg 4)
      | `Lean.Parser.Term.letPatDecl => (((args.get! 1).getArg 0).getIdAt 0, (args.get! 1).getArg 3)
      | _                            => unreachable!;
    val ← toPreterm val;
    lctx ← getLCtx;
    let lctx := lctx.mkLetDecl n n exprPlaceholder val;
    adaptReader (fun (ctx : Context) => { lctx := lctx, .. ctx }) $ do
      e ← toPreterm $ args.get! 3;
      pure $ lctx.mkLambda #[mkFVar n] e
  | `Lean.Parser.Term.app => do
    fn ← toPreterm $ args.get! 0;
    arg ← toPreterm $ args.get! 1;
    pure $ mkApp fn arg
  | `Lean.Parser.Term.if => do
    let con := args.get! 2;
    let yes := args.get! 4;
    let no := args.get! 6;
    toPreterm $ Unhygienic.run `(ite $con $yes $no)
  | `Lean.Parser.Term.paren =>
    let inner := (args.get! 1).getArgs;
    if inner.size == 0 then pure $ Lean.mkConst `Unit.unit
    else toPreterm $ inner.get! 0
  | `Lean.Parser.Term.band =>
    let lhs := args.get! 0; let rhs := args.get! 2;
    toPreterm $ Unhygienic.run `(and $lhs $rhs)
  | `Lean.Parser.Term.beq =>
    let lhs := args.get! 0; let rhs := args.get! 2;
    toPreterm $ Unhygienic.run `(HasBeq.beq $lhs $rhs)
  | `Lean.Parser.Term.str => pure $ mkStrLit $ (stx.getArg 0).isStrLit?.getD ""
  | `Lean.Parser.Term.num => pure $ mkNatLit $ (stx.getArg 0).isNatLit?.getD 0
  | `expr => pure $ unsafeCast $ stx.getArg 0  -- HACK: see below
  | k => throwError stx $ "stxQuot: unimplemented kind " ++ toString k

@[export lean_parse_expr]
def oldParseExpr (env : Environment) (input : String) (pos : String.Pos) : Except String (Syntax × String.Pos) := do
let c := Parser.mkParserContext env (Parser.mkInputContext input "<foo>");
let s := Parser.mkParserState c.input;
let s := s.setPos pos;
let s := (Parser.termParser Parser.appPrec : Parser.Parser).fn Parser.appPrec c s;
let stx := s.stxStack.back;
match s.errorMsg with
| some errorMsg =>
  Except.error $ toString errorMsg
| none =>
  Except.ok (stx, s.pos)

structure OldContext :=
(env : Environment)
(locals : List Name)
(open_nss : List Name)

private def oldRunTermElabM {α} (ctx : OldContext) (x : TermElabM α) : Except String α := do
match x {fileName := "foo", fileMap := FileMap.ofString "", cmdPos := 0,
  currNamespace := ctx.env.getNamespace, currRecDepth := 0, maxRecDepth := 10000,
  openDecls := ctx.open_nss.map $ fun n => OpenDecl.simple n [],
  lctx := ctx.locals.foldl (fun lctx l => LocalContext.mkLocalDecl lctx l l exprPlaceholder) $ LocalContext.mkEmpty ()}
  {env := ctx.env} with
| EStateM.Result.ok a _      => Except.ok a
| EStateM.Result.error msg _ => Except.error $ toString msg

@[export lean_expand_stx_quot]
unsafe def oldExpandStxQuot (ctx : OldContext) (stx : Syntax) : Except String Expr := oldRunTermElabM ctx $ do
stx ← stxQuot.expand stx;
toPreterm stx

@[export lean_get_antiquot_vars]
def oldGetPatternVars (ctx : OldContext) (pats : List Syntax) : Except String (List Name) := oldRunTermElabM ctx $ do
vars ← List.join <$> pats.mapM getPatternVars;
pure $ vars.map $ fun var => var.getIdAt 0

@[export lean_expand_match_syntax]
unsafe def oldExpandMatchSyntax (ctx : OldContext) (discr : Syntax) (alts : List (List Syntax × Syntax)) : Except String Expr := oldRunTermElabM ctx $ do
-- HACK: discr and the RHSs are actually `Expr`
let discr := Syntax.node `expr #[discr];
let alts := alts.map $ fun alt =>
  let pats := alt.1.map elimAntiquotChoices;
  (pats, Syntax.node `expr #[alt.2]);
-- letBindRhss (compileStxMatch Syntax.missing [discr]) alts []
stx ← compileStxMatch Syntax.missing [discr] alts;
toPreterm stx

end Term
end Elab
end Lean
