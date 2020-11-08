/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Elaboration of syntax quotations as terms and patterns (in `match_syntax`). See also `./Hygiene.lean` for the basic
hygiene workings and data types.
-/
import Lean.Syntax
import Lean.ResolveName
import Lean.Elab.Term

namespace Lean.Elab.Term.Quotation

open Lean.Syntax (isQuot isAntiquot)
open Meta

-- Antiquotations can be escaped as in `$$x`, which is useful for nesting macros.
def isEscapedAntiquot (stx : Syntax) : Bool :=
  !stx[1].getArgs.isEmpty

def unescapeAntiquot (stx : Syntax) : Syntax :=
  if isAntiquot stx then
    stx.setArg 1 $ mkNullNode stx[1].getArgs.pop
  else
    stx

def getAntiquotTerm (stx : Syntax) : Syntax :=
  let e := stx[2]
  if e.isIdent then e
  else
    -- `e` is from `"(" >> termParser >> ")"`
    e[1]

def antiquotKind? : Syntax → Option SyntaxNodeKind
  | Syntax.node (Name.str k "antiquot" _) args =>
    if args[3].isOfKind `antiquotName then some k
    else
      -- we treat all antiquotations where the kind was left implicit (`$e`) the same (see `elimAntiquotChoices`)
      some Name.anonymous
  | _                                          => none

-- `$e*` is an antiquotation "splice" matching an arbitrary number of syntax nodes
def isAntiquotSplice (stx : Syntax) : Bool :=
  isAntiquot stx && stx[4].getOptional?.isSome

-- If any item of a `many` node is an antiquotation splice, its result should
-- be substituted into the `many` node's children
def isAntiquotSplicePat (stx : Syntax) : Bool :=
  stx.isOfKind nullKind && stx.getArgs.any fun arg => isAntiquotSplice arg && !isEscapedAntiquot arg

/-- A term like `($e) is actually ambiguous: the antiquotation could be of kind `term`,
    or `ident`, or ... . But it shouldn't really matter because antiquotations without
    explicit kinds behave the same at runtime. So we replace `choice` nodes that contain
    at least one implicit antiquotation with that antiquotation. -/
private partial def elimAntiquotChoices : Syntax → Syntax
  | Syntax.node `choice args => match args.find? fun arg => antiquotKind? arg == Name.anonymous with
    | some anti => anti
    | none      => Syntax.node `choice $ args.map elimAntiquotChoices
  | Syntax.node k args       => Syntax.node k $ args.map elimAntiquotChoices
  | stx                      => stx

-- Elaborate the content of a syntax quotation term
private partial def quoteSyntax : Syntax → TermElabM Syntax
  | Syntax.ident info rawVal val preresolved => do
    -- Add global scopes at compilation time (now), add macro scope at runtime (in the quotation).
    -- See the paper for details.
    let r ← resolveGlobalName val
    let preresolved := r ++ preresolved
    let val := quote val
    -- `scp` is bound in stxQuot.expand
    `(Syntax.ident (SourceInfo.mk none none none) $(quote rawVal) (addMacroScope mainModule $val scp) $(quote preresolved))
  -- if antiquotation, insert contents as-is, else recurse
  | stx@(Syntax.node k _) => do
    if isAntiquot stx && !isEscapedAntiquot stx then
      -- splices must occur in a `many` node
      if isAntiquotSplice stx then throwErrorAt stx "unexpected antiquotation splice"
      else pure $ getAntiquotTerm stx
    else
      let empty ← `(Array.empty);
      -- if escaped antiquotation, decrement by one escape level
      let stx := unescapeAntiquot stx
      let args ← stx.getArgs.foldlM (fun args arg =>
        if k == nullKind && isAntiquotSplice arg then
          -- antiquotation splice pattern: inject args array
          `(Array.append $args $(getAntiquotTerm arg))
        else do
          let arg ← quoteSyntax arg;
          `(Array.push $args $arg)) empty
      `(Syntax.node $(quote k) $args)
  | Syntax.atom info val =>
    `(Syntax.atom (SourceInfo.mk none none none) $(quote val))
  | Syntax.missing => unreachable!

def stxQuot.expand (stx : Syntax) : TermElabM Syntax := do
  let quoted := stx[1]
  /- Syntax quotations are monadic values depending on the current macro scope. For efficiency, we bind
     the macro scope once for each quotation, then build the syntax tree in a completely pure computation
     depending on this binding. Note that regular function calls do not introduce a new macro scope (i.e.
     we preserve referential transparency), so we can refer to this same `scp` inside `quoteSyntax` by
     including it literally in a syntax quotation. -/
  -- TODO: simplify to `(do scp ← getCurrMacroScope; pure $(quoteSyntax quoted))
  let stx ← quoteSyntax (elimAntiquotChoices quoted);
  `(Bind.bind getCurrMacroScope (fun scp => Bind.bind getMainModule (fun mainModule => Pure.pure $stx)))
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

@[builtinTermElab Parser.Level.quot] def elabLevelQuot : TermElab := adaptExpander stxQuot.expand
@[builtinTermElab Parser.Term.quot] def elabTermQuot : TermElab := adaptExpander stxQuot.expand
@[builtinTermElab Parser.Term.funBinder.quot] def elabfunBinderQuot : TermElab := adaptExpander stxQuot.expand
@[builtinTermElab Parser.Tactic.quot] def elabTacticQuot : TermElab := adaptExpander stxQuot.expand
@[builtinTermElab Parser.Tactic.quotSeq] def elabTacticQuotSeq : TermElab := adaptExpander stxQuot.expand
@[builtinTermElab Parser.Term.stx.quot] def elabStxQuot : TermElab := adaptExpander stxQuot.expand
@[builtinTermElab Parser.Term.doElem.quot] def elabDoElemQuot : TermElab := adaptExpander stxQuot.expand

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

instance : Inhabited HeadInfo := ⟨{}⟩

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
  let unconditional (rhsFn) := { rhsFn := rhsFn : HeadInfo };
  -- variable pattern
  if pat.isIdent then unconditional $ fun rhs => `(let $pat := discr; $rhs)
  -- wildcard pattern
  else if pat.isOfKind `Lean.Parser.Term.hole then unconditional pure
  -- quotation pattern
  else if isQuot pat then
    let quoted := pat[1]
    if quoted.isAtom then
      -- We assume that atoms are uniquely determined by the node kind and never have to be checked
      unconditional pure
    else if isAntiquot quoted && !isEscapedAntiquot quoted then
      -- quotation contains a single antiquotation
      let k := antiquotKind? quoted;
      -- Antiquotation kinds like `$id:ident` influence the parser, but also need to be considered by
      -- match_syntax (but not by quotation terms). For example, `($id:ident) and `($e) are not
      -- distinguishable without checking the kind of the node to be captured. Note that some
      -- antiquotations like the latter one for terms do not correspond to any actual node kind
      -- (signified by `k == Name.anonymous`), so we would only check for `ident` here.
      --
      -- if stx.isOfKind `ident then
      --   let id := stx; ...
      -- else
      --   let e := stx; ...
      let kind := if k == Name.anonymous then none else k
      let anti := getAntiquotTerm quoted
      -- Splices should only appear inside a nullKind node, see next case
      if isAntiquotSplice quoted then unconditional $ fun _ => throwErrorAt quoted "unexpected antiquotation splice"
      else if anti.isIdent then { kind := kind, rhsFn :=  fun rhs => `(let $anti := discr; $rhs) }
      else unconditional fun _ => throwErrorAt anti ("match_syntax: antiquotation must be variable " ++ toString anti)
    else if isAntiquotSplicePat quoted && quoted.getArgs.size == 1 then
      -- quotation is a single antiquotation splice => bind args array
      let anti := getAntiquotTerm quoted[0]
      unconditional fun rhs => `(let $anti := Syntax.getArgs discr; $rhs)
      -- TODO: support for more complex antiquotation splices
    else
      -- not an antiquotation or escaped antiquotation: match head shape
      let quoted  := unescapeAntiquot quoted
      let argPats := quoted.getArgs.map (pat.setArg 1);
      { kind := quoted.getKind, argPats := argPats }
  else
    unconditional $ fun _ => throwErrorAt pat ("match_syntax: unexpected pattern kind " ++ toString pat)

-- Assuming that the first pattern of the alternative is taken, replace it with patterns (if any) for its
-- child nodes.
-- Ex: `($a + (- $b)) => `($a), `(+), `(- $b)
-- Note: The atom pattern `(+) will be discarded in a later step
private def explodeHeadPat (numArgs : Nat) : HeadInfo × Alt → TermElabM Alt
  | (info, (pat::pats, rhs)) => do
      let newPats := match info.argPats with
        | some argPats => argPats.toList
        | none         => List.replicate numArgs $ Unhygienic.run `(_)
      let rhs ← info.rhsFn rhs
      pure (newPats ++ pats, rhs)
  | _ => unreachable!

private partial def compileStxMatch : List Syntax → List Alt → TermElabM Syntax
  | [],            ([], rhs)::_ => pure rhs  -- nothing left to match
  | _,             []           => throwError "non-exhaustive 'match_syntax'"
  | discr::discrs, alts         => do
    let alts := (alts.map getHeadInfo).zip alts;
    -- Choose a most specific pattern, ie. a minimal element according to `generalizes`.
    -- If there are multiple minimal elements, the choice does not matter.
    let (info, alt) := alts.tail!.foldl (fun (min : HeadInfo × Alt) (alt : HeadInfo × Alt) => if min.1.generalizes alt.1 then alt else min) alts.head!;
    -- introduce pattern matches on the discriminant's children if there are any nested patterns
    let newDiscrs ← match info.argPats with
      | some pats => (List.range pats.size).mapM fun i => `(Syntax.getArg discr $(quote i))
      | none      => pure []
    -- collect matching alternatives and explode them
    let yesAlts := alts.filter fun (alt : HeadInfo × Alt) => alt.1.generalizes info
    let yesAlts ← yesAlts.mapM $ explodeHeadPat newDiscrs.length
    -- NOTE: use fresh macro scopes for recursive call so that different `discr`s introduced by the quotations below do not collide
    let yes ← withFreshMacroScope $ compileStxMatch (newDiscrs ++ discrs) yesAlts
    let some kind ← pure info.kind
      -- unconditional match step
      | `(let discr := $discr; $yes)
    -- conditional match step
    let noAlts  := (alts.filter $ fun (alt : HeadInfo × Alt) => !info.generalizes alt.1).map (·.2)
    let no ← withFreshMacroScope $ compileStxMatch (discr::discrs) noAlts
    let cond ← match info.argPats with
    | some pats => `(Syntax.isOfKind discr $(quote kind) && Array.size (Syntax.getArgs discr) == $(quote pats.size))
    | none      => `(Syntax.isOfKind discr $(quote kind))
    `(let discr := $discr; if $cond = true then $yes else $no)
  | _, _ => unreachable!

private partial def getPatternVarsAux : Syntax → List Syntax
  | stx@(Syntax.node k args) =>
    if isAntiquot stx && !isEscapedAntiquot stx then
      let anti := getAntiquotTerm stx
      if anti.isIdent then [anti]
      else []
    else
      List.join $ args.toList.map getPatternVarsAux
  | _ => []

-- Get all pattern vars (as `Syntax.ident`s) in `stx`
partial def getPatternVars (stx : Syntax) : List Syntax :=
  if isQuot stx then do
    let quoted := stx.getArg 1;
    getPatternVarsAux stx
  else if stx.isIdent then
    [stx]
  else []

-- Transform alternatives by binding all right-hand sides to outside the match_syntax in order to prevent
-- code duplication during match_syntax compilation
private def letBindRhss (cont : List Alt → TermElabM Syntax) : List Alt → List Alt → TermElabM Syntax
  | [],                altsRev' => cont altsRev'.reverse
  | (pats, rhs)::alts, altsRev' => do
    let vars := List.join $ pats.map getPatternVars
    match vars with
    -- no antiquotations => introduce Unit parameter to preserve evaluation order
    | [] =>
      -- NOTE: references binding below
      let rhs' ← `(rhs ())
      -- NOTE: new macro scope so that introduced bindings do not collide
      let stx ← withFreshMacroScope $ letBindRhss cont alts ((pats, rhs')::altsRev')
      `(let rhs := fun _ => $rhs; $stx)
    | _ =>
      -- rhs ← `(fun $vars* => $rhs)
      let rhs := Syntax.node `Lean.Parser.Term.fun #[mkAtom "fun", Syntax.node `null vars.toArray, mkAtom "=>", rhs]
      let rhs' ← `(rhs)
      let stx ← withFreshMacroScope $ letBindRhss cont alts ((pats, rhs')::altsRev')
      `(let rhs := $rhs; $stx)

def match_syntax.expand (stx : Syntax) : TermElabM Syntax := do
  let discr := stx[1]
  let alts  := stx[3][1]
  let alts ← alts.getSepArgs.mapM $ fun alt => do
    let pats := alt.getArg 0;
    let pat ←
      if pats.getArgs.size == 1 then pure pats[0]
      else throwError "match_syntax: expected exactly one pattern per alternative"
    let pat := if isQuot pat then pat.setArg 1 $ elimAntiquotChoices $ pat[1] else pat
    match pat.find? $ fun stx => stx.getKind == choiceKind with
    | some choiceStx => throwErrorAt choiceStx "invalid pattern, nested syntax has multiple interpretations"
    | none           =>
      let rhs := alt.getArg 2
      pure ([pat], rhs)
  -- letBindRhss (compileStxMatch stx [discr]) alts.toList []
  compileStxMatch [discr] alts.toList

@[builtinTermElab «match_syntax»] def elabMatchSyntax : TermElab :=
  adaptExpander match_syntax.expand

end Lean.Elab.Term.Quotation
