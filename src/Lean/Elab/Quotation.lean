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
import Lean.Elab.Quotation.Util
import Lean.Parser.Term

namespace Lean.Elab.Term.Quotation
open Lean.Parser.Term
open Lean.Syntax
open Meta

/-- `C[$(e)]` ~> `let a := e; C[$a]`. Used in the implementation of antiquot splices. -/
private partial def floatOutAntiquotTerms : Syntax → StateT (Syntax → TermElabM Syntax) TermElabM Syntax
  | stx@(Syntax.node k args) => do
    if isAntiquot stx && !isEscapedAntiquot stx then
      let e := getAntiquotTerm stx
      if !e.isIdent then
        return ← withFreshMacroScope do
          let a ← `(a)
          modify (fun cont stx => (`(let $a:ident := $e; $stx) : TermElabM _))
          stx.setArg 2 a
    Syntax.node k (← args.mapM floatOutAntiquotTerms)
  | stx => pure stx

private def getSepFromSplice (splice : Syntax) : Syntax := do
  let Syntax.atom _ sep ← getAntiquotSpliceSuffix splice | unreachable!
  Syntax.mkStrLit (sep.dropRight 1)

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
      getAntiquotTerm stx
    else if isAntiquotSuffixSplice stx && !isEscapedAntiquot stx then
      -- splices must occur in a `many` node
      throwErrorAt stx "unexpected antiquotation splice"
    else if isAntiquotSplice stx && !isEscapedAntiquot stx then
      throwErrorAt stx "unexpected antiquotation splice"
    else
      let empty ← `(Array.empty);
      -- if escaped antiquotation, decrement by one escape level
      let stx := unescapeAntiquot stx
      let args ← stx.getArgs.foldlM (fun args arg => do
        if k == nullKind && isAntiquotSuffixSplice arg then
          let antiquot := getAntiquotSuffixSpliceInner arg
          match antiquotSuffixSplice? arg with
          | `optional => `(Array.appendCore $args (match $(getAntiquotTerm antiquot):term with
            | some x => Array.empty.push x
            | none   => Array.empty))
          | `many     => `(Array.appendCore $args $(getAntiquotTerm antiquot))
          | `sepBy    => `(Array.appendCore $args (@SepArray.elemsAndSeps $(getSepFromSplice arg) $(getAntiquotTerm antiquot)))
          | k         => throwErrorAt! arg "invalid antiquotation suffix splice kind '{k}'"
        else if k == nullKind && isAntiquotSplice arg then
          let k := antiquotSpliceKind? arg
          let (arg, bindLets) ← floatOutAntiquotTerms arg |>.run pure
          let inner ← (getAntiquotSpliceContents arg).mapM quoteSyntax
          let arr ← match (← getAntiquotationIds arg) with
            | #[] => throwErrorAt stx "antiquotation splice must contain at least one antiquotation"
            | #[id] => match k with
              | `optional => `(match $id:ident with
                | some $id:ident => $(quote inner)
                | none           => Array.empty)
              | _ => `(Array.map (fun $id => $(inner[0])) $id)
            | #[id1, id2] => match k with
              | `optional => `(match $id1:ident, $id2:ident with
                | some $id1:ident, some $id2:ident => $(quote inner)
                | _                                => Array.empty)
              | _ => `(Array.zipWith $id1 $id2 fun $id1 $id2 => $(inner[0]))
            | _ => throwErrorAt stx "too many antiquotations in antiquotation splice; don't be greedy"
          let arr ←
            if k == `sepBy then
              `(mkSepArray $arr (mkAtom $(getSepFromSplice arg)))
            else arr
          let arr ← bindLets arr
          `(Array.appendCore $args $arr)
        else do
          let arg ← quoteSyntax arg;
          `(Array.push $args $arg)) empty
      `(Syntax.node $(quote k) $args)
  | Syntax.atom info val =>
    `(Syntax.atom (SourceInfo.mk none none none) $(quote val))
  | Syntax.missing => unreachable!

def stxQuot.expand (stx : Syntax) : TermElabM Syntax := do
  /- Syntax quotations are monadic values depending on the current macro scope. For efficiency, we bind
     the macro scope once for each quotation, then build the syntax tree in a completely pure computation
     depending on this binding. Note that regular function calls do not introduce a new macro scope (i.e.
     we preserve referential transparency), so we can refer to this same `scp` inside `quoteSyntax` by
     including it literally in a syntax quotation. -/
  -- TODO: simplify to `(do scp ← getCurrMacroScope; pure $(quoteSyntax quoted))
  let stx ← quoteSyntax stx.getQuotContent;
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

macro "elabStxQuot!" kind:ident : command =>
  `(@[builtinTermElab $kind:ident] def elabQuot : TermElab := adaptExpander stxQuot.expand)

--

elabStxQuot! Parser.Level.quot
elabStxQuot! Parser.Term.quot
elabStxQuot! Parser.Term.funBinder.quot
elabStxQuot! Parser.Term.bracketedBinder.quot
elabStxQuot! Parser.Term.matchDiscr.quot
elabStxQuot! Parser.Tactic.quot
elabStxQuot! Parser.Tactic.quotSeq
elabStxQuot! Parser.Term.stx.quot
elabStxQuot! Parser.Term.prec.quot
elabStxQuot! Parser.Term.attr.quot
elabStxQuot! Parser.Term.prio.quot
elabStxQuot! Parser.Term.doElem.quot
elabStxQuot! Parser.Term.dynamicQuot

/- match -/

-- an "alternative" of patterns plus right-hand side
private abbrev Alt := List Syntax × Syntax

/--
  In a single match step, we match the first discriminant against the "head" of the first pattern of the first
  alternative. This datatype describes what kind of check this involves, which helps other patterns decide if
  they are covered by the same check and don't have to be checked again (see also `MatchResult`). -/
inductive HeadCheck where
  -- match step that always succeeds: _, x, `($x), ...
  | unconditional
  -- match step based on kind and, optionally, arity of discriminant
  -- If `arity` is given, that number of new discriminants is introduced. `covered` patterns should then introduce the
  -- same number of new patterns.
  -- We actually check the arity at run time only in the case of `null` nodes since it should otherwise by implied by
  -- the node kind.
  -- without arity: `($x:k)
  -- with arity: any quotation without an antiquotation head pattern
  | shape (k : SyntaxNodeKind) (arity : Option Nat)
  -- other, complicated match step that will probably only cover identical patterns
  -- example: antiquotation splices `($[...]*)
  | other (pat : Syntax)

open HeadCheck

/-- Describe whether a pattern is covered by a head check (induced by the pattern itself or a different pattern). -/
inductive MatchResult where
  -- Pattern agrees with head check, remove and transform remaining alternative.
  -- If `exhaustive` is `false`, *also* include unchanged alternative in the "no" branch.
  | covered (f : Alt → TermElabM Alt) (exhaustive : Bool)
  -- Pattern disagrees with head check, include in "no" branch only
  | uncovered
  -- Pattern is not quite sure yet; include unchanged in both branches
  | undecided

open MatchResult

/-- All necessary information on a pattern head. -/
structure HeadInfo where
  -- check induced by the pattern
  check : HeadCheck
  -- compute compatibility of pattern with given head check
  onMatch (taken : HeadCheck) : MatchResult
  -- actually run the specified head check, with the discriminant bound to `discr`
  doMatch (yes : (newDiscrs : List Syntax) → TermElabM Syntax) (no : TermElabM Syntax) : TermElabM Syntax

partial def mkTuple : Array Syntax → TermElabM Syntax
  | #[]  => `(Unit.unit)
  | #[e] => e
  | es   => do
    let stx ← mkTuple (es.eraseIdx 0)
    `(Prod.mk $(es[0]) $stx)

/-- Adapt alternatives that do not introduce new discriminants in `doMatch`, but are covered by those that do so. -/
private def noOpMatchAdaptPats : HeadCheck → Alt → Alt
  | shape k (some sz), (pats, rhs) => (List.replicate sz (Unhygienic.run `(_)) ++ pats, rhs)
  | _,                 alt         => alt

private def adaptRhs (fn : Syntax → TermElabM Syntax) : Alt → TermElabM Alt
  | (pats, rhs) => do (pats, ← fn rhs)

private partial def getHeadInfo (alt : Alt) : TermElabM HeadInfo :=
  let pat := alt.fst.head!
  let unconditionally (rhsFn) := pure {
    check := unconditional,
    doMatch := fun yes no => yes [],
    onMatch := fun taken => covered (adaptRhs rhsFn ∘ noOpMatchAdaptPats taken) (match taken with | unconditional => true | _ => false)
  }
  -- quotation pattern
  if isQuot pat then
    let quoted := getQuotContent pat
    if quoted.isAtom then
      -- We assume that atoms are uniquely determined by the node kind and never have to be checked
      unconditionally pure
    else if isAntiquot quoted && !isEscapedAntiquot quoted then
      -- quotation contains a single antiquotation
      let k := antiquotKind? quoted |>.get!
      -- Antiquotation kinds like `$id:ident` influence the parser, but also need to be considered by
      -- `match` (but not by quotation terms). For example, `($id:ident) and `($e) are not
      -- distinguishable without checking the kind of the node to be captured. Note that some
      -- antiquotations like the latter one for terms do not correspond to any actual node kind
      -- (signified by `k == Name.anonymous`), so we would only check for `ident` here.
      --
      -- if stx.isOfKind `ident then
      --   let id := stx; let e := stx; ...
      -- else
      --   let e := stx; ...
      let anti := getAntiquotTerm quoted
      if anti.isIdent then
        let rhsFn := (`(let $anti := discr; $(·)))
        if k == Name.anonymous then unconditionally rhsFn else pure {
          check   := shape k none,
          onMatch := fun
            | taken@(shape k' sz) =>
              if k' == k then
                covered (adaptRhs rhsFn ∘ noOpMatchAdaptPats taken) (exhaustive := sz.isNone)
              else uncovered
            | _ => uncovered,
          doMatch := fun yes no => do `(if Syntax.isOfKind discr $(quote k) then $(← yes []) else $(← no)),
        }
      else throwErrorAt! anti "match_syntax: antiquotation must be variable {anti}"
    else if isAntiquotSuffixSplice quoted then throwErrorAt quoted "unexpected antiquotation splice"
    else if isAntiquotSplice quoted then throwErrorAt quoted "unexpected antiquotation splice"
    else if quoted.getArgs.size == 1 && isAntiquotSuffixSplice quoted[0] then
      let anti := getAntiquotTerm (getAntiquotSuffixSpliceInner quoted[0])
      unconditionally fun rhs => match antiquotSuffixSplice? quoted[0] with
        | `optional => `(let $anti := Syntax.getOptional? discr; $rhs)
        | `many     => `(let $anti := Syntax.getArgs discr; $rhs)
        | `sepBy    => `(let $anti := @SepArray.mk $(getSepFromSplice quoted[0]) (Syntax.getArgs discr); $rhs)
        | k         => throwErrorAt! quoted "invalid antiquotation suffix splice kind '{k}'"
      -- TODO: support for more complex antiquotation splices
    else if quoted.getArgs.size == 1 && isAntiquotSplice quoted[0] then pure {
      check   := other pat,
      onMatch := fun
        | other pat' => if pat' == pat then covered pure (exhaustive := true) else undecided
        | _          => undecided,
      doMatch := fun yes no => do
        let splice := quoted[0]
        let k := antiquotSpliceKind? splice
        let contents := getAntiquotSpliceContents splice
        let ids ← getAntiquotationIds splice
        let yes ← yes []
        let no ← no
        match k with
        | `optional =>
          let mut yesMatch := yes
          for id in ids do
            yesMatch ← `(let $id := some $id; $yesMatch)
          let mut yesNoMatch := yes
          for id in ids do
            yesNoMatch ← `(let $id := none; $yesNoMatch)
          `(if discr.isNone then $yesNoMatch
            else match discr with
              | `($(mkNullNode contents)) => $yesMatch
              | _                         => $no)
        | _ =>
          let mut discrs ← `(Syntax.getArgs discr)
          if k == `sepBy then
            discrs ← `(Array.getSepElems $discrs)
          let tuple ← mkTuple ids
          let mut yes := yes
          let resId ← match ids with
            | #[id] => id
            | _     =>
              for i in [:ids.size] do
                let idx := Syntax.mkLit fieldIdxKind (toString (i + 1));
                yes ← `(let $(ids[i]) := tuples.map (·.$idx:fieldIdx); $yes)
              `(tuples)
          `(match ($(discrs).sequenceMap fun
              | `($(contents[0])) => some $tuple
              | _                 => none) with
            | some $resId => $yes
            | none => $no)
    }
    else
      -- not an antiquotation, or an escaped antiquotation: match head shape
      let quoted  := unescapeAntiquot quoted
      let kind := quoted.getKind
      let argPats := quoted.getArgs.map fun arg => Unhygienic.run `(`($(arg)))
      pure {
        check := shape kind argPats.size,
        onMatch := fun taken =>
          if (match taken with | shape k' sz => k' == kind && sz == argPats.size | _ => false : Bool) then
            covered (fun (pats, rhs) => (argPats.toList ++ pats, rhs)) (exhaustive := true)
          else
            uncovered,
        doMatch := fun yes no => do
          let cond ← match kind with
          | `null => `(and (Syntax.isOfKind discr $(quote kind)) (BEq.beq (Array.size (Syntax.getArgs discr)) $(quote argPats.size)))
          | _     => `(Syntax.isOfKind discr $(quote kind))
          let newDiscrs ← (List.range argPats.size).mapM fun i => `(Syntax.getArg discr $(quote i))
          `(ite (Eq $cond true) $(← yes newDiscrs) $(← no))
      }
  else match pat with
    | `(_)              => unconditionally pure
    | `($id:ident)      => unconditionally (`(let $id := discr; $(·)))
    | `($id:ident@$pat) => do
      let info ← getHeadInfo (pat::alt.1.tail!, alt.2)
      { info with onMatch := fun taken => match info.onMatch taken with
          | covered f exh => covered (fun alt => f alt >>= adaptRhs (`(let $id := discr; $(·)))) exh
          | r             => r }
    | _               => throwErrorAt! pat "match_syntax: unexpected pattern kind {pat}"

private partial def compileStxMatch (discrs : List Syntax) (alts : List Alt) : TermElabM Syntax := do
  trace[Elab.match_syntax]! "match {discrs} with {alts}"
  match discrs, alts with
  | [],            ([], rhs)::_ => pure rhs  -- nothing left to match
  | _,             []           => throwError "non-exhaustive 'match_syntax'"
  | discr::discrs, alt::alts    => do
    let info ← getHeadInfo alt
    let pat  := alt.1.head!
    let alts ← (alt::alts).mapM fun alt => do ((← getHeadInfo alt).onMatch info.check, alt)
    let mut yesAlts           := #[]
    let mut undecidedAlts     := #[]
    let mut nonExhaustiveAlts := #[]
    for alt in alts do match alt with
      | (covered f exh, alt) =>
        -- we can only factor out a common check if there are no undecided patterns in between;
        -- otherwise we would change the order of alternatives
        if undecidedAlts.isEmpty then
          yesAlts ← yesAlts.push <$> f (alt.1.tail!, alt.2)
          if !exh then
            nonExhaustiveAlts := nonExhaustiveAlts.push alt
        else
          undecidedAlts := undecidedAlts.push alt
          nonExhaustiveAlts := nonExhaustiveAlts.push alt
      | (undecided, alt) =>
        undecidedAlts := undecidedAlts.push alt
        nonExhaustiveAlts := nonExhaustiveAlts.push alt
      | (uncovered, alt) =>
        nonExhaustiveAlts := nonExhaustiveAlts.push alt
    let m ← info.doMatch
      (yes := fun newDiscrs => do
        let mut yesAlts := yesAlts
        if !undecidedAlts.isEmpty then
          -- group undecided alternatives in a new default case `| discr2, ... => match discr, discr2, ... with ...`
          let vars ← discrs.mapM fun _ => withFreshMacroScope `(discr)
          let pats := List.replicate newDiscrs.length (Unhygienic.run `(_)) ++ vars
          let alts ← undecidedAlts.mapM fun alt => `(matchAltExpr| | $(alt.1.toArray),* => $(alt.2))
          let rhs  ← `(match discr, $[$(vars.toArray):term],* with $alts:matchAlt*)
          yesAlts := yesAlts.push (pats, rhs)
        withFreshMacroScope $ compileStxMatch (newDiscrs ++ discrs) yesAlts.toList)
      (no := withFreshMacroScope $ compileStxMatch (discr::discrs) nonExhaustiveAlts.toList)
    `(let discr := $discr; $m)
  | _, _ => unreachable!

-- Transform alternatives by binding all right-hand sides to outside the match in order to prevent
-- code duplication during match compilation
private def letBindRhss (cont : List Alt → TermElabM Syntax) : List Alt → List Alt → TermElabM Syntax
  | [],                altsRev' => cont altsRev'.reverse
  | (pats, rhs)::alts, altsRev' => do
    match ← getPatternsVars pats.toArray with
    -- no antiquotations => introduce Unit parameter to preserve evaluation order
    | #[] =>
      -- NOTE: references binding below
      let rhs' ← `(rhs ())
      -- NOTE: new macro scope so that introduced bindings do not collide
      let stx ← withFreshMacroScope $ letBindRhss cont alts ((pats, rhs')::altsRev')
      `(let rhs := fun _ => $rhs; $stx)
    | vars =>
      -- rhs ← `(fun $vars* => $rhs)
      let rhs := Syntax.node `Lean.Parser.Term.fun #[mkAtom "fun", Syntax.node `null vars, mkAtom "=>", rhs]
      let rhs' ← `(rhs)
      let stx ← withFreshMacroScope $ letBindRhss cont alts ((pats, rhs')::altsRev')
      `(let rhs := $rhs; $stx)

def match_syntax.expand (stx : Syntax) : TermElabM Syntax := do
  match stx with
  | `(match $[$discrs:term],* with $[| $[$patss],* => $rhss]*) => do
    -- letBindRhss ...
    if !patss.any (·.any (fun
      | `($id@$pat) => pat.isQuot
      | pat         => pat.isQuot)) then
      -- no quotations => fall back to regular `match`
      throwUnsupportedSyntax
    let stx ← compileStxMatch discrs.toList (patss.map (·.toList) |>.zip rhss).toList
    trace[Elab.match_syntax.result]! "{stx}"
    stx
  | _ => throwUnsupportedSyntax

@[builtinTermElab «match»] def elabMatchSyntax : TermElab :=
  adaptExpander match_syntax.expand

builtin_initialize
  registerTraceClass `Elab.match_syntax
  registerTraceClass `Elab.match_syntax.result

end Lean.Elab.Term.Quotation
