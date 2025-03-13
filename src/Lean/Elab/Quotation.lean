/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Elaboration of syntax quotations as terms and patterns (in `match_syntax`). See also `./Hygiene.lean` for the basic
hygiene workings and data types. -/
prelude
import Lean.Syntax
import Lean.ResolveName
import Lean.Elab.Term
import Lean.Elab.Quotation.Util
import Lean.Elab.Quotation.Precheck
import Lean.Elab.Syntax
import Lean.Parser.Syntax

namespace Lean.Elab.Term.Quotation
open Lean.Parser.Term
open Lean.Syntax
open Meta
open TSyntax.Compat

-- TODO(gabriel): We heavily use `have` here to keep the local context clean.
-- We should replace this by non-dependent lets in the future.

/-- `C[$(e)]` ~> `let a := e; C[$a]`. Used in the implementation of antiquot splices. -/
private partial def floatOutAntiquotTerms (stx : Syntax) : StateT (Syntax → TermElabM Syntax) TermElabM Syntax :=
  if isAntiquots stx && !isEscapedAntiquot (getCanonicalAntiquot stx) then
    let e := getAntiquotTerm (getCanonicalAntiquot stx)
    if !e.isIdent || !e.getId.isAtomic then
      withFreshMacroScope do
        let a ← `(__stx_lift)
        modify (fun _ (stx : Syntax) => (`(let $a:ident := $e; $stx) : TermElabM Syntax))
        let stx := if stx.isOfKind choiceKind then
            mkNullNode <| stx.getArgs.map (·.setArg 2 a)
          else
            stx.setArg 2 a
        return stx
    else
      return stx
  else if let Syntax.node i k args := stx then
    return Syntax.node i k (← args.mapM floatOutAntiquotTerms)
  else
    return stx

private def getSepFromSplice (splice : Syntax) : String :=
  if let Syntax.atom _ sep := getAntiquotSpliceSuffix splice then
    sep.dropRight 1 -- drop trailing *
  else
    unreachable!

private def getSepStxFromSplice (splice : Syntax) : Syntax := Unhygienic.run do
  match getSepFromSplice splice with
  | "" => `(mkNullNode) -- sepByIdent uses the null node for separator-less enumerations
  | sep => `(mkAtom $(Syntax.mkStrLit sep))

partial def mkTuple : Array Syntax → TermElabM Syntax
  | #[]  => `(Unit.unit)
  | #[e] => return e
  | es   => do
    let stx ← mkTuple (es.eraseIdxIfInBounds 0)
    `(Prod.mk $(es[0]!) $stx)

def resolveSectionVariable (sectionVars : NameMap Name) (id : Name) : List (Name × List String) :=
  -- decode macro scopes from name before recursion
  let extractionResult := extractMacroScopes id
  let rec loop : Name → List String → List (Name × List String)
    | id@(.str p s), projs =>
      -- NOTE: we assume that macro scopes always belong to the projected constant, not the projections
      let id := { extractionResult with name := id }.review
      match sectionVars.find? id with
      | some newId => [(newId, projs)]
      | none       => loop p (s::projs)
    | _, _ => []
  loop extractionResult.name []

/-- Transform sequence of pushes and appends into acceptable code -/
def ArrayStxBuilder := Sum (Array Term) Term

namespace ArrayStxBuilder

def empty : ArrayStxBuilder := .inl #[]

def build : ArrayStxBuilder → Term
  | .inl elems => quote elems
  | .inr arr   => arr

def push (b : ArrayStxBuilder) (elem : Syntax) : ArrayStxBuilder :=
  match b with
  | .inl elems => .inl <| elems.push elem
  | .inr arr   => .inr <| mkCApp ``Array.push #[arr, elem]

def append (b : ArrayStxBuilder) (arr : Syntax) (appendName := ``Array.append) : ArrayStxBuilder :=
  .inr <| mkCApp appendName #[b.build, arr]

def mkNode (b : ArrayStxBuilder) (k : SyntaxNodeKind) : TermElabM Term := do
  let k := quote k
  match b with
  | .inl #[a₁] => `(Syntax.node1 info $(k) $(a₁))
  | .inl #[a₁, a₂] => `(Syntax.node2 info $(k) $(a₁) $(a₂))
  | .inl #[a₁, a₂, a₃] => `(Syntax.node3 info $(k) $(a₁) $(a₂) $(a₃))
  | .inl #[a₁, a₂, a₃, a₄] => `(Syntax.node4 info $(k) $(a₁) $(a₂) $(a₃) $(a₄))
  | .inl #[a₁, a₂, a₃, a₄, a₅] => `(Syntax.node5 info $(k) $(a₁) $(a₂) $(a₃) $(a₄) $(a₅))
  | .inl #[a₁, a₂, a₃, a₄, a₅, a₆] => `(Syntax.node6 info $(k) $(a₁) $(a₂) $(a₃) $(a₄) $(a₅) $(a₆))
  | .inl #[a₁, a₂, a₃, a₄, a₅, a₆, a₇] => `(Syntax.node7 info $(k) $(a₁) $(a₂) $(a₃) $(a₄) $(a₅) $(a₆) $(a₇))
  | .inl #[a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈] => `(Syntax.node8 info $(k) $(a₁) $(a₂) $(a₃) $(a₄) $(a₅) $(a₆) $(a₇) $(a₈))
  | _ => `(Syntax.node info $(k) $(b.build))

end ArrayStxBuilder

def tryAddSyntaxNodeKindInfo (stx : Syntax) (k : SyntaxNodeKind) : TermElabM Unit := do
  if (← getEnv).contains k then
    addTermInfo' stx (← mkConstWithFreshMVarLevels k)
  else
    -- HACK to support built in categories, which use a different naming convention
    let k := ``Lean.Parser.Category ++ k
    if (← getEnv).contains k then
      addTermInfo' stx (← mkConstWithFreshMVarLevels k)

instance : Quote Syntax.Preresolved where
  quote
    | .namespace ns => Unhygienic.run ``(Syntax.Preresolved.namespace $(quote ns))
    | .decl n fs    => Unhygienic.run ``(Syntax.Preresolved.decl $(quote n) $(quote fs))

/-- Elaborate the content of a syntax quotation term -/
private partial def quoteSyntax : Syntax → TermElabM Term
  | Syntax.ident _ rawVal val preresolved => do
    if !hygiene.get (← getOptions) then
      return ← `(Syntax.ident info $(quote rawVal) $(quote val) $(quote preresolved))
    -- Add global scopes at compilation time (now), add macro scope at runtime (in the quotation).
    -- See the paper for details.
    let consts ← resolveGlobalName val
    -- extension of the paper algorithm: also store unique section variable names as top-level scopes
    -- so they can be captured and used inside the section, but not outside
    let sectionVars := resolveSectionVariable (← read).sectionVars val
    -- extension of the paper algorithm: resolve namespaces as well
    let namespaces ← resolveNamespaceCore (allowEmpty := true) val
    let preresolved := (consts ++ sectionVars).map (fun (n, projs) => Preresolved.decl n projs) ++
      namespaces.map .namespace ++
      preresolved
    let val := quote val
    -- `scp` is bound in stxQuot.expand
    `(Syntax.ident info $(quote rawVal) (addMacroScope mainModule $val scp) $(quote preresolved))
  -- if antiquotation, insert contents as-is, else recurse
  | stx@(Syntax.node _ k _) => do
    if let some (k, _) := stx.antiquotKind? then
      if let some name := getAntiquotKindSpec? stx then
        tryAddSyntaxNodeKindInfo name k
    if isAntiquots stx && !isEscapedAntiquot (getCanonicalAntiquot stx) then
      let ks := antiquotKinds stx
      `(@TSyntax.raw $(quote <| ks.map (·.1)) $(getAntiquotTerm (getCanonicalAntiquot stx)))
    else if isTokenAntiquot stx && !isEscapedAntiquot stx then
      match stx[0] with
      | Syntax.atom _ val => `(Syntax.atom (SourceInfo.fromRef $(getAntiquotTerm stx) (canonical := true)) $(quote val))
      | _                 => throwErrorAt stx "expected token"
    else if isAntiquotSuffixSplice stx && !isEscapedAntiquot (getCanonicalAntiquot (getAntiquotSuffixSpliceInner stx)) then
      -- splices must occur in a `many` node
      throwErrorAt stx "unexpected antiquotation splice"
    else if isAntiquotSplice stx && !isEscapedAntiquot stx then
      throwErrorAt stx "unexpected antiquotation splice"
    else
      -- if escaped antiquotation, decrement by one escape level
      let stx := unescapeAntiquot stx
      let mut args := ArrayStxBuilder.empty
      let appendName := if (← getEnv).contains ``Array.append then ``Array.append else ``Array.appendCore
      for arg in stx.getArgs do
        if k == nullKind && isAntiquotSuffixSplice arg && !isEscapedAntiquot (getCanonicalAntiquot (getAntiquotSuffixSpliceInner arg)) then
          let antiquot := getAntiquotSuffixSpliceInner arg
          let ks := antiquotKinds antiquot |>.map (·.1)
          let val := getAntiquotTerm (getCanonicalAntiquot antiquot)
          args := args.append (appendName := appendName) <| ←
            match antiquotSuffixSplice? arg with
            | `optional => `(match Option.map (@TSyntax.raw $(quote ks)) $val:term with
              | some x => Array.empty.push x
              | none   => Array.empty)
            | `many     => `(@TSyntaxArray.raw $(quote ks) $val)
            | `sepBy    =>
              let sep := quote <| getSepFromSplice arg
              `(@TSepArray.elemsAndSeps $(quote ks) $sep $val)
            | k         => throwErrorAt arg "invalid antiquotation suffix splice kind '{k}'"
        else if k == nullKind && isAntiquotSplice arg && !isEscapedAntiquot arg then
          let k := antiquotSpliceKind? arg
          let (arg, bindLets) ← floatOutAntiquotTerms arg |>.run pure
          let inner ← (getAntiquotSpliceContents arg).mapM quoteSyntax
          let ids ← getAntiquotationIds arg
          if ids.isEmpty then
            throwErrorAt stx "antiquotation splice must contain at least one antiquotation"
          let arr ← match k with
            | `optional => `(match $[$ids:ident],* with
                | $[some $ids:ident],* => $(quote inner)
                | $[_%$ids],*          => Array.empty)
            | _ =>
              let arr ← ids[:ids.size - 1].foldrM (fun id arr => `(Array.zip $id:ident $arr)) ids.back!
              `(Array.map (fun $(← mkTuple ids) => $(inner[0]!)) $arr)
          let arr ← if k == `sepBy then
            `(mkSepArray $arr $(getSepStxFromSplice arg))
          else
            pure arr
          let arr ← bindLets arr
          args := args.append (appendName := appendName) arr
        else do
          let arg ← quoteSyntax arg
          args := args.push arg
      args.mkNode k
  | Syntax.atom _ val =>
    `(Syntax.atom info $(quote val))
  | Syntax.missing => throwUnsupportedSyntax

def addNamedQuotInfo (stx : Syntax) (k : SyntaxNodeKind) : TermElabM SyntaxNodeKind := do
  if stx.getNumArgs == 3 && stx[0].isAtom then
    let s := stx[0].getAtomVal
    if s.length > 3 then
      if let (some l, some r) := (stx[0].getPos? true, stx[0].getTailPos? true) then
        -- HACK: The atom is the string "`(foo|", so chop off the edges.
        let name := stx[0].setInfo <| .synthetic ⟨l.1 + 2⟩ ⟨r.1 - 1⟩ (canonical := true)
        tryAddSyntaxNodeKindInfo name k
  pure k

def getQuotKind (stx : Syntax) : TermElabM SyntaxNodeKind := do
  match stx.getKind with
  | ``Parser.Command.quot => addNamedQuotInfo stx `command
  | ``Parser.Term.quot => addNamedQuotInfo stx `term
  | ``Parser.Tactic.quot => addNamedQuotInfo stx `tactic
  | ``Parser.Tactic.quotSeq => addNamedQuotInfo stx `tactic.seq
  | .str kind "quot" => addNamedQuotInfo stx kind
  | ``dynamicQuot =>
    let id := stx[1]
    match (← elabParserName id) with
    | .parser n _ => return n
    | .category c => return c
    | .alias _    => return (← Parser.getSyntaxKindOfParserAlias? id.getId.eraseMacroScopes).get!
  | k => throwError "unexpected quotation kind {k}"

def mkSyntaxQuotation (stx : Syntax) (kind : Name) : TermElabM Syntax := do
  /- Syntax quotations are monadic values depending on the current macro scope. For efficiency, we bind
     the macro scope once for each quotation, then build the syntax tree in a completely pure computation
     depending on this binding. Note that regular function calls do not introduce a new macro scope (i.e.
     we preserve referential transparency), so we can refer to this same `scp` inside `quoteSyntax` by
     including it literally in a syntax quotation. -/
  `(Bind.bind MonadRef.mkInfoFromRefPos (fun info =>
      Bind.bind getCurrMacroScope (fun scp =>
        Bind.bind getMainModule (fun mainModule => Pure.pure (@TSyntax.mk $(quote kind) $stx)))))
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

def stxQuot.expand (stx : Syntax) : TermElabM Syntax := do
  let stx := if stx.getNumArgs == 1 then stx[0] else stx
  let kind ← getQuotKind stx
  let stx ← quoteSyntax stx.getQuotContent
  mkSyntaxQuotation stx kind

macro "elab_stx_quot" kind:ident : command =>
  `(@[builtin_term_elab $kind:ident] def elabQuot : TermElab := adaptExpander stxQuot.expand)

elab_stx_quot Parser.Term.quot
elab_stx_quot Parser.Tactic.quot
elab_stx_quot Parser.Tactic.quotSeq
elab_stx_quot Parser.Term.dynamicQuot
elab_stx_quot Parser.Command.quot

/-! # match -/

/-- an "alternative" of patterns plus right-hand side -/
private abbrev Alt := List Term × Term

/--
  In a single match step, we match the first discriminant against the "head" of the first pattern of the first
  alternative. This datatype describes what kind of check this involves, which helps other patterns decide if
  they are covered by the same check and don't have to be checked again (see also `MatchResult`). -/
inductive HeadCheck where
  /-- match step that always succeeds: _, x, `($x), ... -/
  | unconditional
  /-- match step based on kind and, optionally, arity of discriminant
  If `arity` is given, that number of new discriminants is introduced. `covered` patterns should then introduce the
  same number of new patterns.
  We actually check the arity at run time only in the case of `null` nodes since it should otherwise by implied by
  the node kind.
  without arity: `($x:k)
  with arity: any quotation without an antiquotation head pattern -/
  | shape (k : List SyntaxNodeKind) (arity : Option Nat)
  /-- Match step that succeeds on `null` nodes of arity at least `numPrefix + numSuffix`, introducing discriminants
  for the first `numPrefix` children, one `null` node for those in between, and for the `numSuffix` last children.
  example: `([$x, $xs,*, $y]) is `slice 2 2` -/
  | slice (numPrefix numSuffix : Nat)
  /-- other, complicated match step that will probably only cover identical patterns
  example: antiquotation splices `($[...]*) -/
  | other (pat : Syntax)

open HeadCheck

/-- Describe whether a pattern is covered by a head check (induced by the pattern itself or a different pattern). -/
inductive MatchResult where
  /-- Pattern agrees with head check, remove and transform remaining alternative.
  If `exhaustive` is `false`, *also* include unchanged alternative in the "no" branch. -/
  | covered (f : Alt → TermElabM Alt) (exhaustive : Bool)
  /-- Pattern disagrees with head check, include in "no" branch only -/
  | uncovered
  /-- Pattern is not quite sure yet; include unchanged in both branches -/
  | undecided

instance : Repr MatchResult where
  reprPrec
    | .covered _ e, _ => f!"covered _ {repr e}"
    | .uncovered,   _ => "uncovered"
    | .undecided,   _ => "undecided"

open MatchResult

/-- All necessary information on a pattern head. -/
structure HeadInfo where
  /-- check induced by the pattern -/
  check : HeadCheck
  /-- compute compatibility of pattern with given head check -/
  onMatch (taken : HeadCheck) : MatchResult
  /-- actually run the specified head check, with the discriminant bound to `__discr` -/
  doMatch (yes : (newDiscrs : List Term) → TermElabM Term) (no : TermElabM Term) : TermElabM Term

/-- Adapt alternatives that do not introduce new discriminants in `doMatch`, but are covered by those that do so. -/
private def noOpMatchAdaptPats : HeadCheck → Alt → Alt
  | shape _ (some sz), (pats, rhs) => (List.replicate sz (Unhygienic.run `(_)) ++ pats, rhs)
  | slice p s,         (pats, rhs) => (List.replicate (p + 1 + s) (Unhygienic.run `(_)) ++ pats, rhs)
  | _,                 alt         => alt

private def adaptRhs (fn : Term → TermElabM Term) : Alt → TermElabM Alt
  | (pats, rhs) => return (pats, ← fn rhs)

private partial def getHeadInfo (alt : Alt) : TermElabM HeadInfo :=
  let pat := alt.fst.head!
  let unconditionally rhsFn := pure {
    check := unconditional,
    doMatch := fun yes _ => yes [],
    onMatch := fun taken => covered (adaptRhs rhsFn ∘ noOpMatchAdaptPats taken) (taken matches unconditional)
  }
  -- quotation pattern
  if isQuot pat then do
    let quoted := getQuotContent pat
    if let some (k, _) := quoted.antiquotKind? then
      if let some name := getAntiquotKindSpec? quoted then
        tryAddSyntaxNodeKindInfo name k
    if quoted.isAtom || quoted.isOfKind `patternIgnore then
      -- We assume that atoms are uniquely determined by the node kind and never have to be checked
      unconditionally pure
    else if quoted.isTokenAntiquot then
      unconditionally (`(have $(quoted.getAntiquotTerm) := __discr; $(·)))
    else if isAntiquots quoted && !isEscapedAntiquot (getCanonicalAntiquot quoted) then
      -- quotation contains a single antiquotation
      let (ks, pseudoKinds) := antiquotKinds quoted |>.unzip
      let rhsFn := match getAntiquotTerm (getCanonicalAntiquot quoted) with
        | `(_)         => pure
        | `($id:ident) => fun stx => `(have $id := @TSyntax.mk $(quote ks) __discr; $(stx))
        | anti =>         fun _   => throwErrorAt anti "unsupported antiquotation kind in pattern"
      -- Antiquotation kinds like `$id:ident` influence the parser, but also need to be considered by
      -- `match` (but not by quotation terms). For example, `($id:ident) and `($e) are not
      -- distinguishable without checking the kind of the node to be captured. Note that some
      -- antiquotations like the latter one for terms do not correspond to any actual node kind,
      -- so we would only check for `ident` here.
      --
      -- if stx.isOfKind `ident then
      --   let id := stx; let e := stx; ...
      -- else
      --   let e := stx; ...
      if (getCanonicalAntiquot quoted)[3].isNone || pseudoKinds.all id then unconditionally rhsFn else pure {
        check   := shape ks none,
        onMatch := fun
          | taken@(shape ks' sz) =>
            if ks' == ks then
              covered (adaptRhs rhsFn ∘ noOpMatchAdaptPats taken) (exhaustive := sz.isNone)
            else uncovered
          | _ => undecided,
        doMatch := fun yes no => do
          let cond ← ks.foldlM (fun cond k => `(or $cond (Syntax.isOfKind __discr $(quote k)))) (← `(false))
          `(cond $cond $(← yes []) $(← no)),
      }
    else if isAntiquotSuffixSplice quoted then throwErrorAt quoted "unexpected antiquotation splice"
    else if isAntiquotSplice quoted then throwErrorAt quoted "unexpected antiquotation splice"
    else if quoted.getArgs.size == 1 && isAntiquotSuffixSplice quoted[0] then
      let inner := getAntiquotSuffixSpliceInner quoted[0]
      let ks := antiquotKinds inner |>.map (·.1)
      unconditionally <| match getAntiquotTerm (getCanonicalAntiquot inner) with
        | `(_)         => pure
        | `($id:ident) => fun rhs => match antiquotSuffixSplice? quoted[0] with
          | `optional => `(have $id := Option.map (@TSyntax.mk $(quote ks)) (Syntax.getOptional? __discr); $rhs)
          | `many     => `(have $id := @TSyntaxArray.mk $(quote ks) (Syntax.getArgs __discr); $rhs)
          | `sepBy    => `(have $id := @TSepArray.mk $(quote ks) $(quote <| getSepFromSplice quoted[0]) (Syntax.getArgs __discr); $rhs)
          | k         => throwErrorAt quoted "invalid antiquotation suffix splice kind '{k}'"
        | anti         => fun _   => throwErrorAt anti "unsupported antiquotation kind in pattern"
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
          let nones := mkArray ids.size (← `(none))
          `(let_delayed yes _ $ids* := $yes;
            if __discr.isNone then yes () $[ $nones]*
            else match __discr with
              | `($(mkNullNode contents)) => yes () $[ (some $ids)]*
              | _                         => $no)
        | _ =>
          let mut discrs ← `(Syntax.getArgs __discr)
          if k == `sepBy then
            discrs ← `(Array.getSepElems $discrs)
          let tuple ← mkTuple ids
          let mut yes := yes
          let resId ← match ids with
            | #[id] => pure id
            | _     =>
              for id in ids do
                yes ← `(have $id := tuples.map (fun $tuple => $id); $yes)
              `(tuples)
          let contents := if contents.size == 1
            then contents[0]!
            else mkNullNode contents
          -- We use `no_error_if_unused%` in auxiliary `match`-syntax to avoid spurious error messages,
          -- the outer `match` is checking for unused alternatives
          `(match ($(discrs).mapM fun
                | `($contents) => no_error_if_unused% some $tuple
                | _            => no_error_if_unused% none) with
              | some $resId => $yes
              | none => $no)
    }
    else if let some idx := quoted.getArgs.findIdx? (fun arg => isAntiquotSuffixSplice arg || isAntiquotSplice arg) then do
      /-
        patterns of the form `match __discr, ... with | `(pat_0 ... pat_(idx-1) $[...]* pat_(idx+1) ...), ...`
        transform to
        ```
        if __discr.getNumArgs >= $quoted.getNumArgs - 1 then
          match __discr[0], ..., __discr[idx-1], mkNullNode (__discr.getArgs.extract idx (__discr.getNumArgs - $numSuffix))), ..., __discr[quoted.getNumArgs - 1] with
            | `(pat_0), ... `(pat_(idx-1)), `($[...])*, `(pat_(idx+1)), ...
        ```
      -/
      let numSuffix := quoted.getNumArgs - 1 - idx
      pure {
        check    := slice idx numSuffix
        onMatch  := fun
          | slice p s =>
            if p == idx && s == numSuffix then
              let argPats := quoted.getArgs.mapIdx fun i arg =>
                let arg := if (i : Nat) == idx then mkNullNode #[arg] else arg
                Unhygienic.run `(`($(arg)))
              covered (fun (pats, rhs) => pure (argPats.toList ++ pats, rhs)) (exhaustive := true)
            else uncovered
          | _ => undecided
        doMatch := fun yes no => do
          let prefixDiscrs ← (List.range idx).mapM (`(Syntax.getArg __discr $(quote ·)))
          let sliceDiscr ← `(mkNullNode (__discr.getArgs.extract $(quote idx) (Nat.sub __discr.getNumArgs $(quote numSuffix))))
          let suffixDiscrs ← (List.range numSuffix).mapM fun i =>
            `(Syntax.getArg __discr (Nat.sub __discr.getNumArgs $(quote (numSuffix - i))))
          `(ite (GE.ge __discr.getNumArgs $(quote (quoted.getNumArgs - 1)))
              $(← yes (prefixDiscrs ++ sliceDiscr :: suffixDiscrs))
              $(← no))
      }
    else
      -- not an antiquotation, or an escaped antiquotation: match head shape
      let quoted  := unescapeAntiquot quoted
      let kind := quoted.getKind
      let lit := isLitKind kind
      let argPats := quoted.getArgs.map fun arg => Unhygienic.run `(`($(arg)))
      pure {
        check :=
          -- Atoms are matched only within literals because it would be a waste of time for keywords
          -- such as `if` and `then` and would blow up the generated code.
          -- See also `elabMatchSyntax` docstring below.
          if quoted.isIdent || lit then
            -- NOTE: We could make this case split more precise by refining `HeadCheck`,
            -- but matching on literals is quite rare.
            other quoted
          else
            shape [kind] argPats.size,
        onMatch := fun
          | other stx' =>
            if quoted.isIdent || lit then
              if quoted == stx' then
                covered pure (exhaustive := true)
              else
                uncovered
            else
              undecided
          | shape ks sz =>
            if ks == [kind] && sz == argPats.size then
              covered (fun (pats, rhs) => pure (argPats.toList ++ pats, rhs)) (exhaustive := true)
            else
              uncovered
          | _ => undecided,
        doMatch := fun yes no => do
          let (cond, newDiscrs) ← if lit then
            let cond ← `(Syntax.matchesLit __discr $(quote kind) $(quote (isLit? kind quoted).get!))
            pure (cond, [])
          else
            let cond ← match kind with
            | `null => `(Syntax.matchesNull __discr $(quote argPats.size))
            | `ident => `(Syntax.matchesIdent __discr $(quote quoted.getId))
            | _     => `(Syntax.isOfKind __discr $(quote kind))
            let newDiscrs ← (List.range argPats.size).mapM fun i => `(Syntax.getArg __discr $(quote i))
            pure (cond, newDiscrs)
          `(ite (Eq $cond true) $(← yes newDiscrs) $(← no))
      }
  else match pat with
    | `(_)              => unconditionally pure
    | `($id:ident)      => unconditionally (`(have $id := __discr; $(·)))
    | `($id:ident@$pat) => do
      let info ← getHeadInfo (pat::alt.1.tail!, alt.2)
      return { info with onMatch := fun taken => match info.onMatch taken with
          | covered f exh => covered (fun alt => f alt >>= adaptRhs (`(have $id := __discr; $(·)))) exh
          | r             => r }
    | _               => throwErrorAt pat "match (syntax) : unexpected pattern kind {pat}"

/-- Bind right-hand side to new `let_delayed` decl in order to prevent code duplication -/
private def deduplicate (floatedLetDecls : Array Syntax) : Alt → TermElabM (Array Syntax × Alt)
  -- NOTE: new macro scope so that introduced bindings do not collide
  | (pats, rhs) => do
    if let `($_:ident $[ $_:ident]*) := rhs then
      -- looks simple enough/created by this function, skip
      return (floatedLetDecls, (pats, rhs))
    withFreshMacroScope do
      match (← getPatternsVars pats.toArray) with
      | #[] =>
        -- no antiquotations => introduce Unit parameter to preserve evaluation order
        let rhs' ← `(rhs Unit.unit)
        pure (floatedLetDecls.push (← `(letDecl|rhs _ := $rhs)), (pats, rhs'))
      | vars =>
        let rhs' ← `(rhs $vars*)
        pure (floatedLetDecls.push (← `(letDecl|rhs $vars:ident* := $rhs)), (pats, rhs'))

private partial def compileStxMatch (discrs : List Term) (alts : List Alt) : TermElabM Syntax := do
  trace[Elab.match_syntax] "match {discrs} with {alts}"
  match discrs, alts with
  | [],            ([], rhs)::_ => pure rhs  -- nothing left to match
  | _,             []           =>
   logError "non-exhaustive 'match' (syntax)"
   pure Syntax.missing
  | discr::discrs, alt::alts    => do
    let info ← getHeadInfo alt
    let alts := (info.onMatch info.check, alt) :: (← alts.mapM fun alt =>
      return ((← getHeadInfo alt).onMatch info.check, alt))
    let mut yesAlts           := #[]
    let mut undecidedAlts     := #[]
    let mut nonExhaustiveAlts := #[]
    let mut floatedLetDecls   := #[]
    for (x, alt') in alts do
      let mut alt' := alt'
      trace[Elab.match_syntax.onMatch] "{alt'} ~> {repr x}"
      match x with
      | covered f exh =>
        -- we can only factor out a common check if there are no undecided patterns in between;
        -- otherwise we would change the order of alternatives
        if undecidedAlts.isEmpty then
          yesAlts ← yesAlts.push <$> f (alt'.1.tail!, alt'.2)
          if !exh then
            nonExhaustiveAlts := nonExhaustiveAlts.push alt'
        else
          (floatedLetDecls, alt') ← deduplicate floatedLetDecls alt'
          undecidedAlts := undecidedAlts.push alt'
          nonExhaustiveAlts := nonExhaustiveAlts.push alt'
      | undecided =>
        (floatedLetDecls, alt') ← deduplicate floatedLetDecls alt'
        undecidedAlts := undecidedAlts.push alt'
        nonExhaustiveAlts := nonExhaustiveAlts.push alt'
      | uncovered =>
        nonExhaustiveAlts := nonExhaustiveAlts.push alt'
    let mut stx ← info.doMatch
      (yes := fun newDiscrs => do
        let mut yesAlts := yesAlts
        if !undecidedAlts.isEmpty then
          -- group undecided alternatives in a new default case `| discr2, ... => match discr, discr2, ... with ...`
          let vars ← discrs.mapM fun _ => withFreshMacroScope `(__discr)
          let pats := List.replicate newDiscrs.length (Unhygienic.run `(_)) ++ vars
          let alts ← undecidedAlts.mapM fun alt => `(matchAltExpr| | $(alt.1.toArray),* => no_error_if_unused% $(alt.2))
          let rhs  ← `(match __discr, $[$(vars.toArray):term],* with $alts:matchAlt*)
          yesAlts := yesAlts.push (pats, rhs)
        withFreshMacroScope $ compileStxMatch (newDiscrs ++ discrs) yesAlts.toList)
      (no := withFreshMacroScope $ compileStxMatch (discr::discrs) nonExhaustiveAlts.toList)
    for d in floatedLetDecls do
      stx ← `(let_delayed $d:letDecl; $stx)
    `(have __discr := $discr; $stx)
  | _, _ => unreachable!

abbrev IdxSet := Std.HashSet Nat

private partial def hasNoErrorIfUnused : Syntax → Bool
  | `(no_error_if_unused% $_) => true
  | `(clear% $_; $body) => hasNoErrorIfUnused body
  | _ => false

/--
Given `rhss` the right-hand-sides of a `match`-syntax notation,
We tag them with fresh identifiers `alt_idx`. We use them to detect whether an alternative
has been used or not.
The result is a triple `(altIdxMap, ignoreIfUnused, rhssNew)` where
- `altIdxMap` is a mapping from the `alt_idx` identifiers to right-hand-side indices.
  That is, the map contains the entry `alt_idx ↦ i` if `alt_idx` was used to mark `rhss[i]`.
- `i ∈ ignoreIfUnused` if `rhss[i]` is marked with `no_error_if_unused%`
- `rhssNew` is the updated array of right-hand-sides.
-/
private def markRhss (rhss : Array Term) : TermElabM (NameMap Nat × IdxSet × Array Term) := do
  let mut altIdxMap : NameMap Nat := {}
  let mut ignoreIfUnused : IdxSet := {}
  let mut rhssNew := #[]
  for rhs in rhss do
    if hasNoErrorIfUnused rhs then
      ignoreIfUnused := ignoreIfUnused.insert rhssNew.size
    let (idx, rhs) ← withFreshMacroScope do
      let idx ← `(alt_idx)
      let rhs ← `(alt_idx $rhs)
      return (idx, rhs)
    altIdxMap := altIdxMap.insert idx.getId rhssNew.size
    rhssNew := rhssNew.push rhs
  return (altIdxMap, ignoreIfUnused, rhssNew)

/--
Given the mapping `idxMap` built using `markRhss`, and `stx` the resulting syntax after expanding `match`-syntax,
return the pair `(stxNew, usedSet)`, where `stxNew` is `stx` after removing the `alt_idx` markers in `idxMap`,
and `i ∈ usedSet` if `stx` contains an `alt_idx` s.t. `alt_idx ↦ i` is in `idxMap`.
That is, `usedSet` contains the index of the used match-syntax right-hand-sides.
-/
private partial def findUsedAlts (stx : Syntax) (altIdxMap : NameMap Nat) : TermElabM (Syntax × IdxSet) := do
  go stx |>.run {}
where
  go (stx : Syntax) : StateRefT IdxSet TermElabM Syntax := do
    match stx with
    | `($id:ident $rhs:term) =>
      if let some idx := altIdxMap.find? id.getId then
        modify fun s => s.insert idx
        return rhs
    | _ => pure ()
    match stx with
    | .node info kind cs => return .node info kind (← cs.mapM go)
    | _ => return stx

/--
Check whether `stx` has unused alternatives, and remove the auxiliary `alt_idx` markers from it (see `markRhss`).
The parameter `alts` provides position information for alternatives.
`altIdxMap` and `ignoreIfUnused` are the map and set built using `markRhss`.
-/
private def checkUnusedAlts (stx : Syntax) (alts : Array Syntax) (altIdxMap : NameMap Nat) (ignoreIfUnused : IdxSet) : TermElabM Syntax := do
  let (stx, used) ← findUsedAlts stx altIdxMap
  for h : i in [:alts.size] do
    unless used.contains i || ignoreIfUnused.contains i do
      logErrorAt alts[i] s!"redundant alternative #{i+1}"
  return stx

def match_syntax.expand (stx : Syntax) : TermElabM Syntax := do
  match stx with
  | `(match $[$discrs:term],* with $[|%$alt $[$patss],* => $rhss]*) => do
    if !patss.any (·.any (fun
      | `($_@$pat) => pat.raw.isQuot
      | pat        => pat.raw.isQuot)) then
      -- no quotations => fall back to regular `match`
      throwUnsupportedSyntax
    let (altIdxMap, ignoreIfUnused, rhss) ← markRhss rhss
    -- call `getQuotKind` on all the patterns, which adds
    -- term info for all `(foo| ...)` as a side effect
    patss.forM (·.forM fun ⟨pat⟩ => do if pat.isQuot then _ ← getQuotKind pat)
    let stx ← compileStxMatch discrs.toList (patss.map (·.toList) |>.zip rhss).toList
    let stx ← checkUnusedAlts stx alt altIdxMap ignoreIfUnused
    trace[Elab.match_syntax.result] "{stx}"
    return stx
  | _ => throwUnsupportedSyntax

@[builtin_term_elab «match»] def elabMatchSyntax : TermElab :=
  adaptExpander match_syntax.expand

@[builtin_term_elab noErrorIfUnused] def elabNoErrorIfUnused : TermElab := fun stx expectedType? =>
  match stx with
  | `(no_error_if_unused% $term) => elabTerm term expectedType?
  | _ => throwUnsupportedSyntax

builtin_initialize
  registerTraceClass `Elab.match_syntax
  registerTraceClass `Elab.match_syntax.alt (inherited := true)
  registerTraceClass `Elab.match_syntax.result (inherited := true)
  registerTraceClass `Elab.match_syntax.onMatch

end Lean.Elab.Term.Quotation
