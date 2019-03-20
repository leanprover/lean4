/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Macro expander for the Lean language, using a variant of the [sets of scopes](http://www.cs.utah.edu/plt/scope-sets/) hygiene algorithm.

TODO(Sebastian): document/link to documentation of algorithm

-/
prelude
import init.lean.parser.module
import init.lean.expr

namespace lean
namespace expander
open parser
open parser.combinators
open parser.term
open parser.command

structure transformerConfig extends frontendConfig
-- TODO(Sebastian): the recursion point for `localExpand` probably needs to be stored here

instance transformerConfigCoeFrontendConfig : hasCoe transformerConfig frontendConfig :=
⟨transformerConfig.toFrontendConfig⟩

-- TODO(Sebastian): recursive expansion
@[derive monad monadReader monadExcept]
def transformM := readerT frontendConfig $ exceptT message id
abbrev transformer := syntax → transformM (option syntax)

/-- We allow macros to refuse expansion. This means that nodes can decide whether to act as macros
    or not depending on their contents, allowing them to unfold to some normal form without changing
    the general node kind and shape (and thus view type). -/
def noExpansion : transformM (option syntax) :=
pure none

def error {m : Type → Type} {ρ : Type} [monad m] [monadReader ρ m] [hasLiftT ρ frontendConfig]
  [monadExcept message m] {α : Type}
  (context : option syntax) (text : string) : m α :=
do cfg ← read,
   throw {
     filename := frontendConfig.filename ↑cfg,
     pos := (frontendConfig.fileMap ↑cfg).toPosition $ (context >>= syntax.getPos).getOrElse (default _),
     text := text
   }

/-- Coercion useful for introducing macro-local variables. Use `globId` to refer to global bindings instead. -/
instance coeNameIdent : hasCoe name syntaxIdent :=
⟨λ n, {val := n, rawVal := substring.ofString n.toString}⟩

/-- Create an identifier preresolved against a global binding. Because we cannot use syntax quotations yet,
    which the expander would have preresolved against the global context at macro declaration time,
    we have to do the preresolution manually instead. -/
def globId (n : name) : syntax :=
review identUnivs {
  id :={val := n, rawVal := substring.ofString n.toString, preresolved := [n]},
}

instance coeIdentIdentUnivs : hasCoe syntaxIdent identUnivs.view :=
⟨λ id, {id := id}⟩

instance coeIdentBinderId : hasCoe syntaxIdent binderIdent.view :=
⟨binderIdent.view.id⟩

instance coeBindersExt {α : Type} [hasCoeT α binderIdent.view] : hasCoe (list α) term.bindersExt.view :=
⟨λ ids, {leadingIds := ids.map coe}⟩

instance coeBindersExtBinders : hasCoe term.bindersExt.view term.binders.view :=
⟨term.binders.view.extended⟩

instance coeSimpleBinderBinders : hasCoe term.simpleBinder.view term.binders.view :=
⟨term.binders.view.simple⟩

instance coeBinderBracketedBinder : hasCoe term.binder.view term.bracketedBinder.view :=
⟨λ b, match b with
 | binder.view.bracketed bb := bb
 | binder.view.unbracketed bc := term.bracketedBinder.view.explicit
   {content := explicitBinderContent.view.other bc}⟩

section «notation»
open parser.command.notationSpec

/-- A notation together with a unique node kind. -/
structure notationMacro :=
(kind : syntaxNodeKind)
(nota : notation.view)

/-- Helper state of the loop in `mkNotationTransformer`. -/
structure notationTransformerState :=
(stx : syntax)
-- children of `stx` that have not been consumed yet
(stxArgs : list syntax := [])
-- substitutions for notation variables (reversed)
(substs : list (syntaxIdent × syntax) := [])
-- filled by `binders` transitions, consumed by `scoped` actions
(scoped : option $ term.binders.view := none)

private def popStxArg : stateT notationTransformerState transformM syntax :=
do st ← get,
   match st.stxArgs with
   | arg::args := put {st with stxArgs := args} *> pure arg
   | _         := error st.stx "mkNotationTransformer: unreachable"

def mkNotationTransformer (nota : notationMacro) : transformer :=
λ stx, do
  some {args := stxArgs, ..} ← pure stx.asNode
    | error stx "mkNotationTransformer: unreachable",
  flip stateT.run' {notationTransformerState . stx := stx, stxArgs := stxArgs} $ do
    let spec := nota.nota.spec,
    -- Walk through the notation specification, consuming `stx` args and building up substitutions
    -- for the notation RHS.
    -- Also see `commandParserConfig.registerNotationParser` for the expected structure of `stx`.
    match spec.prefixArg with
    | none     := pure ()
    | some arg := do { stxArg ← popStxArg, modify $ λ st, {st with substs := (arg, stxArg)::st.substs} },
    nota.nota.spec.rules.mfor (λ r : rule.view, do
      match r.symbol with
      | notationSymbol.view.quoted {symbol := some a ..} := popStxArg
      | _ := error stx "mkNotationTransformer: unreachable",
      match r.transition with
      | some (transition.view.binder b) :=
        do { stxArg ← popStxArg, modify $ λ st, {st with scoped := some $ binders.view.extended {leadingIds := [view binderIdent.parser stxArg]}} }
      | some (transition.view.binders b) :=
        do { stxArg ← popStxArg, modify $ λ st, {st with scoped := some $ view term.binders.parser stxArg} }
      | some (transition.view.arg {action := none, id := id}) :=
        do { stxArg ← popStxArg, modify $ λ st, {st with substs := (id, stxArg)::st.substs} }
      | some (transition.view.arg {action := some {kind := actionKind.view.prec _}, id := id}) :=
        do { stxArg ← popStxArg, modify $ λ st, {st with substs := (id, stxArg)::st.substs} }
      | some (transition.view.arg {action := some {kind := actionKind.view.scoped sc}, id := id}) := do
        stxArg ← popStxArg,
        {scoped := some bnders, ..} ← get
          | error stx "mkNotationTransformer: unreachable",
        -- TODO(Sebastian): not correct with multiple binders
        let scLam := review lambda {binders := [sc.id], body := sc.term},
        let lam := review lambda {binders := bnders, body := stxArg},
        let arg := review app {fn := scLam, arg := lam},
        modify $ λ st, {st with substs := (id, arg)::st.substs}
      | none := pure ()
      | _ := error stx "mkNotationTransformer: unimplemented"),
    st ← get,
    -- apply substitutions
    -- HACK: this substitution completely disregards binders on the notation's RHS.
    -- We have discussed switching to a more explicit antiquotation syntax like %%_
    -- that cannot be abstracted over.
    let substs := st.substs.map (λ ⟨id, t⟩, (id.val, t)),
    let t := nota.nota.term.replace $ λ stx, match tryView identUnivs stx with
      | some {id := id, univs := none} := pure $ substs.assoc id.val
      | _                              := pure none,
    pure $ some $ t

def mixfixToNotationSpec (k : mixfix.kind.view) (sym : notationSymbol.view) : transformM notationSpec.view :=
let prec := match sym with
| notationSymbol.view.quoted q := q.prec
/-| _ := none -/ in
-- `notation` allows more syntax after `:` than mixfix commands, so we have to do a small conversion
let precToAction := λ prec, {action.view . kind := actionKind.view.prec prec} in
match k with
| mixfix.kind.view.prefix _ :=
  -- `prefix sym:prec` ~> `notation sym:prec b:prec`
  pure {
    rules := [{
      symbol := sym,
      transition := transition.view.arg {id := `b,
        action := precToAction <$> precedence.view.term <$> prec}}]}
| mixfix.kind.view.postfix _ :=
  -- `postfix tk:prec` ~> `notation a tk:prec`
  pure {
    prefixArg := `a,
    rules := [{symbol := sym}]}
| mixfix.kind.view.infixr _ := do
  -- `infixr tk:prec` ~> `notation a tk:prec b:(prec-1)`
  act ← match prec with
  | some prec := if prec.term.toNat = 0
    then error (review «precedence» prec) "invalid `infixr` declaration, given precedence must greater than zero"
    else pure $ some $ precToAction $ precedenceTerm.view.lit $ precedenceLit.view.num $ number.view.ofNat $ prec.term.toNat - 1
  | none := pure none,
  pure {
    prefixArg := `a,
    rules := [{
      symbol := sym,
      transition := transition.view.arg {id := `b,
        action := act}}]}
| _ :=
  -- `infix/infixl tk:prec` ~> `notation a tk:prec b:prec`
  pure {
    prefixArg := `a,
    rules := [{
      symbol := sym,
      transition := transition.view.arg {id := `b,
        action := precToAction <$> precedence.view.term <$> prec}}]}

def mixfix.transform : transformer :=
λ stx, do
  let v := view mixfix stx,
  let notaSym := match v.symbol with
  | mixfixSymbol.view.quoted q := notationSymbol.view.quoted q
  | mixfixSymbol.view.unquoted u := notationSymbol.view.quoted {symbol := u},
  spec ← mixfixToNotationSpec v.kind notaSym,
  let term := match v.kind with
  | mixfix.kind.view.prefix _ :=
    -- `prefix tk:prec? := e` ~> `notation tk:prec? b:prec? := e b`
    review app {fn := v.term, arg := review identUnivs `b}
  | mixfix.kind.view.postfix _ :=
    -- `postfix tk:prec? := e` ~> `notation tk:prec? b:prec? := e b`
    review app {fn := v.term, arg := review identUnivs `a}
  | _ :=
    review app {fn := review app {fn := v.term, arg := review identUnivs `a}, arg := review identUnivs `b},
  pure $ review «notation» {«local» := v.local, spec := spec, term := term}

def reserveMixfix.transform : transformer :=
λ stx, do
  let v := view reserveMixfix stx,
  spec ← mixfixToNotationSpec v.kind v.symbol,
  pure $ review reserveNotation {spec := spec}

end «notation»

def mkSimpleBinder (id : syntaxIdent) (bi : binderInfo) (type : syntax) : simpleBinder.view :=
let bc : binderContent.view := {ids := [id], type := some {type := type}} in
match bi with
| binderInfo.default := simpleBinder.view.explicit {id := id, type := type}
| binderInfo.implicit := simpleBinder.view.implicit {id := id, type := type}
| binderInfo.strictImplicit := simpleBinder.view.strictImplicit {id := id, type := type}
| binderInfo.instImplicit := simpleBinder.view.instImplicit {id := id, type := type}
| binderInfo.auxDecl := /- should not happen -/
  simpleBinder.view.explicit {id := id, type := type}

def binderIdentToIdent : binderIdent.view → syntaxIdent
| (binderIdent.view.id id)  := id
| (binderIdent.view.hole _) := "a"

def getOptType : option typeSpec.view → syntax
| none     := review hole {}
| (some v) := v.type

def expandBracketedBinder : bracketedBinder.view → transformM (list simpleBinder.view)
-- local notation: should have been handled by caller, erase
| (bracketedBinder.view.explicit {content := explicitBinderContent.view.notation _}) := pure []
| mbb := do
  (bi, bc) ← match mbb with
  | bracketedBinder.view.explicit {content := bc} := pure (match bc with
    | explicitBinderContent.view.other bc := (binderInfo.default, bc)
    | _ := (binderInfo.default, {ids := []})  /- unreachable, see above -/)
  | bracketedBinder.view.implicit {content := bc} := pure (binderInfo.implicit, bc)
  | bracketedBinder.view.strictImplicit {content := bc} := pure (binderInfo.strictImplicit, bc)
  | bracketedBinder.view.instImplicit {content := bc} :=
    pure $ prod.mk binderInfo.instImplicit $ (match bc with
      | instImplicitBinderContent.view.anonymous bca :=
        {ids := ["_inst_"], type := some {type := bca.type}}
      | instImplicitBinderContent.view.named bcn :=
        {ids := [bcn.id], type := some {type := bcn.type}})
  | bracketedBinder.view.anonymousConstructor ctor :=
    error (review anonymousConstructor ctor) "unexpected anonymous constructor",
  let type := getOptType bc.type,
  type ← match bc.default with
  | none := pure type
  | some (binderDefault.view.val bdv) := pure $ mkApp (globId `optParam) [type, bdv.term]
  | some bdv@(binderDefault.view.tac bdt) := match bc.type with
    | none := pure $ mkApp (globId `autoParam) [bdt.term]
    | some _ := error (review binderDefault bdv) "unexpected auto param after type annotation",
  pure $ bc.ids.map (λ bid, mkSimpleBinder (binderIdentToIdent bid) bi type)

/-- Unfold `binders.view.extended` into `binders.view.simple`. -/
def expandBinders (mkBinding : binders.view → syntax → syntax) (bnders : binders.view)
  (body : syntax) : transformM (option syntax) := do
  binders.view.extended extBinders ← pure bnders
    | noExpansion,
  -- build result `r` bottom-up
  let r := body,
  r ← match extBinders.remainder with
  | bindersRemainder.view.mixed brms := brms.mfoldr (λ brm r, match brm with
    -- anonymous constructor binding ~> binding + match
    | mixedBinder.view.bracketed (bracketedBinder.view.anonymousConstructor ctor) :=
      pure $ mkBinding (mkSimpleBinder "x" binderInfo.default (review hole {})) $ review «match» {
        scrutinees := [review identUnivs ↑"x"],
        equations := [{item := {lhs := [review anonymousConstructor ctor], rhs := r}}]
      }
    -- local notation: should have been handled by caller, erase
    | mixedBinder.view.bracketed mbb := do
      bnders ← expandBracketedBinder mbb,
      pure $ bnders.foldr (λ bnder, mkBinding bnder) r
    | mixedBinder.view.id bid := pure $
      mkBinding (mkSimpleBinder (binderIdentToIdent bid) binderInfo.default (review hole {})) r
    ) r
  | _ := pure r,
  let leadingTy := match extBinders.remainder with
  | bindersRemainder.view.type brt := brt.type
  | _ := review hole {},
  let r := extBinders.leadingIds.foldr (λ bid r,
    mkBinding (mkSimpleBinder (binderIdentToIdent bid) binderInfo.default leadingTy) r) r,
  pure r

def bracketedBinders.transform : transformer :=
λ stx, do
  let v := view bracketedBinders stx,
  match v with
  | bracketedBinders.view.simple _ := noExpansion
  | bracketedBinders.view.extended bnders := do
    bnders ← bnders.mmap expandBracketedBinder,
    pure $ review bracketedBinders $ bracketedBinders.view.simple $ list.join bnders

def lambda.transform : transformer :=
λ stx, do
  let v := view lambda stx,
  expandBinders (λ binders body, review lambda {binders := binders, body := body}) v.binders v.body

def pi.transform : transformer :=
λ stx, do
  let v := view pi stx,
  expandBinders (λ binders body, review pi {op := v.op, binders := binders, range := body}) v.binders v.range

def arrow.transform : transformer :=
λ stx, do
  let v := view arrow stx,
  pure $ review pi {
    op := syntax.atom {val := "Π"},
    binders := binders.view.simple $ simpleBinder.view.explicit {id := `a, type := v.dom},
    range := v.range}

def paren.transform : transformer :=
λ stx, do
  let v := view paren stx,
  match v.content with
  | none := pure $ globId `unit.star
  | some {term := t, special := none} := pure t
  | some {term := t, special := parenSpecial.view.tuple tup} :=
    pure $ (t::tup.tail.map sepBy.elem.view.item).foldr1Opt (λ t tup, mkApp (globId `prod.mk) [t, tup])
  | some {term := t, special := parenSpecial.view.typed pst} :=
    pure $ mkApp (globId `typedExpr) [pst.type, t]

def assume.transform : transformer :=
λ stx, do
  let v := view «assume» stx,
  let binders : binders.view := match v.binders with
  | assumeBinders.view.anonymous aba := binders.view.simple $
    -- TODO(Sebastian): unhygienic!
    simpleBinder.view.explicit {id := "this", type := aba.type}
  | assumeBinders.view.binders abb := abb,
  pure $ review lambda {binders := binders, body := v.body}

def if.transform : transformer :=
λ stx, do
  let v := view «if» stx,
  pure $ match v.id with
  | some id := mkApp (globId `dite) [v.prop,
    review lambda {binders := binders.view.simple $ simpleBinder.view.explicit {id := id.id, type := v.prop}, body := v.thenBranch},
    review lambda {binders := binders.view.simple $ simpleBinder.view.explicit {id := id.id, type := mkApp (globId `not) [v.prop]}, body := v.elseBranch}]
  | none := mkApp (globId `ite) [v.prop, v.thenBranch, v.elseBranch]

def let.transform : transformer :=
λ stx, do
  let v := view «let» stx,
  match v.lhs with
  | letLhs.view.id {id := _, binders := [], type := some _} := noExpansion
  | letLhs.view.id lli@{id := _, binders := [], type := none} :=
    pure $ review «let» {v with lhs := letLhs.view.id {lli with type := some {type := review hole {}}}}
  | letLhs.view.id lli@{id := _, binders := _, type := ty} :=
    let bindrs := binders.view.extended {
      leadingIds := [],
      remainder := bindersRemainder.view.mixed $ lli.binders.map mixedBinder.view.bracketed} in
    pure $ review «let» {v with
      lhs := letLhs.view.id {
        id := lli.id,
        binders := [],
        type := some {type := review pi {op := syntax.atom {val := "Π"}, binders := bindrs, range := getOptType ty}}},
      value := review lambda {binders := bindrs, body := v.value}}
  | letLhs.view.pattern llp :=
    pure $ review «match» {
      scrutinees := [v.value],
      equations := [{item := {lhs := [llp], rhs := v.body}}]}

-- move parameters into type
def axiom.transform : transformer :=
λ stx, do
  let v := view «axiom» stx,
  match v with
  | {sig := {params := bracketedBinders.view.extended bindrs, type := type}, ..} := do
    let bindrs := binders.view.extended {
      leadingIds := [],
      remainder := bindersRemainder.view.mixed $ bindrs.map mixedBinder.view.bracketed},
    pure $ review «axiom» {v with sig := {
      params := bracketedBinders.view.simple [],
      type := {type := review pi {op := syntax.atom {val := "Π"}, binders := bindrs, range := type.type}}}}
  | _ := noExpansion

def declaration.transform : transformer :=
λ stx, do
  let v := view «declaration» stx,
  match v.inner with
  | declaration.inner.view.inductive ind@{«class» := some _, ..} :=
    let attrs := v.modifiers.attrs.getOrElse {attrs := []} in
    pure $ review «declaration» {v with
      modifiers := {v.modifiers with attrs := some {attrs with attrs :=
        {item := {name := "class", args := []}} :: attrs.attrs}},
      inner := declaration.inner.view.inductive {ind with «class» := none}
    }
  | declaration.inner.view.structure s@{keyword := structureKw.view.class _, ..} :=
    let attrs := v.modifiers.attrs.getOrElse {attrs := []} in
    pure $ review «declaration» {v with
      modifiers := {v.modifiers with attrs := some {attrs with attrs :=
        {item := {name := "class", args := []}} :: attrs.attrs}},
      inner := declaration.inner.view.structure {s with keyword := structureKw.view.structure}
    }
  | _ := noExpansion

def introRule.transform : transformer :=
λ stx, do
  let v := view «introRule» stx,
  match v.sig with
  | {params := bracketedBinders.view.extended bindrs, type := some type} := do
    let bindrs := binders.view.extended {
      leadingIds := [],
      remainder := bindersRemainder.view.mixed $ bindrs.map mixedBinder.view.bracketed},
    pure $ review «introRule» {v with sig := {
      params := bracketedBinders.view.simple [],
      type := some {type := review pi {op := syntax.atom {val := "Π"}, binders := bindrs,
        range := type.type}}}}
  | _ := noExpansion

/- We expand `variable` into `variables` instead of the other way around since, in theory,
   elaborating multiple variables at the same time makes it possible to omit more information. -/
def variable.transform : transformer :=
λ stx, do
  let v := view «variable» stx,
  pure $ review «variables» {binders := bracketedBinders.view.extended [v.binder]}

@[derive hasView]
def bindingAnnotationUpdate.parser : termParser :=
node! bindingAnnotationUpdate ["dummy"] -- FIXME: bad node! expansion

def variables.transform : transformer :=
λ stx, do
  let v := view «variables» stx,
  match v.binders with
  | bracketedBinders.view.simple _ := noExpansion
  | bracketedBinders.view.extended bnders := do
    bnders ← bnders.mmap $ λ b, match b with
    -- binding annotation update
    | bracketedBinder.view.explicit eb@{content :=
      explicitBinderContent.view.other bc@{ids := ids, type := none, default := none}} :=
      expandBracketedBinder $ bracketedBinder.view.explicit {eb with content :=
        explicitBinderContent.view.other {bc with type := some {type := review bindingAnnotationUpdate {}}}}
    | _ := expandBracketedBinder b,
    pure $ review «variables» {binders := bracketedBinders.view.simple $ list.join bnders}

def level.leading.transform : transformer :=
λ stx, do
  let v := view level.leading stx,
  match v with
  | level.leading.view.paren p := pure p.inner
  | _ := noExpansion

def subtype.transform : transformer :=
λ stx, do
  let v := view term.subtype stx,
  pure $ mkApp (globId `subtype) [review lambda {
    binders := mkSimpleBinder v.id binderInfo.default $ getOptType v.type,
    body := v.prop
  }]

def universes.transform : transformer :=
λ stx, do
  let v := view «universes» stx,
  pure $ syntax.list $ v.ids.map (λ id, review «universe» {id := id})

def sorry.transform : transformer :=
λ stx, pure $ mkApp (globId `sorryAx) [review hole {}, globId `bool.ff]

local attribute [instance] name.hasLtQuick

-- TODO(Sebastian): replace with attribute
def builtinTransformers : rbmap name transformer (<) := rbmap.fromList [
  (mixfix.name, mixfix.transform),
  (reserveMixfix.name, reserveMixfix.transform),
  (bracketedBinders.name, bracketedBinders.transform),
  (lambda.name, lambda.transform),
  (pi.name, pi.transform),
  (arrow.name, arrow.transform),
  (paren.name, paren.transform),
  (assume.name, assume.transform),
  (if.name, if.transform),
  (let.name, let.transform),
  (axiom.name, axiom.transform),
  (declaration.name, declaration.transform),
  (introRule.name, introRule.transform),
  (variable.name, variable.transform),
  (variables.name, variables.transform),
  (level.leading.name, level.leading.transform),
  (term.subtype.name, subtype.transform),
  (universes.name, universes.transform),
  (sorry.name, sorry.transform)
] _

structure expanderState :=
(nextScope : macroScope)

structure expanderConfig extends transformerConfig :=
(transformers : rbmap name transformer (<))

instance expanderConfig.hasLift : hasLift expanderConfig transformerConfig :=
⟨expanderConfig.toTransformerConfig⟩

@[reducible] def expanderM := stateT expanderState $ readerT expanderConfig $ exceptT message id

section
local attribute [reducible] macroScope
def expanderState.new : expanderState := ⟨0⟩
def mkScope : expanderM macroScope :=
do st ← get,
   put {st with nextScope := st.nextScope + 1},
   pure st.nextScope
end

private def expandCore : nat → syntax → expanderM syntax
| 0 stx := error stx "macro expansion limit exceeded"
| (fuel + 1) stx :=
do some n ← pure stx.asNode | pure stx,
   cfg ← read,
   some t ← pure $ cfg.transformers.find n.kind.name
     -- not a macro: recurse
     | syntax.mkNode n.kind <$> n.args.mmap (expandCore fuel),
   sc ← mkScope,
   let n' := syntax.mkNode n.kind $ n.args.map (syntax.flipScopes [sc]),
   some stx' ← stateT.lift $ λ cfg, t n' ↑cfg
     -- no unfolding: recurse
     | syntax.mkNode n.kind <$> n.args.mmap (expandCore fuel),
   -- flip again, expand iteratively
   expandCore fuel $ stx'.flipScopes [sc]

def expand (stx : syntax) : readerT expanderConfig (except message) syntax :=
-- TODO(Sebastian): persist macro scopes across commands/files
prod.fst <$> expandCore 1000 stx expanderState.new

end expander
end lean
