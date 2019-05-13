/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Macro Expander for the Lean language, using a variant of the [sets of scopes](http://www.cs.utah.edu/plt/Scope-sets/) hygiene algorithm.

TODO(Sebastian): document/link to documentation of algorithm

-/
prelude
import init.lean.parser.module
import init.lean.expr

namespace Lean
namespace Expander
open Parser
open Parser.Combinators
open Parser.Term
open Parser.command

structure TransformerConfig extends FrontendConfig
-- TODO(Sebastian): the recursion point for `localExpand` probably needs to be stored here

instance transformerConfigCoeFrontendConfig : HasCoe TransformerConfig FrontendConfig :=
⟨TransformerConfig.toFrontendConfig⟩

-- TODO(Sebastian): recursive expansion
@[derive Monad MonadReader MonadExcept]
def TransformM := ReaderT FrontendConfig $ ExceptT Message Id
abbrev transformer := Syntax → TransformM (Option Syntax)

/-- We allow macros to refuse expansion. This means that nodes can decide whether to act as macros
    or not depending on their contents, allowing them to unfold to some normal form without changing
    the general Node kind and shape (and thus View Type). -/
def noExpansion : TransformM (Option Syntax) :=
pure none

def error {m : Type → Type} {ρ : Type} [Monad m] [MonadReader ρ m] [HasLiftT ρ FrontendConfig]
  [MonadExcept Message m] {α : Type}
  (context : Option Syntax) (text : String) : m α :=
do cfg ← read,
   throw {
     filename := FrontendConfig.filename ↑cfg,
     pos := (FrontendConfig.fileMap ↑cfg).toPosition $ (context >>= Syntax.getPos).getOrElse (default _),
     text := text
   }

/-- Coercion useful for introducing macro-local variables. Use `globId` to refer to global bindings instead. -/
instance coeNameIdent : HasCoe Name SyntaxIdent :=
⟨λ n, {val := n, rawVal := Substring.ofString n.toString}⟩

/-- Create an identifier preresolved against a global binding. Because we cannot use Syntax quotations yet,
    which the Expander would have preresolved against the global context at macro declaration time,
    we have to do the preresolution manually instead. -/
def globId (n : Name) : Syntax :=
review identUnivs {
  id :={val := n, rawVal := Substring.ofString n.toString, preresolved := [n]},
}

instance coeIdentIdentUnivs : HasCoe SyntaxIdent identUnivs.View :=
⟨λ id, {id := id}⟩

instance coeIdentBinderId : HasCoe SyntaxIdent binderIdent.View :=
⟨binderIdent.View.id⟩

instance coeIdentsBindersExt {α : Type} [HasCoeT α binderIdent.View] : HasCoe (List α) Term.bindersExt.View :=
⟨λ ids, {leadingIds := ids.map coe}⟩

instance coeBracketedBinderMixedBinder : HasCoe bracketedBinder.View mixedBinder.View :=
⟨mixedBinder.View.bracketed⟩

instance coeMixedBindersBindersExt {α : Type} [HasCoeT α mixedBinder.View] : HasCoe (List α) Term.bindersExt.View :=
⟨λ mbs, {leadingIds := [], remainder := some $ bindersRemainder.View.mixed $ mbs.map coe}⟩

instance coeBindersExtBinders : HasCoe Term.bindersExt.View Term.binders.View :=
⟨Term.binders.View.extended⟩

instance coeSimpleBinderBinders : HasCoe Term.simpleBinder.View Term.binders.View :=
⟨Term.binders.View.simple⟩

instance coeBinderBracketedBinder : HasCoe Term.binder.View Term.bracketedBinder.View :=
⟨λ b, match b with
 | binder.View.bracketed bb := bb
 | binder.View.unbracketed bc := Term.bracketedBinder.View.explicit
   {content := explicitBinderContent.View.other bc}⟩

section «notation»
open Parser.command.NotationSpec

/-- A notation together with a unique Node kind. -/
structure NotationMacro :=
(kind : SyntaxNodeKind)
(nota : notation.View)

/-- Helper State of the loop in `mkNotationTransformer`. -/
structure NotationTransformerState :=
(stx : Syntax)
-- children of `stx` that have not been consumed yet
(stxArgs : List Syntax := [])
-- substitutions for notation variables (reversed)
(substs : List (SyntaxIdent × Syntax) := [])
-- filled by `binders` transitions, consumed by `scoped` actions
(scoped : Option $ Term.binders.View := none)

private def popStxArg : StateT NotationTransformerState TransformM Syntax :=
do st ← get,
   match st.stxArgs with
   | Arg::args := set {st with stxArgs := args} *> pure Arg
   | _         := error st.stx "mkNotationTransformer: unreachable"

def mkNotationTransformer (nota : NotationMacro) : transformer :=
λ stx, do
  some {args := stxArgs, ..} ← pure stx.asNode
    | error stx "mkNotationTransformer: unreachable",
  flip StateT.run' {NotationTransformerState . stx := stx, stxArgs := stxArgs} $ do
    let spec := nota.nota.spec,
    -- Walk through the notation specification, consuming `stx` args and building up substitutions
    -- for the notation RHS.
    -- Also see `CommandParserConfig.registerNotationParser` for the expected structure of `stx`.
    match spec.prefixArg with
    | none     := pure ()
    | some Arg := do { stxArg ← popStxArg, modify $ λ st, {st with substs := (Arg, stxArg)::st.substs} },
    nota.nota.spec.rules.mfor (λ r : rule.View, do
      match r.symbol with
      | notationSymbol.View.quoted {symbol := some a ..} := popStxArg
      | _ := error stx "mkNotationTransformer: unreachable",
      match r.transition with
      | some (transition.View.binder b) :=
        do { stxArg ← popStxArg, modify $ λ st, {st with scoped := some $ binders.View.extended {leadingIds := [view binderIdent.Parser stxArg]}} }
      | some (transition.View.binders b) :=
        do { stxArg ← popStxArg, modify $ λ st, {st with scoped := some $ view Term.binders.Parser stxArg} }
      | some (transition.View.Arg {action := none, id := id}) :=
        do { stxArg ← popStxArg, modify $ λ st, {st with substs := (id, stxArg)::st.substs} }
      | some (transition.View.Arg {action := some {kind := actionKind.View.prec _}, id := id}) :=
        do { stxArg ← popStxArg, modify $ λ st, {st with substs := (id, stxArg)::st.substs} }
      | some (transition.View.Arg {action := some {kind := actionKind.View.scoped sc}, id := id}) := do
        stxArg ← popStxArg,
        {scoped := some bnders, ..} ← get
          | error stx "mkNotationTransformer: unreachable",
        -- TODO(Sebastian): not correct with multiple binders
        let scLam := review lambda {binders := [sc.id], body := sc.Term},
        let lam := review lambda {binders := bnders, body := stxArg},
        let Arg := review app {fn := scLam, Arg := lam},
        modify $ λ st, {st with substs := (id, Arg)::st.substs}
      | none := pure ()
      | _ := error stx "mkNotationTransformer: unimplemented"),
    st ← get,
    -- apply substitutions
    -- HACK: this substitution completely disregards binders on the notation's RHS.
    -- We have discussed switching to a more explicit antiquotation Syntax like %%_
    -- that cannot be abstracted over.
    let substs := st.substs.map (λ ⟨id, t⟩, (id.val, t)),
    let t := nota.nota.Term.replace $ λ stx, match tryView identUnivs stx with
      | some {id := id, univs := none} := pure $ substs.lookup id.val
      | _                              := pure none,
    pure $ some $ t

def mixfixToNotationSpec (k : mixfix.kind.View) (sym : notationSymbol.View) : TransformM NotationSpec.View :=
let prec := match sym with
| notationSymbol.View.quoted q := q.prec
/-| _ := none -/ in
-- `notation` allows more Syntax after `:` than mixfix commands, so we have to do a small conversion
let precToAction := λ prec, {action.View . kind := actionKind.View.prec prec} in
match k with
| mixfix.kind.View.prefix _ :=
  -- `prefix sym:prec` ~> `notation sym:prec b:prec`
  pure {
    rules := [{
      symbol := sym,
      transition := transition.View.Arg {id := `b,
        action := precToAction <$> precedence.View.Term <$> prec}}]}
| mixfix.kind.View.postfix _ :=
  -- `postfix tk:prec` ~> `notation a tk:prec`
  pure {
    prefixArg := `a,
    rules := [{symbol := sym}]}
| mixfix.kind.View.infixr _ := do
  -- `infixr tk:prec` ~> `notation a tk:prec b:(prec-1)`
  act ← match prec with
  | some prec := if prec.Term.toNat = 0
    then error (review «precedence» prec) "invalid `infixr` declaration, given precedence must greater than zero"
    else pure $ some $ precToAction $ precedenceTerm.View.lit $ precedenceLit.View.num $ number.View.ofNat $ prec.Term.toNat - 1
  | none := pure none,
  pure {
    prefixArg := `a,
    rules := [{
      symbol := sym,
      transition := transition.View.Arg {id := `b,
        action := act}}]}
| _ :=
  -- `infix/infixl tk:prec` ~> `notation a tk:prec b:prec`
  pure {
    prefixArg := `a,
    rules := [{
      symbol := sym,
      transition := transition.View.Arg {id := `b,
        action := precToAction <$> precedence.View.Term <$> prec}}]}

def mixfix.transform : transformer :=
λ stx, do
  let v := view mixfix stx,
  let notaSym := match v.symbol with
  | mixfixSymbol.View.quoted q := notationSymbol.View.quoted q
  | mixfixSymbol.View.unquoted u := notationSymbol.View.quoted {symbol := u},
  spec ← mixfixToNotationSpec v.kind notaSym,
  let Term := match v.kind with
  | mixfix.kind.View.prefix _ :=
    -- `prefix tk:prec? := e` ~> `notation tk:prec? b:prec? := e b`
    review app {fn := v.Term, Arg := review identUnivs `b}
  | mixfix.kind.View.postfix _ :=
    -- `postfix tk:prec? := e` ~> `notation tk:prec? b:prec? := e b`
    review app {fn := v.Term, Arg := review identUnivs `a}
  | _ :=
    review app {fn := review app {fn := v.Term, Arg := review identUnivs `a}, Arg := review identUnivs `b},
  pure $ review «notation» {«local» := v.local, spec := spec, Term := Term}

def reserveMixfix.transform : transformer :=
λ stx, do
  let v := view reserveMixfix stx,
  spec ← mixfixToNotationSpec v.kind v.symbol,
  pure $ review reserveNotation {spec := spec}

end «notation»

def mkSimpleBinder (id : SyntaxIdent) (bi : BinderInfo) (type : Syntax) : simpleBinder.View :=
let bc : binderContent.View := {ids := [id], type := some {type := type}} in
match bi with
| BinderInfo.default := simpleBinder.View.explicit {id := id, type := type}
| BinderInfo.implicit := simpleBinder.View.implicit {id := id, type := type}
| BinderInfo.strictImplicit := simpleBinder.View.strictImplicit {id := id, type := type}
| BinderInfo.instImplicit := simpleBinder.View.instImplicit {id := id, type := type}
| BinderInfo.auxDecl := /- should not happen -/
  simpleBinder.View.explicit {id := id, type := type}

def binderIdentToIdent : binderIdent.View → SyntaxIdent
| (binderIdent.View.id id)  := id
| (binderIdent.View.hole _) := "a"

def getOptType : Option typeSpec.View → Syntax
| none     := review hole {}
| (some v) := v.type

def expandBracketedBinder : bracketedBinder.View → TransformM (List simpleBinder.View)
-- local notation: should have been handled by caller, erase
| (bracketedBinder.View.explicit {content := explicitBinderContent.View.notation _}) := pure []
| mbb := do
  (bi, bc) ← match mbb with
  | bracketedBinder.View.explicit {content := bc} := pure (match bc with
    | explicitBinderContent.View.other bc := (BinderInfo.default, bc)
    | _ := (BinderInfo.default, {ids := []})  /- unreachable, see above -/)
  | bracketedBinder.View.implicit {content := bc} := pure (BinderInfo.implicit, bc)
  | bracketedBinder.View.strictImplicit {content := bc} := pure (BinderInfo.strictImplicit, bc)
  | bracketedBinder.View.instImplicit {content := bc} :=
    pure $ Prod.mk BinderInfo.instImplicit $ match bc with
      | instImplicitBinderContent.View.anonymous bca :=
        {ids := ["_inst_"], type := some {type := bca.type}}
      | instImplicitBinderContent.View.named bcn :=
        {ids := [bcn.id], type := some {type := bcn.type}}
  | bracketedBinder.View.anonymousConstructor ctor :=
    error (review anonymousConstructor ctor) "unexpected anonymous Constructor",
  let type := getOptType bc.type,
  type ← match bc.default with
  | none := pure type
  | some (binderDefault.View.val bdv) := pure $ mkApp (globId `optParam) [type, bdv.Term]
  | some bdv@(binderDefault.View.tac bdt) := match bc.type with
    | none := pure $ mkApp (globId `autoParam) [bdt.Term]
    | some _ := error (review binderDefault bdv) "unexpected auto Param after Type annotation",
  pure $ bc.ids.map (λ bid, mkSimpleBinder (binderIdentToIdent bid) bi type)

/-- Unfold `binders.View.extended` into `binders.View.simple`. -/
def expandBinders (mkBinding : binders.View → Syntax → Syntax) (bnders : binders.View)
  (body : Syntax) : TransformM (Option Syntax) := do
  binders.View.extended extBinders ← pure bnders
    | noExpansion,
  -- build Result `r` bottom-up
  let r := body,
  r ← match extBinders.remainder with
  | bindersRemainder.View.mixed brms := brms.mfoldr (λ brm r, match brm with
    -- anonymous Constructor binding ~> binding + match
    | mixedBinder.View.bracketed (bracketedBinder.View.anonymousConstructor ctor) :=
      pure $ mkBinding (mkSimpleBinder "x" BinderInfo.default (review hole {})) $ review «match» {
        scrutinees := [review identUnivs ↑"x"],
        equations := [{item := {lhs := [review anonymousConstructor ctor], rhs := r}}]
      }
    -- local notation: should have been handled by caller, erase
    | mixedBinder.View.bracketed mbb := do
      bnders ← expandBracketedBinder mbb,
      pure $ bnders.foldr (λ bnder, mkBinding bnder) r
    | mixedBinder.View.id bid := pure $
      mkBinding (mkSimpleBinder (binderIdentToIdent bid) BinderInfo.default (review hole {})) r
    ) r
  | _ := pure r,
  let leadingTy := match extBinders.remainder with
  | bindersRemainder.View.type brt := brt.type
  | _ := review hole {},
  let r := extBinders.leadingIds.foldr (λ bid r,
    mkBinding (mkSimpleBinder (binderIdentToIdent bid) BinderInfo.default leadingTy) r) r,
  pure r

def bracketedBinders.transform : transformer :=
λ stx, do
  let v := view bracketedBinders stx,
  match v with
  | bracketedBinders.View.simple _ := noExpansion
  | bracketedBinders.View.extended bnders := do
    bnders ← bnders.mmap expandBracketedBinder,
    pure $ review bracketedBinders $ bracketedBinders.View.simple $ List.join bnders

def lambda.transform : transformer :=
λ stx, do
  let v := view lambda stx,
  expandBinders (λ binders body, review lambda {binders := binders, body := body}) v.binders v.body

def pi.transform : transformer :=
λ stx, do
  let v := view pi stx,
  expandBinders (λ binders body, review pi {op := v.op, binders := binders, range := body}) v.binders v.range

def depArrow.transform : transformer :=
λ stx, do
  let v := view depArrow stx,
  pure $ review pi {
    op := Syntax.atom {val := "Π"},
    binders := binders.View.extended [v.binder],
    range := v.range}

def arrow.transform : transformer :=
λ stx, do
  let v := view arrow stx,
  pure $ review pi {
    op := Syntax.atom {val := "Π"},
    binders := binders.View.simple $ simpleBinder.View.explicit {id := `a, type := v.dom},
    range := v.range}

def paren.transform : transformer :=
λ stx, do
  let v := view paren stx,
  match v.content with
  | none := pure $ globId `Unit.unit
  | some {Term := t, special := none} := pure t
  | some {Term := t, special := parenSpecial.View.tuple tup} :=
    pure $ (t::tup.tail.map SepBy.Elem.View.item).foldr1Opt (λ t tup, mkApp (globId `Prod.mk) [t, tup])
  | some {Term := t, special := parenSpecial.View.typed pst} :=
    pure $ mkApp (globId `typedExpr) [pst.type, t]

def assume.transform : transformer :=
λ stx, do
  let v := view «assume» stx,
  let binders : binders.View := match v.binders with
  | assumeBinders.View.anonymous aba := binders.View.simple $
    -- TODO(Sebastian): unhygienic!
    simpleBinder.View.explicit {id := "this", type := aba.type}
  | assumeBinders.View.binders abb := abb,
  pure $ review lambda {binders := binders, body := v.body}

def if.transform : transformer :=
λ stx, do
  let v := view «if» stx,
  pure $ match v.id with
  | some id := mkApp (globId `dite) [v.prop,
    review lambda {binders := binders.View.simple $ simpleBinder.View.explicit {id := id.id, type := v.prop}, body := v.thenBranch},
    review lambda {binders := binders.View.simple $ simpleBinder.View.explicit {id := id.id, type := mkApp (globId `Not) [v.prop]}, body := v.elseBranch}]
  | none := mkApp (globId `ite) [v.prop, v.thenBranch, v.elseBranch]

def let.transform : transformer :=
λ stx, do
  let v := view «let» stx,
  match v.lhs with
  | letLhs.View.id {id := _, binders := [], type := some _} := noExpansion
  | letLhs.View.id lli@{id := _, binders := [], type := none} :=
    pure $ review «let» {v with lhs := letLhs.View.id {lli with type := some {type := review hole {}}}}
  | letLhs.View.id lli@{id := _, binders := _, type := ty} :=
    let bindrs := binders.View.extended lli.binders in
    pure $ review «let» {v with
      lhs := letLhs.View.id {
        id := lli.id,
        binders := [],
        type := some {type := review pi {op := Syntax.atom {val := "Π"}, binders := bindrs, range := getOptType ty}}},
      value := review lambda {binders := bindrs, body := v.value}}
  | letLhs.View.pattern llp :=
    pure $ review «match» {
      scrutinees := [v.value],
      equations := [{item := {lhs := [llp], rhs := v.body}}]}

-- move parameters into Type
def axiom.transform : transformer :=
λ stx, do
  let v := view «axiom» stx,
  match v with
  | {sig := {params := bracketedBinders.View.extended bindrs, type := type}, ..} := do
    let bindrs := binders.View.extended bindrs,
    pure $ review «axiom» {v with sig := {
      params := bracketedBinders.View.simple [],
      type := {type := review pi {op := Syntax.atom {val := "Π"}, binders := bindrs, range := type.type}}}}
  | _ := noExpansion

def declaration.transform : transformer :=
λ stx, do
  let v := view «declaration» stx,
  match v.inner with
  | declaration.inner.View.inductive ind@{«class» := some _, ..} :=
    let attrs := v.modifiers.attrs.getOrElse {attrs := []} in
    pure $ review «declaration» {v with
      modifiers := {v.modifiers with attrs := some {attrs with attrs :=
        {item := {Name := "class", args := []}} :: attrs.attrs}},
      inner := declaration.inner.View.inductive {ind with «class» := none}
    }
  | declaration.inner.View.structure s@{keyword := structureKw.View.class _, ..} :=
    let attrs := v.modifiers.attrs.getOrElse {attrs := []} in
    pure $ review «declaration» {v with
      modifiers := {v.modifiers with attrs := some {attrs with attrs :=
        {item := {Name := "class", args := []}} :: attrs.attrs}},
      inner := declaration.inner.View.structure {s with keyword := structureKw.View.structure}
    }
  | _ := noExpansion

def introRule.transform : transformer :=
λ stx, do
  let v := view «introRule» stx,
  match v.sig with
  | {params := bracketedBinders.View.extended bindrs, type := some type} := do
    let bindrs := binders.View.extended bindrs,
    pure $ review «introRule» {v with sig := {
      params := bracketedBinders.View.simple [],
      type := some {type := review pi {op := Syntax.atom {val := "Π"}, binders := bindrs,
        range := type.type}}}}
  | _ := noExpansion

/- We expand `variable` into `variables` instead of the other way around since, in theory,
   elaborating multiple variables at the same time makes it possible to omit more information. -/
def variable.transform : transformer :=
λ stx, do
  let v := view «variable» stx,
  pure $ review «variables» {binders := bracketedBinders.View.extended [v.binder]}

@[derive HasView]
def bindingAnnotationUpdate.Parser : termParser :=
node! bindingAnnotationUpdate ["dummy"] -- FIXME: bad node! expansion

def variables.transform : transformer :=
λ stx, do
  let v := view «variables» stx,
  match v.binders with
  | bracketedBinders.View.simple _ := noExpansion
  | bracketedBinders.View.extended bnders := do
    bnders ← bnders.mmap $ λ b, match b with
    -- binding annotation update
    | bracketedBinder.View.explicit eb@{content :=
      explicitBinderContent.View.other bc@{ids := ids, type := none, default := none}} :=
      expandBracketedBinder $ bracketedBinder.View.explicit {eb with content :=
        explicitBinderContent.View.other {bc with type := some {type := review bindingAnnotationUpdate {}}}}
    | _ := expandBracketedBinder b,
    pure $ review «variables» {binders := bracketedBinders.View.simple $ List.join bnders}

def Level.leading.transform : transformer :=
λ stx, do
  let v := view Level.leading stx,
  match v with
  | Level.leading.View.paren p := pure p.inner
  | _ := noExpansion

def Subtype.transform : transformer :=
λ stx, do
  let v := view Term.Subtype stx,
  pure $ mkApp (globId `Subtype) [review lambda {
    binders := mkSimpleBinder v.id BinderInfo.default $ getOptType v.type,
    body := v.prop
  }]

def universes.transform : transformer :=
λ stx, do
  let v := view «universes» stx,
  pure $ Syntax.list $ v.ids.map (λ id, review «universe» {id := id})

def sorry.transform : transformer :=
λ stx, pure $ mkApp (globId `sorryAx) [review hole {}, globId `Bool.false]

-- TODO(Sebastian): replace with attribute
def builtinTransformers : RBMap Name transformer Name.quickLt := RBMap.fromList [
  (mixfix.name, mixfix.transform),
  (reserveMixfix.name, reserveMixfix.transform),
  (bracketedBinders.name, bracketedBinders.transform),
  (lambda.name, lambda.transform),
  (pi.name, pi.transform),
  (depArrow.name, depArrow.transform),
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
  (Level.leading.name, Level.leading.transform),
  (Term.Subtype.name, Subtype.transform),
  (universes.name, universes.transform),
  (sorry.name, sorry.transform)
] _

structure ExpanderState :=
(nextScope : MacroScope)

structure ExpanderConfig extends TransformerConfig :=
(transformers : RBMap Name transformer Name.quickLt)

instance ExpanderConfig.HasLift : HasLift ExpanderConfig TransformerConfig :=
⟨ExpanderConfig.toTransformerConfig⟩

@[reducible] def ExpanderM := StateT ExpanderState $ ReaderT ExpanderConfig $ ExceptT Message Id

section
local attribute [reducible] MacroScope
def ExpanderState.new : ExpanderState := ⟨0⟩
def mkScope : ExpanderM MacroScope :=
do st ← get,
   set {st with nextScope := st.nextScope + 1},
   pure st.nextScope
end

private def expandCore : Nat → Syntax → ExpanderM Syntax
| 0 stx := error stx "macro expansion limit exceeded"
| (fuel + 1) stx :=
do some n ← pure stx.asNode | pure stx,
   cfg ← read,
   some t ← pure $ cfg.transformers.find n.kind.name
     -- not a macro: recurse
     | Syntax.mkNode n.kind <$> n.args.mmap (expandCore fuel),
   sc ← mkScope,
   let n' := Syntax.mkNode n.kind $ n.args.map (Syntax.flipScopes [sc]),
   some stx' ← StateT.lift $ λ cfg, t n' ↑cfg
     -- no unfolding: recurse
     | Syntax.mkNode n.kind <$> n.args.mmap (expandCore fuel),
   -- flip again, expand iteratively
   expandCore fuel $ stx'.flipScopes [sc]

def expand (stx : Syntax) : ReaderT ExpanderConfig (Except Message) Syntax :=
-- TODO(Sebastian): persist macro scopes across commands/files
Prod.fst <$> expandCore 1000 stx ExpanderState.new

end Expander
end Lean
