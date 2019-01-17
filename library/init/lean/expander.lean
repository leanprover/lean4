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

structure transformer_config extends frontend_config
-- TODO(Sebastian): the recursion point for `local_expand` probably needs to be stored here

instance transformer_config_coe_frontend_config : has_coe transformer_config frontend_config :=
⟨transformer_config.to_frontend_config⟩

-- TODO(Sebastian): recursive expansion
@[derive monad monad_reader monad_except]
def transform_m := reader_t frontend_config $ except_t message id
abbreviation transformer := syntax → transform_m (option syntax)

/-- We allow macros to refuse expansion. This means that nodes can decide whether to act as macros
    or not depending on their contents, allowing them to unfold to some normal form without changing
    the general node kind and shape (and thus view type). -/
def no_expansion : transform_m (option syntax) :=
pure none

def error {m : Type → Type} {ρ : Type} [monad m] [monad_reader ρ m] [has_lift_t ρ frontend_config]
  [monad_except message m] {α : Type}
  (context : syntax) (text : string) : m α :=
do cfg ← read,
   throw {
     filename := frontend_config.filename ↑cfg,
     pos := (frontend_config.file_map ↑cfg).to_position $ context.get_pos.get_or_else (default _),
     text := text
   }

/-- Coercion useful for introducing macro-local variables. Use `glob_id` to refer to global bindings instead. -/
instance coe_name_ident : has_coe name syntax_ident :=
⟨λ n, {val := n, raw_val := substring.of_string n.to_string}⟩

/-- Create an identifier preresolved against a global binding. Because we cannot use syntax quotations yet,
    which the expander would have preresolved against the global context at macro declaration time,
    we have to do the preresolution manually instead. -/
def glob_id (n : name) : syntax :=
review ident_univs {
  id :={val := n, raw_val := substring.of_string n.to_string, preresolved := [n]},
}

instance coe_ident_ident_univs : has_coe syntax_ident ident_univs.view :=
⟨λ id, {id := id}⟩

instance coe_ident_binder_id : has_coe syntax_ident binder_ident.view :=
⟨binder_ident.view.id⟩

instance coe_binders_ext {α : Type} [has_coe_t α binder_ident.view] : has_coe (list α) term.binders_ext.view :=
⟨λ ids, {leading_ids := ids.map coe}⟩

instance coe_binders_ext_binders : has_coe term.binders_ext.view term.binders.view :=
⟨term.binders.view.extended⟩

instance coe_simple_binder_binders : has_coe term.simple_binder.view term.binders.view :=
⟨term.binders.view.simple⟩

instance coe_binder_bracketed_binder : has_coe term.binder.view term.bracketed_binder.view :=
⟨λ b, match b with
 | binder.view.bracketed bb := bb
 | binder.view.unbracketed bc := term.bracketed_binder.view.explicit
   {content := explicit_binder_content.view.other bc}⟩

section «notation»
open parser.command.notation_spec

/-- A notation together with a unique node kind. -/
structure notation_macro :=
(kind : syntax_node_kind)
(nota : notation.view)

/-- Helper state of the loop in `mk_notation_transformer`. -/
structure notation_transformer_state :=
(stx : syntax)
-- children of `stx` that have not been consumed yet
(stx_args : list syntax := [])
-- substitutions for notation variables (reversed)
(substs : list (syntax_ident × syntax) := [])
-- filled by `binders` transitions, consumed by `scoped` actions
(scoped : option $ term.binders.view := none)

private def pop_stx_arg : state_t notation_transformer_state transform_m syntax :=
do st ← get,
   match st.stx_args with
   | arg::args := put {st with stx_args := args} *> pure arg
   | _         := error st.stx "mk_notation_transformer: unreachable"

def mk_notation_transformer (nota : notation_macro) : transformer :=
λ stx, do
  some {args := stx_args, ..} ← pure stx.as_node
    | error stx "mk_notation_transformer: unreachable",
  flip state_t.run' {notation_transformer_state . stx := stx, stx_args := stx_args} $ do
    let spec := nota.nota.spec,
    -- Walk through the notation specification, consuming `stx` args and building up substitutions
    -- for the notation RHS.
    -- Also see `command_parser_config.register_notation_parser` for the expected structure of `stx`.
    match spec.prefix_arg with
    | none     := pure ()
    | some arg := do { stx_arg ← pop_stx_arg, modify $ λ st, {st with substs := (arg, stx_arg)::st.substs} },
    nota.nota.spec.rules.mfor (λ r : rule.view, do
      match r.symbol with
      | notation_symbol.view.quoted {symbol := some a ..} := pop_stx_arg
      | _ := error stx "mk_notation_transformer: unreachable",
      match r.transition with
      | some (transition.view.binder b) :=
        do { stx_arg ← pop_stx_arg, modify $ λ st, {st with scoped := some $ binders.view.extended {leading_ids := [view binder_ident.parser stx_arg]}} }
      | some (transition.view.binders b) :=
        do { stx_arg ← pop_stx_arg, modify $ λ st, {st with scoped := some $ view term.binders.parser stx_arg} }
      | some (transition.view.arg {action := none, id := id}) :=
        do { stx_arg ← pop_stx_arg, modify $ λ st, {st with substs := (id, stx_arg)::st.substs} }
      | some (transition.view.arg {action := some {kind := action_kind.view.prec _}, id := id}) :=
        do { stx_arg ← pop_stx_arg, modify $ λ st, {st with substs := (id, stx_arg)::st.substs} }
      | some (transition.view.arg {action := some {kind := action_kind.view.scoped sc}, id := id}) := do
        stx_arg ← pop_stx_arg,
        {scoped := some bnders, ..} ← get
          | error stx "mk_notation_transformer: unreachable",
        -- TODO(Sebastian): not correct with multiple binders
        let sc_lam := review lambda {binders := [sc.id], body := sc.term},
        let lam := review lambda {binders := bnders, body := stx_arg},
        let arg := review app {fn := sc_lam, arg := lam},
        modify $ λ st, {st with substs := (id, arg)::st.substs}
      | none := pure ()
      | _ := error stx "mk_notation_transformer: unimplemented"),
    st ← get,
    -- apply substitutions
    -- HACK: this substitution completely disregards binders on the notation's RHS.
    -- We have discussed switching to a more explicit antiquotation syntax like %%_
    -- that cannot be abstracted over.
    let substs := st.substs.map (λ ⟨id, t⟩, (id.val, t)),
    let t := nota.nota.term.replace $ λ stx, match try_view ident_univs stx with
      | some {id := id, univs := none} := pure $ substs.assoc id.val
      | _                              := pure none,
    pure $ some $ t

def mixfix_to_notation_spec (k : mixfix.kind.view) (sym : notation_symbol.view) : transform_m notation_spec.view :=
let prec := match sym with
| notation_symbol.view.quoted q := q.prec
/-| _ := none -/ in
-- `notation` allows more syntax after `:` than mixfix commands, so we have to do a small conversion
let prec_to_action := λ prec, {action.view . kind := action_kind.view.prec prec} in
match k with
| mixfix.kind.view.prefix _ :=
  -- `prefix sym:prec` ~> `notation sym:prec b:prec`
  pure {
    rules := [{
      symbol := sym,
      transition := transition.view.arg {id := `b,
        action := prec_to_action <$> precedence.view.term <$> prec}}]}
| mixfix.kind.view.postfix _ :=
  -- `postfix tk:prec` ~> `notation a tk:prec`
  pure {
    prefix_arg := `a,
    rules := [{symbol := sym}]}
| mixfix.kind.view.infixr _ := do
  -- `infixr tk:prec` ~> `notation a tk:prec b:(prec-1)`
  act ← match prec with
  | some prec := if prec.term.to_nat = 0
    then error (review «precedence» prec) "invalid `infixr` declaration, given precedence must greater than zero"
    else pure $ some $ prec_to_action $ precedence_term.view.lit $ precedence_lit.view.num $ number.view.of_nat $ prec.term.to_nat - 1
  | none := pure none,
  pure {
    prefix_arg := `a,
    rules := [{
      symbol := sym,
      transition := transition.view.arg {id := `b,
        action := act}}]}
| _ :=
  -- `infix/infixl tk:prec` ~> `notation a tk:prec b:prec`
  pure {
    prefix_arg := `a,
    rules := [{
      symbol := sym,
      transition := transition.view.arg {id := `b,
        action := prec_to_action <$> precedence.view.term <$> prec}}]}

def mixfix.transform : transformer :=
λ stx, do
  let v := view mixfix stx,
  let nota_sym := match v.symbol with
  | mixfix_symbol.view.quoted q := notation_symbol.view.quoted q
  | mixfix_symbol.view.unquoted u := notation_symbol.view.quoted {symbol := u},
  spec ← mixfix_to_notation_spec v.kind nota_sym,
  let term := match v.kind with
  | mixfix.kind.view.prefix _ :=
    -- `prefix tk:prec? := e` ~> `notation tk:prec? b:prec? := e b`
    review app {fn := v.term, arg := review ident_univs `b}
  | mixfix.kind.view.postfix _ :=
    -- `postfix tk:prec? := e` ~> `notation tk:prec? b:prec? := e b`
    review app {fn := v.term, arg := review ident_univs `a}
  | _ :=
    review app {fn := review app {fn := v.term, arg := review ident_univs `a}, arg := review ident_univs `b},
  pure $ review «notation» {«local» := v.local, spec := spec, term := term}

def reserve_mixfix.transform : transformer :=
λ stx, do
  let v := view reserve_mixfix stx,
  spec ← mixfix_to_notation_spec v.kind v.symbol,
  pure $ review reserve_notation {spec := spec}

end «notation»

def mk_simple_binder (id : syntax_ident) (bi : binder_info) (type : syntax) : simple_binder.view :=
let bc : binder_content.view := {ids := [id], type := some {type := type}} in
match bi with
| binder_info.default := simple_binder.view.explicit {id := id, type := type}
| binder_info.implicit := simple_binder.view.implicit {id := id, type := type}
| binder_info.strict_implicit := simple_binder.view.strict_implicit {id := id, type := type}
| binder_info.inst_implicit := simple_binder.view.inst_implicit {id := id, type := type}
| binder_info.aux_decl := /- should not happen -/
  simple_binder.view.explicit {id := id, type := type}

def binder_ident_to_ident : binder_ident.view → syntax_ident
| (binder_ident.view.id id)  := id
| (binder_ident.view.hole _) := "a"

def get_opt_type : option type_spec.view → syntax
| none     := review hole {}
| (some v) := v.type

def expand_bracketed_binder : bracketed_binder.view → transform_m (list simple_binder.view)
-- local notation: should have been handled by caller, erase
| (bracketed_binder.view.explicit {content := explicit_binder_content.view.notation _}) := pure []
| mbb := do
  (bi, bc) ← match mbb with
  | bracketed_binder.view.explicit {content := bc} := pure (match bc with
    | explicit_binder_content.view.other bc := (binder_info.default, bc)
    | _ := (binder_info.default, {ids := []})  /- unreachable, see above -/)
  | bracketed_binder.view.implicit {content := bc} := pure (binder_info.implicit, bc)
  | bracketed_binder.view.strict_implicit {content := bc} := pure (binder_info.strict_implicit, bc)
  | bracketed_binder.view.inst_implicit {content := bc} :=
    pure $ prod.mk binder_info.inst_implicit $ (match bc with
      | inst_implicit_binder_content.view.anonymous bca :=
        {ids := ["_inst_"], type := some {type := bca.type}}
      | inst_implicit_binder_content.view.named bcn :=
        {ids := [bcn.id], type := some {type := bcn.type}})
  | bracketed_binder.view.anonymous_constructor ctor :=
    error (review anonymous_constructor ctor) "unexpected anonymous constructor",
  let type := get_opt_type bc.type,
  type ← match bc.default with
  | none := pure type
  | some (binder_default.view.val bdv) := pure $ mk_app (glob_id `opt_param) [type, bdv.term]
  | some bdv@(binder_default.view.tac bdt) := match bc.type with
    | none := pure $ mk_app (glob_id `auto_param) [bdt.term]
    | some _ := error (review binder_default bdv) "unexpected auto param after type annotation",
  pure $ bc.ids.map (λ bid, mk_simple_binder (binder_ident_to_ident bid) bi type)

/-- Unfold `binders.view.extended` into `binders.view.simple`. -/
def expand_binders (mk_binding : binders.view → syntax → syntax) (bnders : binders.view)
  (body : syntax) : transform_m (option syntax) := do
  binders.view.extended ext_binders ← pure bnders
    | no_expansion,
  -- build result `r` bottom-up
  let r := body,
  r ← match ext_binders.remainder with
  | binders_remainder.view.mixed brms := brms.mfoldr (λ brm r, match brm with
    -- anonymous constructor binding ~> binding + match
    | mixed_binder.view.bracketed (bracketed_binder.view.anonymous_constructor ctor) :=
      pure $ mk_binding (mk_simple_binder "x" binder_info.default (review hole {})) $ review «match» {
        scrutinees := [syntax.ident "x"],
        equations := [{item := {lhs := [review anonymous_constructor ctor], rhs := r}}]
      }
    -- local notation: should have been handled by caller, erase
    | mixed_binder.view.bracketed mbb := do
      bnders ← expand_bracketed_binder mbb,
      pure $ bnders.foldr (λ bnder, mk_binding bnder) r
    | mixed_binder.view.id bid := pure $
      mk_binding (mk_simple_binder (binder_ident_to_ident bid) binder_info.default (review hole {})) r
    ) r
  | _ := pure r,
  let leading_ty := match ext_binders.remainder with
  | binders_remainder.view.type brt := brt.type
  | _ := review hole {},
  let r := ext_binders.leading_ids.foldr (λ bid r,
    mk_binding (mk_simple_binder (binder_ident_to_ident bid) binder_info.default leading_ty) r) r,
  pure r

def bracketed_binders.transform : transformer :=
λ stx, do
  let v := view bracketed_binders stx,
  match v with
  | bracketed_binders.view.simple _ := no_expansion
  | bracketed_binders.view.extended bnders := do
    bnders ← bnders.mmap expand_bracketed_binder,
    pure $ review bracketed_binders $ bracketed_binders.view.simple $ list.join bnders

def lambda.transform : transformer :=
λ stx, do
  let v := view lambda stx,
  expand_binders (λ binders body, review lambda {binders := binders, body := body}) v.binders v.body

def pi.transform : transformer :=
λ stx, do
  let v := view pi stx,
  expand_binders (λ binders body, review pi {op := v.op, binders := binders, range := body}) v.binders v.range

def arrow.transform : transformer :=
λ stx, do
  let v := view arrow stx,
  pure $ review pi {
    op := syntax.atom {val := "Π"},
    binders := binders.view.simple $ simple_binder.view.explicit {id := `a, type := v.dom},
    range := v.range}

def paren.transform : transformer :=
λ stx, do
  let v := view paren stx,
  match v.content with
  | none := pure $ glob_id `unit.star
  | some {term := t, special := none} := pure t
  | some {term := t, special := paren_special.view.tuple tup} :=
    pure $ some $ (tup.tail.map sep_by.elem.view.item).foldr (λ t tup, mk_app (glob_id `prod.mk) [t, tup]) t
  | some {term := t, special := paren_special.view.typed pst} :=
    pure $ mk_app (glob_id `typed_expr) [pst.type, t]

def assume.transform : transformer :=
λ stx, do
  let v := view «assume» stx,
  let binders : binders.view := match v.binders with
  | assume_binders.view.anonymous aba := binders.view.simple $
    -- TODO(Sebastian): unhygienic!
    simple_binder.view.explicit {id := "this", type := aba.type}
  | assume_binders.view.binders abb := abb,
  pure $ review lambda {binders := binders, body := v.body}

def if.transform : transformer :=
λ stx, do
  let v := view «if» stx,
  pure $ match v.id with
  | some id := mk_app (glob_id `dite) [v.prop,
    review lambda {binders := binders.view.simple $ simple_binder.view.explicit {id := id.id, type := v.prop}, body := v.then_branch},
    review lambda {binders := binders.view.simple $ simple_binder.view.explicit {id := id.id, type := mk_app (glob_id `not) [v.prop]}, body := v.else_branch}]
  | none := mk_app (glob_id `ite) [v.prop, v.then_branch, v.else_branch]

def let.transform : transformer :=
λ stx, do
  let v := view «let» stx,
  match v.lhs with
  | let_lhs.view.id {id := _, binders := [], type := some _} := no_expansion
  | let_lhs.view.id lli@{id := _, binders := _, type := none} :=
    pure $ review «let» {v with lhs := let_lhs.view.id {lli with type := some {type := review hole {}}}}
  | let_lhs.view.id lli@{id := _, binders := _, type := some ty} :=
    let bindrs := binders.view.extended {
      leading_ids := [],
      remainder := binders_remainder.view.mixed $ lli.binders.map mixed_binder.view.bracketed} in
    pure $ review «let» {v with
      lhs := let_lhs.view.id {
        id := lli.id,
        binders := [],
        type := some {type := review pi {op := syntax.atom {val := "Π"}, binders := bindrs, range := ty.type}}},
      body := review lambda {binders := bindrs, body := v.body}}
  | let_lhs.view.pattern llp :=
    pure $ review «match» {
      scrutinees := [v.value],
      equations := [{item := {lhs := [llp], rhs := v.body}}]}

-- move parameters into type
def constant.transform : transformer :=
λ stx, do
  let v := view «constant» stx,
  match v with
  | {sig := {params := bracketed_binders.view.extended bindrs, type := type}, ..} := do
    let bindrs := binders.view.extended {
      leading_ids := [],
      remainder := binders_remainder.view.mixed $ bindrs.map mixed_binder.view.bracketed},
    pure $ review «constant» {v with sig := {
      params := bracketed_binders.view.simple [],
      type := {type := review pi {op := syntax.atom {val := "Π"}, binders := bindrs, range := type.type}}}}
  | _ := no_expansion

def declaration.transform : transformer :=
λ stx, do
  let v := view «declaration» stx,
  match v.inner with
  | declaration.inner.view.inductive ind@{«class» := some _, ..} :=
    let attrs := v.modifiers.attrs.get_or_else {attrs := []} in
    pure $ review «declaration» {v with
      modifiers := {v.modifiers with attrs := some {attrs with attrs :=
        {item := {name := "class", args := []}} :: attrs.attrs}},
      inner := declaration.inner.view.inductive {ind with «class» := none}
    }
  | declaration.inner.view.structure s@{keyword := structure_kw.view.class _, ..} :=
    let attrs := v.modifiers.attrs.get_or_else {attrs := []} in
    pure $ review «declaration» {v with
      modifiers := {v.modifiers with attrs := some {attrs with attrs :=
        {item := {name := "class", args := []}} :: attrs.attrs}},
      inner := declaration.inner.view.structure {s with keyword := structure_kw.view.structure}
    }
  | _ := no_expansion

def intro_rule.transform : transformer :=
λ stx, do
  let v := view «intro_rule» stx,
  match v.sig with
  | {params := bracketed_binders.view.extended bindrs, type := some type} := do
    let bindrs := binders.view.extended {
      leading_ids := [],
      remainder := binders_remainder.view.mixed $ bindrs.map mixed_binder.view.bracketed},
    pure $ review «intro_rule» {v with sig := {
      params := bracketed_binders.view.simple [],
      type := some {type := review pi {op := syntax.atom {val := "Π"}, binders := bindrs,
        range := type.type}}}}
  | _ := no_expansion

/- We expand `variable` into `variables` instead of the other way around since, in theory,
   elaborating multiple variables at the same time makes it possible to omit more information. -/
def variable.transform : transformer :=
λ stx, do
  let v := view «variable» stx,
  pure $ review «variables» {binders := bracketed_binders.view.extended [v.binder]}

@[derive has_view]
def binding_annotation_update.parser : term_parser :=
node! binding_annotation_update ["dummy"] -- FIXME: bad node! expansion

def variables.transform : transformer :=
λ stx, do
  let v := view «variables» stx,
  match v.binders with
  | bracketed_binders.view.simple _ := no_expansion
  | bracketed_binders.view.extended bnders := do
    bnders ← bnders.mmap $ λ b, match b with
    -- binding annotation update
    | bracketed_binder.view.explicit eb@{content :=
      explicit_binder_content.view.other bc@{ids := ids, type := none, default := none}} :=
      expand_bracketed_binder $ bracketed_binder.view.explicit {eb with content :=
        explicit_binder_content.view.other {bc with type := some {type := review binding_annotation_update {}}}}
    | _ := expand_bracketed_binder b,
    pure $ review «variables» {binders := bracketed_binders.view.simple $ list.join bnders}

def level.leading.transform : transformer :=
λ stx, do
  let v := view level.leading stx,
  match v with
  | level.leading.view.paren p := pure p.inner
  | _ := no_expansion

def subtype.transform : transformer :=
λ stx, do
  let v := view term.subtype stx,
  pure $ mk_app (glob_id `subtype) [review lambda {
    binders := mk_simple_binder v.id binder_info.default $ get_opt_type v.type,
    body := v.prop
  }]

def universes.transform : transformer :=
λ stx, do
  let v := view «universes» stx,
  pure $ syntax.list $ v.ids.map (λ id, review «universe» {id := id})

def sorry.transform : transformer :=
λ stx, pure $ mk_app (glob_id `sorry_ax) [review hole {}, glob_id `bool.ff]

local attribute [instance] name.has_lt_quick

-- TODO(Sebastian): replace with attribute
def builtin_transformers : rbmap name transformer (<) := rbmap.from_list [
  (mixfix.name, mixfix.transform),
  (reserve_mixfix.name, reserve_mixfix.transform),
  (bracketed_binders.name, bracketed_binders.transform),
  (lambda.name, lambda.transform),
  (pi.name, pi.transform),
  (arrow.name, arrow.transform),
  (paren.name, paren.transform),
  (assume.name, assume.transform),
  (if.name, if.transform),
  (let.name, let.transform),
  (constant.name, constant.transform),
  (declaration.name, declaration.transform),
  (intro_rule.name, intro_rule.transform),
  (variable.name, variable.transform),
  (variables.name, variables.transform),
  (level.leading.name, level.leading.transform),
  (term.subtype.name, subtype.transform),
  (universes.name, universes.transform),
  (sorry.name, sorry.transform)
] _

structure expander_state :=
(next_scope : macro_scope)

structure expander_config extends transformer_config :=
(transformers : rbmap name transformer (<))

instance expander_config.has_lift : has_lift expander_config transformer_config :=
⟨expander_config.to_transformer_config⟩

@[reducible] def expander_m := state_t expander_state $ reader_t expander_config $ except_t message id

section
local attribute [reducible] macro_scope
def expander_state.new : expander_state := ⟨0⟩
def mk_scope : expander_m macro_scope :=
do st ← get,
   put {st with next_scope := st.next_scope + 1},
   pure st.next_scope
end

private def expand_core : nat → syntax → expander_m syntax
| 0 stx := error stx "macro expansion limit exceeded"
| (fuel + 1) stx :=
do some n ← pure stx.as_node | pure stx,
   cfg ← read,
   some t ← pure $ cfg.transformers.find n.kind.name
     -- not a macro: recurse
     | syntax.mk_node n.kind <$> n.args.mmap (expand_core fuel),
   sc ← mk_scope,
   let n' := syntax.mk_node n.kind $ n.args.map (syntax.flip_scopes [sc]),
   some stx' ← state_t.lift $ λ cfg, t n' ↑cfg
     -- no unfolding: recurse
     | syntax.mk_node n.kind <$> n.args.mmap (expand_core fuel),
   -- flip again, expand iteratively
   expand_core fuel $ stx'.flip_scopes [sc]

def expand (stx : syntax) : reader_t expander_config (except message) syntax :=
-- TODO(Sebastian): persist macro scopes across commands/files
prod.fst <$> expand_core 1000 stx expander_state.new

end expander
end lean
