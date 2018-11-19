/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Macro expander for the Lean language
-/
prelude
import init.lean.parser.module
import init.lean.expr

namespace lean
namespace expander
open parser
open parser.term
open parser.command
open parser.command.notation_spec

structure expander_config :=
(filename : string)

@[derive monad monad_reader monad_except]
def transform_m := reader_t expander_config $ except_t message id
abbreviation transformer := syntax → transform_m syntax

def error {m : Type → Type} [monad m] [monad_reader expander_config m] [monad_except message m] {α : Type}
  (context : syntax) (text : string) : m α :=
do cfg ← read,
   -- TODO(Sebastian): convert position
   throw {filename := cfg.filename, pos := /-context.get_pos.get_or_else-/ ⟨1,0⟩, text := text}

instance coe_name_ident : has_coe name syntax_ident :=
⟨λ n, {val := n, raw_val := substring.of_string n.to_string}⟩

instance coe_ident_ident_univs : has_coe syntax_ident ident_univs.view :=
⟨λ id, {id := id}⟩

instance coe_ident_binder_id : has_coe syntax_ident binder_ident.view :=
⟨binder_ident.view.id⟩

instance coe_binders {α : Type} [has_coe_t α binder_ident.view] : has_coe (list α) term.binders.view :=
⟨λ ids, {leading_ids := ids.map coe}⟩

def mk_app (fn : syntax_ident) (args : list syntax) : syntax :=
args.foldl (λ fn arg, syntax.mk_node app [fn, arg]) (syntax.ident fn)

def mk_simple_lambda (id : syntax_ident) (bi : binder_info) (dom body : syntax) : syntax :=
let bc : binder_content.view := {ids := [id], type := some {type := dom}} in
review lambda {
  binders := {leading_ids := [], remainder := binders_remainder.view.mixed [
    mixed_binder.view.bracketed $ match bi with
    | binder_info.default := bracketed_binder.view.explicit {content := explicit_binder_content.view.other bc}
    | binder_info.implicit := bracketed_binder.view.implicit {content := bc}
    | binder_info.strict_implicit := bracketed_binder.view.strict_implicit {content := bc}
    | binder_info.inst_implicit := bracketed_binder.view.inst_implicit
      {content := inst_implicit_binder_content.view.named {id := id, type := dom}}
    | binder_info.aux_decl := /- should not happen -/
      bracketed_binder.view.explicit {content := explicit_binder_content.view.other bc}
  ]},
  body := body
}

-- TODO(Sebastian): share this with other forms taking binders? Using local_expand?
def lambda.transform : transformer :=
λ stx, do
  let lam := view lambda stx,
  let to_ident (bid : binder_ident.view) : syntax_ident :=
    match bid with
    | binder_ident.view.id id := id
    | binder_ident.view.hole _ := "a",
  let r := lam.body,
  (r, ty) ← match lam.binders.remainder with
    | none := pure (r, none)
    | binders_remainder.view.type brt := pure (r, some brt.type)
    | binders_remainder.view.mixed brms := do {
      r ← brms.mfoldr (λ brm r, match brm with
      | mixed_binder.view.bracketed (bracketed_binder.view.anonymous_constructor ctor) :=
        pure $ mk_simple_lambda "x" binder_info.default (review hole {}) $ review «match» {
          scrutinees := [(syntax.ident "x", none)],
          equations := [({lhs := [(review anonymous_constructor ctor, none)], rhs := r}, none)]
        }
      -- local notation: erase
      | mixed_binder.view.bracketed
        (bracketed_binder.view.explicit {content := explicit_binder_content.view.notation _}) := pure r
      | mixed_binder.view.bracketed mbb := do
        let (bi, bc) : binder_info × binder_content.view := (match mbb with
        | bracketed_binder.view.explicit {content := bc} := (match bc with
          | explicit_binder_content.view.other bc := (binder_info.default, bc)
          | _ := (binder_info.default, {ids := []})  /- unreachable, see above -/)
        | bracketed_binder.view.implicit {content := bc} := (binder_info.implicit, bc)
        | bracketed_binder.view.strict_implicit {content := bc} := (binder_info.strict_implicit, bc)
        | bracketed_binder.view.inst_implicit {content := bc} :=
          prod.mk binder_info.inst_implicit $ (match bc with
            | inst_implicit_binder_content.view.anonymous bca :=
              {ids := ["_inst_"], type := some {type := bca.type}}
            | inst_implicit_binder_content.view.named bcn :=
              {ids := [bcn.id], type := some {type := bcn.type}})
        | bracketed_binder.view.anonymous_constructor _ := (binder_info.default, {ids := []}) /- unreachable -/),
        let type := (binder_content_type.view.type <$> bc.type).get_or_else $ review hole {},
        type ← match bc.default with
        | none := pure type
        | some (binder_default.view.val bdv) := pure $ mk_app "_root_.opt_param" [type, bdv.term]
        | some bdv@(binder_default.view.tac bdt) := match bc.type with
          | none := pure $ mk_app "_root_.auto_param" [bdt.term]
          | some _ := error (review binder_default bdv) "unexpected auto param after type annotation",
        pure $ bc.ids.foldr (λ bid r, mk_simple_lambda (to_ident bid) bi type r) r
      | mixed_binder.view.id bid := pure $ mk_simple_lambda (to_ident bid) binder_info.default (review hole {}) r
      ) r,
      pure (r, none)
  },
  let r := lam.binders.leading_ids.foldr (λ bid r,
    mk_simple_lambda (to_ident bid) binder_info.default (ty.get_or_else $ review hole {}) r) r,
  pure r

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

local attribute [instance] name.has_lt_quick

-- TODO(Sebastian): replace with attribute
def transformers : rbmap name transformer (<) := rbmap.from_list [
  (mixfix.name, mixfix.transform),
  (reserve_mixfix.name, reserve_mixfix.transform),
  (lambda.name, lambda.transform)
] _

structure expander_state :=
(next_scope : macro_scope)

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
   some t ← pure $ transformers.find n.kind.name
     | syntax.mk_node n.kind <$> n.args.mmap (expand_core fuel),
   sc ← mk_scope,
   let n' := syntax.mk_node n.kind $ n.args.map (syntax.flip_scopes [sc]),
   stx' ← state_t.lift $ t n',
   ---- expand recursively
   --expand_core fuel $ stx'.flip_scopes [sc]
   let stx' := stx'.flip_scopes [sc],
   some n ← pure stx'.as_node | pure stx',
   syntax.mk_node n.kind <$> n.args.mmap (expand_core fuel)

def expand (stx : syntax) : reader_t expander_config (except message) syntax :=
-- TODO(Sebastian): persist macro scopes across commands/files
prod.fst <$> expand_core 1000 stx expander_state.new

end expander
end lean
