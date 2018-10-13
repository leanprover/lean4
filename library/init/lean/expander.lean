/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Macro expander for the Lean language
-/
prelude
import init.lean.parser.module

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

def error {α : Type} (context : syntax) (text : string) : transform_m α :=
do cfg ← read,
   -- TODO(Sebastian): convert position
   throw {filename := cfg.filename, pos := /-context.get_pos.get_or_else-/ ⟨1,0⟩, text := text}

instance coe_name_ident : has_coe name parser.ident.view :=
⟨λ n, (n.components.foldr (λ n suffix, match n with
  | name.mk_string _ s := some {parser.ident.view .
      part := ident_part.view.default (some {val := s}),
      suffix := suffix <&> λ suffix, {ident := review parser.ident suffix}}
  | _ := some $ view parser.ident syntax.missing) none).get_or_else (view parser.ident syntax.missing)⟩

instance coe_ident_ident_univs : has_coe parser.ident.view ident_univs.view :=
⟨λ id, {id := id}⟩

instance coe_ident_binder_id : has_coe ident.view binder_ident.view :=
⟨binder_ident.view.id⟩

instance coe_binders {α : Type} [has_coe_t α binder_ident.view] : has_coe (list α) term.binders.view :=
⟨λ ids, {leading_ids := ids.map coe}⟩

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
  (reserve_mixfix.name, reserve_mixfix.transform)
] _

def expand (stx : syntax) : reader_t expander_config (except message) syntax :=
--TODO(Sebastian): recursion, hygiene
do syntax.node {kind := some k, ..} ← pure stx | pure stx,
   some t ← pure $ transformers.find k.name | pure stx,
   t stx

end expander
end lean
