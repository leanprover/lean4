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

@[derive monad monad_except]
def transform_m := except_t message id
abbreviation transformer := syntax → transform_m syntax

instance coe_name_ident : has_coe name parser.ident.view :=
⟨λ n, (n.components.foldr (λ n suffix, match n with
  | name.mk_string _ s := some {parser.ident.view .
      part := ident_part.view.default s,
      suffix := ident_suffix.view.mk "." <$> review parser.ident <$> suffix}
  | _ := some $ view parser.ident syntax.missing) none).get_or_else (view parser.ident syntax.missing)⟩

instance coe_ident_term_ident : has_coe parser.ident.view term.ident.view :=
⟨λ id, {id := id}⟩

instance coe_term_ident_binder_id : has_coe term.ident.view binder_id.view :=
⟨binder_id.view.id⟩

instance coe_binders {α : Type} [has_coe_t α binder_id.view] : has_coe (list α) term.binders.view :=
⟨λ ids, binders.view.unbracketed {ids := ids.map coe}⟩

def mixfix.transform : transformer :=
λ stx, do
  let v := view mixfix stx,
   -- TODO: reserved token case
   notation_symbol.view.quoted quoted ← pure v.symbol,
   -- `notation` allows more syntax after `:` than mixfix commands, so we have to do a small conversion
   let prec_to_action : precedence.view → action.view :=
     λ prec, {action := action_kind.view.prec prec.prec},
   do some (spec, term) ← pure (match v.kind : _ → option (notation_spec.view × syntax) with
     | mixfix.kind.view.prefix _ :=
       some (notation_spec.view.rules {
          rules := [{
            symbol := v.symbol,
            transition := transition.view.arg {
              id := `b,
              action := prec_to_action <$> quoted.prec}}]},
        review lambda {binders := [`b],
          body := review app {fn := v.term, arg := review term.ident `b}})
     | _ := none) | pure stx,
   pure $ review «notation» {spec := spec, term := term}

local attribute [instance] name.has_lt_quick

-- TODO(Sebastian): replace with attribute
def transformers : rbmap name transformer (<) := rbmap.from_list [
  (mixfix.name, mixfix.transform)
] _

def expand (stx : syntax) : except message syntax :=
--TODO(Sebastian): recursion, hygiene, error messages
do syntax.node {kind := some k, ..} ← pure stx | pure stx,
   some t ← pure $ transformers.find k.name | pure stx,
   t stx

end expander
end lean
