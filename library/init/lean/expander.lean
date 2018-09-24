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

def mixfix.transform : transformer :=
λ stx, do
  let v := view mixfix stx,
   -- TODO: reserved token case
   notation_symbol.view.quoted quoted ← pure v.symbol,
   -- `notation` allows more syntax after `:` than mixfix commands, so we have to do a small conversion
   let prec_to_action : precedence.view → action.view :=
     λ prec, {action := action_kind.view.prec prec.prec, ..prec},
   do some (spec, term) ← pure (match v.kind : _ → option (notation_spec.view × syntax) with
     | mixfix.kind.view.prefix _ :=
       let b := {parser.ident.view . part := ident_part.view.default "b"} in
       some (notation_spec.view.rules {
          rules := [{
            symbol := v.symbol,
            transition := some $ transition.view.arg {
              id := b,
              action := prec_to_action <$> quoted.prec}}]},
        review lambda {op := lambda_op.view.«λ», binders := [
            binder.view.unbracketed {
              ids := [binder_id.view.id {id := b}]}
          ],
          body := review app {fn := v.term, arg := review term.ident {id := b}}})
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
