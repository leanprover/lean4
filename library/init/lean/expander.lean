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

@[derive monad]
def transform_m := option_t $ except message
abbreviation transformer := syntax → transform_m syntax

section
local attribute [reducible] transform_m
instance coe_option_transform_m {α : Type} : has_coe (option α) (transform_m α) :=
⟨λ o, match o with some a := pure a | none := failure⟩
end

def mixfix.transform (stx : tysyntax mixfix.view) : transform_m (tysyntax notation.view) :=
do v ← view stx,
   -- TODO: reserved token case
   notation_symbol.view.quoted quoted ← view v.symbol,
   quoted ← view quoted,
   prec ← view quoted.prec,
   -- `notation` allows more syntax after `:` than mixfix commands, so we have to do a small conversion
   let prec_to_action : precedence.view → action.view :=
     λ prec, {action := review $ action_kind.view.prec prec.prec, ..prec},
   k ← view v.kind,
   let (spec, term) := match k : _ → (notation_spec.view × syntax) with
     | mixfix.kind.view.prefix _ :=
       let b : tysyntax parser.ident.view := review {part := review $ ident_part.view.default "b"} in
       (notation_spec.view.rules $ review {
          rules := review [review {
            symbol := v.symbol,
            transition := review $ some $ review $ transition.view.arg $ review {
              id := b,
              action := review $ do prec ← prec, prec ← view prec, pure $ review $ prec_to_action prec}}]},
        review {lambda.view . op := review lambda_op.view.«λ», binders := review [review $
            binder.view.unbracketed $ review {
              ids := review [review $ binder_id.view.id $ review {id := b}]}
          ],
          body := review_as app.view {fn := v.term, arg := b}})
     | _ := sorry,
   pure $ review {spec := review spec, term := term}

local attribute [instance] name.has_lt_quick

-- TODO(Sebastian): replace with attribute
def transformers : rbmap name transformer (<) := rbmap.from_list [
  (mixfix.name, mixfix.transform)
] _

def expand (stx : syntax) : except message syntax :=
--TODO(Sebastian): recursion, hygiene, error messages
do syntax.node {kind := some k, ..} ← pure stx | pure stx,
   some t ← pure $ transformers.find k.name | pure stx,
   flip option.get_or_else stx <$> t stx

end expander
end lean
