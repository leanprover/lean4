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

def mixfix.transform (stx : tysyntax mixfix.view) : option (tysyntax notation.view) :=
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

end expander
end lean
