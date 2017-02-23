/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.data.option.basic init.category.monad init.category.alternative
import init.meta.pexpr init.meta.interaction_monad

namespace lean

-- TODO: make inspectable (and pure)
meta constant parser_state : Type
meta constant parser_state.cur_pos : parser_state → pos

@[reducible] meta def parser := interaction_monad parser_state
@[reducible] meta def parser_result := interaction_monad.result parser_state

open interaction_monad
open interaction_monad.result

namespace parser

/-- Make sure the next token is an identifier, consume it, and
    produce the quoted name `t, where t is the identifier. -/
meta constant ident : parser name
/-- Check that the next token is `tk` and consume it. `tk` must be a registered token. -/
meta constant tk (tk : string) : parser unit
/-- Parse an unelaborated expression using the given right-binding power. The expression
    may contain antiquotations (`%%e`). -/
meta constant qexpr (rbp := nat.of_num std.prec.max) : parser pexpr

/-- Return the current parser position without consuming any input. -/
meta def cur_pos : parser pos := λ s, success (parser_state.cur_pos s) s

meta def parser_orelse {α : Type} (p₁ p₂ : parser α) : parser α :=
λ s,
let pos₁ := parser_state.cur_pos s in
result.cases_on (p₁ s)
  success
  (λ e₁ ref₁ s',
    let pos₂ := parser_state.cur_pos s' in
    if pos₁ ≠ pos₂ then
      exception e₁ ref₁ s'
    else result.cases_on (p₂ s)
     success
     exception)

meta instance : alternative parser :=
⟨@interaction_monad_fmap parser_state, (λ α a s, success a s), (@fapp _ _), @interaction_monad.failed parser_state, @parser_orelse⟩


-- TODO: move
meta def {u v} many {f : Type u → Type v} [monad f] [alternative f] {a : Type u} : f a → f (list a)
| x := (do y ← x,
           ys ← many x,
           return $ y::ys) <|> pure list.nil

local postfix ?:100 := optional
local postfix * := many

meta def sep_by {α : Type} : string → parser α → parser (list α)
| s p := (list.cons <$> p <*> (tk s *> p)*) <|> return []

end parser
end lean
