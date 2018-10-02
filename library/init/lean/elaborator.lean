/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Elaborator for the Lean language
-/
prelude
import init.lean.parser.module

namespace lean
namespace elaborator
open parser
open parser.term
open parser.command
open parser.command.notation_spec

structure elaborator_config :=
(filename : string)

structure elaborator_state :=
(reserved_notations : list reserve_notation.view := [])
(parser_cfg : module_parser_config)

@[derive monad monad_reader monad_state monad_except]
def elaborator_m := reader_t elaborator_config $ state_t elaborator_state $ except_t message id
abbreviation elaborator := syntax → elaborator_m unit

def error {α : Type} (context : syntax) (text : string) : elaborator_m α :=
do cfg ← read,
   -- TODO(Sebastian): convert position
   throw {filename := cfg.filename, pos := /-context.get_pos.get_or_else-/ ⟨1,0⟩, text := text}

local attribute [instance] name.has_lt_quick

def prec_to_nat (prec : option precedence.view) : nat :=
(prec <&> λ p, p.term.to_nat).get_or_else 0

def command_parser_config.register_notation_tokens (spec : notation_spec.view) (cfg : command_parser_config) :
  except string command_parser_config :=
do spec.rules.mfoldl (λ (cfg : command_parser_config) r, match r.symbol with
   | notation_symbol.view.quoted {symbol := syntax.atom a, prec := prec, ..} :=
     pure {cfg with tokens := cfg.tokens.insert a.val.trim {«prefix» := a.val.trim, lbp := prec_to_nat prec}}
   | _ := throw "register_notation_tokens: unreachable") cfg

def command_parser_config.register_notation_parser (spec : notation_spec.view) (cfg : command_parser_config) :
  except string command_parser_config :=
do -- build and register parser
   let k : syntax_node_kind := {name := "notation<TODO>"},
   ps ← spec.rules.mmap (λ r : rule.view, do
     psym ← match r.symbol with
     | notation_symbol.view.quoted {symbol := syntax.atom a ..} :=
       pure (symbol a.val : term_parser)
     | _ := throw "register_notation_parser: unreachable",
     ptrans ← match r.transition with
     | some (transition.view.binders b) :=
       pure $ some $ term.binders.parser
     | some (transition.view.arg {action := none, ..}) :=
       pure $ some term.parser
     | some (transition.view.arg {action := some {action := action_kind.view.prec prec}, ..}) :=
       pure $ some $ term.parser prec.to_nat
     | some (transition.view.arg {action := some {action := action_kind.view.scoped sc}, ..}) :=
       pure $ some $ term.parser $ prec_to_nat sc.prec
     | none := pure $ none
     | _ := throw "register_notation_parser: unimplemented",
     pure $ psym::ptrans.to_monad
   ),
   let ps := ps.bind id,
   cfg ← match spec.prefix_arg with
   | none   := pure {cfg with leading_term_parsers :=
     parser.combinators.node k ps::cfg.leading_term_parsers}
   | some _ := pure {cfg with trailing_term_parsers :=
     parser.combinators.node k (read::ps.map coe)::cfg.trailing_term_parsers},
   pure cfg

def postprocess_notation_spec (spec : notation_spec.view) : notation_spec.view :=
-- default leading tokens to `max`
-- NOTE: should happen after copying precedences from reserved notation
match spec with
| {prefix_arg := none, rules := r@{symbol := notation_symbol.view.quoted sym@{prec := none, ..}, ..}::rs} :=
  {spec with rules := {r with symbol := notation_symbol.view.quoted {sym with prec := some
    {term := precedence_term.view.lit $ precedence_lit.view.num $ number.view.of_nat max_prec}
  }}::rs}
| _ := spec

def reserve_notation.elaborate : elaborator :=
λ stx, do
  let v := view reserve_notation stx,
  let v := {v with spec := postprocess_notation_spec v.spec},
  -- TODO: sanity checks?
  st ← get,
  cfg ← match command_parser_config.register_notation_tokens v.spec st.parser_cfg with
  | except.ok cfg  := pure cfg
  | except.error e := error stx e,
  put {st with reserved_notations := v::st.reserved_notations,
    parser_cfg := {st.parser_cfg with to_command_parser_config := cfg}}

def match_precedence : option precedence.view → option precedence.view → bool
| none      (some rp) := tt
| (some sp) (some rp) := sp.term.to_nat = rp.term.to_nat
| _         _         := ff

/-- Check if a notation is compatible with a reserved notation, and if so, copy missing
    precedences in the notation from the reserved notation. -/
def match_spec (spec reserved : notation_spec.view) : option notation_spec.view :=
do guard $ spec.prefix_arg.is_some = reserved.prefix_arg.is_some,
   rules ← (spec.rules.zip reserved.rules).mmap $ λ ⟨sr, rr⟩, do {
     notation_symbol.view.quoted sq@{symbol := syntax.atom sa, ..} ← pure sr.symbol
       | failure,
     notation_symbol.view.quoted rq@{symbol := syntax.atom ra, ..} ← pure rr.symbol
       | failure,
     guard $ sa.val.trim = ra.val.trim,
     guard $ match_precedence sq.prec rq.prec,
     st ← match sr.transition, rr.transition with
     | some (transition.view.binder sb), some (transition.view.binder rb) :=
       guard (match_precedence sb.prec rb.prec) *> pure rr.transition
     | some (transition.view.binders sb), some (transition.view.binders rb) :=
       guard (match_precedence sb.prec rb.prec) *> pure rr.transition
     | some (transition.view.arg sarg), some (transition.view.arg rarg) := do
       sact ← match action.view.action <$> sarg.action, action.view.action <$> rarg.action with
       | some (action_kind.view.prec sp), some (action_kind.view.prec rp) :=
         guard (sp.to_nat = rp.to_nat) *> pure sarg.action
       | none,                            some (action_kind.view.prec rp) :=
         pure rarg.action
       | _, _ := failure,
       pure $ some $ transition.view.arg {sarg with action := sact}
     | none,    none    := pure none
     | _,       _       := failure,
     pure $ {rule.view .
       symbol := notation_symbol.view.quoted rq,
       transition := st}
   },
   pure $ {spec with rules := rules}

def notation.elaborate : elaborator :=
λ stx, do
  let nota := view «notation» stx,
  st ← get,

  -- check reserved notations
  matched ← pure $ st.reserved_notations.filter_map $
    λ rnota, match_spec nota.spec rnota.spec,
  nota ← match matched with
  | [matched] := pure {nota with spec := matched}
  | []        := pure nota
  | _         := error stx "invalid notation, matches multiple reserved notations",
  let nota := {nota with spec := postprocess_notation_spec nota.spec},
  -- TODO: sanity checks

  cfg ← match command_parser_config.register_notation_tokens nota.spec st.parser_cfg >>=
              command_parser_config.register_notation_parser nota.spec with
  | except.ok cfg  := pure cfg
  | except.error e := error stx e,
  put {st with parser_cfg := {st.parser_cfg with to_command_parser_config := cfg}}

-- TODO(Sebastian): replace with attribute
def elaborators : rbmap name elaborator (<) := rbmap.from_list [
  (notation.name, notation.elaborate),
  (reserve_notation.name, reserve_notation.elaborate)
] _

def elaborate (stx : syntax) : elaborator_m unit :=
do syntax.node {kind := some k, ..} ← pure stx | pure (),
   some t ← pure $ elaborators.find k.name | pure (),
   t stx

end elaborator
end lean
