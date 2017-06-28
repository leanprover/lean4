/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Converter monad for building simplifiers.
-/
prelude
import init.meta.interactive init.meta.converter.conv

namespace conv
meta def save_info (p : pos) : conv unit :=
λ r lhs, do
  ts ← tactic.read,
  -- TODO(Leo): include context
  tactic.save_info_thunk p (λ _, ts.format_expr lhs) >>
  return ⟨(), lhs, none⟩

meta def step {α : Type} (c : conv α) : conv unit :=
c >> return ()

meta def istep {α : Type} (line0 col0 line col : nat) (c : conv α) : conv unit :=
λ r lhs ts, (@scope_trace _ line col (λ _, (c >> return ()) r lhs ts)).clamp_pos line0 line col

meta def execute (c : conv unit) : tactic unit :=
conversion c

namespace interactive
open lean.parser
open interactive
open interactive.types

meta def itactic : Type :=
conv unit

meta def whnf : conv unit :=
conv.whnf

meta def dsimp : conv unit :=
conv.dsimp

meta def trace_state : conv unit :=
conv.trace_lhs

meta def change (p : parse texpr) : conv unit :=
conv.change p

meta def find (p : parse qexpr) (c : itactic) : conv unit :=
λ r lhs, do
  pat ← tactic.pexpr_to_pattern p,
  s   ← simp_lemmas.mk_default, -- to be able to use congruence lemmas @[congr]
  (found, new_lhs, pr) ←
     tactic.ext_simplify_core ff {zeta := ff, beta := ff, single_pass := tt, eta := ff, proj := ff} s
       (λ u, return u)
       (λ found s r p e, do
         guard (not found),
         matched ← (tactic.match_pattern_core reducible pat e >> return tt) <|> return ff,
         guard matched,
         ⟨u, new_e, pr⟩ ← c r e,
         return (tt, new_e, pr, ff))
       (λ a s r p e, tactic.failed)
       r lhs,
  if not found then tactic.fail "find converter failed, pattern was not found"
  else return ⟨(), new_lhs, some pr⟩

end interactive
end conv

namespace tactic
namespace interactive
open lean.parser
open interactive
open interactive.types

meta def conv (c : conv.interactive.itactic) : tactic unit :=
do t ← target,
   (new_t, pr) ← c.to_tactic `eq t,
   replace_target new_t pr

meta def find (p : parse qexpr) (c : conv.interactive.itactic) : tactic unit :=
conv $ conv.interactive.find p c

end interactive
end tactic
