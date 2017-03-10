meta def mytac :=
state_t (name_map nat) tactic

meta instance : monad mytac :=
state_t.monad _ _

meta instance : monad.has_monad_lift tactic mytac :=
monad.monad_transformer_lift (state_t (name_map nat)) tactic

meta instance (α : Type) : has_coe (tactic α) (mytac α) :=
⟨monad.monad_lift⟩

namespace mytac

meta def step {α : Type} (t : mytac α) : mytac unit :=
t >> return ()

meta def rstep {α : Type} (line : nat) (col : nat) (t : mytac α) : mytac unit :=
λ v s, result.cases_on (@scope_trace _ line col (t v s))
  (λ ⟨a, v⟩ new_s, result.success ((), v) new_s)
  (λ opt_msg_thunk e new_s, match opt_msg_thunk with
        | some msg_thunk :=  let msg := msg_thunk () ++ format.line ++ to_fmt "value: " ++ to_fmt v ++ format.line ++ to_fmt "state:" ++ format.line ++ new_s^.to_format in
        (tactic.report_error line col msg >> interaction_monad.silent_fail) new_s | none := interaction_monad.silent_fail new_s end)

meta def execute (tac : mytac unit) : tactic unit :=
tac (name_map.mk nat) >> return ()

meta def save_info (p : pos) : mytac unit :=
do v ← state_t.read,
   s ← tactic.read,
   tactic.save_info_thunk p
      (λ _, to_fmt "Custom state: " ++ to_fmt v ++ format.line ++
                tactic_state.to_format s)

namespace interactive
meta def intros : mytac unit :=
tactic.intros >> return ()

meta def constructor : mytac unit :=
tactic.constructor

meta def trace (s : string) : mytac unit :=
tactic.trace s

meta def assumption : mytac unit :=
tactic.assumption

open lean.parser
open interactive
open interactive.types

meta def add (n : parse ident) (v : nat) : mytac unit :=
do m ← state_t.read, state_t.write (m^.insert n v)

end interactive
end mytac

lemma ex₁ (p q : Prop) : p → q → p ∧ q :=
begin [mytac]
  intros,
  add x 10,
  trace "test",
--^ "command": "info"
  constructor,
  add y 20,
  assumption,
--^ "command": "info"
  assumption
end

#print ex₁

lemma ex₂ (p q : Prop) : p → q → p ∧ q :=
begin [mytac]
  intros,
  add x 10,
  trace "test",
  constructor,
  add y 20,
  assumption,
--^ "command": "info"
  assumption
end

#print ex₂
