meta def mytac :=
state_t nat tactic

meta instance : monad mytac :=
state_t.monad _ _

meta instance : monad.has_monad_lift tactic mytac :=
monad.monad_transformer_lift (state_t nat) tactic

meta instance (α : Type) : has_coe (tactic α) (mytac α) :=
⟨monad.monad_lift⟩

namespace mytac

meta def step {α : Type} (t : mytac α) : mytac unit :=
t >> return ()

meta def istep {α : Type} (line0 col0 line col : nat) (t : mytac α) : mytac unit :=
λ v s, result.cases_on (@scope_trace _ line col (t v s))
  (λ ⟨a, v⟩ new_s, result.success ((), v) new_s)
  (λ opt_msg_thunk e new_s, match opt_msg_thunk with
    | some msg_thunk :=
      let msg := λ _ : unit, msg_thunk () ++ format.line ++ to_fmt "value: " ++ to_fmt v ++ format.line ++ to_fmt "state:" ++ format.line ++ new_s^.to_format in
          interaction_monad.result.exception (some msg) (some ⟨line, col⟩) new_s
    | none := interaction_monad.silent_fail new_s
    end)

meta def execute (tac : mytac unit) : tactic unit :=
tac 0 >> return ()

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

meta def inc : mytac unit :=
do v ← state_t.read, state_t.write (v+1)

end interactive
end mytac

example (p q : Prop) : p → q → p ∧ q :=
begin [mytac]
  intros,
  inc,
  trace "test",
  constructor,
  inc,
  assumption,
--^ "command": "info"
  assumption
end
