/- test cases for coinduction -/
import data.stream

open expr tactic

/-

coinductive {u} all_stream {α : Type u} (s : set α) : stream α → Prop
| step {} : ∀{a : α} {ω : stream α}, a ∈ s → all_stream ω → all_stream (a :: ω)

-/

run_cmd
do
  let n := `all_stream,
  let p := 2,
  let u := `u,
  let us : list name := [u],
  let Ty : expr := sort $ level.succ $ level.param u,
  type ← to_expr ``(Π{α : %%Ty} (s : set α), stream α → Prop),
  let l' : expr := local_const n n binder_info.default type,
  intro₁ ← to_expr ``(∀{α : %%Ty} {s : set α} {a : α} {ω : stream α}, a ∈ s → %%l' s ω → %%l' s (a :: ω)),
  let intro₁ := instantiate_local n (const n [level.param u]) intro₁,
  let intros := [(`all_stream.step, intro₁)],
  add_coinductive_predicate n us p type intros

#print prefix all_stream

section
universe u
#check (@all_stream : Π {α : Type u}, set α → stream α → Prop)
#check (@all_stream.step : ∀ {α : Type u} {s : set α} {a : α} {ω : stream α},
  a ∈ s → all_stream s ω → all_stream s (a :: ω))
end
