/- test cases for coinduction -/
import data.stream

open level expr tactic

coinductive {u} all_stream {α : Type u} (s : set α) : stream α → Prop
| step {} : ∀{a : α} {ω : stream α}, a ∈ s → all_stream ω → all_stream (a :: ω)

/-
run_cmd
do
  let n := `all_stream,
  let p := 2,
  let u := `u,
  let us : list name := [u],
  let Ty : expr := sort $ succ $ param u,
  let α := local_const `α `α binder_info.implicit Ty,
  let s := local_const `s `s binder_info.default ((const `set [param u] : expr) $ α),
  type ← to_expr ``(stream %%α → Prop),
  let l : expr := local_const n n binder_info.default type,
  intro₁ ← to_expr ``(∀{a : %%α} {ω : stream %%α}, a ∈ %%s → %%l ω → %%l (a :: ω)),
  let intros := [local_const `all_stream.step `all_stream.step binder_info.default intro₁],
  add_coinductive_predicate us [α, s] [(l, intros)]
-/

#print prefix all_stream

section
universe u
#check (@all_stream : Π {α : Type u}, set α → stream α → Prop)
#check (@all_stream.step : ∀ {α : Type u} {s : set α} {a : α} {ω : stream α},
  a ∈ s → all_stream s ω → all_stream s (a :: ω))
end
