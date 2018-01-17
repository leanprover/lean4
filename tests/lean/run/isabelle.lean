/-
Isabelle style tactics.
This test is based on a file created by Gabriel Ebner.
-/
universe variables u

inductive lazy_list (α : Type u) : Type u
| nil {} : lazy_list
| cons   : α → thunk (lazy_list) → lazy_list

namespace lazy_list
variables {α β : Type u}
def singleton : α → lazy_list α
| a := cons a nil

def append : lazy_list α → thunk (lazy_list α) → lazy_list α
| nil        l  := l ()
| (cons h t) l  := cons h (@append (t ()) l)

def join : lazy_list (lazy_list α) → lazy_list α
| nil        := nil
| (cons h t) := append h (join (t ()))

def map (f : α → β) : lazy_list α → lazy_list β
| nil        := nil
| (cons h t) := cons (f h) (map (t ()))

def for (l : lazy_list α) (f : α → β) : lazy_list β :=
map f l

def of_list : list α → lazy_list α
| []     := nil
| (h::t) := cons h (of_list t)
end lazy_list

meta def lazy_tactic (α : Type u) :=
tactic_state → lazy_list (α × tactic_state)

namespace lazy_tactic
open lazy_list

meta def of_tactic {α : Type u} (t : tactic α) : lazy_tactic α :=
λ s, match t s with
| result.success a new_s    := lazy_list.singleton (a, new_s)
| result.exception f e s := lazy_list.nil
end

meta instance {α : Type} : has_coe (tactic α) (lazy_tactic α) :=
⟨of_tactic⟩

protected meta def return {α} (a : α) : lazy_tactic α :=
λ s, lazy_list.singleton (a, s)

protected meta def bind {α β} : lazy_tactic α → (α → lazy_tactic β) → lazy_tactic β :=
λ t₁ t₂ s, join (for (t₁ s) (λ ⟨a, new_s⟩, t₂ a new_s))

protected meta def orelse {α} (t₁ t₂ : lazy_tactic α) : lazy_tactic α :=
λ s, append (t₁ s) (t₂ s)

protected meta def failure {α} : lazy_tactic α :=
λ s, nil

meta instance : monad lazy_tactic :=
monad_from_pure_bind @lazy_tactic.return @lazy_tactic.bind

meta instance : alternative lazy_tactic :=
{ lazy_tactic.monad with
  failure := @lazy_tactic.failure,
  orelse  := @lazy_tactic.orelse }

meta def choose {α} (xs : list α) : lazy_tactic α :=
λ s, of_list $ xs^.map (λ a, (a, s))

protected meta def run {α} (t : lazy_tactic α) : tactic α :=
λ s, match t s with
| nil                := tactic.failed s
| cons (a, new_s) ss := result.success a new_s
end

open tactic

private meta def try_constructors : list name → lazy_tactic unit
| []      := failure
| (c::cs) := (mk_const c >>= apply >> skip : tactic unit) <|> try_constructors cs

/- Backtracking version of constructor -/
meta def constructor : lazy_tactic unit :=
do t ← target,
   cs ← get_constructors_for t,
   try_constructors cs

end lazy_tactic

open lazy_tactic

example (p q : Prop) : q → p ∨ q :=
by lazy_tactic.run $ do
 tactic.intros,
 constructor,
 tactic.trace_state,
 tactic.assumption

meta def naive_instantiation : lazy_tactic unit :=
let vals := [``(1),``(2),``(3)] in do
x ← choose vals,
y ← choose vals,
e ← tactic.to_expr ``(nat.add_comm %%x %%y),
tactic.trace e,
tactic.exact e

lemma ex : 1 + 3 = 3 + 1 :=
by naive_instantiation^.run
