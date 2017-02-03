/-
Isabelle style tactics.
This test is based on a file created by Gabriel Ebner.
-/
universe variables u v

inductive lazy_list (α : Type u) : Type u
| nil {} : lazy_list
| cons   : α → thunk (lazy_list) → lazy_list

namespace lazy_list
variables {α : Type u} {β : Type v}

def singleton : α → lazy_list α
| a := cons a nil

def of_list : list α → lazy_list α
| []     := nil
| (h::t) := cons h (of_list t)

def append : lazy_list α → thunk (lazy_list α) → lazy_list α
| nil        l  := l ()
| (cons h t) l  := cons h (append (t ()) (l ()))

def map (f : α → β) : lazy_list α → lazy_list β
| nil        := nil
| (cons h t) := cons (f h) (map (t ()))

def join : lazy_list (lazy_list α) → lazy_list α
| nil        := nil
| (cons h t) := append h (join (t ()))

def for (l : lazy_list α) (f : α → β) : lazy_list β :=
map f l

def approx : nat → lazy_list α → list α
| 0     l          := []
| _     nil        := []
| (a+1) (cons h t) := h :: approx a (t ())

meta def above : nat → lazy_list nat
| i     := cons i (above (i+1))

end lazy_list

meta def lazy_tactic (α : Type u) :=
tactic_state → lazy_list (α × tactic_state)

namespace lazy_tactic
open lazy_list

meta def of_tactic {α : Type u} (t : tactic α) : lazy_tactic α :=
λ s, match t s with
| tactic_result.success a new_s    := lazy_list.singleton (a, new_s)
| tactic_result.exception .α f e s := lazy_list.nil
end

meta instance {α : Type} : has_coe (tactic α) (lazy_tactic α) :=
⟨of_tactic⟩

protected meta def return {α} (a : α) : lazy_tactic α :=
λ s, lazy_list.singleton (a, s)

protected meta def map {α β} (f : α → β) : lazy_tactic α → lazy_tactic β
| t s := (t s)^.for (λ p, (f p.1, p.2))

protected meta def bind {α β} : lazy_tactic α → (α → lazy_tactic β) → lazy_tactic β :=
λ t₁ t₂ s, join (map (λ p : α × tactic_state, t₂ p.1 p.2) (t₁ s))

protected meta def orelse {α} (t₁ t₂ : lazy_tactic α) : lazy_tactic α :=
λ s, append (t₁ s) (t₂ s)

protected meta def failure {α} : lazy_tactic α :=
λ s, nil

meta instance : monad lazy_tactic :=
{ ret  := @lazy_tactic.return,
  bind := @lazy_tactic.bind,
  map  := @lazy_tactic.map }

meta instance : alternative lazy_tactic :=
{ map     := @lazy_tactic.map,
  pure    := @lazy_tactic.return,
  seq     := @fapp _ _,
  failure := @lazy_tactic.failure,
  orelse  := @lazy_tactic.orelse
}

meta def choose {α} (xs : list α) : lazy_tactic α :=
λ s, of_list $ xs^.for (λ a, (a, s))

meta def run {α} (t : lazy_tactic α) : tactic α :=
λ s, match t s with
| nil                := tactic.failed s
| cons (a, new_s) ss := tactic_result.success a new_s
end

open tactic

private meta def try_constructors : list name → lazy_tactic unit
| []      := failure
| (c::cs) := (mk_const c >>= apply : tactic unit) <|> try_constructors cs

/- Backtracking version of constructor -/
meta def constructor : lazy_tactic unit :=
do t ← target,
   cs ← get_constructors_for t,
   try_constructors cs

end lazy_tactic

open lazy_tactic

example (p q : Prop) : q → p ∨ q :=
by run $ do
 tactic.intros,
 constructor,
 tactic.trace_state,
 tactic.assumption

meta def naive_instantiation : lazy_tactic unit :=
let vals := [`(1),`(2),`(3)] in do
x ← choose vals,
y ← choose vals,
e ← tactic.to_expr `(nat.add_comm %%x %%y),
tactic.trace e,
tactic.exact e

lemma ex : 1 + 3 = 3 + 1 :=
by naive_instantiation^.run
