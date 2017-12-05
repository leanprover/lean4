/- test cases for coinductive predicates -/
universe u

def stream (α : Type u) := nat → α
constant stream.cons {α} : α → stream α → stream α
constant stream.head {α} : stream α → α
constant stream.tail {α} : stream α → stream α
notation h :: t := stream.cons h t

coinductive all_stream {α : Type u} (s : set α) : stream α → Prop
| step {} : ∀{a : α} {ω : stream α}, a ∈ s → all_stream ω → all_stream (a :: ω)

#print prefix all_stream

#check (@all_stream : Π {α : Type u}, set α → stream α → Prop)
#check (@all_stream.step :
  ∀ {α : Type u} {s : set α} {a : α} {ω : stream α}, a ∈ s → all_stream s ω → all_stream s (a :: ω))
#check (@all_stream.corec_functional :
  ∀ {α : Type u} (s : set α) (C : stream α → Prop),
    (∀ (a : stream α), C a → all_stream.functional s C a) → ∀ (a : stream α), C a → all_stream s a)

coinductive all_stream' {α : Type u} (s : set α) : stream α → Prop
| step {} : ∀{ω : stream α}, stream.head ω ∈ s → all_stream' (stream.tail ω) → all_stream' ω


coinductive alt_stream : stream bool → Prop
| tt_step : ∀{ω : stream bool}, alt_stream (ff :: ω) → alt_stream (tt :: ff :: ω)
| ff_step : ∀{ω : stream bool}, alt_stream (tt :: ω) → alt_stream (ff :: tt :: ω)

#print prefix alt_stream

#check (@alt_stream : stream bool → Prop)
#check (@alt_stream.tt_step : ∀ {ω : stream bool}, alt_stream (ff :: ω) → alt_stream (tt :: ff :: ω))
#check (@alt_stream.ff_step : ∀ {ω : stream bool}, alt_stream (tt :: ω) → alt_stream (ff :: tt :: ω))
#check (@alt_stream.corec_functional :
  ∀ (C : stream bool → Prop),
    (∀ (a : stream bool), C a → alt_stream.functional C a) → ∀ (a : stream bool), C a → alt_stream a)



mutual coinductive tt_stream, ff_stream
with tt_stream : stream bool → Prop
| step {} : ∀{ω : stream bool}, ff_stream ω → tt_stream (stream.cons tt ω)
with ff_stream : stream bool → Prop
| step {} : ∀{ω : stream bool}, tt_stream ω → ff_stream (stream.cons ff ω)

#print prefix tt_stream
#print prefix ff_stream

#check (@tt_stream : stream bool → Prop)
#check (@tt_stream.corec_functional :
  ∀ (C_tt_stream C_ff_stream : stream bool → Prop),
    (∀ (a : stream bool), C_tt_stream a → tt_stream.functional C_tt_stream C_ff_stream a) →
    (∀ (a : stream bool), C_ff_stream a → ff_stream.functional C_tt_stream C_ff_stream a) →
    ∀ (a : stream bool), C_tt_stream a → tt_stream a)
#check (@ff_stream : stream bool → Prop)
#check (@ff_stream.corec_functional :
  ∀ (C_tt_stream C_ff_stream : stream bool → Prop),
    (∀ (a : stream bool), C_tt_stream a → tt_stream.functional C_tt_stream C_ff_stream a) →
    (∀ (a : stream bool), C_ff_stream a → ff_stream.functional C_tt_stream C_ff_stream a) →
    ∀ (a : stream bool), C_ff_stream a → ff_stream a)


mutual coinductive tt_ff_stream, ff_tt_stream
with tt_ff_stream : stream bool → Prop
| step {} : ∀{ω : stream bool}, tt_ff_stream ω ∨ ff_tt_stream ω → tt_ff_stream (stream.cons tt ω)
with ff_tt_stream : stream bool → Prop
| step {} : ∀{ω : stream bool}, ff_tt_stream ω ∨ tt_ff_stream ω → ff_tt_stream (stream.cons ff ω)

#print prefix tt_ff_stream

inductive all_list {α : Type} (p : α → Prop) : list α → Prop
| nil  : all_list []
| cons : ∀a xs, p a → all_list xs → all_list (a :: xs)

@[monotonicity]
lemma monotonicity.all_list {α : Type} {p q : α → Prop} (h : ∀a, implies (p a) (q a)) :
  ∀xs, implies (all_list p xs) (all_list q xs)
| ._ (all_list.nil ._)           := all_list.nil _
| ._ (all_list.cons a xs ha hxs) := all_list.cons _ _ (h a ha) (monotonicity.all_list _ hxs)

mutual coinductive walk_a, walk_b {α β : Type} (f : α → list β) (g : β → α) (p : α → Prop) (t : α → Prop)
with walk_a : α → Prop
| step : ∀a, all_list walk_b (f a) → p a → walk_a a
| term : ∀a, t a → walk_a a
with walk_b : β → Prop
| step : ∀b, walk_a (g b) → walk_b b


coinductive walk_list {α : Type} (f : α → list α) (p : α → Prop) : ℕ → α → Prop
| step : ∀n a, all_list (walk_list n) (f a) → p a → walk_list (n + 1) a

-- #check walk_a.corec_on

example {f : ℕ → list ℕ} {a' : ℕ} {n : ℕ} {a : fin n}:
  walk_list f (λ a'', a'' = a') (n + 1) a' :=
begin
  coinduction walk_list.corec_on generalizing a n,
  show ∃ (n : ℕ),
    all_list (λ (a : ℕ), ∃ {n_1 : ℕ} {a_1 : fin n_1}, n_1 + 1 = n ∧ a' = a) (f a') ∧
      a' = a' ∧ n + 1 = w + 1,
  admit
end

coinductive foo : list ℕ → Prop
| mk : ∀ xs, (∀ k l m, foo (k::l::m::xs)) → foo xs
