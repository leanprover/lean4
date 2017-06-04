/- test cases for coinductive predicates -/
import data.stream

universe u

open level expr tactic

coinductive all_stream {α : Type u} (s : set α) : stream α → Prop
| step {} : ∀{a : α} {ω : stream α}, a ∈ s → all_stream ω → all_stream (a :: ω)

#print prefix all_stream

#check (@all_stream : Π {α : Type u}, set α → stream α → Prop)
#check (@all_stream.step :
  ∀ {α : Type u} {s : set α} {a : α} {ω : stream α}, a ∈ s → all_stream s ω → all_stream s (a :: ω))
#check (@all_stream.corec_functional :
  ∀ {α : Type u} (s : set α) (C : stream α → Prop),
    (∀ (a : stream α), C a → all_stream.functional s C a) → ∀ (a : stream α), C a → all_stream s a)



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
