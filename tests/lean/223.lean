universe u v

inductive Imf {α : Type u} {β : Type v} (f : α → β) : β → Type (max u v)
| mk : (a : α) → Imf f (f a)

def h {α β} {f : α → β} : {b : β} → Imf f b → α
| _, Imf.mk a => a

#print h
infix:50 " ≅ "  => HEq
theorem ex : ∀ {α β : Sort u} (h : α = β) (a : α), cast h a ≅ a
  | α, _, rfl, a => HEq.refl a

#print ex
