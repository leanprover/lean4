variable {α : Type} {r : α → α → Prop} {b : α}

inductive ReflTransGen (r : α → α → Prop) (a : α) : α → Prop
| refl : ReflTransGen r a a
| tail {b c} : ReflTransGen r a b → r b c → ReflTransGen r a c

namespace ReflTransGen

theorem head (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction hbc
  case refl => exact refl.tail hab
  case tail c d _ hcd hac => exact hac.tail hcd

@[elab_as_elim]
theorem head_induction_on {P : ∀ a : α, ReflTransGen r a b → Prop} {a : α} (h : ReflTransGen r a b)
    (refl : P b refl)
    (head : ∀ {a c} (h' : r a c) (h : ReflTransGen r c b), P c h → P a (h.head h')) : P a h := by
  induction h
  case refl => exact refl
  case tail b c _ hbc ih =>
  apply ih
  { exact head hbc _ refl }
  { exact fun h1 h2 => head h1 (h2.tail hbc) }

end ReflTransGen
