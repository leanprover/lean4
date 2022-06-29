@[simp]
theorem exists_prop {p q : Prop} : (∃ h : p, q) ↔ p ∧ q :=
Iff.intro (fun ⟨hp, hq⟩ => And.intro hp hq) (fun ⟨hp, hq⟩ => Exists.intro hp hq)

namespace Option

def get {α : Type u} : ∀ {o : Option α}, isSome o → α
| some x, h => x

@[simp] theorem isSome_none : @isSome α none = false := rfl
@[simp] theorem isSome_some {a : α} : isSome (some a) = true := rfl
@[simp] theorem get_some (x : α) (h : isSome (some x)) : Option.get h = x := rfl

theorem eq_some_iff_get_eq {o : Option α} {a : α} :
  o = some a ↔ ∃ h : o.isSome, Option.get h = a := by
  cases o; simp; intro h; cases h; contradiction
  simp [exists_prop]
