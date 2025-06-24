module

prelude
import Init.Data.Iterators.Combinators.Monadic.Attach
import Init.Data.Iterators.Combinators.FilterMap

namespace Std.Iterators

@[always_inline, inline]
def Iter.attachWith {α β : Type w}
    [Iterator α Id β]
    (it : Iter (α := α) β) (P : β → Prop) (h : ∀ out, it.IsPlausibleIndirectOutput out → P out) :=
  haveI h' : ∀ out, it.toIterM.IsPlausibleIndirectOutput out → P out := by
    simp only [← isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM]
    exact h
  ((it.toIterM.attachWith P h').toIter : Iter { out : β // P out })

end Std.Iterators
