module

prelude
import Init.Data.Iterators.Combinators.Monadic.Attach

namespace Std.Iterators

instance {α β : Type w} [Membership β (IterM (α := α) Id β)] :
    Membership β (Iter (α := α) β) where
  mem it out := out ∈ it.toIterM

@[always_inline, inline]
def Iter.attach {α β : Type w}
    [Iterator α Id β] [Membership β (IterM (α := α) Id β)] [LawfulIteratorMembership α Id]
    (it : Iter (α := α) β) : Iter (α := Types.Attach it.toIterM) { out : β // out ∈ it } :=
  it.toIterM.attach.toIter

end Std.Iterators
