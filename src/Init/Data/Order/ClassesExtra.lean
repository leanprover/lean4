module

prelude
public import Init.Data.Order.Classes
public import Init.Data.Ord

namespace Std

/--
This typeclass states that the synthesized `Ord α` instance is compatible with the `OrderData α`
instance. This means that according to `compare`, the following are equivalent:

* `a` is less or equal to `b` according to `compare`
* `b` is greater than or equal to `b` according to compare`
* `OrderData.IsLE a b`.

This property uniquely determines `Ord α` in terms of `OrderData α`.

`LawfulOrderOrd α` automatically entails that `Ord α` is oriented (see `OrientedOrd α`)
and that `OrderData.IsLE` is total.
-/
public class LawfulOrderOrd (α : Type u) [Ord α] [OrderData α] where
  compare_isLE : ∀ a b : α, (compare a b).isLE ↔ OrderData.IsLE a b
  compare_isGE : ∀ a b : α, (compare a b).isGE ↔ OrderData.IsLE b a

end Std
