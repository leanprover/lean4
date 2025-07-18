module

prelude
public import Init.Data.Order.Classes
public import Init.Data.Ord

/-!
This is an extension of `Init.Data.Order.Classes` that has been moved into a separate module
because `Init.Data.Ord` has lots of imports.
-/

section Ord

open Std

public class LawfulOrderOrd (α : Type u) [Ord α] [OrderData α] where
  compare_isLE_iff : ∀ a b : α, (compare a b).isLE ↔ OrderData.IsLE a b
  compare_isGE_iff : ∀ a b : α, (compare a b).isGE ↔ OrderData.IsLE b a

end Ord
