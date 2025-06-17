module

prelude
import Init.Data.Range.New.Nat
import Init.Data.Range.New.Lemmas

namespace Std.PRange.Nat

-- -- idea: show that toList = range'
-- @[simp] theorem forIn'_eq_forIn'_range' [Monad m] (r : PRange ⟨.closed, .open⟩ Nat)
--     (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) :
--     forIn' r init f =
--       forIn' (List.range' r.lower r.size 1) init (fun a h => f a (mem_of_mem_range' h)) := by

theorem ClosedClosed.toList_succ_succ  {m n : Nat} :
    ((m+1),,(n+1)).toList = (m,,n).toList.map (· + 1) := sorry

end Std.PRange.Nat
