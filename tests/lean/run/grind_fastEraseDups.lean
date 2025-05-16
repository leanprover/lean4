
import Std.Data.HashSet

open Std

set_option grind.warning false

namespace List

-- Fast duplicate-removing function, using a hash set to check if an element was seen before
def fastEraseDups [BEq α] [Hashable α] (l : List α) : List α :=
  go l [] ∅
where
  go : List α → List α → Std.HashSet α → List α
  | [], seenl, _ => seenl.reverse
  | (x::l), seenl, seen => if x ∈ seen then go l seenl seen else go l (x::seenl) (seen.insert x)

-- Easy to verify using available hash set lemmas
theorem eraseDups_eq_fastEraseDups [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (l : List α) : l.eraseDups = l.fastEraseDups :=
  loop_eq_go _ _ _ (by simp)
where
  loop_eq_go (l seenl : List α) (seen : Std.HashSet α) (hs : ∀ x, seenl.contains x ↔ x ∈ seen) :
      eraseDupsBy.loop (· == ·) l seenl = fastEraseDups.go l seenl seen := by
    induction l generalizing seenl seen with
    | nil => grind [eraseDupsBy.loop, fastEraseDups.go]
    | cons x => cases h : seenl.contains x <;> grind [eraseDupsBy.loop, fastEraseDups.go]

end List
