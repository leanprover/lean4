import Std.Data.HashMap

set_option grind.warning false

open Std
open scoped HashMap

example (m : HashMap Nat Nat) :
    (m.insert 1 2).filter (fun k _ => k > 1000) ~m m.filter fun k _ => k > 1000 := by
  apply HashMap.Equiv.of_forall_getElem?_eq
  grind [HashMap.getElem?_eq_some_getElem ]

example [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
  {m : HashMap α β} {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.map (f k) := by
  grind
