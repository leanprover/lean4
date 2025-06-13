import Std.Data.HashMap
import Std.Data.TreeMap

open Std

/--
info: Std.DTreeMap.contains_iff_mem.{u, v} {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : DTreeMap α β cmp}
  {k : α} : t.contains k = true ↔ k ∈ t
-/
#guard_msgs in
#check DTreeMap.contains_iff_mem

-- I like what `[grind _=_]` does here!
/--
info: DTreeMap.contains_iff_mem: [@DTreeMap.contains #4 #3 #2 #1 #0, true]
---
info: DTreeMap.contains_iff_mem: [@Membership.mem #4 (@DTreeMap _ #3 #2) _ #1 #0]
-/
#guard_msgs in
attribute [grind? _=_] DTreeMap.contains_iff_mem

-- Similarly for every other `contains_iff_mem` we encounter (`List`, `Array`, `Vector`, `HashSet`, `HashMap`, etc.)

-- But:

/--
info: Std.DHashMap.contains_iff_mem.{u, v} {α : Type u} {β : α → Type v} {x✝ : BEq α} {x✝¹ : Hashable α} {m : DHashMap α β}
  {a : α} : m.contains a = true ↔ a ∈ m
-/
#guard_msgs in
#check DHashMap.contains_iff_mem

-- Here the reverse direction of `[grind _=_]` gives a pattern than matches too often: `@Membership.mem #5 _ _ #1 #0`.
/--
info: DHashMap.contains_iff_mem: [@DHashMap.contains #5 #4 #3 #2 #1 #0, true]
---
info: DHashMap.contains_iff_mem: [@Membership.mem #5 _ _ #1 #0]
-/
#guard_msgs in
attribute [grind? _=_] DHashMap.contains_iff_mem

-- We can do this manually with
grind_pattern DHashMap.contains_iff_mem => @Membership.mem α (DHashMap α β) _ m a
