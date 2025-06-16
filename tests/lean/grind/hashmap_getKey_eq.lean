import Std.Data.HashMap

reset_grind_attrs%
set_option grind.warning false

open Std
open scoped HashMap

attribute [grind]
  HashMap.getElem?_eq_some_getElem HashMap.getElem?_filter
  HashMap.getElem?_insert HashMap.getElem_insert HashMap.mem_insert
  HashMap.Equiv.of_forall_getElem?_eq
  HashMap.getKey_eq
  Option.pfilter_eq_filter

example (m : HashMap Nat Nat) :
    (m.insert 1 2).filter (fun k v => k > 1000) ~m m.filter fun k v => k > 1000 := by
  grind -- fails, but I'd like it to work!

-- One of the equivalence classes here is:
-- {(HashMap.filter (fun k v => decide (1001 ≤ k)) m)[w]?,
--   m[w]?.pfilter fun x h' => decide (1001 ≤ m.getKey w ⋯)}
-- What I would like to happen is `getKey_eq` fires,
-- replacing `m.getKey w ⋯` with `w`, and then `Option.pfilter_eq_filter` to fire
-- (now that the proof argument `h'` is not used.)
-- I'm not sure why this is not working, perhaps the proof abstraction `⋯`
-- is getting in the way?

-- Here's a similar example that *does* work, but where abstraction hasn't occurred.
example [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
  {m : HashMap α β} {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.map (f k) := by
  -- Fails, because we've left out the critical lemma `Option.pmap_eq_map`
  fail_if_success grind [HashMap.getElem?_map, HashMap.getKey_eq]
  -- We see a similar equivalence class
  -- {(HashMap.map f m)[k]?, Option.pmap (fun v h' => f (m.getKey k h') v) m[k]? ⋯}
  -- although this time `⋯` has not been abstracted.

  -- Now it works:
  grind [HashMap.getElem?_map, HashMap.getKey_eq, Option.pmap_eq_map]
