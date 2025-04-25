/-!
This file contains notes about further `grind` attributes for `Option`.

-/

attribute [grind] Option.some_get Option.get_some
attribute [grind] Option.map_map -- `[grind _=_]`?
attribute [grind] Option.get_map -- ??
attribute [grind] Option.map_id_fun Option.map_id_fun'
attribute [grind] Option.all_guard Option.any_guard
attribute [grind] Option.bind_map Option.map_bind
attribute [grind] Option.join_map_eq_map_join
attribute [grind] Option.join_join -- `[grind _=_]`?
attribute [grind] Option.map_orElse

-- Look again at `Option.guard` lemmas, consider `bind_gaurd`.
-- Fix statement of `isSome_guard`, add `isNone_guard`

attribute [grind] Option.or_assoc -- unless `grind` gains native associativity support in the meantime!

-- attribute [grind] Option.none_beq_none -- warning: this generates just `none` as the pattern!
-- attribute [grind] Option.none_beq_some
-- attribute [grind] Option.some_beq_none -- warning: this generates just `some _` as the pattern!
-- attribute [grind] Option.some_beq_some

attribute [grind] Option.isSome_filter
attribute [grind] Option.get_filter Option.get_pfilter

attribute [grind] Option.map_pbind Option.pbind_map
attribute [grind] Option.map_pmap Option.pmap_map Option.elim_pmap

-- Lemmas about inequalities?

-- The `min_none_none` family of lemmas result in grind issues:
-- failed to synthesize instance when instantiating Option.min_none_none
--         Min α
