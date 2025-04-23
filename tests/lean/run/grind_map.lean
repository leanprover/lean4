import Std.Data.HashMap
import Std.Data.DHashMap

set_option grind.warning false

open Std

variable [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α ]

example : (∅ : DHashMap α β).isEmpty := by grind
example (m : DHashMap α β) (h : m = ∅): m.isEmpty := by grind

example : (((∅ : HashMap Nat Nat).insert 3 6).insert 4 7).contains 3 := by grind

example : (((∅ : HashMap Nat Nat).insert 3 6).insert 4 7).contains 9 == false := by grind

example (m : HashMap Nat Nat) (h : m.contains 3) : (m.erase 2).contains 3 := by grind
example (m : HashMap Nat Nat) (h : (m.erase 2).contains 3) : m.contains 3 := by grind
example (m : HashMap Nat Nat) : (m.erase 3).contains 3 = false := by grind
example (m : HashMap Nat Nat) (h : m.contains 3 = false) : (m.erase 2).contains 3 = false := by grind

-- A grind bug!
-- example (m : HashMap Nat Nat) : ((m.insert 1 2).insert 3 4).size ≤ m.size := by grind

attribute [grind] Option.pmap_eq_map

-- This probably should be in the library to begin with.
theorem getElem?_map'
  {m : HashMap α β} {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.map (f k) := by
  grind

-- Do we want this?
example (m : HashMap Nat Nat) (h : m.isEmpty) : m[3]? = none := by grind [HashMap.getElem?_of_isEmpty]

example : (((∅ : HashMap Nat Nat).insert 3 6).erase 4)[3]? = some 6 := by
  grind

attribute [grind] id

attribute [grind] HashMap.getElem?_eq_some_getElem -- Do we do this for list?
attribute [grind] Option.isSome_none Option.isSome_some Option.isNone_none Option.isNone_some

example (m : HashMap Nat Nat) : ((m.alter 5 id).erase 7).size ≥ m.size - 1 := by grind

open scoped HashMap

attribute [grind] Option.pfilter_eq_filter

-- attribute [ext, grind ext] HashMap.Equiv.of_forall_getElem?_eq
attribute [grind] HashMap.Equiv.of_forall_getElem?_eq

example (m : HashMap Nat Nat) :
    (m.insert 1 2).filter (fun k v => k > 1000) ~m m.filter fun k v => k > 1000 := by
  -- apply HashMap.Equiv.of_forall_getElem?_eq
  grind -- Aggressively abstracting proofs means we can't tell when an argument is unused.


example (m : HashMap Nat Nat) :
    (((m.insert 1 2).insert 3 4).insert 5 6).filter (fun k v => k > 6) ~m m.filter fun k v => k > 6 := by
  apply HashMap.Equiv.of_forall_getElem?_eq
  grind (gen := 10)


#exit

* Push the `grind_hashmap_list_issue` branch, and tell Leo about it.
* Push the `grind_getKey_eq` branch, and tell Leo about it.
* Push the branch `findrev` and merge it
* Push the branch `eraseDupsBy` and merge it


I've been looking at adding `@[grind]` annotations to the HashMap/TreeMap family, and now have quite a number of questions about the API.

(I'll post questions separately. If anyone would like to claim something and do it, please emoji it with :working on it:. If you approve of the change without wanting to work on it in the short term, a +1. Appropriate emojis or replies for any other reactions! :-)

* I'm surprised that we don't set up simp lemmas to rewrite `m[k]!` and `m.getD k d` in terms of `m[k]?`, and then avoid giving much API for these functions. (This is what I did with `List` etc.) I appreciate it's nice to have the theorems about these functions, but I'd argue it's nicer for the user to see these functions as little as possible.

* Similarly for simping `getKeyD` and `getKey!` away in terms of `getKey?`. (I'd be further tempted to simp away `getKey` as well, but for parity with `xs[i]?` and `xs[i]`, on balance I think it's worth keeping.)

* `get_getKey?` should be `@[simp]`.

* Can `contains_eq_isSome_getElem?` and `contains_eq_isSome_getKey?` be flipped, and made into `@[simp]` lemmas? (I would like the flipped versions for `grind`, too.)

* Statement of `getKey_insert` is incorrect. (TODO: add `@[grind]` when fixed)

* I think `insertMany_cons` and `ofList_cons` should be `@[simp]` lemmas, but don't mind. They will be `grind _=_` lemmas.

* There are lots of conditional lemmas about `(m.insertMany l)[k]?`, but the unconditional formula is missing. I think it's important that we always have these, even when the right hand side is complicated. It helps with automation / mindless proofs to always just be able to blast through things. There are many ways to formulate the RHS but one is:

```
theorem getElem?_insertMany_list [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} :
    (insertMany m l)[k]? =
      (l.findRevSome? (fun ⟨a, b⟩ => if a == k then some b else none)).or m[k]? := by
  induction l generalizing m with
  | nil => simp
  | cons x l ih =>
    rcases x with ⟨a, b⟩
    simp only [insertMany_cons, ih, List.filterMap_cons, getElem?_insert]
    by_cases h : a == k <;> simp [h, List.getLast?_cons]
```
(more natural would be to use `List.findRevSome?`, implemented on branch `findrev`)

* The same applies to `(m.insertMany l).getKey?`.

* I'm not sure about `size_insertMany_list`: somewhat painful to state, I guess:

```
theorem size_insertMany_list' [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany m l).size =
      ((l.eraseDupsBy (·.1 == ·.1)).filter fun ⟨a, b⟩ => ¬ a ∈ m).length + m.size := sorry
 ```
using the recently added `eraseDupsBy`.


* Similarly `getElem?_ofList` needs an unconditional statement. (And the same concern for `size_ofList` as for `size_insertMany_list` above.)

* If would be good to have lemmas relating `ofList` and `insertMany`? (Including the `ofList_append` lemma.) I don't see these?

* `Equiv.getElem?_eq` has the wrong statement

* `contains_filterMap` is missing (also `contains_filter`)

* We have `theorem getKey_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey k h = k`, but apparently not `theorem getKey?_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey? k h = some k`.

* I'm sad that we have `getElem?_map_of_getKey?_eq_some` but not the version of `getElem?_map` that assumes everything is lawful and has the nice RHS:
```
theorem getElem?_map'
  {m : HashMap α β} {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.map (f k) := by grind
```
Indeed I'd argue that we want this "friendly" version to occupy the obvious name, and the stronger but more finicky current one to have to hide behind the prime!
