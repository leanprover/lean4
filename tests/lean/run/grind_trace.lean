module
reset_grind_attrs%

attribute [grind =] List.length_cons
attribute [grind =] List.getElem?_eq_getElem
attribute [grind =] List.length_replicate
attribute [grind =] List.getElem_replicate
attribute [grind =] List.getElem?_eq_none
attribute [grind =] List.getElem?_eq_some_iff
attribute [grind =] getElem!_pos

attribute [grind =] Option.map_some Option.map_none
attribute [grind =] List.getElem?_map
attribute [grind =] List.getElem?_replicate

attribute [grind =] List.getLast?_eq_some_iff
attribute [grind ←] List.mem_concat_self

attribute [grind =] List.getElem_cons_zero in
attribute [grind =] List.getElem?_cons_zero in

/--
info: Try these:
  [apply] grind only [= List.getElem?_replicate]
  [apply] grind => instantiate only [= List.getElem?_replicate]
-/
#guard_msgs (info) in
theorem getElem?_replicate' : (List.replicate n a)[m]? = if m < n then some a else none := by
  grind?

/--
info: Try these:
  [apply] grind only [= List.length_cons]
  [apply] grind => instantiate only [= List.length_cons]
-/
#guard_msgs (info) in
example : 0 < (x :: t).length := by
  grind?

attribute [grind ext] List.ext_getElem?
/--
info: Try these:
  [apply] grind only [= List.getElem?_replicate, = List.getElem?_map, = List.getElem?_eq_none,
    = List.getElem?_eq_getElem, = List.length_replicate, = List.getElem?_eq_some_iff, = Option.map_some,
    = Option.map_none, #648a, #bb68, #a564]
  [apply] grind only [= List.getElem?_replicate, = List.getElem?_map, = List.getElem?_eq_none,
    = List.getElem?_eq_getElem, = List.length_replicate, = List.getElem?_eq_some_iff, = Option.map_some,
    = Option.map_none]
  [apply] grind =>
    cases #648a
    instantiate only [= List.getElem?_replicate, = List.getElem?_map, = List.getElem?_eq_none,
      = List.getElem?_eq_getElem]
    instantiate only [= List.getElem?_replicate, = List.getElem?_eq_none, = List.getElem?_eq_getElem,
      = List.length_replicate]
    instantiate only [= List.length_replicate]
    cases #bb68
    · instantiate only [= List.getElem?_eq_some_iff]
      cases #a564
      · instantiate only [= Option.map_some]
      · instantiate only [= Option.map_none]
    · instantiate only [= Option.map_some]
-/
#guard_msgs (info) in
theorem map_replicate' : (List.replicate n a).map f = List.replicate n (f a) := by
  grind?

/--
info: Try these:
  [apply] grind only [= List.getLast?_eq_some_iff, ← List.mem_concat_self, #1ecf]
  [apply] grind only [= List.getLast?_eq_some_iff, ← List.mem_concat_self]
  [apply] grind =>
    instantiate only [= List.getLast?_eq_some_iff]
    cases #1ecf <;> instantiate only [← List.mem_concat_self]
-/
#guard_msgs (info) in
theorem mem_of_getLast?_eq_some' {xs : List α} {a : α} (h : xs.getLast? = some a) : a ∈ xs := by
  grind?

@[expose] public def f : Nat → Nat
  | 0 => 1
  | _ => 2

/--
info: Try these:
  [apply] grind only
  [apply] grind => instantiate only
-/
#guard_msgs (info) in
example : x = 0 → f x = 1 := by
  unfold f
  grind? -- should not include match equations

attribute [grind] f

/--
info: Try these:
  [apply] grind only [f]
  [apply] grind => instantiate only [f]
-/
#guard_msgs (info) in
example : x = 0 → f x = 1 := by
  grind? [f]

opaque g : Nat → Nat

theorem gthm : g (g x) = g x := sorry

grind_pattern gthm => g (g x)

/--
info: Try these:
  [apply] grind only [usr gthm]
  [apply] grind => instantiate only [usr gthm]
-/
#guard_msgs (info) in
example : g (g (g x)) = g x := by
  grind?

/--
error: `And` is marked as a built-in case-split for `grind` and cannot be erased
-/
#guard_msgs (error) in
attribute [-grind] And

/--
error: `And` is marked as a built-in case-split for `grind` and cannot be erased
-/
#guard_msgs (error) in
example : p ∧ q → p := by
  grind [-And]

example : (List.replicate n a)[m]? = if m < n then some a else none := by
  grind?

reset_grind_attrs%

set_option warn.sorry false

/--
info: Try this:
  [apply] grind => sorry
-/
#guard_msgs in
example : (List.replicate n a)[m]? = if m < n then some a else none := by
  grind?
