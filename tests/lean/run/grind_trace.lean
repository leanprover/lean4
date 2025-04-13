reset_grind_attrs%

attribute [grind =] List.length_cons
attribute [grind →] List.getElem?_eq_getElem
attribute [grind =] List.length_replicate
attribute [grind =] List.getElem_replicate
attribute [grind =] List.getElem?_eq_none
attribute [grind =] List.getElem?_eq_some_iff
attribute [grind =] getElem!_pos

attribute [grind =] Option.map_some Option.map_none
attribute [grind =] List.getElem?_map
attribute [grind =] List.getElem?_replicate

attribute [grind =] List.getLast?_eq_some_iff
attribute [grind] List.mem_concat_self

attribute [grind =] List.getElem_cons_zero in
attribute [grind =] List.getElem?_cons_zero in

/--
info: Try this: grind only [= List.getElem?_replicate, = List.getElem?_eq_none]
-/
#guard_msgs (info) in
theorem getElem?_replicate' : (List.replicate n a)[m]? = if m < n then some a else none := by
  grind?

/--
info: Try this: grind only [= List.length_cons]
-/
#guard_msgs (info) in
example : 0 < (x :: t).length := by
  grind?

/--
info: Try this: grind only [= Option.map_some, = Option.map_none, = List.getElem?_replicate, = List.getElem?_eq_some_iff, =
  List.getElem?_map, = List.getElem_replicate, = List.getElem?_eq_none, = List.length_replicate, →
  List.getElem?_eq_getElem]
-/
#guard_msgs (info) in
theorem map_replicate' : (List.replicate n a).map f = List.replicate n (f a) := by
  grind?

/-- info: Try this: grind only [List.mem_concat_self, = List.getLast?_eq_some_iff] -/
#guard_msgs (info) in
theorem mem_of_getLast?_eq_some' {xs : List α} {a : α} (h : xs.getLast? = some a) : a ∈ xs := by
  grind?

def f : Nat → Nat
  | 0 => 1
  | _ => 2

/--
info: Try this: grind only
-/
#guard_msgs (info) in
example : x = 0 → f x = 1 := by
  unfold f
  grind? -- should not include match equations

attribute [grind] f

/--
info: Try this: grind only [f]
-/
#guard_msgs (info) in
example : x = 0 → f x = 1 := by
  grind? [f]

opaque g : Nat → Nat

theorem gthm : g (g x) = g x := sorry

grind_pattern gthm => g (g x)

/--
info: Try this: grind only [usr gthm]
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

example : (List.replicate n a)[m]? = if m < n then some a else none := by
  fail_if_success grind?
  sorry
