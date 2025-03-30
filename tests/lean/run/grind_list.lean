reset_grind_attrs%

namespace List

attribute [local grind =] List.length_cons in
example : 0 < (x :: t).length := by grind

attribute [local grind →] getElem?_eq_getElem in
attribute [local grind =] length_replicate in
attribute [local grind =] getElem_replicate in
attribute [local grind =] getElem?_eq_none in
theorem getElem?_replicate' : (replicate n a)[m]? = if m < n then some a else none := by
  grind

attribute [local grind =] getElem?_eq_some_iff in
attribute [local grind =] getElem!_pos in
theorem getElem!_of_getElem?' [Inhabited α] :
    ∀ {l : List α} {i : Nat}, l[i]? = some b → l[i]! = b := by
  grind

attribute [local grind =] Option.map_some' Option.map_none' in
attribute [local grind =] getElem?_map in
attribute [local grind =] getElem?_replicate in
theorem map_replicate' : (replicate n a).map f = replicate n (f a) := by
  grind?

#print map_replicate'

attribute [local grind =] getLast?_eq_some_iff in
attribute [local grind] mem_concat_self in
theorem mem_of_getLast?_eq_some' {xs : List α} {a : α} (h : xs.getLast? = some a) : a ∈ xs := by
  grind

attribute [local grind =] getElem_cons_zero in
attribute [local grind =] getElem?_cons_zero in
example (h : (a :: t)[0]? = some b) : (a :: t)[0] = b := by
  grind
