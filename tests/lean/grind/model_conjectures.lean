attribute [grind] Vector.getElem_swap_of_ne

/- This fails, but after obtaining the cutsat model:
```
  [cutsat] Assignment satisfying linear contraints ▼
    [assign] i := 2
    [assign] n := 3
    [assign] j := 1
    [assign] k := 0
```
it would be reasonable to look at the asserted fact
```
¬k = i → ¬k = j → (as.swap i j ⋯ ⋯)[k] = as[k]
```
and conjecture that `¬k = i` is true, and derive a proof for this from cutsat.
-/
example (hi : i < n) (hj : j < i) (hk : k < j) (as : Vector α n) (p : α → Prop) (h : p as[k]) :
    p (as.swap i j)[k] := by
  grind

/- Similarly here, we fail with the asserted facts (among others):
```
    [prop] i ≤ j
    [prop] ¬p i
    [prop] i + 1 ≤ j → p i
    [prop] ¬j = i
```
and the cutsat model:
```
  [cutsat] Assignment satisfying linear contraints ▼
    [assign] j := 1
    [assign] i := 0
```
At this point it would be reasonable to conjecture that `i + 1 ≤ j`.
-/
example (p : Nat → Prop) (h : p j) (h' : ∀ i, i < j → p i) : ∀ i, i < j + 1 → p i := by grind
