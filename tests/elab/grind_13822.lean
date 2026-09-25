/-!
Regression test for #13822: `grind => seq` used to fail to parse inside a `match`
alternative because the optional goal-filter `|` of a `grind` step consumed the `|`
starting the next `match` alternative. The `|` must now be indented past the start
of the `grind` sequence.
-/

def x := 1

example : x = 1 := by
  match true with
  | true => grind => instantiate only [x]
  | false => rfl

example : x = 1 := by
  match true with
  | true => rfl
  | false => grind => instantiate only [x]

-- `first` alternatives separated by `|` used to be consumed as well.
example : x = 1 := by
  first
  | grind => instantiate only [x]
  | rfl

-- Goal-state filters on the same line as the step still parse.
example : x = 1 := by
  match true with
  | true => grind => instantiate only [x] | gen ≤ 1
  | false => rfl

-- A bare trailing `|` on the same line still parses.
example : x = 1 := by
  match true with
  | true => grind => instantiate only [x] |
  | false => rfl
