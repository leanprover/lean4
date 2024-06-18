open List

variable {α : Type _}
variable {x y : α}
variable (l l₁ l₂ l₃ : List α)

variable (m n : Nat)

/-! ## Preliminaries -/

/-! ### cons -/

/-! ### length -/

/-! ### L[i] and L[i]? -/

/-! ### mem -/

/-! ### set -/

/-! ### foldlM and foldrM -/

/-! ### foldl and foldr -/

/-! ### Equality -/

/-! ### Lexicographic order -/

/-! ## Getters -/

/-! ### get, get!, get?, getD -/

/-! ### getLast, getLast!, getLast?, getLastD -/

/-! ## Head and tail -/

/-! ### head, head!, head?, headD -/

/-! ### tail!, tail?, tailD -/

/-! ## Basic operations -/

/-! ### map -/

/-! ### filter -/

/-! ### filterMap -/

/-! ### append -/

/-! ### concat -/

/-! ### join -/

/-! ### bind -/

/-! ### replicate -/

-- `∈` and `contains

#check_simp y ∈ replicate 0 x ~> False

variable [BEq α] in
#check_simp (replicate 0 x).contains y ~> false

variable [BEq α] [LawfulBEq α] in
#check_simp (replicate 0 x).contains y ~> false

#check_simp y ∈ replicate 7 x ~> y = x

variable [BEq α] in
#check_simp (replicate 7 x).contains y ~> y == x

variable [BEq α] [LawfulBEq α] in
#check_simp (replicate 7 x).contains y ~> y == x

-- `getElem` and `getElem?`

variable (h : n < m) in
#check_tactic (replicate m x)[n] ~> x by simp [h]

variable (h : n < m) in
#check_tactic (replicate m x)[n]? ~> some x by simp [h]

#check_simp (replicate 7 x)[5] ~> x

-- fails, needs a simproc:
-- #check_simp (replicate 7 x)[5]? ~> some x -- gets stuck at `[x, x, x, x, x, x, x][5]?`

-- injectivity

#check_simp replicate 3 x = replicate 7 x ~> False
#check_simp replicate 3 x = replicate 3 y ~> x = y
#check_simp replicate 3 "1" = replicate 3 "1" ~> True
#check_simp replicate n x = replicate m y ~> n = m ∧ (n = 0 ∨ x = y)

#check_simp replicate n x ++ replicate m x ~> replicate (n + m) x

#check_simp (replicate n "x").map (fun s => s ++ s) ~> replicate n "xx"

-- Hmmm: metavariable handling bug in `#check_tactic`:
-- #check_tactic (replicate n "x").filter (fun s => s.length = 1) ~> replicate n "x" by simp [filter_replicate]

/-! ### reverse -/

/-! ## List membership -/

/-! ### elem / contains -/

/-! ## Sublists -/

/-! ### take and drop -/

/-! ### takeWhile and dropWhile -/

/-! ### partition -/

/-! ### dropLast  -/

/-! ### isPrefixOf -/

/-! ### isSuffixOf -/

variable [BEq α] in
#check_simp ([] : List α).isSuffixOf l ~> true

/-! ### rotateLeft -/

/-! ### rotateRight -/

/-! ## Manipulating elements -/

/-! ### replace -/

/-! ### insert -/

/-! ### erase -/

/-! ### find? -/

/-! ### findSome? -/

/-! ### lookup -/

/-! ## Logic -/

/-! ### any / all -/

/-! ## Zippers -/

/-! ### zip -/

/-! ### zipWith -/

/-! ### zipWithAll -/

/-! ## Ranges and enumeration -/

/-! ### enumFrom -/

/-! ### minimum? -/

/-! ### maximum? -/

/-! ## Monadic operations -/

/-! ### mapM -/

/-! ### forM -/
