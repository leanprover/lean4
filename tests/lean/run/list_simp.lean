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

#check_simp y ∈ (replicate 7 x) ~> y = x

-- It makes me very sad that the equality ends up the other way here.
-- This will take some fixing!
variable [BEq α] in
#check_simp (replicate 7 x).contains y ~> x == y

-- And adding `LawfulBEq` switches it back the other way!
variable [BEq α] [LawfulBEq α] in
#check_simp (replicate 7 x).contains y ~> y == x

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
