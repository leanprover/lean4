set_option autoImplicit false -- For compatibility with downstream projects, so we can retest after Mathlib.
set_option relaxedAutoImplicit false

open List

variable {α : Type _}
variable {x y z : α}
variable (l l₁ l₂ l₃ : List α)

variable (L₁ L₂ : List (List α))

variable {β : Type _}
variable {f g : α → β}

variable {γ : Type _}
variable {f' : β → γ}

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

#check_simp [x, y, x, y][0] ~> x
#check_simp [x, y, x, y][1] ~> y
#check_simp [x, y, x, y][2] ~> x
#check_simp [x, y, x, y][3] ~> y

#check_simp [x, y, x, y][0]? ~> some x
#check_simp [x, y, x, y][1]? ~> some y
#check_simp [x, y, x, y][2]? ~> some x
#check_simp [x, y, x, y][3]? ~> some y

/-! ### get, get!, get?, getD -/

/-! ### getLast, getLast!, getLast?, getLastD -/

/-! ## Head and tail -/

/-! ### head, head!, head?, headD -/

#check_simp l.headD x ~> l.head?.getD x

#check_simp l.head? = none ~> l = []

/-! ### tail!, tail?, tailD -/

/-! ## Basic operations -/

/-! ### map -/

#check_simp l.map id ~> l
#check_simp l.map (fun x => x) ~> l
#check_simp [].map f ~> []
#check_simp [x].map f ~> [f x]

#check_simp map f l = map g l ~> ∀ a ∈ l, f a = g a
variable (l : List Nat) in
#check_simp map (· + 1) l = map (·.succ) l ~> True
variable (l : List Nat) in
#check_simp map (0 * ·) l ~> map (fun _ => 0) l
variable (l : List String) in
#check_simp map (fun s => s ++ s) ("a" :: l) ~> "aa" :: map (fun s => s ++ s) l

#check_simp l.map f = [] ~> l = []

variable (w : l ≠ []) in
#check_simp head (l.map f) (by simpa) ~> f (head l (by simpa))
variable (l : List String) in
#check_simp head (("a" :: l).map fun s => s ++ s) (by simp) ~> "aa"

variable (w : l ≠ []) in
#check_simp getLast (l.map f) (by simpa) ~> f (getLast l (by simpa))

#check_simp (l₁ ++ l₂).map f ~> l₁.map f ++ l₂.map f
#check_simp (l.map f).map f' ~> l.map (f' ∘ f)
#check_simp (concat l x).map f ~> map f l ++ [f x]

variable (L : List (List α)) in
#check_simp L.join.map f ~> (L.map (map f)).join
#check_simp [l₁, l₂].join.map f ~> map f l₁ ++ map f l₂

#check_simp l.map (Function.const α "1") ~> replicate l.length "1"
#check_simp [x, y].map (Function.const α "1") ~> ["1", "1"]

#check_simp l.reverse.map f ~> (l.map f).reverse

#check_simp (l.take 3).map f ~> (l.map f).take 3
#check_simp (l.drop 3).map f ~> (l.map f).drop 3

#check_simp l.dropLast.map f ~> (l.map f).dropLast

variable (p : β → Bool) in
#check_simp (l.map f).find? p ~> (l.find? (p ∘ f)).map f

/-! ### filter -/

/-! ### filterMap -/

/-! ### append -/

variable (w : l₁ ≠ []) in
#check_tactic head (l₁ ++ l₂) (by simp_all) ~> head l₁ w by simp_all

#check_simp (l₁ ++ l₂).head? ~> l₁.head?.or l₂.head?
#check_simp (l₁ ++ l₂).getLast? ~> l₂.getLast?.or l₁.getLast?

/-! ### concat -/

/-! ### join -/

#check_simp (L₁ ++ L₂).join ~> L₁.join ++ L₂.join

/-! ### bind -/

/-! ### replicate -/

#check_simp replicate 0 x ~> []
#check_simp replicate 1 x ~> [x]
#check_simp replicate 5 x ~> [x, x, x, x, x]

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

variable (h : n < m) (w) in
#check_tactic (replicate m x)[n]'w ~> x by simp [h]

variable (h : n < m) in
#check_tactic (replicate m x)[n]? ~> some x by simp [h]

#check_simp (replicate 7 x)[5] ~> x

#check_simp (replicate 7 x)[5]? ~> some x

variable (w : replicate n x ≠ []) in
#check_tactic (replicate n x).head w ~> x by simp_all

variable (w : replicate n x ≠ []) in
#check_tactic (replicate n x).getLast w ~> x by simp_all

-- injectivity

#check_simp replicate 3 x = replicate 7 x ~> False
#check_simp replicate 3 x = replicate 3 y ~> x = y
#check_simp replicate 3 "1" = replicate 3 "1" ~> True
#check_simp replicate n x = replicate m y ~> n = m ∧ (n = 0 ∨ x = y)

-- append

#check_simp replicate n x ++ replicate m x ~> replicate (n + m) x

-- map

#check_simp (replicate n "x").map (fun s => s ++ s) ~> replicate n "xx"

-- filter

#check_simp (replicate n [1]).filter (fun s => s.length = 1) ~> replicate n [1]
#check_simp (replicate n [1]).filter (fun s => s.length = 2) ~> []

-- filterMap

#check_simp (replicate n [1]).filterMap (fun s => if s.length = 1 then some s else none) ~> replicate n [1]
#check_simp (replicate n [1]).filterMap (fun s => if s.length = 2 then some s else none) ~> []

-- join

#check_simp (replicate n (replicate m x)).join ~> replicate (n * m) x
#check_simp (replicate 1 (replicate m x)).join ~> replicate m x
#check_simp (replicate n (replicate 1 x)).join ~> replicate n x
#check_simp (replicate n (replicate 0 x)).join ~> []
#check_simp (replicate 0 (replicate m x)).join ~> []
#check_simp (replicate 0 (replicate 0 x)).join ~> []

-- isEmpty

#check_simp (replicate (n + 1) x).isEmpty ~> false
#check_simp (replicate 0 x).isEmpty ~> true
variable (h : ¬ n = 0) in -- It would be nice if this also worked with `h : 0 < n`
#check_tactic (replicate n x).isEmpty ~> false by simp [h]

-- reverse

#check_simp (replicate n x).reverse ~> replicate n x

-- dropLast

#check_simp (replicate 0 x).dropLast ~> []
#check_simp (replicate n x).dropLast ~> replicate (n-1) x
#check_simp (replicate (n+1) x).dropLast ~> replicate n x

-- isPrefixOf

variable [BEq α] [LawfulBEq α] in
#check_simp isPrefixOf [x, y, x] (replicate n x) ~> decide (3 ≤ n) && y == x

attribute [local simp] isPrefixOf_cons₂ in
variable [BEq α] [LawfulBEq α] in
#check_simp isPrefixOf [x, y, x] (replicate (n+3) x) ~> y == x

-- isSuffixOf

variable [BEq α] [LawfulBEq α] in
#check_simp isSuffixOf [x, y, x] (replicate n x) ~> decide (3 ≤ n) && y == x

-- rotateLeft

#check_simp (replicate n x).rotateLeft m ~> replicate n x

-- rotateRight

#check_simp (replicate n x).rotateRight m ~> replicate n x

-- replace

variable [BEq α] [LawfulBEq α] in
#check_simp (replicate (n+1) x).replace x y ~> y :: replicate n x

#check_simp (replicate n "1").replace "2" "3" ~> (replicate n "1")

-- insert

variable [BEq α] [LawfulBEq α] (h : 0 < n) in
#check_tactic (replicate n x).insert x ~> replicate n x by simp [h]

#check_simp (replicate n "1").insert "2" ~> "2" :: replicate n "1"

-- erase

variable [BEq α] [LawfulBEq α] in
#check_simp (replicate (n+1) x).erase x ~> replicate n x

#check_simp (replicate n "1").erase "2" ~> replicate n "1"

-- find?

#check_simp (replicate (n+1) x).find? (fun _ => true) ~> some x
#check_simp (replicate (n+1) x).find? (fun _ => false) ~> none

variable {p : α → Bool} (w : p x) in
#check_tactic (replicate (n+1) x).find? p ~> some x by simp [w]
variable {p : α → Bool} (w : ¬ p x) in
#check_tactic (replicate (n+1) x).find? p ~> none by simp [w]

variable (h : 0 < n) in
#check_tactic (replicate n x).find? (fun _ => true) ~> some x by simp [h]
variable (h : 0 < n) in
#check_tactic (replicate n x).find? (fun _ => false) ~> none by simp [h]

variable {p : α → Bool} (w : p x) (h : 0 < n) in
#check_tactic (replicate n x).find? p ~> some x by simp [w, h]
variable {p : α → Bool} (w : ¬ p x) (h : 0 < n) in
#check_tactic (replicate n x).find? p ~> none by simp [w, h]

-- findSome?

#check_simp (replicate (n+1) x).findSome? (fun x => some x) ~> some x
#check_simp (replicate (n+1) x).findSome? (fun _ => (none : Option β)) ~> none

variable {f : α → Option β} (w : (f x).isSome) in
#check_tactic (replicate (n+1) x).findSome? f ~> f x by simp [w]
variable {f : α → Option β} (w : (f x).isNone) in
#check_tactic (replicate (n+1) x).findSome? f ~> none by simp_all [w]

variable (h : 0 < n) in
#check_tactic (replicate n x).findSome? (fun x => some x) ~> some x by simp [h]
variable (h : 0 < n) in
#check_tactic (replicate n x).findSome? (fun _ => (none : Option β)) ~> none by simp [h]

variable {f : α → Option β} (w : (f x).isSome) (h : 0 < n) in
#check_tactic (replicate n x).findSome? f ~> f x by simp [w, h]
variable {f : α → Option β} (w : (f x).isNone) (h : 0 < n) in
#check_tactic (replicate n x).findSome? f ~> none by simp_all [w, h]

-- lookup

variable [BEq α] [LawfulBEq α] in
#check_simp (replicate (n+1) (x, y)).lookup x ~> some y

variable [BEq α] [LawfulBEq α] (h : 0 < n) in
#check_tactic (replicate n (x, y)).lookup x ~> some y by simp [h]

#check_simp (replicate n ("1", "2")).lookup "3" ~> none

-- zip

#check_simp (replicate n x).zip (replicate n y) ~> replicate n (x, y)
#check_simp (replicate n x).zip (replicate m y) ~> replicate (min n m) (x, y)
variable (h : n ≤ m) in
#check_tactic (replicate n x).zip (replicate m y) ~> replicate n (x, y) by simp [h, Nat.min_eq_left]

-- zipWith
section
variable (f : α → α → α)

#check_simp zipWith f (replicate n x) (replicate n y) ~> replicate n (f x y)
#check_simp zipWith f (replicate n x) (replicate m y) ~> replicate (min n m) (f x y)
variable (h : n ≤ m) in
#check_tactic zipWith f (replicate n x) (replicate m y) ~> replicate n (f x y) by simp [h, Nat.min_eq_left]

-- unzip
#check_simp unzip (replicate n (x, y)) ~> (replicate n x, replicate n y)

-- min?

-- Note this relies on the fact that we do not have `replicate_succ` as a `@[simp]` lemma
#check_simp (replicate (n+1) 7).min? ~> some 7

variable (h : 0 < n) in
#check_tactic (replicate n 7).min? ~> some 7 by simp [h]

-- max?

-- Note this relies on the fact that we do not have `replicate_succ` as a `@[simp]` lemma
#check_simp (replicate (n+1) 7).max? ~> some 7

variable (h : 0 < n) in
#check_tactic (replicate n 7).max? ~> some 7 by simp [h]

end

/-! ### reverse -/

variable (p : α → Bool) in
#check_simp (l.reverse.filter p) ~> (l.filter p).reverse

variable (f : α → Option β) in
#check_simp (l.reverse.filterMap f) ~> (l.filterMap f).reverse

#check_simp l.reverse.head? ~> l.getLast?
#check_simp l.reverse.getLast? ~> l.head?

variable (h : l.reverse ≠ []) in
#check_simp l.reverse.head h ~> l.getLast (by simp_all)

variable (h : l.reverse ≠ []) in
#check_simp l.reverse.getLast h ~> l.head (by simp_all)

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


/-! ## Pairwise and Nodup -/

/-! ### Pairwise -/
section Pairwise
variable (R : α → α → Prop)
#check_simp Pairwise R [] ~> True
#check_simp Pairwise R (x :: l) ~> (∀ (a' : α), a' ∈ l → R x a') ∧ Pairwise R l
#check_simp Pairwise R [x, y, z] ~> (R x y ∧ R x z) ∧ R y z

#check_simp Pairwise R (replicate n x) ~> n ≤ 1 ∨ R x x
#check_simp Pairwise R (replicate 1 x) ~> True
#check_simp Pairwise R (replicate (n+2) x) ~> R x x
#check_simp Pairwise (· < ·) (replicate 2 m) ~> False
#check_simp Pairwise (· < ·) (replicate n m) ~> n ≤ 1
#check_simp Pairwise (· < ·) (replicate (n + 2) m) ~> False
#check_simp Pairwise (· = ·) (replicate 2 m) ~> True
#check_simp Pairwise (· = ·) (replicate n m) ~> True

end Pairwise

/-! ### Nodup -/

#check_simp Nodup [] ~> True
#check_simp Nodup (x :: l) ~> ¬x ∈ l ∧ l.Nodup
#check_simp Nodup [x, y, z] ~> (¬x = y ∧ ¬x = z) ∧ ¬y = z

#check_simp Nodup (replicate (n+2) x) ~> False
#check_simp Nodup (replicate 2 x) ~> False

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

/-! ### min? -/

/-! ### max? -/

/-! ## Monadic operations -/
attribute [local simp] Id.run in
#check_simp
  (Id.run do
    let mut s := 0
    for i in [1,2,3,4] do
      s := s + i
    pure s) ~> 10

attribute [local simp] Id.run in
#check_simp
  (Id.run do
    let mut s := 0
    for h : i in [1,2,3,4] do
      s := s + i
    pure s) ~> 10

attribute [local simp] Id.run in
variable (l : List α) (k m : Nat) in
#check_simp
  (Id.run do
    let mut x := m
    for _ in l do
      x := x + k
    pure x) ~> m + k * l.length

/-! ### mapM -/

/-! ### forM -/
