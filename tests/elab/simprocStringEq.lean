/-!
# Tests for the `String.simpEq` simproc
-/

@[simp] theorem String.toString_eq_self : toString s = s := rfl

/-!
Equality modulo associativity (`denote_eq`)
-/

variable (s t u : String) (c d c₁ c₂ c₃ c₄ : Char) (l l₁ l₂ : List Char)

open String

example : "" ++ s = s := by simp only [String.simpEq]
example : s ++ "" = s := by simp only [String.simpEq]
example : (s ++ t) ++ u = s ++ (t ++ u) := by simp only [String.simpEq]
example : s.push c = s ++ singleton c := by simp only [String.simpEq]
example : "".push c = singleton c := by simp only [String.simpEq]
example : (s ++ t).push c = s ++ t.push c := by simp only [String.simpEq]
example : ofList s.toList = s := by simp only [String.simpEq]
example : ofList (c :: l) = singleton c ++ ofList l := by simp only [String.simpEq]
example : ofList (l₁ ++ l₂) = ofList l₁ ++ ofList l₂ := by simp only [String.simpEq]
example : ofList [c] = singleton c := by simp only [String.simpEq]

example : singleton 'a' = "a" := by simp only [String.simpEq]
example : "a" ++ "b" = "ab" := by simp only [String.simpEq]
example : "a".push 'b' = "ab" := by simp only [String.simpEq]
example : ofList ['a', 'b'] = "ab" := by simp only [String.simpEq, -eq_self]

-- complex example
example : "a" ++ ofList ('b' :: 'c' :: l ++ [c]) ++ ((ofList l).push 'x' ++ singleton c ++ ofList s.toList ++ "y".push 'z') =
  "abc" ++ ofList l ++ singleton c ++ ofList l ++ "x" ++ singleton c ++ s ++ "yz" := by simp only [String.simpEq]

/-!
Translating string equality to character equalities (`denote_char_inj`)
-/

example : singleton c = singleton d ↔ c = d := by simp only [String.simpEq]
example : s.push c = s.push d ↔ c = d := by simp only [String.simpEq]
example : ofList [c₁, c₂] = ofList [c₃, c₄] ↔ c₁ = c₃ ∧ c₂ = c₄ := by simp only [String.simpEq]
example : ofList [c₁, c₂] = ofList [c₁, c₃] ↔ c₂ = c₃ := by simp only [String.simpEq]
example : ofList [c₁, c₂] = ofList [c₃, c₂] ↔ c₁ = c₃ := by simp only [String.simpEq]
example : singleton c = "a" ↔ c = 'a' := by simp only [String.simpEq]
example : "Hel" ++ singleton c ++ "o, world" ++ singleton d = "Hello, world!" ↔
    c = 'l' ∧ d = '!' := by simp only [String.simpEq]

/-!
Disproving equalities by cancelling characters on the left (`denote_ne_left`)
-/

example : "a" ++ s = "b" ++ t ↔ False := by simp only [String.simpEq]
example : "abc" ++ s = "abd" ++ t ↔ False := by simp only [String.simpEq]
example : s ++ singleton 'a' ++ ofList (l₁ ++ l₂ ++ t.toList) ++ "b" ++ u.push c =
    s.push 'a' ++ ofList l₁ ++ ofList l₂ ++ t ++ ofList ['a'] ++ "hello" ↔ False := by
  simp only [String.simpEq]

/-!
Disproving equalities by cancelling characters on the right (`denote_ne_right`)
-/

example : s ++ "a" = t ++ "b" ↔ False := by simp only [String.simpEq]
example : s ++ "cba" = t ++ "dba" ↔ False := by simp only [String.simpEq]
example : singleton c ++ u ++ "b" ++ ofList (t.toList ++ l₂ ++ l₁) ++ singleton 'a' ++ s =
    "olleh" ++ ofList ['a'] ++ t ++ ofList l₂ ++ ofList l₁ ++ singleton 'a' ++ s ↔ False := by
  simp only [String.simpEq]

/-!
Full generality: Splitting an equality into a new equality of strings and
character equalities (`denote_cancel`)
-/

example : s ++ t = s ++ u ↔ t = u := by simp only [String.simpEq]
example : s ++ u = t ++ u ↔ s = t := by simp only [String.simpEq]
example : s.push c = t.push d ↔ s = t ∧ c = d := by simp only [String.simpEq]
example : singleton c ++ s = singleton d ++ t ↔ c = d ∧ s = t := by simp only [String.simpEq]
example : s ++ t = s ↔ t = "" := by simp only [String.simpEq]
example : s ++ t = t ↔ s = "" := by simp only [String.simpEq]

example : "" ++ ("_" ++ s) = String.singleton c ++ t ↔ '_' = c ∧ s = t := by simp only [String.simpEq]

example : "Hello, " ++ s ++ "!" = "Hello, world!" ↔ s = "world" := by simp only [String.simpEq]
example : s.push c = "Test me" ↔ s = "Test m" ∧ c = 'e' := by simp only [String.simpEq]
example : singleton c ++ s = "Test me" ↔ c = 'T' ∧ s = "est me" := by simp only [String.simpEq]
