inductive Palindrome : List α → Prop where
  | nil      : Palindrome []
  | single   : (a : α) → Palindrome [a]
  | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])

attribute [grind] Palindrome
attribute [grind =] List.cons_append List.nil_append List.reverse_cons List.reverse_append List.reverse_nil List.append_cancel_right_eq List.reverse_reverse

theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse := by
  induction h <;> grind

theorem reverse_eq_of_palindrome (h : Palindrome as) : as.reverse = as := by
  induction h <;> grind

example (h : Palindrome as) : Palindrome as.reverse := by
  grind [reverse_eq_of_palindrome]

def List.last : (as : List α) → as ≠ [] → α
  | [a],         _ => a
  | _::a₂:: as, _ => (a₂::as).last (by grind)

@[simp, grind] theorem List.dropLast_append_last (h : as ≠ []) : as.dropLast ++ [as.last h] = as := by
  match as with
  | [] => grind
  | [a] => grind [last, dropLast]
  | a₁ :: a₂ :: as =>
    have := dropLast_append_last (as := a₂ :: as) (by grind)
    grind [last, dropLast]

theorem List.palindrome_ind (motive : List α → Prop)
    (h₁ : motive [])
    (h₂ : (a : α) → motive [a])
    (h₃ : (a b : α) → (as : List α) → motive as → motive ([a] ++ as ++ [b]))
    (as : List α)
    : motive as :=
  match as with
  | []  => h₁
  | [a] => h₂ a
  | a₁::a₂::as' =>
    have ih := palindrome_ind motive h₁ h₂ h₃ (a₂::as').dropLast
    have : [a₁] ++ (a₂::as').dropLast ++ [(a₂::as').last (by grind)] = a₁::a₂::as' := by grind
    by grind
termination_by as.length

theorem List.palindrome_of_eq_reverse (h : as.reverse = as) : Palindrome as := by
  induction as using palindrome_ind <;> grind

def List.isPalindrome [DecidableEq α] (as : List α) : Bool :=
    as.reverse = as

/-!
It is straightforward to prove that `isPalindrome` is correct using the previously proved theorems.
-/
theorem List.isPalindrome_correct [DecidableEq α] (as : List α) : as.isPalindrome ↔ Palindrome as := by
  -- TODO: add support for `decide`
  grind [isPalindrome, palindrome_of_eq_reverse, reverse_eq_of_palindrome]

#eval [1, 2, 1].isPalindrome
#eval [1, 2, 3, 1].isPalindrome

example : [1, 2, 1].isPalindrome := rfl
example : [1, 2, 2, 1].isPalindrome := rfl
example : ![1, 2, 3, 1].isPalindrome := rfl
