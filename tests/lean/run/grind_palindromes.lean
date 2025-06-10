reset_grind_attrs%

attribute [grind cases] Or

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

@[grind] theorem List.last_cons (h₁ : as ≠ []) (h₂ : a :: as ≠ []): (a :: as).last h₂ = as.last h₁ := by
  grind [last.eq_def]

@[grind] theorem List.dropLast_append_last (h : as ≠ []) : as.dropLast ++ [as.last h] = as := by
   induction as, h using List.last.induct <;> grind [last, dropLast]

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

theorem List.isPalindrome_correct [DecidableEq α] (as : List α) : as.isPalindrome ↔ Palindrome as := by
  grind [isPalindrome, palindrome_of_eq_reverse, reverse_eq_of_palindrome]
