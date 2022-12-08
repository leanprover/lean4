/-!
# Palindromes

Palindromes are lists that read the same from left to right and from right to left.
For example, `[a, b, b, a]` and `[a, h, a]` are palindromes.

We use an inductive predicate to specify whether a list is a palindrome or not.
Recall that inductive predicates, or inductively defined propositions, are a convenient
way to specify functions of type `... → Prop`.

This example is a based on an example from the book "The Hitchhiker's Guide to Logical Verification".
-/

inductive Palindrome : List α → Prop where
  | nil      : Palindrome []
  | single   : (a : α) → Palindrome [a]
  | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])

/-!
The definition distinguishes three cases: (1) `[]` is a palindrome; (2) for any element
`a`, the singleton list `[a]` is a palindrome; (3) for any element `a` and any palindrome
`[b₁, . . ., bₙ]`, the list `[a, b₁, . . ., bₙ, a]` is a palindrome.
-/

/-!
We now prove that the reverse of a palindrome is a palindrome using induction on the inductive predicate `h : Palindrome as`.
-/
theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse := by
  induction h with
  | nil => exact Palindrome.nil
  | single a => exact Palindrome.single a
  | sandwich a h ih => simp; exact Palindrome.sandwich _ ih

/-! If a list `as` is a palindrome, then the reverse of `as` is equal to itself. -/
theorem reverse_eq_of_palindrome (h : Palindrome as) : as.reverse = as := by
  induction h with
  | nil => rfl
  | single a => rfl
  | sandwich a h ih => simp [ih]

/-! Note that you can also easily prove `palindrome_reverse` using `reverse_eq_of_palindrome`. -/
example (h : Palindrome as) : Palindrome as.reverse := by
  simp [reverse_eq_of_palindrome h, h]

/-!
Given a nonempty list, the function `List.last` returns its element.
Note that we use `(by simp)` to prove that `a₂ :: as ≠ []` in the recursive application.
-/
def List.last : (as : List α) → as ≠ [] → α
  | [a],         _ => a
  | _::a₂:: as, _ => (a₂::as).last (by simp)

/-!
We use the function `List.last` to prove the following theorem that says that if a list `as` is not empty,
then removing the last element from `as` and appending it back is equal to `as`.
We use the attribute `@[simp]` to instruct the `simp` tactic to use this theorem as a simplification rule.
-/
@[simp] theorem List.dropLast_append_last (h : as ≠ []) : as.dropLast ++ [as.last h] = as := by
  match as with
  | [] => contradiction
  | [a] => simp_all [last, dropLast]
  | a₁ :: a₂ :: as =>
    simp [last, dropLast]
    exact dropLast_append_last (as := a₂ :: as) (by simp)

/-!
We now define the following auxiliary induction principle for lists using well-founded recursion on `as.length`.
We can read it as follows, to prove `motive as`, it suffices to show that: (1) `motive []`; (2) `motive [a]` for any `a`;
(3) if `motive as` holds, then `motive ([a] ++ as ++ [b])` also holds for any `a`, `b`, and `as`.
Note that the structure of this induction principle is very similar to the `Palindrome` inductive predicate.
-/
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
    have : [a₁] ++ (a₂::as').dropLast ++ [(a₂::as').last (by simp)] = a₁::a₂::as' := by simp
    this ▸ h₃ _ _ _ ih
termination_by _ as => as.length

/-!
We use our new induction principle to prove that if `as.reverse = as`, then `Palindrome as` holds.
Note that we use the `using` modifier to instruct the `induction` tactic to use this induction principle
instead of the default one for lists.
-/
theorem List.palindrome_of_eq_reverse (h : as.reverse = as) : Palindrome as := by
  induction as using palindrome_ind
  next   => exact Palindrome.nil
  next a => exact Palindrome.single a
  next a b as ih =>
    have : a = b := by simp_all
    subst this
    have : as.reverse = as := by simp_all
    exact Palindrome.sandwich a (ih this)

/-!
We now define a function that returns `true` iff `as` is a palindrome.
The function assumes that the type `α` has decidable equality. We need this assumption
because we need to compare the list elements.
-/
def List.isPalindrome [DecidableEq α] (as : List α) : Bool :=
    as.reverse = as

/-!
It is straightforward to prove that `isPalindrome` is correct using the previously proved theorems.
-/
theorem List.isPalindrome_correct [DecidableEq α] (as : List α) : as.isPalindrome ↔ Palindrome as := by
  simp [isPalindrome]
  exact Iff.intro (fun h => palindrome_of_eq_reverse h) (fun h => reverse_eq_of_palindrome h)

#eval [1, 2, 1].isPalindrome
#eval [1, 2, 3, 1].isPalindrome

example : [1, 2, 1].isPalindrome := rfl
example : [1, 2, 2, 1].isPalindrome := rfl
example : ![1, 2, 3, 1].isPalindrome := rfl
