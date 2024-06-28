/-!
Testing for linter.constructorNameAsVariable

This linter checks warns when a bound variable's name is the name of a constructor of the variable's
type, which probably indicates a namespace mistake, but can be otherwise hard to find.

The linter is designed to interact well with the suggestions provided when a non-constructor is used
where a constructor would be expected in a pattern, so that users who don't know Lean namespaces
will be guided to the right qualified names. Thus, both are tested together here.
-/
set_option linter.unusedVariables false

inductive A where
  | x | y

-- Test that the linter works even in the presence of errors (making it useful for confused new
-- users)

/--
warning: Local variable 'x' resembles constructor 'A.x' - write '.x' (with a dot) or 'A.x' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
-/
#guard_msgs(drop error, warning) in
def f : A → Unit
  | x => _

-- Show that the linter also works when there are no errors
/--
warning: Local variable 'x' resembles constructor 'A.x' - write '.x' (with a dot) or 'A.x' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
-/
#guard_msgs(warning) in
def g : A → Unit
  | x => ()

-- Check that turning it off works
#guard_msgs in
set_option linter.constructorNameAsVariable false in
def g' : A → Unit
  | x => ()

-- Avoid false positives
#guard_msgs in
def h : A → Unit
  | z => ()

-- Check that it works for let-bindings
/--
warning: Local variable 'x' resembles constructor 'A.x' - write '.x' (with a dot) or 'A.x' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
---
warning: Local variable 'y' resembles constructor 'A.y' - write '.y' (with a dot) or 'A.y' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
-/
#guard_msgs in
def i (a : A × A) : Unit :=
  let (x, y) := a
  ()

/--
warning: Local variable 'x' resembles constructor 'A.x' - write '.x' (with a dot) or 'A.x' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
-/
#guard_msgs in
def i' : Unit :=
  let x : A := .x
  ()

-- Check that it works in tactic proofs
/--
warning: Local variable 'x' resembles constructor 'A.x' - write '.x' (with a dot) or 'A.x' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
-/
#guard_msgs in
theorem j (a : A ⊕ A) : True := by
  cases a with
  | inl x => trivial
  | inr z => trivial

-- Top-level names do not trigger the lint
#guard_msgs in
def x : A := A.x

/-! Test the interaction with the invalid match pattern error messages -/

/--
error: invalid pattern, constructor or constant marked with '[match_pattern]' expected

Suggestions:
  'Add.mk',
  'Alternative.mk',
  'AndOp.mk',
  'AndThen.mk',
  'Antisymm.mk',
  'Append.mk',
  'Applicative.mk',
  'Array.Mem.mk',
  'Array.mk',
  'BEq.mk',
   (or 201 others)
-/
#guard_msgs in
def ctorSuggestion1 (pair : α × β) : β :=
  match pair with
  | mk x y => y

-- This test is a realistic situation if a user doesn't know how Lean namespaces work
/--
error: invalid pattern, constructor or constant marked with '[match_pattern]' expected

Suggestion: 'List.cons' is similar
---
warning: Local variable 'nil' resembles constructor 'List.nil' - write '.nil' (with a dot) or 'List.nil' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
-/
#guard_msgs in
def ctorSuggestion2 (list : List α) : Nat :=
  match list with
  | nil => 0
  | cons x xs => 1 + ctorSuggestion2 xs

-- Adding another `cons` also adds a suggestion
inductive StringList : Type where
  | nil
  | cons (s : String) (ss : StringList)

/--
error: invalid pattern, constructor or constant marked with '[match_pattern]' expected

Suggestions: 'List.cons', 'StringList.cons'
---
warning: Local variable 'nil' resembles constructor 'List.nil' - write '.nil' (with a dot) or 'List.nil' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
-/
#guard_msgs in
def ctorSuggestion3 (list : List α) : Nat :=
  match list with
  | nil => 0
  | cons x xs => 1 + ctorSuggestion2 xs

-- There isn't always a suggestion to provide

/--
error: invalid pattern, constructor or constant marked with '[match_pattern]' expected
-/
#guard_msgs in
def ctorNoSuggestion (x : α) :=
  match x with
  | notAConstructor a b c => 42
