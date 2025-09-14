import Lean
/-!
# Tests of `pp.unicode` pretty printer option
-/

open Lean PrettyPrinter

/-!
Testing a notation with a `unicode` operator.

Respects the current setting of `pp.unicode` exactly.
-/
def And' := And

notation:35 x:36 unicode(" ∧' ", " /\\' ") y:35 => And' x y

/-- info: True ∧' False : Prop -/
#guard_msgs in #check True ∧' False

/-- info: True /\' False : Prop -/
#guard_msgs in set_option pp.unicode false in #check True ∧' False

/-- info: True✝ ∧' False✝ -/
#guard_msgs in #eval do ppTerm (← `(True ∧' False))
/-- info: True✝ ∧' False✝ -/
#guard_msgs in #eval do ppTerm (← `(True /\' False))
/-- info: True✝ /\' False✝ -/
#guard_msgs in set_option pp.unicode false in #eval do ppTerm (← `(True ∧' False))
/-- info: True✝ /\' False✝ -/
#guard_msgs in set_option pp.unicode false in #eval do ppTerm (← `(True /\' False))

/-!
Testing a notation with a `unicode` operator with `preserveForPP`.

Respects the current setting of `pp.unicode` *if* the underlying atom is in the unicode form.
The `notation` command creates a pretty printer using the ASCII form,
so this is only possible if a delaborator creates a syntax quotation with the unicode form.
-/
def And'' := And

notation:35 x:36 unicode(" ∧'' ", " /\\'' ", preserveForPP) y:35 => And'' x y

/-- info: True /\'' False : Prop -/
#guard_msgs in #check True ∧'' False

/-- info: True /\'' False : Prop -/
#guard_msgs in set_option pp.unicode false in #check True ∧'' False

/-- info: True✝ ∧'' False✝ -/
#guard_msgs in #eval do ppTerm (← `(True ∧'' False))
/-- info: True✝ /\'' False✝ -/
#guard_msgs in #eval do ppTerm (← `(True /\'' False))
/-- info: True✝ /\'' False✝ -/
#guard_msgs in set_option pp.unicode false in #eval do ppTerm (← `(True ∧'' False))
/-- info: True✝ /\'' False✝ -/
#guard_msgs in set_option pp.unicode false in #eval do ppTerm (← `(True /\'' False))

/-!
The `fun` notation uses `preserveForPP`.
Whne `pp.unicode.fun` is true, its elaborator uses `↦`.
-/
/-- info: fun x => x : ?m.1 → ?m.1 -/
#guard_msgs in #check fun x => x

/-- info: fun x ↦ x : ?m.1 → ?m.1 -/
#guard_msgs in set_option pp.unicode.fun true in #check fun x => x

/-- info: fun x => x : ?m.1 -> ?m.1 -/
#guard_msgs in set_option pp.unicode.fun true in set_option pp.unicode false in #check fun x => x

-- The delaborator is what uses `↦`, so the option has no effect here.
/-- info: fun x✝ => x✝ -/
#guard_msgs in set_option pp.unicode.fun true in #eval do ppTerm (← `(fun x => x))

/-- info: fun x✝ => x✝ -/
#guard_msgs in #eval do ppTerm (← `(fun x => x))
/-- info: fun x✝ ↦ x✝ -/
#guard_msgs in #eval do ppTerm (← `(fun x ↦ x))
/-- info: fun x✝ => x✝ -/
#guard_msgs in set_option pp.unicode false in #eval do ppTerm (← `(fun x ↦ x))
