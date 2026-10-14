import Lean

open Lean Elab Meta Command

/-! Ensures the `lazy_delta_abbrev` attribute functions correctly.-/

elab "#check_is_lazy_delta_abbrev" i:ident : command => liftTermElabM do
  let info ← getConstInfo (← resolveGlobalConstNoOverload i)
  unless info.hints.isAbbrev do
    throwError "{i} is not a lazy_delta_abbrev"

-- Definitions can be tagged as `lazy_delta_abbrev`
@[lazy_delta_abbrev]
def n : Nat := 2

#check_is_lazy_delta_abbrev n

--Theorems cannot, as they're never unfolded
/--
error: Cannot add attribute `[lazy_delta_abbrev]`: This attribute can only be added when declaring a `def`
-/
#guard_msgs in
@[lazy_delta_abbrev]
theorem n_eq_n (n : Nat): n = n := rfl

/-- error: n_eq_n is not a lazy_delta_abbrev -/
#guard_msgs in
#check_is_lazy_delta_abbrev n_eq_n

-- Same for opaque values
/--
error: Declaration `k` cannot be tagged as `lazy_delta_abbrev`: it is an opaque declaration and is thus never unfolded.
-/
#guard_msgs in
@[lazy_delta_abbrev]
opaque k : Nat := 2

/-- error: k is not a lazy_delta_abbrev -/
#guard_msgs in
#check_is_lazy_delta_abbrev k


-- Instances for classes that are not Prop can be tagged as `lazy_delta_abbrev`
class Foo : Type where

@[lazy_delta_abbrev]
instance foo : Foo := ⟨⟩

#check_is_lazy_delta_abbrev foo

class Bar : Prop where

-- The attribute has no effect on Prop-valued instances and throws an error
/--
error: Declaration `bar` cannot be tagged as `lazy_delta_abbrev`: it is a theorem and is thus never unfolded.
-/
#guard_msgs in
@[lazy_delta_abbrev]
instance bar : Bar := ⟨⟩

/-- error: bar is not a lazy_delta_abbrev -/
#guard_msgs in
#check_is_lazy_delta_abbrev bar

-- Definitions cannot be tagged by the attribute after being declared:

def n' := 2

/--
error: Cannot add attribute `[lazy_delta_abbrev]`: This attribute can only be added when declaring a `def`
-/
#guard_msgs in
attribute [lazy_delta_abbrev] n'

-- Abbreviations tagged with the attribute throw a warning saying the attribute is redundant

/--
warning: Tagging `k'` as `lazy_delta_abbrev` is redundant, `abbrev` declarations are always kernel abbreviations.
-/
#guard_msgs in
@[lazy_delta_abbrev]
abbrev k' : Nat := 2

#check_is_lazy_delta_abbrev k'
