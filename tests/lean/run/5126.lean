/-!
Strict-implicit variables used to misbehave in multiple ways because of a missing
`getBracketedBinderIds` case.
-/

variable ⦃i : Nat⦄
include i

/-- error: invalid declaration name 'i', there is a section variable with the same name -/
#guard_msgs in
def i := i
