/-!
# Deprecate `:=` for `inductive` and `structure`
-/

set_option linter.deprecated true

/--
warning: 'inductive ... :=' has been deprecated in favor of 'inductive ... where'.
You can disable this warning with 'set_option linter.deprecated false'.
-/
#guard_msgs in
inductive DogSound' :=
  | woof
  | grr

/--
warning: 'structure ... :=' has been deprecated in favor of 'structure ... where'.
You can disable this warning with 'set_option linter.deprecated false'.
-/
#guard_msgs in
structure S :=
  (n : Nat)

/--
warning: 'class ... :=' has been deprecated in favor of 'class ... where'.
You can disable this warning with 'set_option linter.deprecated false'.
-/
#guard_msgs in
class C :=
  (n : Nat)
