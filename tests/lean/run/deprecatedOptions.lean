/-!
This file tests that deprecation warnings on also work on built-in options.
It may have to be adjusted as we deprecate different options, since
we probably don't want to have a built-in option just for the sake of testing.
-/


/--
@ +1:0...48
warning: `backward.eqns.deepRecursiveSplit` has been deprecated
-/
#guard_msgs (positions := true) in
set_option backward.eqns.deepRecursiveSplit true

/--
@ +1:0...42
warning: `backward.eqns.nonrecursive` has been deprecated
-/
#guard_msgs (positions := true) in
set_option backward.eqns.nonrecursive true

-- TODO: Why is this reported many times? Can this be avoided?

/--
@ +1:0...42
warning: `backward.eqns.nonrecursive` has been deprecated
---
@ +1:0...+2:12
warning: `backward.eqns.nonrecursive` has been deprecated
---
@ +1:0...+2:12
warning: `backward.eqns.nonrecursive` has been deprecated
---
@ +1:0...+2:12
warning: `backward.eqns.nonrecursive` has been deprecated
-/
#guard_msgs (positions := true) in
set_option backward.eqns.nonrecursive true in
def foo := 0


set_option linter.deprecated.options false

set_option backward.eqns.nonrecursive true

set_option backward.eqns.nonrecursive false in
def bar := 0
