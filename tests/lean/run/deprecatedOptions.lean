/-!
This file tests that deprecation warnings on also work on built-in options.
It may have to be adjusted as we deprecate different options, since
we probably don't want to have a built-in option just for the sake of testing.
-/

-- This doesn't work yet, we do not have built-in deprecation warnings

set_option backward.eqns.deepRecursiveSplit true

set_option backward.eqns.nonrecursive true
