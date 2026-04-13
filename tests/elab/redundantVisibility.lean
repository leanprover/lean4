module

set_option linter.redundantVisibility true

-- `private` outside `public section` should warn
/--
warning: `private` has no effect in a `module` file outside `public section`; declarations are already `private` by default

Note: This linter can be disabled with `set_option linter.redundantVisibility false`
-/
#guard_msgs in
private def foo := 1

-- `private` inside `public section` should not warn
public section
#guard_msgs in
private def bar := 2
end

-- no modifier should not warn
#guard_msgs in
def baz := 3

-- `public` outside `public section` in a module should not warn
#guard_msgs in
set_option linter.missingDocs false in
public def qux := 4

-- `public` inside `public section` should warn
public section
/--
warning: `public` is the default visibility inside a `public section`; the modifier has no effect

Note: This linter can be disabled with `set_option linter.redundantVisibility false`
-/
#guard_msgs in
set_option linter.missingDocs false in
public def qux2 := 5
end

-- disabling the linter should suppress the warning
#guard_msgs in
set_option linter.redundantVisibility false in
private def quux := 6

-- `private` on a theorem should also warn
/--
warning: `private` has no effect in a `module` file outside `public section`; declarations are already `private` by default

Note: This linter can be disabled with `set_option linter.redundantVisibility false`
-/
#guard_msgs in
private theorem thm : True := trivial
