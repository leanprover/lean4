module

set_option linter.all true

-- `private` outside `public section` should warn
/--
warning: `private` has no effect outside a `public section` in a `module` file; declarations are already `private` by default

Note: This linter can be disabled with `set_option linter.privateInPrivate false`
-/
#guard_msgs in
private def foo := 1

-- `private` inside `public section` should not warn
#guard_msgs in
public section
private def bar := 2
end

-- no modifier should not warn
#guard_msgs in
def baz := 3

-- `public` should not warn (suppress missing docs linter for this test)
#guard_msgs in
set_option linter.missingDocs false in
public def qux := 4

-- disabling the linter should suppress the warning
#guard_msgs in
set_option linter.privateInPrivate false in
private def quux := 5

-- `private` on a theorem should also warn
/--
warning: `private` has no effect outside a `public section` in a `module` file; declarations are already `private` by default

Note: This linter can be disabled with `set_option linter.privateInPrivate false`
-/
#guard_msgs in
private theorem thm : True := trivial
