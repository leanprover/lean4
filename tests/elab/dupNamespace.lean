set_option linter.extra.dupNamespace true

/--
warning: The namespace `Foo` is duplicated in the declaration `Foo.Foo`.

Note: This linter can be disabled with `set_option linter.extra.dupNamespace false`
-/
#guard_msgs in
theorem Foo.Foo : True := trivial

theorem Foo.Bar.Foo : True := trivial

/--
warning: The namespaces `Bar` and `Foo` are duplicated in the declaration `Bar.Bar.Foo.Foo`.

Note: This linter can be disabled with `set_option linter.extra.dupNamespace false`
-/
#guard_msgs in
theorem Bar.Bar.Foo.Foo : True := trivial

section
set_option linter.extra.dupNamespace.consecutiveOnly false

/--
warning: The namespace `Bar` is duplicated in the declaration `Bar.Foo.Bar`.

Note: This linter can be disabled with `set_option linter.extra.dupNamespace false`
-/
#guard_msgs in
theorem Bar.Foo.Bar : True := trivial

/--
warning: The namespaces `Bar` and `Foo` are duplicated in the declaration `Bar.Foo.Bar.Foo`.

Note: This linter can be disabled with `set_option linter.extra.dupNamespace false`
-/
#guard_msgs in
theorem Bar.Foo.Bar.Foo : True := trivial
end
