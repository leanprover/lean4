module

prelude
public meta import Module.PrivateImported

/-!
`#eval`-ing a value that (transitively) depends on an imported `initialize`d value needs that
value's IR at compile time. Under separate codegen a plain `public import` only loads the `.olean`
interface, so this requires a `meta import`; the `public import` counterpart in
`ImportedPrivateImported.lean` therefore does not `#eval` it.
-/

/-- info: 5 -/
#guard_msgs in
#eval publicDefOfPrivatelyInitialized
