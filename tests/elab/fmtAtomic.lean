/-!
Tests that the `fmt.missing` linter stays silent for syntax that consists only of atoms, because
`derivedAtomicFmtProvider` derives a formatter for it. Syntax with an argument gets no derived
formatter, so the linter reports it.
-/

macro (name := atomicTest) "atomicTest" : term => `(True)
macro (name := identTest) "identTest " _x:ident : term => `(True)

set_option linter.fmt.missing true

#guard_msgs in
example : Prop := atomicTest

/--
warning: no auto-formatter registered for syntax kind «identTest»

Note: This linter can be disabled with `set_option linter.fmt.missing false`
-/
#guard_msgs in
example : Prop := identTest x
