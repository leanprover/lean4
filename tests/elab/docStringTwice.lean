/-!
`add_decl_doc` rejects a declaration that already has a docstring.
-/

/-- first -/
def f := 1

/-- error: invalid doc string, declaration `f` already has one -/
#guard_msgs in
/-- second -/
add_decl_doc f

def g := 2

/-- only -/
add_decl_doc g
