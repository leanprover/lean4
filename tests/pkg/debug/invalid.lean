/-!
Checks that disabled `debug_assert!` conditions are still typechecked (#14453).
-/

def invalid : Unit :=
  debug_assert! '1' + 2; ()
