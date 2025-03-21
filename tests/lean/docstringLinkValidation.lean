/-!
# Error Locations for Links

This test ensures that errors in reference manual link syntax are reported at the correct positions.
-/

/--
foo [](lean-manual://) [](lean-manual://f)
-/
def x := 44
