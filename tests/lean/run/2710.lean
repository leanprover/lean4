/-!
# Structure field default values can be noncomputable
-/

noncomputable def ohno := 1

structure OhNo where
  x := ohno
