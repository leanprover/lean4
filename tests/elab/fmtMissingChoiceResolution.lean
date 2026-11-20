/-!
Tests that the `fmt.missing` linter reports syntax with several readings (a `choice` node) for which
the elaborator did not record the reading that it picked. The auto-formatter keeps the layout of
such syntax, unless all readings have a formatter and are formatted in the same way.
-/

instance : Singleton α (List α) where
  singleton a := [a]

instance : Insert α (List α) where
  insert a as := a :: as

structure Args where
  n : Nat := 0

syntax (name := twoReadingsA) "twoReadings " term : term
syntax (name := twoReadingsB) "twoReadings " term : term

set_option linter.fmt.missing true

-- The elaborator picks a reading: no report.
def resolved : List Nat := {1, 2}

-- The tactics after `trivial` do not run, so the elaborator picks no reading. The elements of a set
-- and the fields of a structure instance are formatted in different ways.
example : True := by
  first | trivial | exact notElaborated {1, 2}

-- No reading has a formatter. The missing formatters are reported as well.
example : True := by
  first | trivial | exact twoReadings 1

-- The tactic block of the default value is not elaborated here, but both readings of `{}` are
-- formatted in the same way: no report.
def bothReadingsAlike (args : Args := by exact {}) : Nat := args.n
