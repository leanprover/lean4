import Lean.SimpLC.Exceptions

/-!
# simp local confluence testing

If you experience failures here, take the suggested `simp_lc inspect ...` commands
and paste them into a relevant `Lean.SimpLC.Exceptions.ABC` file.

Then decide whether to:
* Remove a `@[simp]` annotation
* Add a new `@[simp]` lemma to restore confluence
* Add a new `simp_lc allow` directive to suppress warnings about a given non-confluent pair.
  Ideally add an `example` immediately before it demonstrating the non-confluence.
* Add a new `simp_lc ignore` directive to suppress all warnings about a given lemma.
  Ideally add a doc-comment justifying why this is reasonable.


This file is intentionally named `000_simplc.lean` to starting running as early as possible in CI.
-/

-- Warning: this takes about 3 minutes to run!
set_option maxHeartbeats 0 in
#guard_msgs (drop info) in
simp_lc check
