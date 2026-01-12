/-!
Sanity-check reported ranges for nested snapshot tree nodes. In particular, ranges of sibling nodes
resolved later should not cover up progress inside earlier nodes.

This test cannot test per se whether such cover-up occurs without a dedicated synchronization
protocol between the test and the involved tactics to control ordering of events like in the
cancellation tests. Instead, it is intended merely to detect timing-independent changes to the
snapshot tree and in the event of such changes, preservation of proper progress reporting needs to
be verified manually.
-/

set_option internal.cmdlineSnapshots false
set_option trace.Elab.snapshotTree true
example : True := by
  sleep 0
  sleep 100
  · next =>
    induction 0 with
    | zero =>
      sleep 100
      trivial
    | succ n =>
      sleep 100
      trivial
