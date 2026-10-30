/-!
When a conflict in the `lia` model search can be explained by bounds that do not depend on the
current case split, that explanation is preferred over one using bounds tightened with a
divisibility constraint of the case. On this goal the untightened bounds refute all 65536 cases of
a Cooper split at once, while the tightened ones refute only the current case, so the solver
enumerated the cases until `liaSteps`.
-/
example (hi lo k : Int) (hhi : 0 ≤ hi ∧ hi < 2 ^ 32) (hlo : 0 ≤ lo ∧ lo < 2 ^ 32) (hk : k = 65536) :
    (4294967296 * hi + lo) / k % 4294967296 = lo / k + hi % k * (4294967296 / k) := by lia
