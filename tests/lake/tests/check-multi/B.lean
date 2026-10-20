prelude
-- `lake check` re-checks everything in scope, so keep all of `Init` out of it.
import Init.Core

theorem b_thm : 2 + 2 = 4 := rfl
