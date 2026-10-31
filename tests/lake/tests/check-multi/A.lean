prelude
-- `lake check` re-checks everything in scope, so keep all of `Init` out of it.
import Init.Core

theorem a_thm : 1 + 1 = 2 := rfl
