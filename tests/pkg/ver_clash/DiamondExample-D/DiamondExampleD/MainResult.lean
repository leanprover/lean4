module

import DiamondExampleB.MainResult
import DiamondExampleC.MainResult

open Ring

-- This uses `foo` from `DiamondExampleB` and `bar` from `DiamondExampleC`
example [Ring α] (a b c d : α) : a + (b + (c + d)) = a + (b + c) + d := by
  rw [foo]
  rw [bar]
