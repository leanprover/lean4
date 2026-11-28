module

import all SplitMod.Basic

-- With `import all`, the bodies from `Basic.private.lean` are visible.
example : f 0 = 1 := rfl
example : addK 2 ⟨1, by decide⟩ = 6 := rfl
example : h [5, 6] = 5 := rfl
