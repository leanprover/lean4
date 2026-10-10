module

import Test.A
meta import Test.A

/-!
Evaluation during elaboration outside the language server runs code of a `meta` import, so unlike
for a plain `import`, the build must provide that import's IR even though this module postpones
its own code generation.
-/

#eval twice 21

theorem twice_two : twice 2 = 4 := by native_decide
