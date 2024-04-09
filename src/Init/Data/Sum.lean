/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
prelude
import Init.Core

namespace Sum

deriving instance DecidableEq for Sum
deriving instance BEq for Sum

/-- Check if a sum is `inl` and if so, retrieve its contents. -/
def getLeft? : α ⊕ β → Option α
  | inl a => some a
  | inr _ => none

/-- Check if a sum is `inr` and if so, retrieve its contents. -/
def getRight? : α ⊕ β → Option β
  | inr b => some b
  | inl _ => none

end Sum
