/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.Hashable
public import Init.Data.String.Defs

public section

namespace String

deriving instance Hashable for String.Pos.Raw
deriving instance Hashable for String.Pos
deriving instance Hashable for String.Slice.Pos

end String
