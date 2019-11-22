/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Name

namespace Lean

structure NameGenerator :=
(namePrefix : Name := `_uniq)
(idx        : Nat  := 1)

namespace NameGenerator

instance : Inhabited NameGenerator := ⟨{}⟩

@[inline] def curr (g : NameGenerator) : Name :=
mkNameNum g.namePrefix g.idx

@[inline] def next (g : NameGenerator) : NameGenerator :=
{ idx := g.idx + 1, .. g }

@[inline] def mkChild (g : NameGenerator) : NameGenerator × NameGenerator :=
({ namePrefix := mkNameNum g.namePrefix g.idx, idx := 1 },
 { idx := g.idx + 1, .. g })

end NameGenerator

end Lean
