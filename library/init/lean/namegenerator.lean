/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name

namespace Lean

structure NameGenerator :=
(namePrefix : Name := `_uniq)
(idx        : Nat  := 1)

namespace NameGenerator

instance : Inhabited NameGenerator := ⟨{}⟩

def curr (g : NameGenerator) : Name :=
Name.mkNumeral g.namePrefix g.idx

def next (g : NameGenerator) : NameGenerator :=
{ idx := g.idx + 1, .. g }

def mkChild (g : NameGenerator) : NameGenerator × NameGenerator :=
({ namePrefix := Name.mkNumeral g.namePrefix g.idx, idx := 1 },
 { idx := g.idx + 1, .. g })

end NameGenerator

end Lean
