/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Defs
import Init.Grind.Attr
public import Init.Data.Order.Classes
import Init.Data.Order.PackageFactories
import Init.Omega
public import Init.Data.Order.PackageFactories

public section

/-!
# Register string positions with `grind`.
-/

namespace String

namespace Internal

scoped macro "order" : tactic => `(tactic| {
    simp [Pos.Raw.lt_iff, Pos.Raw.le_iff, String.Pos.lt_iff, String.Pos.le_iff, Slice.Pos.lt_iff,
      Slice.Pos.le_iff, Pos.Raw.ext_iff, String.Pos.ext_iff, Slice.Pos.ext_iff] at *;
    try omega })

end Internal

open Internal

namespace Pos.Raw

-- Homomorphism rules for `grind`: the injection is `Pos.Raw.byteIdx` into `Nat`.
attribute [grind hom] Pos.Raw.le_iff Pos.Raw.lt_iff Pos.Raw.ext_iff

instance : Std.Total (α := String.Pos.Raw) (· ≤ ·) := ⟨fun _ _ => by order⟩
instance : Trans (α := String.Pos.Raw) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨fun _ _ => by order⟩
instance : Std.Antisymm (α := String.Pos.Raw) (· ≤ ·) := ⟨fun _ _ => by order⟩

instance : Std.LawfulOrderBEq String.Pos.Raw := ⟨fun _ _ => by order⟩
instance : Std.LawfulOrderLT String.Pos.Raw := ⟨fun _ _ => by order⟩

instance : Std.LinearOrderPackage String.Pos.Raw := .ofLE _

end Pos.Raw

namespace Pos

-- Homomorphism rules for `grind`: the injection is `Pos.offset` into `Pos.Raw`,
-- composing with `Pos.Raw.byteIdx` into `Nat`.
attribute [grind hom] Pos.le_iff Pos.lt_iff Pos.ext_iff

/-- Range fact for `grind`: positions are bounded by the string size. -/
@[grind hom_pred] theorem offset_byteIdx_le_utf8ByteSize (s : String) (p : s.Pos) :
    p.offset.byteIdx ≤ s.utf8ByteSize := p.isValid.le_utf8ByteSize

instance {s : String} : Std.Total (α := s.Pos) (· ≤ ·) := ⟨fun _ _ => by order⟩
instance {s : String} : Trans (α := s.Pos) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨fun _ _ => by order⟩
instance {s : String} : Std.Antisymm (α := s.Pos) (· ≤ ·) := ⟨fun _ _ => by order⟩

instance {s : String} : Std.LawfulOrderBEq s.Pos := ⟨fun _ _ => by order⟩
instance {s : String} : Std.LawfulOrderLT s.Pos := ⟨fun _ _ => by order⟩

instance {s : String} : Std.LinearOrderPackage s.Pos := .ofLE _

end Pos

namespace Slice.Pos

-- Homomorphism rules for `grind`: the injection is `Pos.offset` into `Pos.Raw`,
-- composing with `Pos.Raw.byteIdx` into `Nat`.
attribute [grind hom] Pos.le_iff Pos.lt_iff Pos.ext_iff

/-- Range fact for `grind`: positions are bounded by the slice size. -/
@[grind hom_pred] theorem offset_byteIdx_le_utf8ByteSize (s : Slice) (p : s.Pos) :
    p.offset.byteIdx ≤ s.utf8ByteSize := p.isValidForSlice.le_utf8ByteSize

instance {s : Slice} : Std.Total (α := s.Pos) (· ≤ ·) := ⟨fun _ _ => by order⟩
instance {s : Slice} : Trans (α := s.Pos) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨fun _ _ => by order⟩
instance {s : Slice} : Std.Antisymm (α := s.Pos) (· ≤ ·) := ⟨fun _ _ => by order⟩

instance {s : Slice} : Std.LawfulOrderBEq s.Pos := ⟨fun _ _ => by order⟩
instance {s : Slice} : Std.LawfulOrderLT s.Pos := ⟨fun _ _ => by order⟩

instance {s : Slice} : Std.LinearOrderPackage s.Pos := .ofLE _

end Slice.Pos

end String
