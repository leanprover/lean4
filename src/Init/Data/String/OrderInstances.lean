/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Defs
public import Init.Grind.ToInt
public import Init.Data.Order.Classes
import Init.Omega

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

instance : Lean.Grind.ToInt String.Pos.Raw (.ci 0) where
  toInt p := p.byteIdx
  toInt_inj p q := by simp [Pos.Raw.ext_iff, ← Int.ofNat_inj]
  toInt_mem := by simp

@[simp]
theorem toInt_eq {p : Pos.Raw} : Lean.Grind.ToInt.toInt p = p.byteIdx := rfl

instance : Lean.Grind.ToInt.LE String.Pos.Raw (.ci 0) where
  le_iff := by simp [Pos.Raw.le_iff]

instance : Lean.Grind.ToInt.LT String.Pos.Raw (.ci 0) where
  lt_iff := by simp [Pos.Raw.lt_iff]

instance : Std.LawfulOrderLT String.Pos.Raw where
  lt_iff := by order

instance : Std.IsLinearOrder String.Pos.Raw where
  le_refl := by order
  le_trans := by order
  le_antisymm := by order
  le_total := by order

end Pos.Raw

namespace Pos

instance {s : String} : Lean.Grind.ToInt s.Pos (.co 0 (s.utf8ByteSize + 1)) where
  toInt p := p.offset.byteIdx
  toInt_inj p q := by simp [Pos.ext_iff, Pos.Raw.ext_iff, ← Int.ofNat_inj]
  toInt_mem p := by have := p.isValid.le_utf8ByteSize; simp; omega

@[simp]
theorem toInt_eq {s : String} {p : s.Pos} : Lean.Grind.ToInt.toInt p = p.offset.byteIdx := rfl

instance {s : String} : Lean.Grind.ToInt.LE s.Pos (.co 0 (s.utf8ByteSize + 1)) where
  le_iff := by simp [Pos.le_iff, Pos.Raw.le_iff]

instance {s : String} : Lean.Grind.ToInt.LT s.Pos (.co 0 (s.utf8ByteSize + 1)) where
  lt_iff := by simp [Pos.lt_iff, Pos.Raw.lt_iff]

instance {s : String} : Std.LawfulOrderLT s.Pos where
  lt_iff := by order

instance {s : String} : Std.IsLinearOrder s.Pos where
  le_refl := by order
  le_trans := by order
  le_antisymm := by order
  le_total := by order

end Pos

namespace Slice.Pos

instance {s : Slice} : Lean.Grind.ToInt s.Pos (.co 0 (s.utf8ByteSize + 1)) where
  toInt p := p.offset.byteIdx
  toInt_inj p q := by simp [Pos.ext_iff, Pos.Raw.ext_iff, ← Int.ofNat_inj]
  toInt_mem p := by have := p.isValidForSlice.le_utf8ByteSize; simp; omega

@[simp]
theorem toInt_eq {s : Slice} {p : s.Pos} : Lean.Grind.ToInt.toInt p = p.offset.byteIdx := rfl

instance {s : Slice} : Lean.Grind.ToInt.LE s.Pos (.co 0 (s.utf8ByteSize + 1)) where
  le_iff := by simp [Pos.le_iff, Pos.Raw.le_iff]

instance {s : Slice} : Lean.Grind.ToInt.LT s.Pos (.co 0 (s.utf8ByteSize + 1)) where
  lt_iff := by simp [Pos.lt_iff, Pos.Raw.lt_iff]

instance {s : Slice} : Std.LawfulOrderLT s.Pos where
  lt_iff := by order

instance {s : Slice} : Std.IsLinearOrder s.Pos where
  le_refl := by order
  le_trans := by order
  le_antisymm := by order
  le_total := by order

end Slice.Pos

end String
