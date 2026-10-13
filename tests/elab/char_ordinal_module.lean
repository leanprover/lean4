module

/-!
Tests reduction of the `Char.ordinal` family, and of the polymorphic ranges built from it, across a
module boundary.
-/

example : 'a'.ordinal.val = 97 := by cbv

example : Char.ofOrdinal ⟨97, by decide⟩ = 'a' := by cbv

example : 'a'.succ? = some 'b' := by cbv

example : 'a'.succMany? 2 = some 'c' := by cbv

example : ('a'...='c').toList = ['a', 'b', 'c'] := by cbv

-- The surrogate code points are skipped over.
example : (Char.ofNat 0xd7ff).succ? = some (Char.ofNat 0xe000) := by cbv

example : (Char.ofNat 0xd7ff).ordinal.val + 1 = (Char.ofNat 0xe000).ordinal.val := by cbv

-- `Char.succ?` overflows at the last code point.
example : (Char.ofNat 0x10ffff).succ? = none := by cbv

example : 'a'.ordinal.val = 97 := by decide +kernel
