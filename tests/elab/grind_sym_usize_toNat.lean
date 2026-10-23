/-!
`USize.toNat` of a numeral below `2^32` is evaluated by the `Sym.simp` `grind` normalizer, like
the legacy `USize.reduceToNat` simproc. The kernel cannot evaluate it, since `USize.size` depends
on the opaque `System.Platform.numBits`, so the step is justified by `USize.toNat_ofNat_of_lt_32`.
-/

set_option warn.sorry false

abbrev LEAN_RC_INC_MAX : USize := 0x10000

example : USize.toNat 65536 = a := by grind_norm; guard_target =ₛ 65536 = a; sorry
example : USize.toNat 65536 = a := by grind_norm sym; guard_target =ₛ 65536 = a; sorry
#guard_msgs in
example : USize.toNat 65536 = a := by grind_norm check; sorry
-- Not evaluated: the value is platform dependent.
#guard_msgs in
example : USize.toNat 4294967296 = a := by grind_norm check; sorry

section sym
set_option backward.grind.normalizer false
example : 0 < LEAN_RC_INC_MAX.toNat := by grind
example : USize.toNat 65536 = 65536 := by grind
example : USize.toNat 0xFFFFFFFF = 4294967295 := by grind
end sym
