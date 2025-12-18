module
set_option warn.sorry false
abbrev sixteen : UInt32 := 16

theorem foo (x: UInt32) :
    x.toNat ≤ sixteen.toNat := by sorry

theorem aa (x : UInt32) :
  x.toNat ≤ sixteen.toNat := by
  grind [foo]
