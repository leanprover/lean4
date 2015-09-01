notation 1 := eq

postfix `x`:(max+1) := eq

postfix [priority 1] `y`:max := eq

definition foo [instance] [priority 1] : inhabited nat := inhabited.mk nat.zero

definition bar [unfold 1] := @eq
