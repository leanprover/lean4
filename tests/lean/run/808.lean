notation 1 := eq

postfix `x`:(max+1) := eq

postfix [priority 1] `y`:max := eq

attribute [instance, priority 1]
definition foo : inhabited nat := inhabited.mk nat.zero

definition bar := @eq
