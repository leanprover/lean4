import system.io

section
open nat_map

vm_eval size (insert (insert (mk nat) 10 20) 10 21)

meta definition m := (insert (insert (insert (mk nat) 10 20) 5 50) 10 21)

vm_eval find m 10
vm_eval find m 5
vm_eval find m 8
vm_eval contains m 5
vm_eval contains m 8

open list

meta definition m2 := of_list [((1:nat), "one"), (2, "two"), (3, "three")]

vm_eval size m2
vm_eval find m2 1
vm_eval find m2 4
vm_eval find m2 3

vm_eval do pp m2, put_str "\n"
vm_eval m2

end

section
open rb_map
-- Mapping from (nat × nat) → nat
meta definition m3 := insert (insert (mk (nat × nat) nat) (1, 2) 3) (2, 2) 4

vm_eval find m3 (1, 2)
vm_eval find m3 (2, 1)
vm_eval find m3 (2, 2)

vm_eval pp m3
end
