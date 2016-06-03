import meta

open nat_map

vm_eval size (insert (insert (mk nat) 10 20) 10 21)

meta_definition m := (insert (insert (insert (mk nat) 10 20) 5 50) 10 21)

vm_eval find m 10
vm_eval find m 5
vm_eval find m 8
vm_eval contains m 5
vm_eval contains m 8

open list

meta_definition m2 := (of_list nat.cmp [(1, "one"), (2, "two"), (3, "three")])

vm_eval size m2
vm_eval find m2 1
vm_eval find m2 4
vm_eval find m2 3
