import system.io
open io
section
open native.nat_map

#eval size (insert (insert (mk nat) 10 20) 10 21)

meta definition m := (insert (insert (insert (mk nat) 10 20) 5 50) 10 21)

#eval find m 10
#eval find m 5
#eval find m 8
#eval contains m 5
#eval contains m 8

open list

meta definition m2 := of_list [((1:nat), "one"), (2, "two"), (3, "three")]

#eval size m2
#eval find m2 1
#eval find m2 4
#eval find m2 3

section

#eval do pp m2, put_str "\n"
end
#eval m2

end

section
open native.rb_map
-- Mapping from (nat × nat) → nat
meta definition m3 := insert (insert (mk (nat × nat) nat) (1, 2) 3) (2, 2) 4

#eval find m3 (1, 2)
#eval find m3 (2, 1)
#eval find m3 (2, 2)


#eval pp m3
end
