constant f : nat → nat → nat
constant g : string → string → string

infix ` & `:60 := f
infix ` & `:60 := g

set_option pp.notation false

#check 0 & 1
#check "a" & "b"
#check tt & ff

notation `[[`:max l:(foldr `, ` (h t, f h t) 0 `]]`:0) := l
notation `[[`:max l:(foldr `, ` (h t, g h t) "" `]]`:0) := l

#check [[ (1:nat), 2, 3 ]]
#check [[ "a", "b", "c" ]]
