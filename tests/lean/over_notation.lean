constant f : nat → nat → nat
constant g : string → string → string

infix ` & `:60 := f
infix ` & `:60 := g

set_option pp.notation false

#elab 0 & 1
#elab "a" & "b"
#elab tt & ff

notation `[[`:max l:(foldr `, ` (h t, f h t) 0 `]]`:0) := l
notation `[[`:max l:(foldr `, ` (h t, g h t) "" `]]`:0) := l

#elab [[ (1:nat), 2, 3 ]]
#elab [[ "a", "b", "c" ]]
