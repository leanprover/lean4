import Int.

scope
  variable A : Type
  variable B : Type
  variable f : A -> A -> A
  definition g (x y : A) : A := f y x
  variable h : A -> B
  variable hinv : B -> A
  axiom Inv (x : A) : hinv (h x) = x
  axiom H1 (x y : A) : f x y = f y x
  theorem f_eq_g : f = g := Abst (fun x, (Abst (fun y,
                                      let L1 : f x y = f y x := H1 x y,
                                          L2 : f y x = g x y := Refl (g x y)
                                      in Trans L1 L2)))

  theorem Inj (x y : A) (H : h x = h y) : x = y :=
         let L1 : hinv (h x) = hinv (h y) := Congr2 hinv H,
             L2 : hinv (h x) = x          := Inv x,
             L3 : hinv (h y) = y          := Inv y,
             L4 : x = hinv (h x)          := Symm L2,
             L5 : x = hinv (h y)          := Trans L4 L1
         in Trans L5 L3.
end

print environment 3.
eval g Int Int::sub 10 20