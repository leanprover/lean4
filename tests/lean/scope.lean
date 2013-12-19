
Scope
  Variable A : Type
  Variable B : Type
  Variable f : A -> A -> A
  Definition g (x y : A) : A := f y x
  Variable h : A -> B
  Variable hinv : B -> A
  Axiom Inv (x : A) : hinv (h x) = x
  Axiom H1 (x y : A) : f x y = f y x
  Theorem f_eq_g : f = g := Abst (fun x, (Abst (fun y,
                                      let L1 : f x y = f y x := H1 x y,
                                          L2 : f y x = g x y := Refl (g x y)
                                      in Trans L1 L2)))

  Theorem Inj (x y : A) (H : h x = h y) : x = y :=
         let L1 : hinv (h x) = hinv (h y) := Congr2 hinv H,
             L2 : hinv (h x) = x          := Inv x,
             L3 : hinv (h y) = y          := Inv y,
             L4 : x = hinv (h x)          := Symm L2,
             L5 : x = hinv (h y)          := Trans L4 L1
         in Trans L5 L3.
EndScope

Show Environment 3.
Eval g Int Int::sub 10 20