

Set lean::parser::verbose false.
Notation 10 if _ then _ : implies.
Show Environment 1.
Show if true then false.
Variable a : Bool.
Show if true then if a then false.
Set lean::pp::notation false.
Show if true then if a then false.
Variable A : Type.
Variable f : A -> A -> A -> Bool.
Notation 100  _ |- _ ; _  : f.
Show Environment 1.
Variable c : A.
Variable d : A.
Variable e : A.
Show c |- d ; e.
Set lean::pp::notation true.
Show c |- d ; e.
Variable fact : A -> A.
Notation 20 _ ! : fact.
Show a! !.
Set lean::pp::notation false.
Show a! !.
Set lean::pp::notation true.
Variable g : A -> A -> A.
Notation 30 [ _ ; _ ] : g
Show [c;d].
Show [c ; [d;e] ].
Set lean::pp::notation false.
Show [c ; [d;e] ].
Set lean::pp::notation true.
Variable h : A -> A -> A.
Notation 40 _ << _ end : h.
Show Environment 1.
Show d << e end.
Show [c ; d << e end ].
Set lean::pp::notation false.
Show [c ; d << e end ].
Set lean::pp::notation true.
Variable r : A -> A -> A.
Infixl 30 ++ : r.
Variable s : A -> A -> A.
Infixl 40 ** : s.
Show c ** d ++ e ** c.
Variable p1 : Bool.
Variable p2 : Bool.
Variable p3 : Bool.
Show p1 || p2 && p3.
Set lean::pp::notation false.
Show c ** d ++ e ** c.
Show p1 || p2 && p3.
Set lean::pp::notation true.
Show c = d || d = c.
Show  not p1 || p2.
Show p1 && p3 || p2 && p3.
Set lean::pp::notation false.
Show  not p1 || p2.
Show p1 && p3 || p2 && p3.
