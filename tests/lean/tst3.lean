SetOption lean::parser::verbose false.
Notation 10 if _ then _ : implies.
print Environment 1.
print if true then false.
Variable a : Bool.
print if true then if a then false.
SetOption lean::pp::notation false.
print if true then if a then false.
Variable A : Type.
Variable f : A -> A -> A -> Bool.
Notation 100  _ |- _ ; _  : f.
print Environment 1.
Variable c : A.
Variable d : A.
Variable e : A.
print c |- d ; e.
SetOption lean::pp::notation true.
print c |- d ; e.
Variable fact : A -> A.
Notation 20 _ ! : fact.
print c! !.
SetOption lean::pp::notation false.
print c! !.
SetOption lean::pp::notation true.
Variable g : A -> A -> A.
Notation 30 [ _ ; _ ] : g
print [c;d].
print [c ; [d;e] ].
SetOption lean::pp::notation false.
print [c ; [d;e] ].
SetOption lean::pp::notation true.
Variable h : A -> A -> A.
Notation 40 _ << _ end : h.
print Environment 1.
print d << e end.
print [c ; d << e end ].
SetOption lean::pp::notation false.
print [c ; d << e end ].
SetOption lean::pp::notation true.
Variable r : A -> A -> A.
Infixl 30 ++ : r.
Variable s : A -> A -> A.
Infixl 40 ** : s.
print c ** d ++ e ** c.
Variable p1 : Bool.
Variable p2 : Bool.
Variable p3 : Bool.
print p1 || p2 && p3.
SetOption lean::pp::notation false.
print c ** d ++ e ** c.
print p1 || p2 && p3.
SetOption lean::pp::notation true.
print c = d || d = c.
print  not p1 || p2.
print p1 && p3 || p2 && p3.
SetOption lean::pp::notation false.
print  not p1 || p2.
print p1 && p3 || p2 && p3.
