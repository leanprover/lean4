setoption lean::parser::verbose false.
notation 10 if _ then _ : implies.
print environment 1.
print if true then false.
variable a : Bool.
print if true then if a then false.
setoption lean::pp::notation false.
print if true then if a then false.
variable A : Type.
variable f : A -> A -> A -> Bool.
notation 100  _ |- _ ; _  : f.
print environment 1.
variable c : A.
variable d : A.
variable e : A.
print c |- d ; e.
setoption lean::pp::notation true.
print c |- d ; e.
variable fact : A -> A.
notation 20 _ ! : fact.
print c! !.
setoption lean::pp::notation false.
print c! !.
setoption lean::pp::notation true.
variable g : A -> A -> A.
notation 30 [ _ ; _ ] : g
print [c;d].
print [c ; [d;e] ].
setoption lean::pp::notation false.
print [c ; [d;e] ].
setoption lean::pp::notation true.
variable h : A -> A -> A.
notation 40 _ << _ >> : h.
print environment 1.
print d << e >>.
print [c ; d << e >> ].
setoption lean::pp::notation false.
print [c ; d << e >> ].
setoption lean::pp::notation true.
variable r : A -> A -> A.
infixl 30 ++ : r.
variable s : A -> A -> A.
infixl 40 ** : s.
print c ** d ++ e ** c.
variable p1 : Bool.
variable p2 : Bool.
variable p3 : Bool.
print p1 || p2 && p3.
setoption lean::pp::notation false.
print c ** d ++ e ** c.
print p1 || p2 && p3.
setoption lean::pp::notation true.
print c = d || d = c.
print  not p1 || p2.
print p1 && p3 || p2 && p3.
setoption lean::pp::notation false.
print  not p1 || p2.
print p1 && p3 || p2 && p3.
