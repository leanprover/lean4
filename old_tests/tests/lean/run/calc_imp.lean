example (A B C D : Prop) (h1 : A → B) (h2 : B → C) (h3 : C → D) : A → D :=
calc A → B : h1
   ... → C : h2
   ... → D : h3
