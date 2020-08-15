new_frontend

#print "---- Op"

inductive Op : Nat → Nat → Type
| mk : ∀ n, Op n n

structure Node : Type :=
(id₁ id₂ : Nat)
(o : Op id₁ id₂)

def h1 (x : List Node) : Bool :=
match x with
| _ :: Node.mk _ _ (Op.mk Nat.zero) :: _  => true
| _                                       => false

def mkNode (n : Nat) : Node := { id₁ := n, id₂ := n, o := Op.mk n }

#eval h1 [mkNode 1, mkNode 0, mkNode 3]
#eval h1 [mkNode 1, mkNode 1, mkNode 3]
#eval h1 [mkNode 0]
#eval h1 []

#print "---- Foo 1"

inductive Foo : Bool → Type
| bar : Foo false
| baz : Foo false

def h2 {b : Bool} (x : Foo b) : Bool :=
match b, x with
| _, Foo.bar => true
| _, Foo.baz => false

#eval h2 Foo.bar
#eval h2 Foo.baz

#print "---- Foo 2"

def h3 {b : Bool} (x : Foo b) : Bool :=
match b, x with
| _, Foo.bar => true
| _, _       => false

#eval h3 Foo.bar
#eval h3 Foo.baz
