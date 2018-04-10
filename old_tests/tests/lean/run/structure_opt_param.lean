structure S (α : Type := int) :=
(a b : α)

def x : S :=
{a := 10, b := 10}

#check x.a

def y : S nat :=
{a := 10, b := 10}

#check y.a

def z : S string :=
{a := "hello", b := "world"}

#check z.a
