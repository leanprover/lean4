def prod.foo (s : bool × bool) (fst : bool) : bool × bool :=
match s with
(a, b) := (fst, b)
end

variable s : bool × bool

#check prod.foo s
#check prod.foo s tt
#check s.foo
#check s.foo tt

def prod.foo2 {α β} (s : α × β) (fst : α) : α × β :=
match s with
(a, b) := (fst, b)
end

#check s.foo2
#check s.foo2 tt
