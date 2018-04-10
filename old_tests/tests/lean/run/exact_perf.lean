open nat

def f (a : nat) : nat := a
def g (a : nat) : nat := a
constant p : nat → Prop

example (a b : nat) (h1 : false) (h2 : p (g (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f a))))))))))))))))))))))))))))))) :
p (g (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f b)))))))))))))))))))))))))))))))
:=
begin
  try {exact h2},
  contradiction
end
