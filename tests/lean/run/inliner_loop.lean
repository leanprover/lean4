unsafe inductive t
| mk : (t → t) → t

unsafe def loop' : t → t
| t.mk f   => f (t.mk f)

unsafe def loop : t :=
loop' (t.mk loop')
