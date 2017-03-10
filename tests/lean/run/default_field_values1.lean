structure foo (α β : Type) :=
(x : α) (f : α → α) (y : β)

structure bla (α β : Type) extends foo α β :=
(z : α := f x)

structure boo (α : Type) extends bla α α :=
(d := f (f x))

#print bla.z._default
#print boo.z._default
#print boo.d._default

lemma ex₁ : {boo . x := 10, f := nat.succ, y := 10}^.z = 11 :=
rfl

lemma ex₂ : {boo . x := 10, f := (λ x, 2*x), y := 10}^.d = 40 :=
rfl

structure cfg :=
(x : nat  := 10)
(y : bool := tt)

#check {cfg .}

lemma ex₃ : {cfg .} = {x := 10, y := tt} :=
rfl

lemma ex₄ : ({} : cfg) = {x := 10, y := tt} :=
rfl

def default_cfg1 : cfg :=
{}  -- Remark: this is overloaded, it can be the empty collection or the empty structure instance.

def default_cfg2 : cfg :=
{.} -- This is a non ambiguous way of writing the empty structure instance

lemma ex₅ : default_cfg1 = default_cfg2 :=
rfl

lemma ex₆ : default_cfg1 = {x := 10, y := tt} :=
rfl
