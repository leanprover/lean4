open tactic

example (fst fst_1 : nat) : fst = fst :=
by do
  ns ← mk_constructors_fresh_names `prod,
  trace ns, -- [[fst_2, snd]]
  constructor

example (h : nat) : h = h :=
by do
  ns ← mk_constructors_fresh_names `acc,
  trace ns, -- [[x, a_1]
  constructor

inductive Foo
| mk₁ (a b c : nat)  : Foo
| mk₂ (d e : bool)   : Foo
| mk₃ (f g : Foo)    : Foo

example (a d d_1 e : bool) : a = a :=
by do
  ns ← mk_constructors_fresh_names `Foo,
  trace ns, -- [[a_1, b, c], [d_2, e_1], [f, g]]
  constructor
