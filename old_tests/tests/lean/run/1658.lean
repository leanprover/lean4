constant p : bool → bool
constant P : bool → Prop

noncomputable def lp : bool → bool
| ff := p ff
| tt := p tt

def foo (b : bool) : Prop :=
P (lp b)

constant T : bool → Type

def boo (b : bool) : Type :=
T (lp b)
