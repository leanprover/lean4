inductive A : Type
| ctor : A → A
| inh

-- set_option trace.Elab true in
def f : A → A → Bool
| banana, a b | _, lol how => 1 + "test" + f1 -- Error
| _, _ => false


def g : A → A → Bool
| A.inh, _ | _, A.inh => true
| _, _ => false

example : g .inh (.ctor a) = true := rfl
example : g .inh .inh = true := rfl
example : g (.ctor a) .inh = true := rfl
example : g (.ctor a) (.ctor b) = false := rfl
