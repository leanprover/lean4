def foo.f : nat → nat := λ x, x
def bla.f : string → string := λ x, x
open foo bla
example : nat := f 0
               --^ "command": "info"
