import system.io
open io
def bar : io unit :=
do put_str "one", put_str "two", put_str "three"

vm_eval bar

print "---------"

def foo : ℕ → io unit
| 0     := put_str "at zero\n"
| (n+1) := do put_str "in\n", foo n, put_str "out\n"

vm_eval foo 3

print "---------"

def foo2 : ℕ → io unit
| 0     := put_str "at zero\n"
| (n+1) := do put_str "in\n", foo2 n, put_str "out\n", put_str "out2\n"

vm_eval foo2 3
