
meta definition f : nat → nat
| n := if n / 2 = 0 then n + 1 else f (n / 2) + 1

meta definition g : nat × nat → nat
| (0, b)     := b
| (a+1, b+1) := g (a/2 - 1, a + b)
| (a+1, 0)   := 2*a

vm_eval f 200
vm_eval g (10, 20)
