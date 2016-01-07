import data.list
open nat

set_option blast.strategy "cc"

constant f : nat → nat

example (a b c d : nat) : f d = f b → succ a = f b → f d = succ c → a = c :=
by blast

example (a b c d e : nat) : f d = f b → f e = f b → succ a = f b → f e = succ c → a = c :=
by blast

example (a b c d e : nat) : f d = f b → f e = f b → succ a = f b → f e = zero → false :=
by blast

example (a b c d e : nat) : f d = f b → f e = f b → succ a = f b → f e = 0 → false :=
by blast

open list
example (a b c d e f : nat) (l1 l2 l3 l4 : list nat) : l1 = l2 → l2 = l3 → l4 = [a, b, succ c] → l1 = [c, d, succ e] → l3 = l4 → c = e :=
by blast

example (a b c d e f : nat) (l1 l2 l3 l4 : list nat) : l4 = [a, b, succ (succ c)] → l1 = [c, d, succ (succ e)] → l3 = l4 → l1 = l2 → l2 = l3 → c = e :=
by blast

example (a b c d e f : nat) (l1 l2 l3 l4 : list nat) : l4 = [a, b, succ c] → l1 = [c, d, 0] → l3 = l4 → l1 = l2 → l2 = l3 → false :=
by blast

example (a b c d e f : nat) (l1 l2 l3 l4 : list nat) : l4 = [a, b, succ c] → l1 = nil → l3 = l4 → l1 = l2 → l2 = l3 → false :=
by blast

example (a b c d e f : nat) (l1 l2 l3 l4 : list nat) : l1 = l2 → l2 = l3 → l4 = [a, b, succ c] → l1 = nil → l3 = l4 → false :=
by blast
