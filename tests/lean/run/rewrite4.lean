import data.nat
open algebra

constant f {A : Type} : A → A → A

theorem test1 {A : Type} [s : comm_ring A] (a b c : A) (H : a + 0 = 0) : f a a = f 0 0 :=
by rewrite [add_zero at H, H]

theorem test2 {A : Type} [s : comm_ring A] (a b c : A) (H : a + 0 = 0) : f a a = f 0 0 :=
by rewrite [add_zero at *, H]

theorem test3 {A : Type} [s : comm_ring A] (a b c : A) (H : a + 0 = 0 + 0) : f a a = f 0 0 :=
by rewrite [add_zero at H, zero_add at H, H]
