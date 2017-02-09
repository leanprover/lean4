constants (A : Type) (B : A → Type) (C : ∀ (a : A) (ba : B a), Type)
          (D : ∀ (a : A) (ba : B a) (cba : C a ba), Type)
          (E : ∀ (a : A) (ba : B a) (cba : C a ba) (dcba : D a ba cba), Type)
          (F : ∀ (a : A) (ba : B a) (cba : C a ba) (dcba : D a ba cba) (edcba : E a ba cba dcba), Type)
          (C_ss : ∀ a ba, subsingleton (C a ba))
          (a1 a2 a3 : A)
          (mk_B1 mk_B2 : ∀ a, B a)
          (mk_C1 mk_C2 : ∀ {a} ba, C a ba)

          (tr_B : ∀ {a}, B a → B a)
          (x y z : A → A)

          (f f' : ∀ {a : A} {ba : B a} (cba : C a ba), D a ba cba)
          (g : ∀ {a : A} {ba : B a} {cba : C a ba} (dcba : D a ba cba), E a ba cba dcba)
          (h : ∀ {a : A} {ba : B a} {cba : C a ba} {dcba : D a ba cba} (edcba : E a ba cba dcba), F a ba cba dcba edcba)


attribute [instance] C_ss
open tactic

example : ∀ (a a' : A), a == a' → mk_B1 a == mk_B1 a' :=
by cc

example : ∀ (a a' : A), a == a' → mk_B2 a == mk_B2 a' :=
by cc

example : a1 == y a2 → mk_B1 a1 == mk_B1 (y a2) :=
by cc

example : a1 == x a2 → a2 == y a1 → mk_B1 (x (y a1)) == mk_B1 (x (y (x a2))) :=
by cc

example : a1 == y a2 → mk_B1 a1 == mk_B2 (y a2) → f (mk_C1 (mk_B2 a1)) == f (mk_C2 (mk_B1 (y a2))) :=
by cc

example : a1 == y a2 → tr_B (mk_B1 a1) == mk_B2 (y a2) → f (mk_C1 (mk_B2 a1)) == f (mk_C2 (tr_B (mk_B1 (y a2)))) :=
by cc

example : a1 == y a2 → mk_B1 a1 == mk_B2 (y a2) → g (f (mk_C1 (mk_B2 a1))) == g (f (mk_C2 (mk_B1 (y a2)))) :=
by cc

example : a1 == y a2 → tr_B (mk_B1 a1) == mk_B2 (y a2) → g (f (mk_C1 (mk_B2 a1))) == g (f (mk_C2 (tr_B (mk_B1 (y a2))))) :=
by cc

example : a1 == y a2 → a2 == z a3 → a3 == x a1 → mk_B1 a1 == mk_B2 (y (z (x a1))) →
          f (mk_C1 (mk_B2 (y (z (x a1))))) == f' (mk_C2 (mk_B1 a1)) →
          g (f (mk_C1 (mk_B2 (y (z (x a1)))))) == g (f' (mk_C2 (mk_B1 a1))) :=
by cc

example : a1 == y a2 → a2 == z a3 → a3 == x a1 → mk_B1 a1 == mk_B2 (y (z (x a1))) →
          f (mk_C1 (mk_B2 (y (z (x a1))))) == f' (mk_C2 (mk_B1 a1)) →
          f' (mk_C1 (mk_B1 a1)) == f (mk_C2 (mk_B2 (y (z (x a1))))) →
          g (f (mk_C1 (mk_B1 (y (z (x a1)))))) == g (f' (mk_C2 (mk_B2 a1))) :=
by cc

example : a1 == y a2 → a2 == z a3 → a3 == x a1 → tr_B (mk_B1 a1) == mk_B2 (y (z (x a1))) →
          f (mk_C1 (mk_B2 (y (z (x a1))))) == f' (mk_C2 (tr_B (mk_B1 a1))) →
          f' (mk_C1 (tr_B (mk_B1 a1))) == f (mk_C2 (mk_B2 (y (z (x a1))))) →
          g (f (mk_C1 (tr_B (mk_B1 (y (z (x a1))))))) == g (f' (mk_C2 (mk_B2 a1))) :=
by cc
