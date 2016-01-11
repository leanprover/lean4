universes l1 l2 l3 l4 l5 l6
constants (A : Type.{l1}) (B : A → Type.{l2}) (C : ∀ (a : A) (ba : B a), Type.{l3})
          (D : ∀ (a : A) (ba : B a) (cba : C a ba), Type.{l4})
          (E : ∀ (a : A) (ba : B a) (cba : C a ba) (dcba : D a ba cba), Type.{l5})
          (F : ∀ (a : A) (ba : B a) (cba : C a ba) (dcba : D a ba cba) (edcba : E a ba cba dcba), Type.{l6})
          (C_ss : ∀ a ba, subsingleton (C a ba))
          (a1 a2 a3 : A)
          (mk_B1 mk_B2 : ∀ a, B a)
          (mk_C1 mk_C2 : ∀ {a} ba, C a ba)

          (tr_B : ∀ {a}, B a → B a)
          (x y z : A → A)

          (f f' : ∀ {a : A} {ba : B a} (cba : C a ba), D a ba cba)
          (g : ∀ {a : A} {ba : B a} {cba : C a ba} (dcba : D a ba cba), E a ba cba dcba)
          (h : ∀ {a : A} {ba : B a} {cba : C a ba} {dcba : D a ba cba} (edcba : E a ba cba dcba), F a ba cba dcba edcba)

attribute C_ss [instance]

set_option blast.strategy "cc"
set_option blast.cc.heq true

example : ∀ {a a' : A}, a == a' → mk_B1 a == mk_B1 a' :=
by blast

example : ∀ {a a' : A}, a == a' → mk_B2 a == mk_B2 a' :=
by blast

example : a1 == y a2 → mk_B1 a1 == mk_B1 (y a2) :=
by blast

example : a1 == x a2 → a2 == y a1 → mk_B1 (x (y a1)) == mk_B1 (x (y (x a2))) :=
by blast

-- The following examples need subsingleton equality propagation
set_option blast.cc.subsingleton true

example : a1 == y a2 → mk_B1 a1 == mk_B2 (y a2) → f (mk_C1 (mk_B2 a1)) == f (mk_C2 (mk_B1 (y a2))) :=
by blast

example : a1 == y a2 → tr_B (mk_B1 a1) == mk_B2 (y a2) → f (mk_C1 (mk_B2 a1)) == f (mk_C2 (tr_B (mk_B1 (y a2)))) :=
by blast

example : a1 == y a2 → mk_B1 a1 == mk_B2 (y a2) → g (f (mk_C1 (mk_B2 a1))) == g (f (mk_C2 (mk_B1 (y a2)))) :=
by blast

example : a1 == y a2 → tr_B (mk_B1 a1) == mk_B2 (y a2) → g (f (mk_C1 (mk_B2 a1))) == g (f (mk_C2 (tr_B (mk_B1 (y a2))))) :=
by blast

example : a1 == y a2 → a2 == z a3 → a3 == x a1 → mk_B1 a1 == mk_B2 (y (z (x a1))) →
          f (mk_C1 (mk_B2 (y (z (x a1))))) == f' (mk_C2 (mk_B1 a1)) →
          g (f (mk_C1 (mk_B2 (y (z (x a1)))))) == g (f' (mk_C2 (mk_B1 a1))) :=
by blast

example : a1 == y a2 → a2 == z a3 → a3 == x a1 → mk_B1 a1 == mk_B2 (y (z (x a1))) →
          f (mk_C1 (mk_B2 (y (z (x a1))))) == f' (mk_C2 (mk_B1 a1)) →
          f' (mk_C1 (mk_B1 a1)) == f (mk_C2 (mk_B2 (y (z (x a1))))) →
          g (f (mk_C1 (mk_B1 (y (z (x a1)))))) == g (f' (mk_C2 (mk_B2 a1))) :=
by blast

example : a1 == y a2 → a2 == z a3 → a3 == x a1 → tr_B (mk_B1 a1) == mk_B2 (y (z (x a1))) →
          f (mk_C1 (mk_B2 (y (z (x a1))))) == f' (mk_C2 (tr_B (mk_B1 a1))) →
          f' (mk_C1 (tr_B (mk_B1 a1))) == f (mk_C2 (mk_B2 (y (z (x a1))))) →
          g (f (mk_C1 (tr_B (mk_B1 (y (z (x a1))))))) == g (f' (mk_C2 (mk_B2 a1))) :=
by blast
