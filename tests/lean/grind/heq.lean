axiom A : Type
axiom B : A → Type
axiom C : (a : A) → B a → Type
axiom D : (a : A) → (ba : B a) → C a ba → Type
axiom E : (a : A) → (ba : B a) → (cba : C a ba) → D a ba cba → Type
axiom mk_B1 : (a : _) → B a
axiom mk_B2 : (a : _) → B a
axiom mk_C1 : {a : _} → (ba : _) → C a ba
axiom mk_C2 : {a : _} → (ba : _) → C a ba
axiom tr_B : {a : _} → B a → B a
axiom x : A → A
axiom y : A → A
axiom z : A → A
axiom f : {a : A} → {ba : B a} → (cba : C a ba) → D a ba cba
axiom f' : {a : A} → {ba : B a} → (cba : C a ba) → D a ba cba
axiom g : {a : A} → {ba : B a} → {cba : C a ba} → (dcba : D a ba cba) → E a ba cba dcba

-- These succeed:

example : ∀ (a a' : A), HEq a a' → HEq (mk_B1 a) (mk_B1 a') := by
  grind

example : ∀ (a a' : A), HEq a a' → HEq (mk_B2 a) (mk_B2 a') := by
  grind

example : ∀ (a a' : A) (h : a = a') (b : B a), HEq (h ▸ b) b := by
  grind

example : HEq a1 (y a2) → HEq (mk_B1 a1) (mk_B1 (y a2)) := by
  grind

example : HEq a1 (x a2) → HEq a2 (y a1) → HEq (mk_B1 (x (y a1))) (mk_B1 (x (y (x a2)))) := by
  grind

-- Fails from this point onwards:

example : HEq a1 (y a2) → HEq (mk_B1 a1) (mk_B2 (y a2)) →
    HEq (f (mk_C1 (mk_B2 a1))) (f (mk_C2 (mk_B1 (y a2)))) := by
  grind

example : HEq a1 (y a2) → HEq (tr_B (mk_B1 a1)) (mk_B2 (y a2)) →
    HEq (f (mk_C1 (mk_B2 a1))) (f (mk_C2 (tr_B (mk_B1 (y a2))))) := by
  grind

example : HEq a1 (y a2) → HEq (mk_B1 a1) (mk_B2 (y a2)) →
    HEq (g (f (mk_C1 (mk_B2 a1)))) (g (f (mk_C2 (mk_B1 (y a2))))) := by
  grind

example : HEq a1 (y a2) → HEq (tr_B (mk_B1 a1)) (mk_B2 (y a2)) →
    HEq (g (f (mk_C1 (mk_B2 a1)))) (g (f (mk_C2 (tr_B (mk_B1 (y a2)))))) := by
  grind

example : HEq a1 (y a2) → HEq a2 (z a3) → HEq a3 (x a1) → HEq (mk_B1 a1) (mk_B2 (y (z (x a1)))) →
          HEq (f (mk_C1 (mk_B2 (y (z (x a1)))))) (f' (mk_C2 (mk_B1 a1))) →
          HEq (g (f (mk_C1 (mk_B2 (y (z (x a1))))))) (g (f' (mk_C2 (mk_B1 a1)))) := by
  grind

example : HEq a1 (y a2) → HEq a2 (z a3) → HEq a3 (x a1) → HEq (mk_B1 a1) (mk_B2 (y (z (x a1)))) →
          HEq (f (mk_C1 (mk_B2 (y (z (x a1)))))) (f' (mk_C2 (mk_B1 a1))) →
          HEq (f' (mk_C1 (mk_B1 a1))) (f (mk_C2 (mk_B2 (y (z (x a1)))))) →
          HEq (g (f (mk_C1 (mk_B1 (y (z (x a1))))))) (g (f' (mk_C2 (mk_B2 a1)))) := by
  grind

example : HEq a1 (y a2) → HEq a2 (z a3) → HEq a3 (x a1) →
          HEq (tr_B (mk_B1 a1)) (mk_B2 (y (z (x a1)))) →
          HEq (f (mk_C1 (mk_B2 (y (z (x a1)))))) (f' (mk_C2 (tr_B (mk_B1 a1)))) →
          HEq (f' (mk_C1 (tr_B (mk_B1 a1)))) (f (mk_C2 (mk_B2 (y (z (x a1)))))) →
          HEq (g (f (mk_C1 (tr_B (mk_B1 (y (z (x a1)))))))) (g (f' (mk_C2 (mk_B2 a1)))) := by
  grind
