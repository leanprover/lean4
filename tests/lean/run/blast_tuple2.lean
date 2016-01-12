import data.fin
open function

constant tuple.{l} : Type.{l} → nat → Type.{l}
constant nil {A : Type} : tuple A 0
constant cons {A : Type} {n : nat} : A → tuple A n → tuple A (nat.succ n)
constant append {A : Type} {n m : nat} : tuple A n → tuple A m → tuple A (n + m)
constant reverse {A : Type} {n : nat} : tuple A n → tuple A n
constant map {A B : Type} {n : nat} : (A → B) → tuple A n → tuple B n
constant ith {A : Type} {n : nat} : tuple A n → fin n → A
constant tail {A : Type} {n : nat} : tuple A (nat.succ n) → tuple A n

infix ` ++ ` := append
axiom append_nil {A : Type} {n : nat} (v : tuple A n) : v ++ nil = v
axiom nil_append {A : Type} {n : nat} (v : tuple A n) : nil ++ v == v
axiom append_assoc {A : Type} {n₁ n₂ n₃ : nat} (v₁ : tuple A n₁) (v₂ : tuple A n₂) (v₃ : tuple A n₃) : (v₁ ++ v₂) ++ v₃ == v₁ ++ (v₂ ++ v₃)

axiom reverse_reverse {A : Type} {n : nat} (v : tuple A n) : reverse (reverse v) = v
axiom map_cons {A B : Type} {n : nat} (f : A → B) (a : A) (v : tuple A n) : map f (cons a v) = cons (f a) (map f v)
axiom map_map {A B C : Type} {n : nat} (g : B → C) (f : A → B) (v : tuple A n) : map g (map f v) = map (g ∘ f) v
axiom ith_succ_eq_ith_tail {A : Type} {n : nat} (v : tuple A (nat.succ n)) (i : fin n) : ith v (fin.succ i) = ith (tail v) i

attribute append_nil nil_append append_assoc reverse_reverse map_cons map_map ith_succ_eq_ith_tail [simp]

set_option blast.strategy "cc"
set_option blast.cc.heq true
set_option blast.cc.subsingleton true

universes l1 l2 l3
constants {A : Type.{l1}} (a b c : A) (f g : A → A)
          (m n p q : ℕ)
          (xs : tuple A m) (ys : tuple A n) (zs : tuple A p) (ws : tuple A q)
          {B : Type.{l2}} (h1 h2 : A → B)
          {C : Type.{l3}} (k1 k2 : B → C)

example : a = b → m = n → xs == ys → cons a xs == cons b ys := by blast
example : a = b → b = c → m = n → n = p → xs == ys → ys == zs → cons a (cons b xs) == cons c (cons a zs) := by blast
example : a = b → b = c → m = n → n = p → xs == ys → ys == zs → cons (f a) (cons (g b) xs) == cons (f c) (cons (g a) zs) := by blast

example : m = n → xs == ys → xs ++ zs == ys ++ zs := by blast
example : m = n → p = q → xs == ys → zs == ws → xs ++ zs == ys ++ ws := by blast

example : m = n → xs == ys → nil ++ xs == ys := by inst_simp
example : (xs ++ ys) ++ zs == xs ++ (ys ++ zs) := by inst_simp
example : p = m + n → zs == xs ++ ys → zs ++ ws == (xs ++ ys) ++ ws := by inst_simp
example : m + n = p → xs ++ ys == zs → zs ++ ws == xs ++ (ys ++ ws) := by inst_simp
        
example : m = n → p = q → m + n = p → xs == ys → zs == ws → xs ++ ys == zs → ws ++ ws == (ys ++ xs) ++ (xs ++ ys) := by inst_simp

example : m = n → n = p → xs == reverse ys → ys == reverse zs → xs == zs := by inst_simp

example : m = n → xs == ys → f = g → a = b → map f (cons a xs) == cons (g b) (map g ys) := by 
inst_simp

attribute function.compose [semireducible]
example : m = n → xs == ys → h1 = h2 → k1 = k2 → map k1 (map h1 xs) == map (k2 ∘ h2) ys := by inst_simp

example : ∀ (xs : tuple A (nat.succ m)) (ys : tuple A (nat.succ n))
            (i : fin m) (j : fin n),
            m = n → i == j → xs == ys → ith xs (fin.succ i) == ith (tail ys) j := by inst_simp
