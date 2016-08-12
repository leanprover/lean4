open tactic

/- User spec

f 0     0 = some 1
f 0     m = f m 0
f (n+1) m = match f n m with
            | some a := some (a+1)
            | none   := none
            end
-/

/- Define f_aux using well-founded recursion -/
constant R  : (nat × nat) → (nat × nat) → Prop
axioms R_wf : well_founded R

axiom Dec (p₂ p₁ : nat × nat) : R p₂ p₁

definition f_aux : Π (p₁ : nat × nat), (Π (p₂ : nat × nat), R p₂ p₁ → option nat) → option nat
| (0,   0)   F := some 1
| (0,   m)   F := F (m, 0) (Dec (m, 0) (0, m))
| (n+1, m) F := match F (n, m) (Dec (n,m) (n+1, m)) with
                | some a := some (a+1)
                | none   := none
                end

lemma f_aux.eq_1 (F : Π (p₂ : nat × nat), R p₂ (0,0) → option nat) : f_aux (0, 0) F = some 1 :=
rfl

lemma f_aux.eq_2 (m : nat) (F : Π (p₂ : nat × nat), R p₂ (0, m+1) → option nat) :
                      f_aux (0, m+1) F = F (m+1, 0) (Dec (m+1, 0) (0, m+1)) :=
rfl

/- The procedure is bottom-up, and will define the auxiliary function match_1 for the nexted match -/

definition match_1 : option nat → option nat
| (some a) := some (a+1)
| none     := none

lemma match_1.eq_1 (a : nat) : match_1 (some a) = some (a+1) :=
rfl

lemma match_1.eq_2 : match_1 none = none :=
rfl

lemma f_aux.eq_3 (n m : nat) (F : Π (p₂ : nat × nat), R p₂ (n+1, m) → option nat) :
                      f_aux (n+1, m) F = match_1 (F (n, m) (Dec (n,m) (n+1, m))) :=
rfl

/- "Expand" match_1 at f_aux.eq_3 -/

meta_definition rewrite_H (H : expr) : tactic unit :=
rewrite_core semireducible tt occurrences.all ff H

lemma f_aux.eq_3_a
  (n m : nat)
  (a : nat)
  (F : Π (p₂ : nat × nat), R p₂ (n+1, m) → option nat)
  (H : F (n, m) (Dec (n, m) (n+1, m)) = some a) :
     f_aux (n+1, m) F = some (a+1) :=
by do rewrite `f_aux.eq_3, get_local `H >>= rewrite_H, rewrite `match_1.eq_1

lemma f_aux.eq_3_b
  (n m : nat)
  (F : Π (p₂ : nat × nat), R p₂ (n+1, m) → option nat)
  (H : F (n, m) (Dec (n, m) (n+1, m)) = none) :
  f_aux (n+1, m) F = none :=
by do rewrite `f_aux.eq_3, get_local `H >>= rewrite_H, rewrite `match_1.eq_2

/- Define f using fix -/

definition f (n m : nat) : option nat :=
well_founded.fix R_wf f_aux (n, m)

/- Prove lemmas about 'f' using well_founded.fix_eq -/

lemma f.eq_1 : f 0 0 = some 1 :=
well_founded.fix_eq R_wf f_aux (0, 0)

lemma f.eq_2 (m : nat) : f 0 (m+1) = f (m+1) 0 :=
well_founded.fix_eq R_wf f_aux (0, m+1)

lemma f.eq_3_a (n m a : nat) (H : f n m = some a) : f (n+1) m = some (a+1) :=
eq.trans (well_founded.fix_eq R_wf f_aux (n+1, m))
         (f_aux.eq_3_a n m a (λ y h, well_founded.fix R_wf f_aux y) H)

lemma f.eq_3_b (n m : nat) (H : f n m = none) : f (n+1) m = none :=
eq.trans (well_founded.fix_eq R_wf f_aux (n+1, m))
         (f_aux.eq_3_b n m (λ y h, well_founded.fix R_wf f_aux y) H)

/- Create f_aux.ind based on the structure of f_aux and generated equations -/

lemma f_aux.ind
  (C  : nat → nat → Type)
  (m₁ : C 0 0)
  (m₂ : ∀ m, C 0 m)
  (m₃ : ∀ n m a, f n m = some a → C n m → C (n+1) m)
  (m₄ : ∀ n m, f n m = none → C n m → C (n+1) m) :
  Π (p₁ : nat × nat), (Π (p₂ : nat × nat), R p₂ p₁ → C (pr₁ p₂) (pr₂ p₂)) → C (pr₁ p₁) (pr₂ p₁)
| (0,   0)   F := m₁
| (0,   m)   F := m₂ m
| (n+1, m)   F :=
  have C n m, from F (n, m) (Dec (n, m) (n+1, m)),
  match f n m, rfl : ∀ x, f n m = x → _ with
  | some a, H₁  := m₃ n m a H₁ this
  | none,   H₂  := m₄ n m H₂ this
  end

lemma f.ind
  (C  : nat → nat → Type)
  (m₁ : C 0 0)
  (m₂ : ∀ m, C 0 m)
  (m₃ : ∀ n m a, f n m = some a → C n m → C (n+1) m)
  (m₄ : ∀ n m, f n m = none → C n m → C (n+1) m)
  (n m : nat) : C n m :=
well_founded.fix R_wf (f_aux.ind C m₁ m₂ m₃ m₄) (n, m)

constant unpair : nat → nat × nat
constant decode (A : Type) : nat → option A
constant decode_list (A : Type) : nat → nat → option (list A)
/-
User spec
definition decode_list_core : nat → nat → option (list A)
| 0        v  := some []
| (succ n) v  :=
  match unpair v with
  | (v₁, v₂) :=
    match decode A v₁ with
    | some a :=
      match decode_list_core n v₂ with
      | some l := some (a::l)
      | none   := none
      end
    | none   := none
    end
  end
-/

lemma decode_list_aux.ind
 (A  : Type)
 (C  : nat → nat → Type)
 (m₁ : ∀ v, C 0 v)
 (m₂ : ∀ n v v₁ v₂ a ls, unpair v = (v₁, v₂) → decode A v₁ = some a → decode_list A n v₂ = some ls → C n v₂ → C (n+1) v)
 (m₃ : ∀ n v v₁ v₂ a,    unpair v = (v₁, v₂) → decode A v₁ = some a → decode_list A n v₂ = none    → C n v₂ → C (n+1) v)
 (m₄ : ∀ n v v₁ v₂,      unpair v = (v₁, v₂) → decode A v₁ = none                                           → C (n+1) v) :
 Π (p₁ : nat × nat), (Π (p₂ : nat × nat), R p₂ p₁ → C (pr₁ p₂) (pr₂ p₂)) → C (pr₁ p₁) (pr₂ p₁)
| (0, v)   F := m₁ v
| (n+1, v) F :=
  match unpair v, rfl : ∀ x, unpair v = x → _ with
  | (v₁, v₂), Heq₁ :=
    match decode A v₁, rfl : ∀ x, decode A v₁ = x → _ with
    | some a, Heq₂  :=
      have aux : R (n, v₂) (n+1, v) → C n v₂, from F (n, v₂),
      have C n v₂, from aux (Dec (n, v₂) (n+1, v)),
      match decode_list A n v₂, rfl : ∀ x, decode_list A n v₂ = x → _ with
      | some ls, He₃ := m₂ n v v₁ v₂ a ls Heq₁ Heq₂ He₃ this
      | none,    He₃ := m₃ n v v₁ v₂ a Heq₁ Heq₂ He₃ this
      end
    | none,   Heq₂  := m₄ n v v₁ v₂ Heq₁ Heq₂
    end
  end

lemma decode_list.ind
 (A  : Type)
 (C  : nat → nat → Type)
 (m₁ : ∀ v, C 0 v)
 (m₂ : ∀ n v v₁ v₂ a ls, unpair v = (v₁, v₂) → decode A v₁ = some a → decode_list A n v₂ = some ls → C n v₂ → C (n+1) v)
 (m₃ : ∀ n v v₁ v₂ a,    unpair v = (v₁, v₂) → decode A v₁ = some a → decode_list A n v₂ = none    → C n v₂ → C (n+1) v)
 (m₄ : ∀ n v v₁ v₂,      unpair v = (v₁, v₂) → decode A v₁ = none                                           → C (n+1) v)
 (n m : nat) : C n m :=
well_founded.fix R_wf (decode_list_aux.ind A C m₁ m₂ m₃ m₄) (n, m)
