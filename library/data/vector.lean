-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn, Leonardo de Moura
import data.nat.basic data.empty data.prod
open nat eq.ops prod

inductive vector (T : Type) : ℕ → Type :=
  nil {} : vector T 0,
  cons : T → ∀{n}, vector T n → vector T (succ n)

namespace vector
  notation a :: b := cons a b
  notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

  variables {A B C : Type}
  variables {n m : nat}

  protected definition is_inhabited [instance] (H : inhabited A) (n : nat) : inhabited (vector A n) :=
  nat.rec_on n
    (inhabited.mk nil)
    (λ (n : nat) (iH : inhabited (vector A n)),
      inhabited.destruct H
        (λa, inhabited.destruct iH
          (λv, inhabited.mk (a :: v))))

  theorem z_cases_on {C : vector A 0 → Type} (v : vector A 0) (Hnil : C nil) : C v :=
  have aux : ∀ (n₁ : nat) (v₁ : vector A n₁) (eq₁ : n₁ = 0) (eq₂ : v₁ == v) (Hnil : C nil), C v, from
    λ n₁ v₁, vector.rec_on v₁
      (λ (eq₁ : 0 = 0) (eq₂ : nil == v) (Hnil : C nil), eq.rec_on (heq.to_eq eq₂) Hnil)
      (λ h₂ n₂ v₂ ih eq₁ eq₂ hnil, nat.no_confusion eq₁),
  aux 0 v rfl !heq.refl Hnil

  theorem vector0_eq_nil (v : vector A 0) : v = nil :=
  z_cases_on v rfl

  protected definition destruct (v : vector A (succ n)) {P : Π {n : nat}, vector A (succ n) → Type}
                      (H : Π {n : nat} (h : A) (t : vector A n), P (h :: t)) : P v :=
  have aux : ∀ (n₁ : nat) (v₁ : vector A n₁) (eq₁ : n₁ = succ n) (eq₂ : v₁ == v), P v, from
    (λ n₁ v₁, vector.rec_on v₁
       (λ eq₁, nat.no_confusion eq₁)
       (λ h₂ n₂ v₂ ih eq₁ eq₂,
          nat.no_confusion eq₁ (λ e₃ : n₂ = n,
            have aux : Π (n₂ : nat) (e₃ : n₂ = n) (v₂ : vector A n₂) (eq₂ : h₂ :: v₂ == v), P v, from
              λ n₂ e₃, eq.rec_on (eq.rec_on e₃ rfl)
                (λ (v₂ : vector A n) (eq₂ : h₂ :: v₂ == v),
                  have Phv : P (h₂ :: v₂), from H h₂ v₂,
                  eq.rec_on (heq.to_eq eq₂) Phv),
            aux n₂ e₃ v₂ eq₂))),
  aux (succ n) v rfl !heq.refl

  definition nz_cases_on := @destruct

  definition head (v : vector A (succ n)) : A :=
  destruct v (λ n h t, h)

  definition tail (v : vector A (succ n)) : vector A n :=
  destruct v (λ n h t, t)

  theorem head_cons (h : A) (t : vector A n) : head (h :: t) = h :=
  rfl

  theorem tail_cons (h : A) (t : vector A n) : tail (h :: t) = t :=
  rfl

  theorem eta (v : vector A (succ n)) : head v :: tail v = v :=
  -- TODO(Leo): replace 'head_cons h t ▸ tail_cons h t ▸ rfl' with rfl
  -- after issue #318 is fixed
  destruct v (λ n h t, head_cons h t ▸ tail_cons h t ▸ rfl)

  definition last : vector A (succ n) → A :=
  nat.rec_on n
    (λ (v : vector A (succ zero)), head v)
    (λ n₁ r v, r (tail v))

  theorem last_singleton (a : A) : last (a :: nil) = a :=
  rfl

  theorem last_cons (a : A) (v : vector A (succ n)) : last (a :: v) = last v :=
  rfl

  definition const (n : nat) (a : A) : vector A n :=
  nat.rec_on n
    nil
    (λ n₁ r, a :: r)

  theorem head_const (n : nat) (a : A) : head (const (succ n) a) = a :=
  rfl

  theorem last_const (n : nat) (a : A) : last (const (succ n) a) = a :=
  nat.induction_on n
    rfl
    (λ n₁ ih, ih)

  definition map (f : A → B) (v : vector A n) : vector B n :=
  nat.rec_on n
    (λ v, nil)
    (λ n₁ r v, f (head v) :: r (tail v))
    v

  theorem map_vnil (f : A → B) : map f nil = nil :=
  rfl

  theorem map_vcons (f : A → B) (h : A) (t : vector A n) : map f (h :: t) =  f h :: map f t :=
  rfl

  definition map2 (f : A → B → C) (v₁ : vector A n) (v₂ : vector B n) : vector C n :=
  nat.rec_on n
    (λ v₁ v₂, nil)
    (λ n₁ r v₁ v₂, f (head v₁) (head v₂) :: r (tail v₁) (tail v₂))
    v₁ v₂

  theorem map2_vnil (f : A → B → C) : map2 f nil nil = nil :=
  rfl

  theorem map2_vcons (f : A → B → C) (h₁ : A) (h₂ : B) (t₁ : vector A n) (t₂ : vector B n) :
                     map2 f (h₁ :: t₁) (h₂ :: t₂) = f h₁ h₂ :: map2 f t₁ t₂ :=
  rfl

  definition append_core (w : vector A m) (v : vector A n) : vector A (n + m) :=
  rec_on w
    v
    (λ (a₁ : A) (m₁ : nat) (v₁ : vector A m₁) (r₁ : vector A (n + m₁)), a₁ :: r₁)

  theorem append_vnil (v : vector A n) : append_core nil v = v :=
  rfl

  theorem append_vcons (h : A) (t : vector A n) (v : vector A m) :
    append_core (h :: t) v = h :: (append_core t v) :=
  rfl

  definition append (w : vector A n) (v : vector A m) : vector A (n + m) :=
  eq.rec_on !add.comm (append_core w v)

  definition unzip : vector (A × B) n → vector A n × vector B n :=
  nat.rec_on n
    (λ v, (nil, nil))
    (λ a r v,
      let t := r (tail v) in
      (pr₁ (head v) :: pr₁ t, pr₂ (head v) :: pr₂ t))

  definition zip : vector A n → vector B n → vector (A × B) n :=
  nat.rec_on n
    (λ v₁ v₂, nil)
    (λ a r v₁ v₂, (head v₁, head v₂) :: r (tail v₁) (tail v₂))

  theorem unzip_zip : ∀ (v₁ : vector A n) (v₂ : vector B n), unzip (zip v₁ v₂) = (v₁, v₂) :=
  nat.induction_on n
    (λ (v₁ : vector A zero) (v₂ : vector B zero),
       z_cases_on v₁ (z_cases_on v₂ rfl))
    (λ (n₁ : nat) (ih : ∀ (v₁ : vector A n₁) (v₂ : vector B n₁), unzip (zip v₁ v₂) = (v₁, v₂))
       (v₁ : vector A (succ n₁)) (v₂ : vector B (succ n₁)), calc
       unzip (zip v₁ v₂) = unzip ((head v₁, head v₂) :: zip (tail v₁) (tail v₂)) : rfl
                     ... = (head v₁ :: pr₁ (unzip (zip (tail v₁) (tail v₂))),
                            head v₂ :: pr₂ (unzip (zip (tail v₁) (tail v₂))))    : rfl
                     ... = (head v₁ :: pr₁ (tail v₁, tail v₂),
                            head v₂ :: pr₂ (tail v₁, tail v₂))                   : ih
                     ... = (head v₁ :: tail v₁, head v₂ :: tail v₂)              : rfl
                     ... = (v₁, head v₂ :: tail v₂)                              : vector.eta
                     ... = (v₁, v₂)                                              : vector.eta)

  theorem zip_unzip : ∀ (v : vector (A × B) n), zip (pr₁ (unzip v)) (pr₂ (unzip v)) = v :=
  nat.induction_on n
    (λ (v : vector (A × B) zero),
       z_cases_on v rfl)
    (λ (n₁ : nat) (ih : ∀ v, zip (pr₁ (unzip v)) (pr₂ (unzip v)) = v) (v : vector (A × B) (succ n₁)), calc
       zip (pr₁ (unzip v)) (pr₂ (unzip v)) = zip (pr₁ (head v) :: pr₁ (unzip (tail v)))
                                                 (pr₂ (head v) :: pr₂ (unzip (tail v)))                  : rfl
                 ... = (pr₁ (head v), pr₂ (head v)) :: zip (pr₁ (unzip (tail v))) (pr₂ (unzip (tail v))) : rfl
                 ... = (pr₁ (head v), pr₂ (head v)) :: tail v                                            : ih
                 ... = head v :: tail v                                                                  : prod.eta
                 ... = v                                                                                 : vector.eta)

  -- Length
  -- ------

  definition length (v : vector A n) :=
  n

  theorem length_nil : length (@nil A) = 0 :=
  rfl

  theorem length_cons (a : A) (v : vector A n) : length (a :: v) = succ (length v) :=
  rfl

  theorem length_append (v₁ : vector A n) (v₂ : vector A m) : length (append v₁ v₂) = length v₁ + length v₂ :=
  rfl

  -- Concat
  -- ------
  definition concat (v : vector A n) (a : A) : vector A (succ n) :=
  vector.rec_on v
    (a :: nil)
    (λ h n t r, h :: r)

  theorem concat_nil (a : A) : concat nil a = a :: nil :=
  rfl

  theorem last_concat (v : vector A n) (a : A) : last (concat v a) = a :=
  vector.induction_on v
    rfl
    (λ h n t ih, calc
      last (concat (h :: t) a) = last (concat t a) : rfl
                           ... = a : ih)

end vector
