/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn, Leonardo de Moura
-/
import data.nat data.list data.fin
open nat prod fin

inductive vector (A : Type) : nat → Type :=
| nil {} : vector A zero
| cons   : Π {n}, A → vector A n → vector A (succ n)

namespace vector
  notation a :: b := cons a b
  notation `[` l:(foldr `,` (h t, cons h t) nil `]`) := l

  variables {A B C : Type}

  protected definition is_inhabited [instance] [h : inhabited A] : ∀ (n : nat), inhabited (vector A n)
  | 0     := inhabited.mk []
  | (n+1) := inhabited.mk (inhabited.value h :: inhabited.value (is_inhabited n))

  theorem vector0_eq_nil : ∀ (v : vector A 0), v = []
  | [] := rfl

  definition head : Π {n : nat}, vector A (succ n) → A
  | n (a::v) := a

  definition tail : Π {n : nat}, vector A (succ n) → vector A n
  | n (a::v) := v

  theorem head_cons {n : nat} (h : A) (t : vector A n) : head (h :: t) = h :=
  rfl

  theorem tail_cons {n : nat} (h : A) (t : vector A n) : tail (h :: t) = t :=
  rfl

  theorem eta : ∀ {n : nat} (v : vector A (succ n)), head v :: tail v = v
  | n (a::v) := rfl

  definition last : Π {n : nat}, vector A (succ n) → A
  | last [a]    := a
  | last (a::v) := last v

  theorem last_singleton (a : A) : last [a] = a :=
  rfl

  theorem last_cons {n : nat} (a : A) (v : vector A (succ n)) : last (a :: v) = last v :=
  rfl

  definition const : Π (n : nat), A → vector A n
  | 0        a := []
  | (succ n) a := a :: const n a

  theorem head_const (n : nat) (a : A) : head (const (succ n) a) = a :=
  rfl

  theorem last_const : ∀ (n : nat) (a : A), last (const (succ n) a) = a
  | 0     a := rfl
  | (n+1) a := last_const n a

  definition nth : Π {n : nat}, vector A n → fin n → A
  | ⌞0⌟   []       i               := elim0 i
  | ⌞n+1⌟ (a :: v) (mk 0 _)        := a
  | ⌞n+1⌟ (a :: v) (mk (succ i) h) := nth v (mk_pred i h)

  lemma nth_zero {n : nat} (a : A) (v : vector A n) (h : 0 < succ n) : nth (a::v) (mk 0 h) = a :=
  rfl

  lemma nth_succ {n : nat} (a : A) (v : vector A n) (i : nat) (h : succ i < succ n)
                 : nth (a::v) (mk (succ i) h) = nth v (mk_pred i h) :=
  rfl

  definition tabulate : Π {n : nat}, (fin n → A) → vector A n
  | 0      f :=  []
  | (n+1)  f :=  f (@zero n) :: tabulate (λ i : fin n, f (succ i))

  theorem nth_tabulate : ∀ {n : nat} (f : fin n → A) (i : fin n), nth (tabulate f) i = f i
  | 0     f i               := elim0 i
  | (n+1) f (mk 0 h)        := by reflexivity
  | (n+1) f (mk (succ i) h) :=
    begin
      change nth (f (@zero n) :: tabulate (λ i : fin n, f (succ i))) (mk (succ i) h) = f (mk (succ i) h),
      rewrite nth_succ,
      rewrite nth_tabulate
    end

  definition map (f : A → B) : Π {n : nat}, vector A n → vector B n
  | map []     := []
  | map (a::v) := f a :: map v

  theorem map_nil (f : A → B) : map f [] = [] :=
  rfl

  theorem map_cons {n : nat} (f : A → B) (h : A) (t : vector A n) : map f (h :: t) =  f h :: map f t :=
  rfl

  theorem nth_map (f : A → B) : ∀ {n : nat} (v : vector A n) (i : fin n), nth (map f v) i = f (nth v i)
  | 0        v        i               := elim0 i
  | (succ n) (a :: t) (mk 0 h)        := by reflexivity
  | (succ n) (a :: t) (mk (succ i) h) := by rewrite [map_cons, *nth_succ, nth_map]

  section
  open function
  theorem map_id : ∀ {n : nat} (v : vector A n), map id v = v
  | 0        []      := rfl
  | (succ n) (x::xs) := by rewrite [map_cons, map_id]

  theorem map_map (g : B → C) (f : A → B) : ∀ {n :nat} (v : vector A n), map g (map f v) = map (g ∘ f) v
  | 0        []       := rfl
  | (succ n) (a :: l) :=
    show (g ∘ f) a :: map g (map f l) = map (g ∘ f) (a :: l),
    by rewrite (map_map l)
  end

  definition map2 (f : A → B → C) : Π {n : nat}, vector A n → vector B n → vector C n
  | map2 []      []      := []
  | map2 (a::va) (b::vb) := f a b :: map2 va vb

  theorem map2_nil (f : A → B → C) : map2 f [] [] = [] :=
  rfl

  theorem map2_cons {n : nat} (f : A → B → C) (h₁ : A) (h₂ : B) (t₁ : vector A n) (t₂ : vector B n) :
                    map2 f (h₁ :: t₁) (h₂ :: t₂) = f h₁ h₂ :: map2 f t₁ t₂ :=
  rfl

  definition append : Π {n m : nat}, vector A n → vector A m → vector A (n ⊕ m)
  | 0        m []     w := w
  | (succ n) m (a::v) w := a :: (append v w)

  theorem append_nil_left {n : nat} (v : vector A n) : append [] v = v :=
  rfl

  theorem append_cons {n m : nat} (h : A) (t : vector A n) (v : vector A m) :
    append (h::t) v = h :: (append t v) :=
  rfl

  theorem map_append (f : A → B) : ∀ {n m : nat} (v : vector A n) (w : vector A m), map f (append v w) = append (map f v) (map f w)
  | 0     m   []        w   :=  rfl
  | (n+1) m   (h :: t)  w   :=
     begin
       change (f h :: map f (append t w) = f h :: append (map f t) (map f w)),
       rewrite map_append
     end

  definition unzip : Π {n : nat}, vector (A × B) n → vector A n × vector B n
  | unzip []            := ([], [])
  | unzip ((a, b) :: v) := (a :: pr₁ (unzip v), b :: pr₂ (unzip v))

  theorem unzip_nil : unzip (@nil (A × B)) = ([], []) :=
  rfl

  theorem unzip_cons {n : nat} (a : A) (b : B) (v : vector (A × B) n) :
       unzip ((a, b) :: v) = (a :: pr₁ (unzip v), b :: pr₂ (unzip v)) :=
  rfl

  definition zip : Π {n : nat}, vector A n → vector B n → vector (A × B) n
  | zip []      []      := []
  | zip (a::va) (b::vb) := ((a, b) :: zip va vb)

  theorem zip_nil_nil : zip (@nil A) (@nil B) = nil :=
  rfl

  theorem zip_cons_cons {n : nat} (a : A) (b : B) (va : vector A n) (vb : vector B n) :
      zip (a::va) (b::vb) = ((a, b) :: zip va vb) :=
  rfl

  theorem unzip_zip : ∀ {n : nat} (v₁ : vector A n) (v₂ : vector B n), unzip (zip v₁ v₂) = (v₁, v₂)
  | 0     []      []      := rfl
  | (n+1) (a::va) (b::vb) := calc
       unzip (zip (a :: va) (b :: vb))
             = (a :: pr₁ (unzip (zip va vb)), b :: pr₂ (unzip (zip va vb))) : rfl
        ...  = (a :: pr₁ (va, vb), b :: pr₂ (va, vb))                       : by rewrite unzip_zip
        ...  = (a :: va, b :: vb)                                           : rfl

  theorem zip_unzip : ∀ {n : nat} (v : vector (A × B) n), zip (pr₁ (unzip v)) (pr₂ (unzip v)) = v
  | 0     []             := rfl
  | (n+1) ((a, b) :: v)  := calc
    zip (pr₁ (unzip ((a, b) :: v))) (pr₂ (unzip ((a, b) :: v)))
         = (a, b) :: zip (pr₁ (unzip v)) (pr₂ (unzip v)) : rfl
     ... = (a, b) :: v                                   : by rewrite zip_unzip

  /- Concat -/

  definition concat : Π {n : nat}, vector A n → A → vector A (succ n)
  | concat []     a := [a]
  | concat (b::v) a := b :: concat v a

  theorem concat_nil (a : A) : concat [] a = [a] :=
  rfl

  theorem concat_cons {n : nat} (b : A) (v : vector A n) (a : A) : concat (b :: v) a = b :: concat v a :=
  rfl

  theorem last_concat : ∀ {n : nat} (v : vector A n) (a : A), last (concat v a) = a
  | 0     []     a := rfl
  | (n+1) (b::v) a := calc
    last (concat (b::v) a) = last (concat v a) : rfl
                    ...    = a                 : last_concat v a

  /- Reverse -/

  definition reverse : Π {n : nat}, vector A n → vector A n
  | 0     []        := []
  | (n+1) (x :: xs) := concat (reverse xs) x

  theorem reverse_concat : Π {n : nat} (xs : vector A n) (a : A), reverse (concat xs a) = a :: reverse xs
  | 0     []         a := rfl
  | (n+1) (x :: xs)  a :=
    begin
      change (concat (reverse (concat xs a)) x = a :: reverse (x :: xs)),
      rewrite reverse_concat
    end

  theorem reverse_reverse : Π {n : nat} (xs : vector A n), reverse (reverse xs) = xs
  | 0     []        := rfl
  | (n+1) (x :: xs) :=
    begin
      change (reverse (concat (reverse xs) x) = x :: xs),
      rewrite [reverse_concat, reverse_reverse]
    end

  /- list <-> vector -/

  definition of_list : Π (l : list A), vector A (list.length l)
  | list.nil        := []
  | (list.cons a l) := a :: (of_list l)

  definition to_list : Π {n : nat}, vector A n → list A
  | 0     []        := list.nil
  | (n+1) (a :: vs) := list.cons a (to_list vs)

  theorem to_list_of_list : ∀ (l : list A), to_list (of_list l) = l
  | list.nil         := rfl
  | (list.cons a l)  :=
    begin
      change (list.cons a (to_list (of_list l)) = list.cons a l),
      rewrite to_list_of_list
    end

  theorem to_list_nil : to_list [] = (list.nil : list A) :=
  rfl

  theorem length_to_list : ∀ {n : nat} (v : vector A n), list.length (to_list v) = n
  | 0     []        := rfl
  | (n+1) (a :: vs) :=
    begin
      change (succ (list.length (to_list vs)) = succ n),
      rewrite length_to_list
    end

  theorem heq_of_list_eq : ∀ {n m} {v₁ : vector A n} {v₂ : vector A m}, to_list v₁ = to_list v₂ → n = m → v₁ == v₂
  | 0     0     []      []      h₁ h₂ := !heq.refl
  | 0     (m+1) []      (y::ys) h₁ h₂ := by contradiction
  | (n+1) 0     (x::xs) []      h₁ h₂ := by contradiction
  | (n+1) (m+1) (x::xs) (y::ys) h₁ h₂ :=
    assert e₁ : n = m, from succ.inj h₂,
    assert e₂ : x = y, begin unfold to_list at h₁, injection h₁, assumption end,
    have   to_list xs = to_list ys, begin unfold to_list at h₁, injection h₁, assumption end,
    assert xs == ys, from heq_of_list_eq this e₁,
    assert y :: xs == y :: ys, begin clear heq_of_list_eq h₁ h₂, revert xs ys this, induction e₁, intro xs ys h, rewrite [heq.to_eq h] end,
    show x :: xs == y :: ys, by rewrite e₂; exact this

  theorem list_eq_of_heq {n m} {v₁ : vector A n} {v₂ : vector A m} : v₁ == v₂ → n = m → to_list v₁ = to_list v₂ :=
  begin
    intro h₁ h₂, revert v₁ v₂ h₁,
    subst n, intro v₁ v₂ h₁, rewrite [heq.to_eq h₁]
  end

  theorem of_list_to_list {n : nat} (v : vector A n) : of_list (to_list v) == v :=
  begin
    apply heq_of_list_eq, rewrite to_list_of_list, rewrite length_to_list
  end

  theorem to_list_append : ∀ {n m : nat} (v₁ : vector A n) (v₂ : vector A m), to_list (append v₁ v₂) = list.append (to_list v₁) (to_list v₂)
  | 0        m        []      ys      := rfl
  | (succ n) m        (x::xs) ys      := begin unfold append, unfold to_list at {1,2}, krewrite [to_list_append xs ys] end

  theorem to_list_map (f : A → B) : ∀ {n : nat} (v : vector A n), to_list (map f v) = list.map f (to_list v)
  | 0        []      := rfl
  | (succ n) (x::xs) := begin unfold [map, to_list], rewrite to_list_map end

  theorem to_list_concat : ∀ {n : nat} (v : vector A n) (a : A), to_list (concat v a) = list.concat a (to_list v)
  | 0        []      a := rfl
  | (succ n) (x::xs) a := begin unfold [concat, to_list], rewrite to_list_concat end

  theorem to_list_reverse : ∀ {n : nat} (v : vector A n), to_list (reverse v) = list.reverse (to_list v)
  | 0        []      := rfl
  | (succ n) (x::xs) := begin unfold [reverse], rewrite [to_list_concat, to_list_reverse] end

  theorem append_nil_right {n : nat} (v : vector A n) : append v [] == v :=
  begin
    apply heq_of_list_eq,
      rewrite [to_list_append, to_list_nil, list.append_nil_right],
      rewrite [-add_eq_addl]
  end

  theorem append.assoc {n₁ n₂ n₃ : nat} (v₁ : vector A n₁) (v₂ : vector A n₂) (v₃ : vector A n₃) : append v₁ (append v₂ v₃) == append (append v₁ v₂) v₃ :=
  begin
    apply heq_of_list_eq,
      rewrite [*to_list_append, list.append.assoc],
      rewrite [-*add_eq_addl, add.assoc]
  end

  theorem reverse_append {n m : nat} (v : vector A n) (w : vector A m) : reverse (append v w) == append (reverse w) (reverse v) :=
  begin
    apply heq_of_list_eq,
      rewrite [to_list_reverse, to_list_append, list.reverse_append, to_list_append, *to_list_reverse],
      rewrite [-*add_eq_addl, add.comm]
  end

  theorem concat_eq_append {n : nat} (v : vector A n) (a : A) : concat v a == append v [a] :=
  begin
    apply heq_of_list_eq,
      rewrite [to_list_concat, to_list_append, list.concat_eq_append],
      rewrite [-add_eq_addl]
  end

  /- decidable equality -/
  open decidable
  definition decidable_eq [H : decidable_eq A] : ∀ {n : nat} (v₁ v₂ : vector A n), decidable (v₁ = v₂)
  | ⌞0⌟    []      []      := by left; reflexivity
  | ⌞n+1⌟  (a::v₁) (b::v₂) :=
    match H a b with
    | inl Hab  :=
      match decidable_eq v₁ v₂ with
      | inl He := by left; congruence; repeat assumption
      | inr Hn := by right; intro h; injection h; contradiction
      end
    | inr Hnab := by right; intro h; injection h; contradiction
  end

  section
  open equiv function
  definition vector_equiv_of_equiv {A B : Type} : A ≃ B → ∀ n, vector A n ≃ vector B n
  | (mk f g l r) n :=
    mk (map f) (map g)
     begin intros, rewrite [map_map, id_of_left_inverse l, map_id], reflexivity end
     begin intros, rewrite [map_map, id_of_righ_inverse r, map_id], reflexivity end
  end
end vector
