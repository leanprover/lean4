/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.vector
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
  | ⌞n+1⌟ (h :: t) (fz n) := h
  | ⌞n+1⌟ (h :: t) (fs f) := nth t f

  definition tabulate : Π {n : nat}, (fin n → A) → vector A n
  | 0      f :=  []
  | (n+1)  f :=  f (fz n) :: tabulate (λ i : fin n, f (fs i))

  theorem nth_tabulate : ∀ {n : nat} (f : fin n → A) (i : fin n), nth (tabulate f) i = f i
  | (n+1) f (fz n) := rfl
  | (n+1) f (fs i) :=
    begin
      change (nth (tabulate (λ i : fin n, f (fs i))) i = f (fs i)),
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
  | (succ n) (h :: t) (fz n) := rfl
  | (succ n) (h :: t) (fs i) :=
    begin
      change (nth (map f t) i = f (nth t i)),
      rewrite nth_map
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

  theorem nil_append {n : nat} (v : vector A n) : append [] v = v :=
  rfl

  theorem append_cons {n m : nat} (h : A) (t : vector A n) (v : vector A m) :
    append (h::t) v = h :: (append t v) :=
  rfl

  theorem append_nil : Π {n : nat} (v : vector A n), append v [] == v
  | 0      []     := !heq.refl
  | (n+1)  (h::t) :=
    begin
      change (h :: append t [] == h :: t),
      have H₁ : append t [] == t, from append_nil t,
      revert H₁, generalize (append t []),
      rewrite [-add_eq_addl, add_zero],
      intros [w, H₁],
      rewrite [heq.to_eq H₁],
      apply heq.refl
    end

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

  definition of_list {A : Type} : Π (l : list A), vector A (list.length l)
  | list.nil        := []
  | (list.cons a l) := a :: (of_list l)

  definition to_list {A : Type} : Π {n : nat}, vector A n → list A
  | 0     []        := list.nil
  | (n+1) (a :: vs) := list.cons a (to_list vs)

  theorem to_list_of_list {A : Type} : ∀ (l : list A), to_list (of_list l) = l
  | list.nil         := rfl
  | (list.cons a l)  :=
    begin
      change (list.cons a (to_list (of_list l)) = list.cons a l),
      rewrite to_list_of_list
    end

  theorem length_to_list {A : Type} : ∀ {n : nat} (v : vector A n), list.length (to_list v) = n
  | 0     []        := rfl
  | (n+1) (a :: vs) :=
    begin
      change (succ (list.length (to_list vs)) = succ n),
      rewrite length_to_list
    end

  theorem of_list_to_list {A : Type} : ∀ {n : nat} (v : vector A n), of_list (to_list v) == v
  | 0     []        := !heq.refl
  | (n+1) (a :: vs) :=
    begin
      change (a :: of_list (to_list vs) == a :: vs),
      have H₁ : of_list (to_list vs) == vs, from of_list_to_list vs,
      revert H₁,
      generalize (of_list (to_list vs)),
      rewrite length_to_list at *,
      intro vs', intro H,
      have H₂ : vs' = vs, from heq.to_eq H,
      rewrite H₂,
      apply heq.refl
   end

   /- decidable equality -/
  open decidable
  definition decidable_eq [H : decidable_eq A] : ∀ {n : nat} (v₁ v₂ : vector A n), decidable (v₁ = v₂)
  | ⌞0⌟    []      []      := inl rfl
  | ⌞n+1⌟  (a::v₁) (b::v₂) :=
    match H a b with
    | inl Hab  :=
      match decidable_eq v₁ v₂ with
      | inl He := inl (eq.rec_on Hab (eq.rec_on He rfl))
      | inr Hn := inr (λ H₁, vector.no_confusion H₁ (λ e₁ e₂ e₃, absurd (heq.to_eq e₃) Hn))
      end
    | inr Hnab := inr (λ H₁, vector.no_confusion H₁ (λ e₁ e₂ e₃, absurd e₂ Hnab))
  end

end vector
