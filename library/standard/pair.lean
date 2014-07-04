-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic

inductive pair (A : Type) (B : Type) : Type :=
| mk_pair : A → B → pair A B

section
  parameter {A : Type}
  parameter {B : Type}

  definition fst [inline] (p : pair A B) := pair_rec (λ x y, x) p
  definition snd [inline] (p : pair A B) := pair_rec (λ x y, y) p

  theorem pair_inhabited [instance] (H1 : inhabited A) (H2 : inhabited B) : inhabited (pair A B)
  := inhabited_elim H1 (λ a, inhabited_elim H2 (λ b, inhabited_intro (mk_pair a b)))

  theorem fst_mk_pair (a : A) (b : B) : fst (mk_pair a b) = a
  := refl a

  theorem snd_mk_pair (a : A) (b : B) : snd (mk_pair a b) = b
  := refl b

  theorem pair_ext (p : pair A B) : mk_pair (fst p) (snd p) = p
  := pair_rec (λ x y, refl (mk_pair x y)) p
end

-- notation for n-ary tuples
notation `(` h `,` t:(foldl `,` (e r, mk_pair r e) h) `)` := t
