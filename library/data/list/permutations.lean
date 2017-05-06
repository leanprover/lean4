/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
universes u v

namespace list
variables {α : Type u} {β : Type v}
open nat prod well_founded

def permutations_aux2 (t : α) (ts : list α) : list α → (list α → β) → list β → list α × list β
| []      f r := (ts, r)
| (y::ys) f r := let (us, zs) := permutations_aux2 ys (λx : list α, f (y::x)) r in
                (y :: us, f (t :: y :: us) :: zs)

private def meas : list α × list α → ℕ × ℕ | (l, i) := (length l + length i, length l)

local infix ` ≺ `:50 := inv_image (lex (<) (<)) meas

def permutations_aux.F : Π (x : list α × list α), (Π (y : list α × list α), y ≺ x → list (list α)) → list (list α)
| ([],    is) IH := []
| (t::ts, is) IH :=
have h1 : (ts, t :: is) ≺ (t :: ts, is), from
  show lex _ _ (succ (length ts + length is), length ts) (succ (length ts) + length is, length (t :: ts)),
  by rw nat.succ_add; exact lex.right _ _ (lt_succ_self _),
have h2 : (is, []) ≺ (t :: ts, is), from lex.left _ _ _ (lt_add_of_pos_left _ (succ_pos _)),
foldr (λy r, (permutations_aux2 t ts y id r).2) (IH (ts, t::is) h1) (is :: IH (is, []) h2)

def permutations_aux : list α × list α → list (list α) :=
fix (inv_image.wf meas (prod.lex_wf lt_wf lt_wf)) permutations_aux.F

def permutations (l : list α) : list (list α) :=
l :: permutations_aux (l, [])

def permutations_aux.eqn_1 (is : list α) : permutations_aux ([], is) = [] :=
fix_eq _ _ _

def permutations_aux.eqn_2 (t : α) (ts is) : permutations_aux (t::ts, is) =
  foldr (λy r, (permutations_aux2 t ts y id r).2) (permutations_aux (ts, t::is)) (permutations is) :=
fix_eq _ _ _

end list
