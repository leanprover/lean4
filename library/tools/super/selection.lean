/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .prover_state

namespace super

meta def simple_selection_strategy (f : (expr → expr → bool) → clause → list ℕ) : selection_strategy :=
take dc, do gt ← get_term_order, return $
         if dc^.selected^.empty ∧ dc^.c^.num_lits > 0
         then { dc with selected := f gt dc^.c }
         else dc

meta def dumb_selection : selection_strategy :=
simple_selection_strategy $ λgt c,
match c^.lits_where clause.literal.is_neg with
| [] := list.range c^.num_lits
| neg_lit::_ := [neg_lit]
end

meta def selection21 : selection_strategy :=
simple_selection_strategy $ λgt c,
let maximal_lits := list.filter_maximal (λi j,
  gt (c^.get_lit i)^.formula (c^.get_lit j)^.formula) (list.range c^.num_lits) in
if list.length maximal_lits = 1 then maximal_lits else
let neg_lits := list.filter (λi, (c^.get_lit i)^.is_neg) (list.range c^.num_lits),
    maximal_neg_lits := list.filter_maximal (λi j,
      gt (c^.get_lit i)^.formula (c^.get_lit j)^.formula) neg_lits in
if ¬maximal_neg_lits^.empty then
  list.taken 1 maximal_neg_lits
else
  maximal_lits

meta def selection22 : selection_strategy :=
simple_selection_strategy $ λgt c,
let maximal_lits := list.filter_maximal (λi j,
  gt (c^.get_lit i)^.formula (c^.get_lit j)^.formula) (list.range c^.num_lits),
  maximal_lits_neg := list.filter (λi, (c^.get_lit i)^.is_neg) maximal_lits in
if ¬maximal_lits_neg^.empty then
  list.taken 1 maximal_lits_neg
else
  maximal_lits

meta def clause_weight (c : derived_clause) : nat :=
(c^.c^.get_lits^.for (λl, expr_size l^.formula + if l^.is_pos then 10 else 1))^.sum

meta def find_minimal_by (passive : rb_map clause_id derived_clause)
                         {A} [has_ordering A]
                         (f : derived_clause → A) : clause_id :=
match rb_map.min $ rb_map.of_list $ passive^.values^.map $ λc, (f c, c^.id) with
| some id := id
| none := nat.zero
end

meta def age_of_clause_id : name → ℕ
| (name.mk_numeral i _) := unsigned.to_nat i
| _ := 0

meta def find_minimal_weight (passive : rb_map clause_id derived_clause) : clause_id :=
find_minimal_by passive $ λc, (c^.sc^.priority, clause_weight c + c^.sc^.cost, c^.sc^.age, c^.id)

meta def find_minimal_age (passive : rb_map clause_id derived_clause) : clause_id :=
find_minimal_by passive $ λc, (c^.sc^.priority, c^.sc^.age, c^.id)

meta def weight_clause_selection : clause_selection_strategy :=
take iter, do state ← state_t.read, return $ find_minimal_weight state^.passive

meta def oldest_clause_selection : clause_selection_strategy :=
take iter, do state ← state_t.read, return $ find_minimal_age state^.passive

meta def age_weight_clause_selection (thr mod : ℕ) : clause_selection_strategy :=
take iter, if iter % mod < thr then
              weight_clause_selection iter
           else
              oldest_clause_selection iter

end super
