import data.finset
open list

namespace finset
variable {A : Type}
variable [h : decidable_eq A]
include h

set_option pp.implicit true
set_option pp.notation false

protected theorem induction₂ {P : finset A → Prop}
    (H1 : P empty)
    (H2 : ∀⦃s : finset A⦄, ∀{a : A}, a ∉ s → P s → P (insert a s)) :
  ∀s, P s :=
take s,
quot.induction_on s
  take u,
  subtype.destruct u
    take l,
    list.induction_on l
      (assume nodup_l, H1)
      (take a l',
        assume IH nodup_al',
        assert anl' : a ∉ l', from not_mem_of_nodup_cons nodup_al',
        assert H3 : list.insert a l' = a :: l', from insert_eq_of_not_mem anl',
        assert nodup_l' : nodup l', from nodup_of_nodup_cons nodup_al',
        assert P_l' : P (quot.mk (subtype.tag l' nodup_l')), from IH nodup_l',
        assert H4 : P (insert a (quot.mk (subtype.tag l' nodup_l'))), from H2 anl' P_l',
        begin rewrite [eq.symm H3], apply H4 end)
