import data.list

inductive typ : Type :=
| nat : typ
| arr : typ → typ → typ

inductive const : Type :=
| z | s

inductive exp : Type :=
| var   : nat → exp
| cnst  : const → exp
| lam   : nat → typ → exp → exp
| ap    : exp → exp → exp

open exp

inductive direct_subterm : exp → exp → Prop :=
| lam    : ∀ n t e, direct_subterm e (lam n t e)
| ap_fn  : ∀ f a, direct_subterm f (ap f a)
| ap_arg : ∀ f a, direct_subterm a (ap f a)

theorem direct_subterm_wf : well_founded direct_subterm :=
begin
  constructor, intro e, induction e,
  repeat (constructor; intro y hlt; cases hlt; repeat assumption)
end

definition subterm := tc direct_subterm

theorem subterm_wf : well_founded subterm :=
tc.wf direct_subterm_wf

inductive is_val : exp → Prop :=
| vcnst    : Π c,     is_val (cnst c)
| vlam     : Π x t e, is_val (lam x t e)
| vcnst_ap : Π {e} c, is_val e → is_val (ap (cnst c) e)

inductive step : exp → exp → Prop :=
infix `➤`:50 := step
| stepl : Π {e1 e1'} e2,     e1 ➤ e1' → ap e1 e2 ➤ ap e1' e2
| stepr : Π {e1 e2 e2'},     is_val e1 → e2 ➤ e2' → ap e1 e2 ➤ ap e1 e2'
| subst : Π {x e1 e1' e2} t, is_val e2 → ap (lam x t e1) e2 ➤ e1'

infix `➤`:50 := step

open is_val
open step

theorem nostep : ∀ {e} e', is_val e → e ➤ e' → false
| nostep e' (vcnst c) Hsteps    := by cases Hsteps
| nostep e' (vlam x t e) Hsteps := by cases Hsteps
| nostep (ap e' e) (@vcnst_ap e c Hval) (stepl e Hbad) :=
  have Hvalc : is_val (cnst c), from vcnst c,
  have IH : not (cnst c ➤ e'), from nostep e' Hvalc,
  absurd Hbad IH
| nostep (ap (cnst c) e') (@vcnst_ap e c Hvale) (stepr Hvalc Hbad) :=
  have IH : not (e ➤ e'), from nostep e' Hvale,
  absurd Hbad IH
