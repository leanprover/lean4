// Lean compiler output
// Module: init.core
// Imports:
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_xor;
obj* l_cast___rarg(obj*);
uint8 l_bor___main(uint8, uint8);
obj* l_unit_star;
uint8 l_forall__prop__decidable___rarg(uint8, obj*);
obj* l_bor___boxed(obj*, obj*);
obj* l_or_intro__left;
obj* l_or_by__cases___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_or_by__cases(obj*, obj*);
obj* l_nonempty__of__inhabited;
obj* l_psigma_has__sizeof(obj*, obj*);
obj* l_quotient_mk(obj*, obj*);
uint8 l_prod__has__decidable__lt___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_band___main(uint8, uint8);
uint8 l_sum_decidable__eq___rarg(obj*, obj*, obj*, obj*);
uint8 l_xor_decidable___rarg(uint8, uint8);
uint8 l_ite_decidable___rarg(uint8, uint8, uint8);
uint8 l_true_decidable;
obj* l_inline___rarg(obj*);
obj* l_setoid__has__equiv(obj*, obj*);
obj* l_or_decidable(obj*, obj*);
obj* l_fun_inhabited___rarg(obj*, obj*);
obj* l_gt;
obj* l___private_init_core_26__fun__to__extfun___rarg(obj*);
obj* l_bool_inhabited___boxed;
obj* l_superset;
obj* l_bxor___boxed(obj*, obj*);
obj* l_nat_sizeof___main(obj*);
obj* l_typed__expr___rarg(obj*);
obj* l_bool_sizeof___boxed(obj*);
obj* l_decidable_to__bool___rarg___boxed(obj*);
obj* l_total;
uint8 l_decidable__of__decidable__of__eq___rarg(uint8, obj*);
obj* l_std_priority_max;
obj* l_quot_rec___rarg(obj*, obj*, obj*);
obj* l_or_intro__right;
obj* l_ne;
obj* l_thunk_pure___boxed(obj*, obj*);
obj* l_prod_has__lt(obj*, obj*, obj*, obj*);
obj* l_eq_ndrec__on(obj*, obj*, obj*, obj*, obj*);
obj* l_inline(obj*);
obj* l_quotient_decidable__eq___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_exists_intro;
obj* l_task_bind___rarg(obj*, obj*, obj*);
obj* l_subtype_decidable__eq(obj*, obj*);
obj* l_decidable__of__decidable__of__eq(obj*, obj*);
obj* l_bit1___rarg(obj*, obj*, obj*);
obj* l_quotient_lift__on_u_2082(obj*, obj*, obj*, obj*, obj*);
obj* l_quotient_rec__on__subsingleton_u_2082(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_cond___main___rarg___boxed(obj*, obj*, obj*);
obj* l_infer__instance__as(obj*);
obj* l_decidable__pred;
obj* l___private_init_core_27__extfun__app(obj*, obj*);
obj* l_flip___rarg(obj*, obj*, obj*);
obj* l_sigma_has__sizeof(obj*, obj*);
obj* l_id__delta___rarg(obj*);
obj* l_bool_has__sizeof;
obj* l_thunk_get___boxed(obj*, obj*);
obj* l_prod_map(obj*, obj*, obj*, obj*);
obj* l_subtype_sizeof___main___rarg(obj*, obj*, obj*);
obj* l_prod__has__decidable__lt(obj*, obj*, obj*, obj*);
obj* l_bxor___main___boxed(obj*, obj*);
obj* l_exists__prop__decidable(obj*, obj*);
obj* l_sum_has__sizeof(obj*, obj*);
uint8 l_false_decidable;
obj* l_decidable_by__cases___rarg(uint8, obj*, obj*);
uint8 l_iff_decidable___rarg(uint8, uint8);
obj* l_right__cancelative;
obj* l_quotient_rec__on(obj*, obj*, obj*);
obj* l_sigma_sizeof___main___rarg(obj*, obj*, obj*);
obj* l_list_has__sizeof___rarg(obj*);
obj* l___private_init_core_25__extfun;
obj* l_bor___main___boxed(obj*, obj*);
obj* l_reflexive;
uint8 l_punit_decidable__eq(obj*, obj*);
obj* l_prod_sizeof___main___rarg(obj*, obj*, obj*);
uint8 l_decidable__of__decidable__of__iff___rarg(uint8, obj*);
obj* l_opt__param;
obj* l_singleton___rarg(obj*, obj*, obj*);
obj* l_id__delta(obj*);
obj* l_bool_sizeof___main(uint8);
obj* l_ite___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_ite_decidable(obj*, obj*, obj*);
obj* l_is__dec__eq;
obj* l_or_symm;
obj* l_decidable_rec__on__false___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_sum_sizeof___main(obj*, obj*);
obj* l_prod_decidable__eq___rarg___boxed(obj*, obj*, obj*, obj*);
uint8 l_bxor___main(uint8, uint8);
obj* l_nat_add___boxed(obj*, obj*);
obj* l_of__as__true;
obj* l_quotient_decidable__eq___rarg(obj*, obj*, obj*, obj*);
obj* l_sigma_sizeof___main___at_sigma_has__sizeof___spec__2___rarg(obj*, obj*, obj*);
obj* l_quotient_lift__on_u_2082___rarg(obj*, obj*, obj*, obj*);
obj* l_psum_has__sizeof(obj*, obj*);
obj* l_quotient_lift___rarg(obj*, obj*, obj*);
obj* l_punit_sizeof(obj*);
obj* l_unit;
obj* l_sum_sizeof(obj*, obj*);
obj* l_decidable_rec__on__true___rarg(uint8, obj*, obj*, obj*, obj*);
obj* l_subsingleton_helim;
obj* l_subsingleton__prop;
obj* l_ite_decidable___rarg___boxed(obj*, obj*, obj*);
obj* l_left__distributive;
obj* l_default_sizeof___main(obj*, obj*);
obj* l_eq_mp(obj*, obj*, obj*);
obj* l_and_elim__right;
obj* l_std_priority_default;
obj* l_quot_rec(obj*, obj*, obj*);
obj* l_decidable_rec__on__false(obj*);
uint8 l_exists__prop__decidable___rarg(uint8, obj*);
obj* l_prod_sizeof___main(obj*, obj*);
obj* l_arbitrary___rarg(obj*);
obj* l_task_pure(obj*);
obj* l_typed__expr(obj*);
obj* l_band___boxed(obj*, obj*);
obj* l_pi_inhabited___rarg(obj*, obj*);
obj* l_not_decidable(obj*);
obj* l_dite(obj*);
obj* l_subtype_exists__of__subtype;
obj* l_quot_rec__on(obj*, obj*, obj*);
obj* l_dite_decidable(obj*, obj*, obj*);
obj* l_decidable__of__decidable__of__eq___rarg___boxed(obj*, obj*);
obj* l_and_decidable___rarg___boxed(obj*, obj*);
obj* l_prod_map___rarg(obj*, obj*, obj*);
obj* l_dite___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_psigma_sizeof___at_psigma_has__sizeof___spec__1(obj*, obj*);
obj* l_prod_map___main___rarg(obj*, obj*, obj*);
obj* l_subtype_decidable__eq___rarg___boxed(obj*, obj*, obj*);
obj* l_as__false;
obj* l_sum_sizeof___rarg(obj*, obj*, obj*);
obj* l_subtype_exists__of__subtype___main;
obj* l___private_init_core_19__rel;
obj* l_psum_sizeof(obj*, obj*);
obj* l_quot_rec__on__subsingleton(obj*, obj*, obj*, obj*);
obj* l_infer__instance___rarg(obj*);
obj* l_right__inverse;
obj* l_decidable__rel;
obj* l_nat_prio;
obj* l_subtype_inhabited(obj*, obj*);
obj* l_quotient_rec___rarg(obj*, obj*, obj*);
obj* l_empty__relation;
obj* l_list_has__sizeof(obj*);
obj* l_eq_ndrec(obj*, obj*, obj*);
obj* l_left__cancelative;
obj* l_pi_inhabited(obj*, obj*);
obj* l_option_has__sizeof(obj*);
uint8 l_bnot___main(uint8);
obj* l_decidable__eq__of__bool__pred___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_infer__instance(obj*);
obj* l_psigma_sizeof___main___at_psigma_has__sizeof___spec__2(obj*, obj*);
obj* l_mk__equivalence;
obj* l_inv__image;
obj* l_default___rarg(obj*);
obj* l_decidable_by__cases(obj*, obj*);
obj* l_quotient_mk___rarg(obj*);
obj* l_quot_lift__on(obj*, obj*, obj*);
obj* l_bit1(obj*);
uint8 l_not_decidable___rarg(uint8);
obj* l_punit_has__sizeof;
obj* l_band___main___boxed(obj*, obj*);
obj* l_psigma_sizeof___main___at_psigma_has__sizeof___spec__2___rarg(obj*, obj*, obj*);
uint8 l_prod_decidable__eq___rarg(obj*, obj*, obj*, obj*);
obj* l_implies_decidable___rarg___boxed(obj*, obj*);
obj* l_dite_decidable___rarg(uint8, obj*, obj*);
obj* l_task_bind(obj*, obj*);
obj* l_nonempty_elim;
obj* l_sum_inhabited__left(obj*, obj*);
obj* l_true_decidable___boxed;
obj* l_transitive;
obj* l_quot_hrec__on___rarg(obj*, obj*, obj*);
obj* l_quotient_sound;
obj* l_option_has__sizeof___rarg(obj*);
obj* l_list_sizeof(obj*);
obj* l_right__identity;
obj* l_std_prec_arrow;
uint8 l_decidable__eq__of__bool__pred___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_bit0___rarg(obj*, obj*);
obj* l_psum_sizeof___main___rarg(obj*, obj*, obj*);
obj* l_bit0(obj*);
obj* l_id(obj*);
obj* l_equivalence;
obj* l_list_sizeof___main___rarg(obj*, obj*);
obj* l_subtype_inhabited___rarg(obj*, obj*);
obj* l_as__true;
obj* l_eq_mpr(obj*, obj*, obj*);
obj* l_sum_inhabited__right___rarg(obj*);
obj* l_psigma_sizeof___rarg(obj*, obj*, obj*);
obj* l_task_get(obj*);
obj* l_prod_inhabited___rarg(obj*, obj*);
obj* l_combinator_I___rarg(obj*);
obj* l_eq_ndrec___rarg(obj*, obj*, obj*);
obj* l_bnot___boxed(obj*);
obj* l_sigma_sizeof___at_sigma_has__sizeof___spec__1(obj*, obj*);
obj* l_anti__symmetric;
obj* l_quot_indep(obj*, obj*, obj*);
obj* l_default_sizeof(obj*, obj*);
obj* l_ite___rarg(uint8, obj*, obj*, obj*);
obj* l___private_init_core_24__fun__setoid(obj*, obj*);
obj* l_cast(obj*, obj*, obj*);
obj* l_type__eq__of__heq;
uint8 l_bool_inhabited;
obj* l_and_elim__left;
obj* l_decidable_rec__on__true___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_id___rarg(obj*);
obj* l_option_sizeof___main___rarg(obj*, obj*);
obj* l_quotient_rec__on__subsingleton___rarg(obj*, obj*);
obj* l_right__commutative;
obj* l_combinator_K___rarg(obj*, obj*);
obj* l_quot_indep___rarg(obj*, obj*);
obj* l_implies_decidable(obj*, obj*);
obj* l_ne_decidable___rarg___boxed(obj*, obj*, obj*);
obj* l_id__rhs___rarg(obj*);
uint8 l_bool_decidable__eq(uint8, uint8);
obj* l_bool_sizeof___main___boxed(obj*);
obj* l_psigma_has__sizeof___rarg(obj*, obj*);
obj* l_pi_subsingleton;
obj* l_default__has__sizeof___closed__1;
obj* l_sigma_sizeof(obj*, obj*);
obj* l_psum_sizeof___rarg(obj*, obj*, obj*);
obj* l_xor_decidable___rarg___boxed(obj*, obj*);
obj* l_psum_has__sizeof___rarg(obj*, obj*);
obj* l_classical_by__cases;
obj* l_bool_decidable__eq___boxed(obj*, obj*);
obj* l_prod__has__decidable__lt___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_quotient_lift_u_2082___rarg(obj*, obj*, obj*, obj*);
obj* l_decidable__of__decidable__eq___rarg(obj*, obj*, obj*);
obj* l_prod_has__sizeof___rarg(obj*, obj*);
obj* l_decidable_rec__on__false___rarg(uint8, obj*, obj*, obj*, obj*);
obj* l_out__param;
obj* l_function_equiv;
uint8 l_implies_decidable___rarg(uint8, uint8);
obj* l_sum_decidable__eq___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_quotient_rec__on__subsingleton_u_2082___at_quotient_decidable__eq___spec__1___rarg(obj*, obj*, obj*);
obj* l_psigma_sizeof(obj*, obj*);
obj* l_decidable__eq__of__bool__pred(obj*);
obj* l_quotient_rec__on__subsingleton_u_2082___at_quotient_decidable__eq___spec__1(obj*, obj*);
obj* l_xor_decidable(obj*, obj*);
obj* l_option_sizeof(obj*);
obj* l_combinator_S(obj*, obj*, obj*);
obj* l_ge;
obj* l_option_sizeof___main(obj*);
obj* l_quot_rec__on___rarg(obj*, obj*, obj*);
obj* l_dite___rarg(uint8, obj*, obj*, obj*);
obj* l_task_map___rarg(obj*, obj*, obj*);
obj* l_quotient_rec__on__subsingleton_u_2082___rarg(obj*, obj*, obj*);
obj* l_subtype_sizeof___main(obj*);
obj* l_decidable__of__decidable__of__iff(obj*, obj*);
obj* l_iff_decidable___rarg___boxed(obj*, obj*);
obj* l_decidable__of__decidable__of__iff___rarg___boxed(obj*, obj*);
obj* l_nat_has__sizeof;
obj* l_id__rhs(obj*);
obj* l_singleton(obj*, obj*);
obj* l_punit_inhabited;
obj* l_cond___rarg(uint8, obj*, obj*);
obj* l_subsingleton_elim;
obj* l_nat_sizeof(obj*);
obj* l_infer__instance__as___rarg(obj*);
obj* l_quotient;
obj* l_heq_rfl;
obj* l_prop_inhabited;
obj* l_false_decidable___boxed;
obj* l_quotient_hrec__on(obj*, obj*, obj*);
obj* l_quot_lift__on___rarg(obj*, obj*, obj*);
obj* l_default__has__sizeof(obj*);
obj* l_decidable_by__cases___rarg___boxed(obj*, obj*, obj*);
uint8 l_band(uint8, uint8);
obj* l_flip(obj*, obj*, obj*);
obj* l_nat_has__add;
uint8 l_or_decidable___rarg(uint8, uint8);
obj* l_nat_has__zero;
obj* l_sum_inhabited__left___rarg(obj*);
obj* l_quotient_rec(obj*, obj*, obj*);
obj* l_right__distributive;
obj* l_std_prec_max;
uint8 l_decidable_to__bool___rarg(uint8);
obj* l_psigma_sizeof___main___rarg(obj*, obj*, obj*);
obj* l_is__dec__refl;
obj* l_subtype_sizeof(obj*);
obj* l_and__implies;
obj* l_cond___main(obj*);
obj* l_not;
obj* l_sigma_has__sizeof___rarg(obj*, obj*);
obj* l_quot_rec__on__subsingleton___rarg(obj*, obj*);
obj* l_quotient_rec__on___rarg(obj*, obj*, obj*);
obj* l_nat_inhabited;
obj* l_prod_sizeof___rarg(obj*, obj*, obj*);
obj* l_cond___rarg___boxed(obj*, obj*, obj*);
obj* l_symmetric;
obj* l_eqv__gen_setoid(obj*, obj*);
obj* l_prod_map___main(obj*, obj*, obj*, obj*);
obj* l_eq_mpr___rarg(obj*);
obj* l_sigma_sizeof___rarg(obj*, obj*, obj*);
obj* l_dite_decidable___rarg___boxed(obj*, obj*, obj*);
obj* l_sum_inhabited__right(obj*, obj*);
obj* l_or_decidable___rarg___boxed(obj*, obj*);
obj* l_subtype_has__sizeof(obj*);
obj* l_ne_decidable(obj*);
uint8 l_ne_decidable___rarg(obj*, obj*, obj*);
obj* l_task_map(obj*, obj*);
obj* l_quotient_rec__on__subsingleton(obj*, obj*, obj*, obj*);
obj* l_not__not__em;
obj* l_implies;
obj* l_psigma_sizeof___main(obj*, obj*);
obj* l_sigma_sizeof___main___at_sigma_has__sizeof___spec__2(obj*, obj*);
uint8 l_bxor(uint8, uint8);
obj* l_default(obj*);
obj* l_decidable_subsingleton;
obj* l_ssuperset;
obj* l_associative;
obj* l_or_by__cases___rarg(uint8, uint8, obj*, obj*, obj*, obj*);
obj* l_prod_sizeof(obj*, obj*);
obj* l_sum_sizeof___main___rarg(obj*, obj*, obj*);
obj* l_eq_ndrec__on___rarg(obj*);
obj* l_quotient_lift(obj*, obj*, obj*);
obj* l_prod_has__sizeof(obj*, obj*);
obj* l_nat_add___main(obj*, obj*);
obj* l_sum_decidable__eq(obj*, obj*);
obj* l_punit_sizeof___main(obj*);
obj* l_subtype_has__sizeof___rarg(obj*, obj*);
obj* l_nat_has__one;
obj* l_trivial;
obj* l_not__true__iff;
obj* l_punit_decidable__eq___boxed(obj*, obj*);
obj* l_quotient_decidable__eq(obj*);
obj* l_forall__prop__decidable___rarg___boxed(obj*, obj*);
obj* l_quotient_hrec__on___rarg(obj*, obj*, obj*);
obj* l_left__commutative;
obj* l_not_decidable___rarg___boxed(obj*);
obj* l_left__identity;
obj* l_iff_decidable(obj*, obj*);
obj* l_psigma_sizeof___at_psigma_has__sizeof___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_sizeof___rarg(obj*, obj*);
uint8 l_bor(uint8, uint8);
obj* l_subtype_sizeof___rarg(obj*, obj*, obj*);
obj* l_sigma_sizeof___at_sigma_has__sizeof___spec__1___rarg(obj*, obj*, obj*);
obj* l_prod_decidable__eq(obj*, obj*);
obj* l_punit_subsingleton;
obj* l_task_get___rarg(obj*);
obj* l_decidable_rec__on__true(obj*);
obj* l_and_decidable(obj*, obj*);
obj* l_and_symm;
obj* l_decidable_to__bool(obj*);
obj* l_quotient_lift_u_2082(obj*, obj*, obj*, obj*, obj*);
uint8 l_bnot(uint8);
obj* l_std_prec_max__plus;
obj* l_absurd(obj*, obj*, obj*, obj*);
obj* l_eq_mp___rarg(obj*);
obj* l___private_init_core_27__extfun__app___rarg(obj*, obj*);
obj* l_quotient_lift__on___rarg(obj*, obj*, obj*);
uint8 l_subtype_decidable__eq___rarg(obj*, obj*, obj*);
obj* l_bnot___main___boxed(obj*);
obj* l_arbitrary(obj*);
obj* l_fun_inhabited(obj*, obj*);
obj* l_false_elim___boxed(obj*, obj*);
obj* l_exists__prop__decidable___rarg___boxed(obj*, obj*);
obj* l_cond___main___rarg(uint8, obj*, obj*);
obj* l_bool_sizeof(uint8);
obj* l_combinator_S___rarg(obj*, obj*, obj*);
obj* l_psum_sizeof___main(obj*, obj*);
obj* l_decidable__of__decidable__eq(obj*);
obj* l_cond(obj*);
obj* l_thunk_map___boxed(obj*, obj*, obj*, obj*);
obj* l_rfl;
obj* l_true_inhabited;
obj* l_subrelation;
obj* l_task_pure___rarg(obj*, obj*);
obj* l_commutative;
obj* l_sum_has__sizeof___rarg(obj*, obj*);
obj* l_ite(obj*);
obj* l_prod_inhabited(obj*, obj*);
uint8 l_quotient_decidable__eq___rarg___lambda__1(obj*, obj*, obj*);
obj* l_list_sizeof___main(obj*);
obj* l_quot_hrec__on(obj*, obj*, obj*);
obj* l_sigma_sizeof___main(obj*, obj*);
obj* l_forall__prop__decidable(obj*, obj*);
uint8 l_and_decidable___rarg(uint8, uint8);
obj* l_combinator_K(obj*, obj*);
obj* l_quotient_lift__on(obj*, obj*, obj*);
obj* l_thunk_bind___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_core_26__fun__to__extfun(obj*, obj*);
obj* l_irreflexive;
obj* l_false_elim(obj*, uint8);
obj* l_option_sizeof___rarg(obj*, obj*);
obj* l_combinator_I(obj*);
obj* l_id___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_id(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg), 1, 0);
return x_2;
}
}
obj* l_inline___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_inline(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_inline___rarg), 1, 0);
return x_2;
}
}
obj* l_flip___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_0, x_2, x_1);
return x_3;
}
}
obj* l_flip(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_flip___rarg), 3, 0);
return x_6;
}
}
obj* l_id__delta___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_id__delta(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id__delta___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_opt__param() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_out__param() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_typed__expr___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_typed__expr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_typed__expr___rarg), 1, 0);
return x_2;
}
}
obj* l_id__rhs___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_id__rhs(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id__rhs___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_unit() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_unit_star() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_thunk_pure___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::thunk_pure(x_1);
return x_2;
}
}
obj* l_thunk_get___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::thunk_get(x_1);
return x_2;
}
}
obj* l_thunk_map___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::thunk_map(x_2, x_3);
return x_4;
}
}
obj* l_thunk_bind___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::thunk_bind(x_2, x_3);
return x_4;
}
}
obj* l_task_pure___rarg(obj* x_0, obj* x_1) {
_start:
{
lean::dec(x_1);
return x_0;
}
}
obj* l_task_pure(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_task_pure___rarg), 2, 0);
return x_2;
}
}
obj* l_task_get___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_task_get(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_task_get___rarg), 1, 0);
return x_2;
}
}
obj* l_task_map___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::dec(x_2);
x_4 = l_task_get___rarg(x_1);
x_5 = lean::apply_1(x_0, x_4);
return x_5;
}
}
obj* l_task_map(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_task_map___rarg), 3, 0);
return x_4;
}
}
obj* l_task_bind___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_2);
x_4 = l_task_get___rarg(x_0);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_task_get___rarg(x_5);
return x_6;
}
}
obj* l_task_bind(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_task_bind___rarg), 3, 0);
return x_4;
}
}
obj* _init_l_not() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_eq_ndrec___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
return x_0;
}
}
obj* l_eq_ndrec(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_eq_ndrec___rarg), 3, 0);
return x_6;
}
}
obj* l_eq_ndrec__on___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_eq_ndrec__on(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_eq_ndrec__on___rarg), 1, 0);
return x_10;
}
}
obj* _init_l_and_elim__left() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_and_elim__right() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_rfl() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_heq_rfl() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_or_intro__left() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_or_intro__right() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_decidable__pred() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_decidable__rel() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_decidable__of__decidable__eq___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_2, x_0, x_1);
return x_3;
}
}
obj* l_decidable__of__decidable__eq(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable__of__decidable__eq___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_ge() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_gt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_superset() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_ssuperset() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_bit0___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_1);
x_3 = lean::apply_2(x_0, x_1, x_1);
return x_3;
}
}
obj* l_bit0(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_bit0___rarg), 2, 0);
return x_2;
}
}
obj* l_bit1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
lean::inc(x_1);
x_5 = lean::apply_2(x_1, x_2, x_2);
x_6 = lean::apply_2(x_1, x_5, x_0);
return x_6;
}
}
obj* l_bit1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_bit1___rarg), 3, 0);
return x_2;
}
}
obj* l_singleton___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_1, x_2, x_0);
return x_3;
}
}
obj* l_singleton(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_singleton___rarg), 3, 0);
return x_4;
}
}
obj* l_nat_add___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_1);
x_8 = l_nat_add___main(x_0, x_6);
x_9 = lean::nat_add(x_8, x_5);
lean::dec(x_5);
lean::dec(x_8);
return x_9;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_nat_add___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::nat_add(x_0, x_1);
return x_2;
}
}
obj* _init_l_nat_has__zero() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(0u);
return x_0;
}
}
obj* _init_l_nat_has__one() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(1u);
return x_0;
}
}
obj* _init_l_nat_has__add() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_std_priority_default() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(1000u);
return x_0;
}
}
obj* _init_l_std_priority_max() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(lean::mpz("4294967295"));
return x_0;
}
}
obj* _init_l_nat_prio() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_std_priority_default;
x_1 = lean::mk_nat_obj(100u);
x_2 = lean::nat_add(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_std_prec_max() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(1024u);
return x_0;
}
}
obj* _init_l_std_prec_arrow() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(25u);
return x_0;
}
}
obj* _init_l_std_prec_max__plus() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_std_prec_max;
x_1 = lean::mk_nat_obj(10u);
x_2 = lean::nat_add(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_default_sizeof___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::mk_nat_obj(0u);
return x_4;
}
}
obj* l_default_sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::mk_nat_obj(0u);
return x_4;
}
}
obj* _init_l_default__has__sizeof___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_default_sizeof), 2, 1);
lean::closure_set(x_0, 0, lean::box(0));
return x_0;
}
}
obj* l_default__has__sizeof(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_default__has__sizeof___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* l_nat_sizeof___main(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_nat_sizeof(obj* x_0) {
_start:
{
return x_0;
}
}
obj* _init_l_nat_has__sizeof() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_sizeof), 1, 0);
return x_0;
}
}
obj* l_prod_sizeof___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::apply_1(x_0, x_3);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_9, x_8);
lean::dec(x_8);
lean::dec(x_9);
x_13 = lean::apply_1(x_1, x_5);
x_14 = lean::nat_add(x_10, x_13);
lean::dec(x_13);
lean::dec(x_10);
return x_14;
}
}
obj* l_prod_sizeof___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_sizeof___main___rarg), 3, 0);
return x_4;
}
}
obj* l_prod_sizeof___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_prod_sizeof___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_prod_sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_sizeof___rarg), 3, 0);
return x_4;
}
}
obj* l_prod_has__sizeof___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_sizeof___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_prod_has__sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_has__sizeof___rarg), 2, 0);
return x_4;
}
}
obj* l_sum_sizeof___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_8, x_7);
lean::dec(x_7);
lean::dec(x_8);
return x_9;
}
else
{
obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::apply_1(x_1, x_13);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
return x_18;
}
}
}
obj* l_sum_sizeof___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sum_sizeof___main___rarg), 3, 0);
return x_4;
}
}
obj* l_sum_sizeof___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_sum_sizeof___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_sum_sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sum_sizeof___rarg), 3, 0);
return x_4;
}
}
obj* l_sum_has__sizeof___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_sum_sizeof___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_sum_has__sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sum_has__sizeof___rarg), 2, 0);
return x_4;
}
}
obj* l_psum_sizeof___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_8, x_7);
lean::dec(x_7);
lean::dec(x_8);
return x_9;
}
else
{
obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::apply_1(x_1, x_13);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
return x_18;
}
}
}
obj* l_psum_sizeof___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_psum_sizeof___main___rarg), 3, 0);
return x_4;
}
}
obj* l_psum_sizeof___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_psum_sizeof___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_psum_sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_psum_sizeof___rarg), 3, 0);
return x_4;
}
}
obj* l_psum_has__sizeof___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_psum_sizeof___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_psum_has__sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_psum_has__sizeof___rarg), 2, 0);
return x_4;
}
}
obj* l_sigma_sizeof___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = lean::apply_1(x_0, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_10, x_9);
lean::dec(x_9);
lean::dec(x_10);
x_14 = lean::apply_2(x_1, x_3, x_5);
x_15 = lean::nat_add(x_11, x_14);
lean::dec(x_14);
lean::dec(x_11);
return x_15;
}
}
obj* l_sigma_sizeof___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sigma_sizeof___main___rarg), 3, 0);
return x_4;
}
}
obj* l_sigma_sizeof___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_sigma_sizeof___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_sigma_sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sigma_sizeof___rarg), 3, 0);
return x_4;
}
}
obj* l_sigma_sizeof___main___at_sigma_has__sizeof___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = lean::apply_1(x_0, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_10, x_9);
lean::dec(x_9);
lean::dec(x_10);
x_14 = lean::apply_2(x_1, x_3, x_5);
x_15 = lean::nat_add(x_11, x_14);
lean::dec(x_14);
lean::dec(x_11);
return x_15;
}
}
obj* l_sigma_sizeof___main___at_sigma_has__sizeof___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sigma_sizeof___main___at_sigma_has__sizeof___spec__2___rarg), 3, 0);
return x_4;
}
}
obj* l_sigma_sizeof___at_sigma_has__sizeof___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_sigma_sizeof___main___at_sigma_has__sizeof___spec__2___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_sigma_sizeof___at_sigma_has__sizeof___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sigma_sizeof___at_sigma_has__sizeof___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_sigma_has__sizeof___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_sigma_sizeof___at_sigma_has__sizeof___spec__1___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_sigma_has__sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sigma_has__sizeof___rarg), 2, 0);
return x_4;
}
}
obj* l_psigma_sizeof___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = lean::apply_1(x_0, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_10, x_9);
lean::dec(x_9);
lean::dec(x_10);
x_14 = lean::apply_2(x_1, x_3, x_5);
x_15 = lean::nat_add(x_11, x_14);
lean::dec(x_14);
lean::dec(x_11);
return x_15;
}
}
obj* l_psigma_sizeof___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_psigma_sizeof___main___rarg), 3, 0);
return x_4;
}
}
obj* l_psigma_sizeof___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_psigma_sizeof___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_psigma_sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_psigma_sizeof___rarg), 3, 0);
return x_4;
}
}
obj* l_psigma_sizeof___main___at_psigma_has__sizeof___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = lean::apply_1(x_0, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_10, x_9);
lean::dec(x_9);
lean::dec(x_10);
x_14 = lean::apply_2(x_1, x_3, x_5);
x_15 = lean::nat_add(x_11, x_14);
lean::dec(x_14);
lean::dec(x_11);
return x_15;
}
}
obj* l_psigma_sizeof___main___at_psigma_has__sizeof___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_psigma_sizeof___main___at_psigma_has__sizeof___spec__2___rarg), 3, 0);
return x_4;
}
}
obj* l_psigma_sizeof___at_psigma_has__sizeof___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_psigma_sizeof___main___at_psigma_has__sizeof___spec__2___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_psigma_sizeof___at_psigma_has__sizeof___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_psigma_sizeof___at_psigma_has__sizeof___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_psigma_has__sizeof___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_psigma_sizeof___at_psigma_has__sizeof___spec__1___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_psigma_has__sizeof(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_psigma_has__sizeof___rarg), 2, 0);
return x_4;
}
}
obj* l_punit_sizeof___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::mk_nat_obj(1u);
return x_2;
}
}
obj* l_punit_sizeof(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::mk_nat_obj(1u);
return x_2;
}
}
obj* _init_l_punit_has__sizeof() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_punit_sizeof), 1, 0);
return x_0;
}
}
obj* l_bool_sizeof___main(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::mk_nat_obj(1u);
return x_1;
}
}
obj* l_bool_sizeof___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_bool_sizeof___main(x_1);
return x_2;
}
}
obj* l_bool_sizeof(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::mk_nat_obj(1u);
return x_1;
}
}
obj* l_bool_sizeof___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_bool_sizeof(x_1);
return x_2;
}
}
obj* _init_l_bool_has__sizeof() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_bool_sizeof___boxed), 1, 0);
return x_0;
}
}
obj* l_option_sizeof___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::mk_nat_obj(1u);
return x_4;
}
else
{
obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::apply_1(x_0, x_5);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_9, x_8);
lean::dec(x_8);
lean::dec(x_9);
return x_10;
}
}
}
obj* l_option_sizeof___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option_sizeof___main___rarg), 2, 0);
return x_2;
}
}
obj* l_option_sizeof___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_option_sizeof___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_option_sizeof(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option_sizeof___rarg), 2, 0);
return x_2;
}
}
obj* l_option_has__sizeof___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option_sizeof___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_option_has__sizeof(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option_has__sizeof___rarg), 1, 0);
return x_2;
}
}
obj* l_list_sizeof___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::mk_nat_obj(1u);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_5);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_12, x_11);
lean::dec(x_11);
lean::dec(x_12);
x_16 = l_list_sizeof___main___rarg(x_0, x_7);
x_17 = lean::nat_add(x_13, x_16);
lean::dec(x_16);
lean::dec(x_13);
return x_17;
}
}
}
obj* l_list_sizeof___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_sizeof___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_sizeof___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_sizeof___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_sizeof(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_sizeof___rarg), 2, 0);
return x_2;
}
}
obj* l_list_has__sizeof___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_sizeof___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_has__sizeof(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__sizeof___rarg), 1, 0);
return x_2;
}
}
obj* l_subtype_sizeof___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_1(x_0, x_2);
return x_4;
}
}
obj* l_subtype_sizeof___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_subtype_sizeof___main___rarg), 3, 0);
return x_2;
}
}
obj* l_subtype_sizeof___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_1(x_0, x_2);
return x_4;
}
}
obj* l_subtype_sizeof(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_subtype_sizeof___rarg), 3, 0);
return x_2;
}
}
obj* l_subtype_has__sizeof___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_subtype_sizeof___rarg), 3, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, lean::box(0));
return x_3;
}
}
obj* l_subtype_has__sizeof(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_subtype_has__sizeof___rarg), 2, 0);
return x_2;
}
}
obj* l_combinator_I___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_combinator_I(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_combinator_I___rarg), 1, 0);
return x_2;
}
}
obj* l_combinator_K___rarg(obj* x_0, obj* x_1) {
_start:
{
lean::dec(x_1);
return x_0;
}
}
obj* l_combinator_K(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_combinator_K___rarg), 2, 0);
return x_4;
}
}
obj* l_combinator_S___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
x_4 = lean::apply_1(x_1, x_2);
x_5 = lean::apply_2(x_0, x_2, x_4);
return x_5;
}
}
obj* l_combinator_S(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_combinator_S___rarg), 3, 0);
return x_6;
}
}
obj* l_infer__instance___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_infer__instance(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_infer__instance___rarg), 1, 0);
return x_2;
}
}
obj* l_infer__instance__as___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_infer__instance__as(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_infer__instance__as___rarg), 1, 0);
return x_2;
}
}
obj* l_cond___main___rarg(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (x_0 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_cond___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_cond___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_cond___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_cond___main___rarg(x_3, x_1, x_2);
return x_4;
}
}
obj* l_cond___rarg(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (x_0 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_cond(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_cond___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_cond___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_cond___rarg(x_3, x_1, x_2);
return x_4;
}
}
uint8 l_bor___main(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
return x_1;
}
else
{
return x_0;
}
}
}
obj* l_bor___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_bor___main(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_bor(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
return x_1;
}
else
{
return x_0;
}
}
}
obj* l_bor___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_bor(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_band___main(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
return x_0;
}
else
{
return x_1;
}
}
}
obj* l_band___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_band___main(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_band(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
return x_0;
}
else
{
return x_1;
}
}
}
obj* l_band___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_band(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_bnot___main(uint8 x_0) {
_start:
{
if (x_0 == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
obj* l_bnot___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_bnot___main(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_bnot(uint8 x_0) {
_start:
{
if (x_0 == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
obj* l_bnot___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_bnot(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_bxor___main(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
return x_0;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
}
obj* l_bxor___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_bxor___main(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_bxor(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
return x_0;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
}
obj* l_bxor___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_bxor(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_implies() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_trivial() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_false_elim(obj* x_0, uint8 x_1) {
_start:
{
obj* x_3; 
lean::dec(x_0);
lean_unreachable();
x_3 = lean::box(0);
lean::inc(x_3);
return x_3;
}
}
obj* l_false_elim___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
x_3 = l_false_elim(x_0, x_2);
return x_3;
}
}
obj* l_absurd(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
lean_unreachable();
x_8 = lean::box(0);
lean::inc(x_8);
return x_8;
}
}
obj* l_eq_mp___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_eq_mp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_eq_mp___rarg), 1, 0);
return x_6;
}
}
obj* l_eq_mpr___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_eq_mpr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_eq_mpr___rarg), 1, 0);
return x_6;
}
}
obj* l_cast___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_cast(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_cast___rarg), 1, 0);
return x_6;
}
}
obj* _init_l_ne() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_type__eq__of__heq() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_and_symm() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_not__not__em() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_or_symm() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_xor() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_not__true__iff() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_and__implies() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_exists_intro() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
uint8 l_decidable_to__bool___rarg(uint8 x_0) {
_start:
{
if (x_0 == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
}
}
obj* l_decidable_to__bool(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable_to__bool___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_decidable_to__bool___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_decidable_to__bool___rarg(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 _init_l_true_decidable() {
_start:
{
uint8 x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_true_decidable___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_true_decidable;
x_1 = lean::box(x_0);
return x_1;
}
}
uint8 _init_l_false_decidable() {
_start:
{
uint8 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_false_decidable___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_false_decidable;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* l_dite___rarg(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
if (x_0 == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::apply_1(x_3, lean::box(0));
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_3);
x_8 = lean::apply_1(x_2, lean::box(0));
return x_8;
}
}
}
obj* l_dite(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dite___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_dite___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_dite___rarg(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_ite___rarg(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
if (x_0 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
lean::dec(x_3);
return x_2;
}
}
}
obj* l_ite(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ite___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_ite___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_ite___rarg(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_decidable_rec__on__true___rarg(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_decidable_rec__on__true(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable_rec__on__true___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_decidable_rec__on__true___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_decidable_rec__on__true___rarg(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_decidable_rec__on__false___rarg(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_decidable_rec__on__false(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable_rec__on__false___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_decidable_rec__on__false___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_decidable_rec__on__false___rarg(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_decidable_by__cases___rarg(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (x_0 == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_1(x_2, lean::box(0));
return x_4;
}
else
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::apply_1(x_1, lean::box(0));
return x_6;
}
}
}
obj* l_decidable_by__cases(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable_by__cases___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_decidable_by__cases___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_decidable_by__cases___rarg(x_3, x_1, x_2);
return x_4;
}
}
uint8 l_decidable__of__decidable__of__iff___rarg(uint8 x_0, obj* x_1) {
_start:
{
lean::dec(x_1);
if (x_0 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_decidable__of__decidable__of__iff(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable__of__decidable__of__iff___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_decidable__of__decidable__of__iff___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = l_decidable__of__decidable__of__iff___rarg(x_2, x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_decidable__of__decidable__of__eq___rarg(uint8 x_0, obj* x_1) {
_start:
{
lean::dec(x_1);
if (x_0 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_decidable__of__decidable__of__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable__of__decidable__of__eq___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_decidable__of__decidable__of__eq___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = l_decidable__of__decidable__of__eq___rarg(x_2, x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_or_by__cases___rarg(uint8 x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
lean::dec(x_3);
lean::dec(x_2);
if (x_0 == 0)
{
obj* x_9; 
lean::dec(x_4);
x_9 = lean::apply_1(x_5, lean::box(0));
return x_9;
}
else
{
obj* x_11; 
lean::dec(x_5);
x_11 = lean::apply_1(x_4, lean::box(0));
return x_11;
}
}
}
obj* l_or_by__cases(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_or_by__cases___rarg___boxed), 6, 0);
return x_4;
}
}
obj* l_or_by__cases___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_0);
x_7 = lean::unbox(x_1);
x_8 = l_or_by__cases___rarg(x_6, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
uint8 l_and_decidable___rarg(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
if (x_1 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
}
obj* l_and_decidable(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_and_decidable___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_and_decidable___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_and_decidable___rarg(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_or_decidable___rarg(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
if (x_1 == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_or_decidable(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_or_decidable___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_or_decidable___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_or_decidable___rarg(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_not_decidable___rarg(uint8 x_0) {
_start:
{
if (x_0 == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
obj* l_not_decidable(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_not_decidable___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_not_decidable___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_not_decidable___rarg(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_implies_decidable___rarg(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
if (x_1 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
}
obj* l_implies_decidable(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_implies_decidable___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_implies_decidable___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_implies_decidable___rarg(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_iff_decidable___rarg(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
if (x_1 == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
else
{
if (x_1 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
}
}
obj* l_iff_decidable(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_iff_decidable___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_iff_decidable___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_iff_decidable___rarg(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_xor_decidable___rarg(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
if (x_1 == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
}
else
{
if (x_1 == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
}
}
obj* l_xor_decidable(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_xor_decidable___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_xor_decidable___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_xor_decidable___rarg(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_exists__prop__decidable___rarg(uint8 x_0, obj* x_1) {
_start:
{
if (x_0 == 0)
{
uint8 x_3; 
lean::dec(x_1);
x_3 = 0;
return x_3;
}
else
{
obj* x_4; uint8 x_5; 
x_4 = lean::apply_1(x_1, lean::box(0));
x_5 = lean::unbox(x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
}
obj* l_exists__prop__decidable(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_exists__prop__decidable___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_exists__prop__decidable___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = l_exists__prop__decidable___rarg(x_2, x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_forall__prop__decidable___rarg(uint8 x_0, obj* x_1) {
_start:
{
if (x_0 == 0)
{
uint8 x_3; 
lean::dec(x_1);
x_3 = 1;
return x_3;
}
else
{
obj* x_4; uint8 x_5; 
x_4 = lean::apply_1(x_1, lean::box(0));
x_5 = lean::unbox(x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
}
obj* l_forall__prop__decidable(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_forall__prop__decidable___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_forall__prop__decidable___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = l_forall__prop__decidable___rarg(x_2, x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_ne_decidable___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::apply_2(x_0, x_1, x_2);
x_4 = lean::unbox(x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
}
obj* l_ne_decidable(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ne_decidable___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_ne_decidable___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_ne_decidable___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_is__dec__eq() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_is__dec__refl() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
uint8 l_bool_decidable__eq(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
if (x_1 == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
else
{
if (x_1 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
}
}
obj* l_bool_decidable__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_bool_decidable__eq(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_decidable__eq__of__bool__pred___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; uint8 x_8; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::apply_2(x_0, x_3, x_4);
x_8 = lean::unbox(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
}
}
obj* l_decidable__eq__of__bool__pred(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable__eq__of__bool__pred___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_decidable__eq__of__bool__pred___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_decidable__eq__of__bool__pred___rarg(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_ite_decidable___rarg(uint8 x_0, uint8 x_1, uint8 x_2) {
_start:
{
if (x_0 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
obj* l_ite_decidable(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ite_decidable___rarg___boxed), 3, 0);
return x_6;
}
}
obj* l_ite_decidable___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; uint8 x_5; uint8 x_6; obj* x_7; 
x_3 = lean::unbox(x_0);
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = l_ite_decidable___rarg(x_3, x_4, x_5);
x_7 = lean::box(x_6);
return x_7;
}
}
obj* l_dite_decidable___rarg(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (x_0 == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_1(x_2, lean::box(0));
return x_4;
}
else
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::apply_1(x_1, lean::box(0));
return x_6;
}
}
}
obj* l_dite_decidable(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_dite_decidable___rarg___boxed), 3, 0);
return x_6;
}
}
obj* l_dite_decidable___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_dite_decidable___rarg(x_3, x_1, x_2);
return x_4;
}
}
obj* _init_l_as__true() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_as__false() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_of__as__true() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_default___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_default(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_default___rarg), 1, 0);
return x_2;
}
}
obj* l_arbitrary___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_arbitrary(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_arbitrary___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_prop_inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_fun_inhabited___rarg(obj* x_0, obj* x_1) {
_start:
{
lean::dec(x_1);
return x_0;
}
}
obj* l_fun_inhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_fun_inhabited___rarg), 2, 0);
return x_4;
}
}
obj* l_pi_inhabited___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_pi_inhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_pi_inhabited___rarg), 2, 0);
return x_4;
}
}
uint8 _init_l_bool_inhabited() {
_start:
{
uint8 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_bool_inhabited___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_bool_inhabited;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* _init_l_true_inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_nat_inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(0u);
return x_0;
}
}
obj* _init_l_nonempty_elim() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_nonempty__of__inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_subsingleton_elim() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_subsingleton_helim() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_subsingleton__prop() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_decidable_subsingleton() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_reflexive() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_symmetric() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_transitive() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_equivalence() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_total() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_mk__equivalence() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_irreflexive() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_anti__symmetric() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_empty__relation() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_subrelation() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_inv__image() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_commutative() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_associative() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_left__identity() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_right__identity() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_right__inverse() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_left__cancelative() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_right__cancelative() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_left__distributive() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_right__distributive() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_right__commutative() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_left__commutative() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_subtype_exists__of__subtype___main() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_subtype_exists__of__subtype() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_subtype_inhabited___rarg(obj* x_0, obj* x_1) {
_start:
{
lean::dec(x_1);
return x_0;
}
}
obj* l_subtype_inhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_subtype_inhabited___rarg), 2, 0);
return x_4;
}
}
uint8 l_subtype_decidable__eq___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::apply_2(x_0, x_1, x_2);
x_4 = lean::unbox(x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
obj* l_subtype_decidable__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_subtype_decidable__eq___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_subtype_decidable__eq___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_subtype_decidable__eq___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_sum_inhabited__left___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_sum_inhabited__left(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sum_inhabited__left___rarg), 1, 0);
return x_4;
}
}
obj* l_sum_inhabited__right___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_sum_inhabited__right(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sum_inhabited__right___rarg), 1, 0);
return x_4;
}
}
uint8 l_sum_decidable__eq___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::apply_2(x_0, x_5, x_8);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
uint8 x_14; 
x_14 = 0;
return x_14;
}
else
{
uint8 x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint8 x_19; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_0);
x_19 = 0;
return x_19;
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_27; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_21);
x_27 = 0;
return x_27;
}
else
{
obj* x_28; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_3, 0);
lean::inc(x_28);
lean::dec(x_3);
x_31 = lean::apply_2(x_1, x_21, x_28);
x_32 = lean::unbox(x_31);
lean::dec(x_31);
if (x_32 == 0)
{
uint8 x_34; 
x_34 = 0;
return x_34;
}
else
{
uint8 x_35; 
x_35 = 1;
return x_35;
}
}
}
}
}
obj* l_sum_decidable__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sum_decidable__eq___rarg___boxed), 4, 0);
return x_4;
}
}
obj* l_sum_decidable__eq___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_sum_decidable__eq___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_prod_inhabited___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_prod_inhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_inhabited___rarg), 2, 0);
return x_4;
}
}
uint8 l_prod_decidable__eq___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_14; uint8 x_15; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
lean::dec(x_3);
x_14 = lean::apply_2(x_0, x_4, x_9);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
uint8 x_20; 
lean::dec(x_6);
lean::dec(x_11);
lean::dec(x_1);
x_20 = 0;
return x_20;
}
else
{
obj* x_21; uint8 x_22; 
x_21 = lean::apply_2(x_1, x_6, x_11);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
uint8 x_24; 
x_24 = 0;
return x_24;
}
else
{
uint8 x_25; 
x_25 = 1;
return x_25;
}
}
}
}
obj* l_prod_decidable__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_decidable__eq___rarg___boxed), 4, 0);
return x_4;
}
}
obj* l_prod_decidable__eq___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_prod_decidable__eq___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_prod_has__lt(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::box(0);
return x_8;
}
}
uint8 l_prod__has__decidable__lt___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_9; obj* x_13; uint8 x_14; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::inc(x_9);
lean::inc(x_7);
x_13 = lean::apply_2(x_2, x_7, x_9);
x_14 = lean::unbox(x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_16; uint8 x_17; 
x_16 = lean::apply_2(x_0, x_7, x_9);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
uint8 x_22; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_22 = 0;
return x_22;
}
else
{
obj* x_23; obj* x_26; obj* x_29; uint8 x_30; 
x_23 = lean::cnstr_get(x_4, 1);
lean::inc(x_23);
lean::dec(x_4);
x_26 = lean::cnstr_get(x_5, 1);
lean::inc(x_26);
lean::dec(x_5);
x_29 = lean::apply_2(x_3, x_23, x_26);
x_30 = lean::unbox(x_29);
lean::dec(x_29);
if (x_30 == 0)
{
uint8 x_32; 
x_32 = 0;
return x_32;
}
else
{
uint8 x_33; 
x_33 = 1;
return x_33;
}
}
}
else
{
uint8 x_40; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_0);
x_40 = 1;
return x_40;
}
}
}
obj* l_prod__has__decidable__lt(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_prod__has__decidable__lt___rarg___boxed), 6, 0);
return x_8;
}
}
obj* l_prod__has__decidable__lt___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = l_prod__has__decidable__lt___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
x_7 = lean::box(x_6);
return x_7;
}
}
obj* l_prod_map___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_7 = x_2;
}
x_8 = lean::apply_1(x_0, x_3);
x_9 = lean::apply_1(x_1, x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_prod_map___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_map___main___rarg), 3, 0);
return x_8;
}
}
obj* l_prod_map___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_prod_map___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_prod_map(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_map___rarg), 3, 0);
return x_8;
}
}
obj* _init_l_punit_subsingleton() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_punit_inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_punit_decidable__eq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 1;
return x_4;
}
}
obj* l_punit_decidable__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_punit_decidable__eq(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_setoid__has__equiv(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
}
obj* l_quot_lift__on___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::apply_1(x_1, x_0);
return x_4;
}
}
obj* l_quot_lift__on(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_quot_lift__on___rarg), 3, 0);
return x_6;
}
}
obj* l_quot_indep___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; 
lean::inc(x_1);
x_3 = lean::apply_1(x_0, x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_quot_indep(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_quot_indep___rarg), 2, 0);
return x_6;
}
}
obj* l_quot_rec___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_1(x_0, x_2);
return x_4;
}
}
obj* l_quot_rec(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_quot_rec___rarg), 3, 0);
return x_6;
}
}
obj* l_quot_rec__on___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::apply_1(x_1, x_0);
return x_4;
}
}
obj* l_quot_rec__on(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_quot_rec__on___rarg), 3, 0);
return x_6;
}
}
obj* l_quot_rec__on__subsingleton___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_1, x_0);
return x_2;
}
}
obj* l_quot_rec__on__subsingleton(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_quot_rec__on__subsingleton___rarg), 2, 0);
return x_8;
}
}
obj* l_quot_hrec__on___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::apply_1(x_1, x_0);
return x_4;
}
}
obj* l_quot_hrec__on(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_quot_hrec__on___rarg), 3, 0);
return x_6;
}
}
obj* _init_l_quotient() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_quotient_mk___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_quotient_mk(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_mk___rarg), 1, 0);
return x_4;
}
}
obj* _init_l_quotient_sound() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_quotient_lift___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_1(x_0, x_2);
return x_4;
}
}
obj* l_quotient_lift(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_lift___rarg), 3, 0);
return x_6;
}
}
obj* l_quotient_lift__on___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::apply_1(x_1, x_0);
return x_4;
}
}
obj* l_quotient_lift__on(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_lift__on___rarg), 3, 0);
return x_6;
}
}
obj* l_quotient_rec___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_1(x_0, x_2);
return x_4;
}
}
obj* l_quotient_rec(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_rec___rarg), 3, 0);
return x_6;
}
}
obj* l_quotient_rec__on___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::apply_1(x_1, x_0);
return x_4;
}
}
obj* l_quotient_rec__on(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_rec__on___rarg), 3, 0);
return x_6;
}
}
obj* l_quotient_rec__on__subsingleton___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_1, x_0);
return x_2;
}
}
obj* l_quotient_rec__on__subsingleton(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_rec__on__subsingleton___rarg), 2, 0);
return x_8;
}
}
obj* l_quotient_hrec__on___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::apply_1(x_1, x_0);
return x_4;
}
}
obj* l_quotient_hrec__on(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_hrec__on___rarg), 3, 0);
return x_6;
}
}
obj* l_quotient_lift_u_2082___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = lean::apply_2(x_0, x_2, x_3);
return x_5;
}
}
obj* l_quotient_lift_u_2082(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_lift_u_2082___rarg), 4, 0);
return x_10;
}
}
obj* l_quotient_lift__on_u_2082___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::apply_2(x_2, x_0, x_1);
return x_5;
}
}
obj* l_quotient_lift__on_u_2082(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_lift__on_u_2082___rarg), 4, 0);
return x_10;
}
}
obj* _init_l___private_init_core_19__rel() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_quotient_rec__on__subsingleton_u_2082___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_2, x_0, x_1);
return x_3;
}
}
obj* l_quotient_rec__on__subsingleton_u_2082(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_rec__on__subsingleton_u_2082___rarg), 3, 0);
return x_12;
}
}
obj* l_eqv__gen_setoid(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
}
obj* l_quotient_rec__on__subsingleton_u_2082___at_quotient_decidable__eq___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_2, x_0, x_1);
return x_3;
}
}
obj* l_quotient_rec__on__subsingleton_u_2082___at_quotient_decidable__eq___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_rec__on__subsingleton_u_2082___at_quotient_decidable__eq___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_quotient_decidable__eq___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; 
lean::dec(x_0);
x_5 = l_quotient_decidable__eq___rarg___lambda__1(x_1, x_2, x_3);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_quotient_decidable__eq___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::apply_2(x_0, x_1, x_2);
x_4 = lean::unbox(x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
obj* l_quotient_decidable__eq(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_quotient_decidable__eq___rarg), 4, 0);
return x_2;
}
}
obj* l_quotient_decidable__eq___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_quotient_decidable__eq___rarg___lambda__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_function_equiv() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l___private_init_core_24__fun__setoid(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
}
obj* _init_l___private_init_core_25__extfun() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l___private_init_core_26__fun__to__extfun___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l___private_init_core_26__fun__to__extfun(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_core_26__fun__to__extfun___rarg), 1, 0);
return x_4;
}
}
obj* l___private_init_core_27__extfun__app___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l___private_init_core_27__extfun__app(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_core_27__extfun__app___rarg), 2, 0);
return x_4;
}
}
obj* _init_l_pi_subsingleton() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_classical_by__cases() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
static bool _G_initialized = false;
void initialize_init_core() {
 if (_G_initialized) return;
 _G_initialized = true;
 l_opt__param = _init_l_opt__param();
 l_out__param = _init_l_out__param();
 l_unit = _init_l_unit();
 l_unit_star = _init_l_unit_star();
 l_not = _init_l_not();
 l_and_elim__left = _init_l_and_elim__left();
 l_and_elim__right = _init_l_and_elim__right();
 l_rfl = _init_l_rfl();
 l_heq_rfl = _init_l_heq_rfl();
 l_or_intro__left = _init_l_or_intro__left();
 l_or_intro__right = _init_l_or_intro__right();
 l_decidable__pred = _init_l_decidable__pred();
 l_decidable__rel = _init_l_decidable__rel();
 l_ge = _init_l_ge();
 l_gt = _init_l_gt();
 l_superset = _init_l_superset();
 l_ssuperset = _init_l_ssuperset();
 l_nat_has__zero = _init_l_nat_has__zero();
 l_nat_has__one = _init_l_nat_has__one();
 l_nat_has__add = _init_l_nat_has__add();
 l_std_priority_default = _init_l_std_priority_default();
 l_std_priority_max = _init_l_std_priority_max();
 l_nat_prio = _init_l_nat_prio();
 l_std_prec_max = _init_l_std_prec_max();
 l_std_prec_arrow = _init_l_std_prec_arrow();
 l_std_prec_max__plus = _init_l_std_prec_max__plus();
 l_default__has__sizeof___closed__1 = _init_l_default__has__sizeof___closed__1();
 l_nat_has__sizeof = _init_l_nat_has__sizeof();
 l_punit_has__sizeof = _init_l_punit_has__sizeof();
 l_bool_has__sizeof = _init_l_bool_has__sizeof();
 l_implies = _init_l_implies();
 l_trivial = _init_l_trivial();
 l_ne = _init_l_ne();
 l_type__eq__of__heq = _init_l_type__eq__of__heq();
 l_and_symm = _init_l_and_symm();
 l_not__not__em = _init_l_not__not__em();
 l_or_symm = _init_l_or_symm();
 l_xor = _init_l_xor();
 l_not__true__iff = _init_l_not__true__iff();
 l_and__implies = _init_l_and__implies();
 l_exists_intro = _init_l_exists_intro();
 l_true_decidable = _init_l_true_decidable();
 l_true_decidable___boxed = _init_l_true_decidable___boxed();
 l_false_decidable = _init_l_false_decidable();
 l_false_decidable___boxed = _init_l_false_decidable___boxed();
 l_is__dec__eq = _init_l_is__dec__eq();
 l_is__dec__refl = _init_l_is__dec__refl();
 l_as__true = _init_l_as__true();
 l_as__false = _init_l_as__false();
 l_of__as__true = _init_l_of__as__true();
 l_prop_inhabited = _init_l_prop_inhabited();
 l_bool_inhabited = _init_l_bool_inhabited();
 l_bool_inhabited___boxed = _init_l_bool_inhabited___boxed();
 l_true_inhabited = _init_l_true_inhabited();
 l_nat_inhabited = _init_l_nat_inhabited();
 l_nonempty_elim = _init_l_nonempty_elim();
 l_nonempty__of__inhabited = _init_l_nonempty__of__inhabited();
 l_subsingleton_elim = _init_l_subsingleton_elim();
 l_subsingleton_helim = _init_l_subsingleton_helim();
 l_subsingleton__prop = _init_l_subsingleton__prop();
 l_decidable_subsingleton = _init_l_decidable_subsingleton();
 l_reflexive = _init_l_reflexive();
 l_symmetric = _init_l_symmetric();
 l_transitive = _init_l_transitive();
 l_equivalence = _init_l_equivalence();
 l_total = _init_l_total();
 l_mk__equivalence = _init_l_mk__equivalence();
 l_irreflexive = _init_l_irreflexive();
 l_anti__symmetric = _init_l_anti__symmetric();
 l_empty__relation = _init_l_empty__relation();
 l_subrelation = _init_l_subrelation();
 l_inv__image = _init_l_inv__image();
 l_commutative = _init_l_commutative();
 l_associative = _init_l_associative();
 l_left__identity = _init_l_left__identity();
 l_right__identity = _init_l_right__identity();
 l_right__inverse = _init_l_right__inverse();
 l_left__cancelative = _init_l_left__cancelative();
 l_right__cancelative = _init_l_right__cancelative();
 l_left__distributive = _init_l_left__distributive();
 l_right__distributive = _init_l_right__distributive();
 l_right__commutative = _init_l_right__commutative();
 l_left__commutative = _init_l_left__commutative();
 l_subtype_exists__of__subtype___main = _init_l_subtype_exists__of__subtype___main();
 l_subtype_exists__of__subtype = _init_l_subtype_exists__of__subtype();
 l_punit_subsingleton = _init_l_punit_subsingleton();
 l_punit_inhabited = _init_l_punit_inhabited();
 l_quotient = _init_l_quotient();
 l_quotient_sound = _init_l_quotient_sound();
 l___private_init_core_19__rel = _init_l___private_init_core_19__rel();
 l_function_equiv = _init_l_function_equiv();
 l___private_init_core_25__extfun = _init_l___private_init_core_25__extfun();
 l_pi_subsingleton = _init_l_pi_subsingleton();
 l_classical_by__cases = _init_l_classical_by__cases();
}
