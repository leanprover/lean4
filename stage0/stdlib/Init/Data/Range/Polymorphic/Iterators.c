// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Iterators
// Imports: public import Init.Data.Range.Polymorphic.RangeIterator public import Init.Data.Range.Polymorphic.Basic public import Init.Data.Iterators.Consumers.Collect import Init.Data.Iterators.Consumers.Loop import Init.Data.Option.Lemmas
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_Internal_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_Internal_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_Internal_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Rcc_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Rcc_toList___redArg___closed__0 = (const lean_object*)&l_Std_Rcc_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Rcc_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_size___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_Internal_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_Internal_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_Internal_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_size___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_Internal_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_Internal_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_Internal_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_size___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_Internal_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_Internal_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_size___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_Internal_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_Internal_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_size___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_Internal_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_Internal_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_size___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_Internal_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_Internal_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_toList___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_toArray___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_size___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_Internal_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_Internal_iter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_Internal_iter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_toList___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_toArray___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_size___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_Internal_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_Internal_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_Internal_iter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_Internal_iter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_size___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_Internal_iter___redArg(lean_object* v_r_1_){
_start:
{
lean_object* v_lower_2_; lean_object* v_upper_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_lower_2_ = lean_ctor_get(v_r_1_, 0);
v_upper_3_ = lean_ctor_get(v_r_1_, 1);
v_isSharedCheck_11_ = !lean_is_exclusive(v_r_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_r_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_upper_3_);
lean_inc(v_lower_2_);
lean_dec(v_r_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7_, 0, v_lower_2_);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v___x_7_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v_upper_3_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_Internal_iter(lean_object* v_00_u03b1_12_, lean_object* v_inst_13_, lean_object* v_r_14_){
_start:
{
lean_object* v_lower_15_; lean_object* v_upper_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_24_; 
v_lower_15_ = lean_ctor_get(v_r_14_, 0);
v_upper_16_ = lean_ctor_get(v_r_14_, 1);
v_isSharedCheck_24_ = !lean_is_exclusive(v_r_14_);
if (v_isSharedCheck_24_ == 0)
{
v___x_18_ = v_r_14_;
v_isShared_19_ = v_isSharedCheck_24_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_upper_16_);
lean_inc(v_lower_15_);
lean_dec(v_r_14_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_24_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_20_, 0, v_lower_15_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_20_);
v___x_22_ = v___x_18_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_upper_16_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_Internal_iter___boxed(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_r_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Std_Rcc_Internal_iter(v_00_u03b1_25_, v_inst_26_, v_r_27_);
lean_dec_ref(v_inst_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_toList___redArg___lam__0(lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_it_31_, lean_object* v_acc_32_, lean_object* v_recur_33_){
_start:
{
lean_object* v_next_34_; 
v_next_34_ = lean_ctor_get(v_it_31_, 0);
lean_inc(v_next_34_);
if (lean_obj_tag(v_next_34_) == 0)
{
lean_dec_ref(v_recur_33_);
lean_dec_ref(v_it_31_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_inst_29_);
return v_acc_32_;
}
else
{
lean_object* v_upperBound_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_49_; 
v_upperBound_35_ = lean_ctor_get(v_it_31_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_it_31_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; 
v_unused_50_ = lean_ctor_get(v_it_31_, 0);
lean_dec(v_unused_50_);
v___x_37_ = v_it_31_;
v_isShared_38_ = v_isSharedCheck_49_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_upperBound_35_);
lean_dec(v_it_31_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_49_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v_val_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_val_39_ = lean_ctor_get(v_next_34_, 0);
lean_inc_n(v_val_39_, 2);
lean_dec_ref(v_next_34_);
lean_inc(v_upperBound_35_);
v___x_40_ = lean_apply_2(v_inst_29_, v_val_39_, v_upperBound_35_);
v___x_41_ = lean_unbox(v___x_40_);
if (v___x_41_ == 0)
{
lean_dec(v_val_39_);
lean_del_object(v___x_37_);
lean_dec(v_upperBound_35_);
lean_dec_ref(v_recur_33_);
lean_dec_ref(v_inst_30_);
return v_acc_32_;
}
else
{
lean_object* v_succ_x3f_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v_succ_x3f_42_ = lean_ctor_get(v_inst_30_, 0);
lean_inc_ref(v_succ_x3f_42_);
lean_dec_ref(v_inst_30_);
lean_inc(v_val_39_);
v___x_43_ = lean_apply_1(v_succ_x3f_42_, v_val_39_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_43_);
v___x_45_ = v___x_37_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_upperBound_35_);
v___x_45_ = v_reuseFailAlloc_48_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_array_push(v_acc_32_, v_val_39_);
v___x_47_ = lean_apply_3(v_recur_33_, v___x_45_, v___x_46_, lean_box(0));
return v___x_47_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_toList___redArg(lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_r_55_){
_start:
{
lean_object* v_lower_56_; lean_object* v_upper_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_69_; 
v_lower_56_ = lean_ctor_get(v_r_55_, 0);
v_upper_57_ = lean_ctor_get(v_r_55_, 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v_r_55_);
if (v_isSharedCheck_69_ == 0)
{
v___x_59_ = v_r_55_;
v_isShared_60_ = v_isSharedCheck_69_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_upper_57_);
lean_inc(v_lower_56_);
lean_dec(v_r_55_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_69_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___f_61_ = lean_alloc_closure((void*)(l_Std_Rcc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_61_, 0, v_inst_53_);
lean_closure_set(v___f_61_, 1, v_inst_54_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v_lower_56_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 0, v___x_62_);
v___x_64_ = v___x_59_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_upper_57_);
v___x_64_ = v_reuseFailAlloc_68_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_66_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_61_, v___x_64_, v___x_65_);
v___x_67_ = lean_array_to_list(v___x_66_);
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_toList(lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_r_76_){
_start:
{
lean_object* v_lower_77_; lean_object* v_upper_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_90_; 
v_lower_77_ = lean_ctor_get(v_r_76_, 0);
v_upper_78_ = lean_ctor_get(v_r_76_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_r_76_);
if (v_isSharedCheck_90_ == 0)
{
v___x_80_ = v_r_76_;
v_isShared_81_ = v_isSharedCheck_90_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_upper_78_);
lean_inc(v_lower_77_);
lean_dec(v_r_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_90_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___f_82_ = lean_alloc_closure((void*)(l_Std_Rcc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_82_, 0, v_inst_72_);
lean_closure_set(v___f_82_, 1, v_inst_73_);
v___x_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_83_, 0, v_lower_77_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_upper_78_);
v___x_85_ = v_reuseFailAlloc_89_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_87_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_82_, v___x_85_, v___x_86_);
v___x_88_ = lean_array_to_list(v___x_87_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_toArray___redArg(lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_r_93_){
_start:
{
lean_object* v_lower_94_; lean_object* v_upper_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_106_; 
v_lower_94_ = lean_ctor_get(v_r_93_, 0);
v_upper_95_ = lean_ctor_get(v_r_93_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_r_93_);
if (v_isSharedCheck_106_ == 0)
{
v___x_97_ = v_r_93_;
v_isShared_98_ = v_isSharedCheck_106_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_upper_95_);
lean_inc(v_lower_94_);
lean_dec(v_r_93_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_106_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___f_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___f_99_ = lean_alloc_closure((void*)(l_Std_Rcc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_99_, 0, v_inst_91_);
lean_closure_set(v___f_99_, 1, v_inst_92_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v_lower_94_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_100_);
v___x_102_ = v___x_97_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_upper_95_);
v___x_102_ = v_reuseFailAlloc_105_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_104_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_99_, v___x_102_, v___x_103_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_toArray(lean_object* v_00_u03b1_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_r_113_){
_start:
{
lean_object* v_lower_114_; lean_object* v_upper_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_126_; 
v_lower_114_ = lean_ctor_get(v_r_113_, 0);
v_upper_115_ = lean_ctor_get(v_r_113_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_r_113_);
if (v_isSharedCheck_126_ == 0)
{
v___x_117_ = v_r_113_;
v_isShared_118_ = v_isSharedCheck_126_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_upper_115_);
lean_inc(v_lower_114_);
lean_dec(v_r_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_126_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___f_119_ = lean_alloc_closure((void*)(l_Std_Rcc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_119_, 0, v_inst_109_);
lean_closure_set(v___f_119_, 1, v_inst_110_);
v___x_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_120_, 0, v_lower_114_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_120_);
v___x_122_ = v___x_117_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_upper_115_);
v___x_122_ = v_reuseFailAlloc_125_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_124_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_119_, v___x_122_, v___x_123_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_size___redArg(lean_object* v_inst_127_, lean_object* v_r_128_){
_start:
{
lean_object* v_lower_129_; lean_object* v_upper_130_; lean_object* v___x_131_; 
v_lower_129_ = lean_ctor_get(v_r_128_, 0);
lean_inc(v_lower_129_);
v_upper_130_ = lean_ctor_get(v_r_128_, 1);
lean_inc(v_upper_130_);
lean_dec_ref(v_r_128_);
v___x_131_ = lean_apply_2(v_inst_127_, v_lower_129_, v_upper_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_size(lean_object* v_00_u03b1_132_, lean_object* v_inst_133_, lean_object* v_r_134_){
_start:
{
lean_object* v_lower_135_; lean_object* v_upper_136_; lean_object* v___x_137_; 
v_lower_135_ = lean_ctor_get(v_r_134_, 0);
lean_inc(v_lower_135_);
v_upper_136_ = lean_ctor_get(v_r_134_, 1);
lean_inc(v_upper_136_);
lean_dec_ref(v_r_134_);
v___x_137_ = lean_apply_2(v_inst_133_, v_lower_135_, v_upper_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0(lean_object* v_toPure_138_, lean_object* v_____do__lift_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_apply_2(v_toPure_138_, lean_box(0), v_____do__lift_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1(lean_object* v_toPure_141_, lean_object* v_inst_142_, lean_object* v_next_143_, lean_object* v_G_144_, lean_object* v_____do__lift_145_){
_start:
{
if (lean_obj_tag(v_____do__lift_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_147_; 
lean_dec(v_G_144_);
lean_dec(v_next_143_);
lean_dec_ref(v_inst_142_);
v_a_146_ = lean_ctor_get(v_____do__lift_145_, 0);
lean_inc(v_a_146_);
lean_dec_ref(v_____do__lift_145_);
v___x_147_ = lean_apply_2(v_toPure_141_, lean_box(0), v_a_146_);
return v___x_147_;
}
else
{
lean_object* v_a_148_; lean_object* v_succ_x3f_149_; lean_object* v___x_150_; 
v_a_148_ = lean_ctor_get(v_____do__lift_145_, 0);
lean_inc(v_a_148_);
lean_dec_ref(v_____do__lift_145_);
v_succ_x3f_149_ = lean_ctor_get(v_inst_142_, 0);
lean_inc_ref(v_succ_x3f_149_);
lean_dec_ref(v_inst_142_);
v___x_150_ = lean_apply_1(v_succ_x3f_149_, v_next_143_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v___x_151_; 
lean_dec(v_G_144_);
v___x_151_ = lean_apply_2(v_toPure_141_, lean_box(0), v_a_148_);
return v___x_151_;
}
else
{
lean_object* v_val_152_; lean_object* v___x_153_; 
lean_dec(v_toPure_141_);
v_val_152_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_val_152_);
lean_dec_ref(v___x_150_);
v___x_153_ = lean_apply_4(v_G_144_, v_val_152_, v_a_148_, lean_box(0), lean_box(0));
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2(lean_object* v_inst_154_, lean_object* v_upper_155_, lean_object* v_toPure_156_, lean_object* v_inst_157_, lean_object* v_f_158_, lean_object* v_toBind_159_, lean_object* v___f_160_, lean_object* v_next_161_, lean_object* v_acc_162_, lean_object* v_h_163_, lean_object* v_G_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
lean_inc(v_next_161_);
v___x_165_ = lean_apply_2(v_inst_154_, v_next_161_, v_upper_155_);
v___x_166_ = lean_unbox(v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
lean_dec(v_G_164_);
lean_dec(v_next_161_);
lean_dec(v___f_160_);
lean_dec(v_toBind_159_);
lean_dec(v_f_158_);
lean_dec_ref(v_inst_157_);
v___x_167_ = lean_apply_2(v_toPure_156_, lean_box(0), v_acc_162_);
return v___x_167_;
}
else
{
lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
lean_inc(v_next_161_);
v___f_168_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1), 5, 4);
lean_closure_set(v___f_168_, 0, v_toPure_156_);
lean_closure_set(v___f_168_, 1, v_inst_157_);
lean_closure_set(v___f_168_, 2, v_next_161_);
lean_closure_set(v___f_168_, 3, v_G_164_);
v___x_169_ = lean_apply_3(v_f_158_, v_next_161_, lean_box(0), v_acc_162_);
lean_inc(v_toBind_159_);
v___x_170_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_169_, v___f_160_);
v___x_171_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_170_, v___f_168_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__3(lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_00_u03b2_175_, lean_object* v_r_176_, lean_object* v_init_177_, lean_object* v_f_178_){
_start:
{
lean_object* v_toApplicative_179_; lean_object* v_lower_180_; lean_object* v_upper_181_; lean_object* v_toBind_182_; lean_object* v_toPure_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___x_186_; 
v_toApplicative_179_ = lean_ctor_get(v_inst_172_, 0);
lean_inc_ref(v_toApplicative_179_);
v_lower_180_ = lean_ctor_get(v_r_176_, 0);
lean_inc(v_lower_180_);
v_upper_181_ = lean_ctor_get(v_r_176_, 1);
lean_inc(v_upper_181_);
lean_dec_ref(v_r_176_);
v_toBind_182_ = lean_ctor_get(v_inst_172_, 1);
lean_inc(v_toBind_182_);
lean_dec_ref(v_inst_172_);
v_toPure_183_ = lean_ctor_get(v_toApplicative_179_, 1);
lean_inc_n(v_toPure_183_, 2);
lean_dec_ref(v_toApplicative_179_);
v___f_184_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_184_, 0, v_toPure_183_);
v___f_185_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2), 11, 7);
lean_closure_set(v___f_185_, 0, v_inst_173_);
lean_closure_set(v___f_185_, 1, v_upper_181_);
lean_closure_set(v___f_185_, 2, v_toPure_183_);
lean_closure_set(v___f_185_, 3, v_inst_174_);
lean_closure_set(v___f_185_, 4, v_f_178_);
lean_closure_set(v___f_185_, 5, v_toBind_182_);
lean_closure_set(v___f_185_, 6, v___f_184_);
v___x_186_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_185_, v_lower_180_, v_init_177_, lean_box(0));
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg(lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_){
_start:
{
lean_object* v___f_190_; 
v___f_190_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__3), 7, 3);
lean_closure_set(v___f_190_, 0, v_inst_189_);
lean_closure_set(v___f_190_, 1, v_inst_188_);
lean_closure_set(v___f_190_, 2, v_inst_187_);
return v___f_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId(lean_object* v_00_u03b1_191_, lean_object* v_m_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__3), 7, 3);
lean_closure_set(v___f_200_, 0, v_inst_198_);
lean_closure_set(v___f_200_, 1, v_inst_195_);
lean_closure_set(v___f_200_, 2, v_inst_193_);
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_Internal_iter___redArg(lean_object* v_r_201_){
_start:
{
lean_object* v_lower_202_; lean_object* v_upper_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_211_; 
v_lower_202_ = lean_ctor_get(v_r_201_, 0);
v_upper_203_ = lean_ctor_get(v_r_201_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_r_201_);
if (v_isSharedCheck_211_ == 0)
{
v___x_205_ = v_r_201_;
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_upper_203_);
lean_inc(v_lower_202_);
lean_dec(v_r_201_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v_lower_202_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_upper_203_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_Internal_iter(lean_object* v_00_u03b1_212_, lean_object* v_inst_213_, lean_object* v_r_214_){
_start:
{
lean_object* v_lower_215_; lean_object* v_upper_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_224_; 
v_lower_215_ = lean_ctor_get(v_r_214_, 0);
v_upper_216_ = lean_ctor_get(v_r_214_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v_r_214_);
if (v_isSharedCheck_224_ == 0)
{
v___x_218_ = v_r_214_;
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_upper_216_);
lean_inc(v_lower_215_);
lean_dec(v_r_214_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v_lower_215_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_220_);
v___x_222_ = v___x_218_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_upper_216_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_Internal_iter___boxed(lean_object* v_00_u03b1_225_, lean_object* v_inst_226_, lean_object* v_r_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Rco_Internal_iter(v_00_u03b1_225_, v_inst_226_, v_r_227_);
lean_dec_ref(v_inst_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_toList___redArg___lam__0(lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_it_231_, lean_object* v_acc_232_, lean_object* v_recur_233_){
_start:
{
lean_object* v_next_234_; 
v_next_234_ = lean_ctor_get(v_it_231_, 0);
lean_inc(v_next_234_);
if (lean_obj_tag(v_next_234_) == 0)
{
lean_dec_ref(v_recur_233_);
lean_dec_ref(v_it_231_);
lean_dec_ref(v_inst_230_);
lean_dec_ref(v_inst_229_);
return v_acc_232_;
}
else
{
lean_object* v_upperBound_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_249_; 
v_upperBound_235_ = lean_ctor_get(v_it_231_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_it_231_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; 
v_unused_250_ = lean_ctor_get(v_it_231_, 0);
lean_dec(v_unused_250_);
v___x_237_ = v_it_231_;
v_isShared_238_ = v_isSharedCheck_249_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_upperBound_235_);
lean_dec(v_it_231_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_249_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_val_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_val_239_ = lean_ctor_get(v_next_234_, 0);
lean_inc_n(v_val_239_, 2);
lean_dec_ref(v_next_234_);
lean_inc(v_upperBound_235_);
v___x_240_ = lean_apply_2(v_inst_229_, v_val_239_, v_upperBound_235_);
v___x_241_ = lean_unbox(v___x_240_);
if (v___x_241_ == 0)
{
lean_dec(v_val_239_);
lean_del_object(v___x_237_);
lean_dec(v_upperBound_235_);
lean_dec_ref(v_recur_233_);
lean_dec_ref(v_inst_230_);
return v_acc_232_;
}
else
{
lean_object* v_succ_x3f_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v_succ_x3f_242_ = lean_ctor_get(v_inst_230_, 0);
lean_inc_ref(v_succ_x3f_242_);
lean_dec_ref(v_inst_230_);
lean_inc(v_val_239_);
v___x_243_ = lean_apply_1(v_succ_x3f_242_, v_val_239_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_243_);
v___x_245_ = v___x_237_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_upperBound_235_);
v___x_245_ = v_reuseFailAlloc_248_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_array_push(v_acc_232_, v_val_239_);
v___x_247_ = lean_apply_3(v_recur_233_, v___x_245_, v___x_246_, lean_box(0));
return v___x_247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_toList___redArg(lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_r_253_){
_start:
{
lean_object* v_lower_254_; lean_object* v_upper_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_267_; 
v_lower_254_ = lean_ctor_get(v_r_253_, 0);
v_upper_255_ = lean_ctor_get(v_r_253_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_r_253_);
if (v_isSharedCheck_267_ == 0)
{
v___x_257_ = v_r_253_;
v_isShared_258_ = v_isSharedCheck_267_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_upper_255_);
lean_inc(v_lower_254_);
lean_dec(v_r_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_267_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___f_259_ = lean_alloc_closure((void*)(l_Std_Rco_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_259_, 0, v_inst_251_);
lean_closure_set(v___f_259_, 1, v_inst_252_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v_lower_254_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_260_);
v___x_262_ = v___x_257_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_upper_255_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_264_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_259_, v___x_262_, v___x_263_);
v___x_265_ = lean_array_to_list(v___x_264_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_toList(lean_object* v_00_u03b1_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_r_274_){
_start:
{
lean_object* v_lower_275_; lean_object* v_upper_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_288_; 
v_lower_275_ = lean_ctor_get(v_r_274_, 0);
v_upper_276_ = lean_ctor_get(v_r_274_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_r_274_);
if (v_isSharedCheck_288_ == 0)
{
v___x_278_ = v_r_274_;
v_isShared_279_ = v_isSharedCheck_288_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_upper_276_);
lean_inc(v_lower_275_);
lean_dec(v_r_274_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_288_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___f_280_ = lean_alloc_closure((void*)(l_Std_Rco_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_280_, 0, v_inst_270_);
lean_closure_set(v___f_280_, 1, v_inst_271_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_lower_275_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_281_);
v___x_283_ = v___x_278_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_upper_276_);
v___x_283_ = v_reuseFailAlloc_287_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_285_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_280_, v___x_283_, v___x_284_);
v___x_286_ = lean_array_to_list(v___x_285_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_toArray___redArg(lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_r_291_){
_start:
{
lean_object* v_lower_292_; lean_object* v_upper_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_304_; 
v_lower_292_ = lean_ctor_get(v_r_291_, 0);
v_upper_293_ = lean_ctor_get(v_r_291_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_r_291_);
if (v_isSharedCheck_304_ == 0)
{
v___x_295_ = v_r_291_;
v_isShared_296_ = v_isSharedCheck_304_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_upper_293_);
lean_inc(v_lower_292_);
lean_dec(v_r_291_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_304_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___f_297_ = lean_alloc_closure((void*)(l_Std_Rco_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_297_, 0, v_inst_289_);
lean_closure_set(v___f_297_, 1, v_inst_290_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v_lower_292_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_298_);
v___x_300_ = v___x_295_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_upper_293_);
v___x_300_ = v_reuseFailAlloc_303_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_302_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_297_, v___x_300_, v___x_301_);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_toArray(lean_object* v_00_u03b1_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_r_311_){
_start:
{
lean_object* v_lower_312_; lean_object* v_upper_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_324_; 
v_lower_312_ = lean_ctor_get(v_r_311_, 0);
v_upper_313_ = lean_ctor_get(v_r_311_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_r_311_);
if (v_isSharedCheck_324_ == 0)
{
v___x_315_ = v_r_311_;
v_isShared_316_ = v_isSharedCheck_324_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_upper_313_);
lean_inc(v_lower_312_);
lean_dec(v_r_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_324_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___f_317_ = lean_alloc_closure((void*)(l_Std_Rco_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_317_, 0, v_inst_307_);
lean_closure_set(v___f_317_, 1, v_inst_308_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v_lower_312_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_318_);
v___x_320_ = v___x_315_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_upper_313_);
v___x_320_ = v_reuseFailAlloc_323_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_322_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_317_, v___x_320_, v___x_321_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_size___redArg(lean_object* v_inst_325_, lean_object* v_r_326_){
_start:
{
lean_object* v_lower_327_; lean_object* v_upper_328_; lean_object* v___x_329_; 
v_lower_327_ = lean_ctor_get(v_r_326_, 0);
lean_inc(v_lower_327_);
v_upper_328_ = lean_ctor_get(v_r_326_, 1);
lean_inc(v_upper_328_);
lean_dec_ref(v_r_326_);
v___x_329_ = lean_apply_2(v_inst_325_, v_lower_327_, v_upper_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_size(lean_object* v_00_u03b1_330_, lean_object* v_inst_331_, lean_object* v_r_332_){
_start:
{
lean_object* v_lower_333_; lean_object* v_upper_334_; lean_object* v___x_335_; 
v_lower_333_ = lean_ctor_get(v_r_332_, 0);
lean_inc(v_lower_333_);
v_upper_334_ = lean_ctor_get(v_r_332_, 1);
lean_inc(v_upper_334_);
lean_dec_ref(v_r_332_);
v___x_335_ = lean_apply_2(v_inst_331_, v_lower_333_, v_upper_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3(lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_00_u03b2_339_, lean_object* v_r_340_, lean_object* v_init_341_, lean_object* v_f_342_){
_start:
{
lean_object* v_toApplicative_343_; lean_object* v_lower_344_; lean_object* v_upper_345_; lean_object* v_toBind_346_; lean_object* v_toPure_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___x_350_; 
v_toApplicative_343_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toApplicative_343_);
v_lower_344_ = lean_ctor_get(v_r_340_, 0);
lean_inc(v_lower_344_);
v_upper_345_ = lean_ctor_get(v_r_340_, 1);
lean_inc(v_upper_345_);
lean_dec_ref(v_r_340_);
v_toBind_346_ = lean_ctor_get(v_inst_336_, 1);
lean_inc(v_toBind_346_);
lean_dec_ref(v_inst_336_);
v_toPure_347_ = lean_ctor_get(v_toApplicative_343_, 1);
lean_inc_n(v_toPure_347_, 2);
lean_dec_ref(v_toApplicative_343_);
v___f_348_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_348_, 0, v_toPure_347_);
v___f_349_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2), 11, 7);
lean_closure_set(v___f_349_, 0, v_inst_337_);
lean_closure_set(v___f_349_, 1, v_upper_345_);
lean_closure_set(v___f_349_, 2, v_toPure_347_);
lean_closure_set(v___f_349_, 3, v_inst_338_);
lean_closure_set(v___f_349_, 4, v_f_342_);
lean_closure_set(v___f_349_, 5, v_toBind_346_);
lean_closure_set(v___f_349_, 6, v___f_348_);
v___x_350_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_349_, v_lower_344_, v_init_341_, lean_box(0));
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_inst_353_){
_start:
{
lean_object* v___f_354_; 
v___f_354_ = lean_alloc_closure((void*)(l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3), 7, 3);
lean_closure_set(v___f_354_, 0, v_inst_353_);
lean_closure_set(v___f_354_, 1, v_inst_352_);
lean_closure_set(v___f_354_, 2, v_inst_351_);
return v___f_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(lean_object* v_00_u03b1_355_, lean_object* v_m_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_inst_365_){
_start:
{
lean_object* v___f_366_; 
v___f_366_ = lean_alloc_closure((void*)(l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3), 7, 3);
lean_closure_set(v___f_366_, 0, v_inst_364_);
lean_closure_set(v___f_366_, 1, v_inst_360_);
lean_closure_set(v___f_366_, 2, v_inst_357_);
return v___f_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_Internal_iter___redArg(lean_object* v_r_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v_r_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_Internal_iter(lean_object* v_00_u03b1_369_, lean_object* v_inst_370_, lean_object* v_r_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v_r_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_Internal_iter___boxed(lean_object* v_00_u03b1_373_, lean_object* v_inst_374_, lean_object* v_r_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_Rci_Internal_iter(v_00_u03b1_373_, v_inst_374_, v_r_375_);
lean_dec_ref(v_inst_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_toList___redArg___lam__0(lean_object* v_inst_377_, lean_object* v_it_378_, lean_object* v_acc_379_, lean_object* v_recur_380_){
_start:
{
if (lean_obj_tag(v_it_378_) == 0)
{
lean_dec_ref(v_recur_380_);
lean_dec_ref(v_inst_377_);
return v_acc_379_;
}
else
{
lean_object* v_val_381_; lean_object* v_succ_x3f_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_val_381_ = lean_ctor_get(v_it_378_, 0);
lean_inc_n(v_val_381_, 2);
lean_dec_ref(v_it_378_);
v_succ_x3f_382_ = lean_ctor_get(v_inst_377_, 0);
lean_inc_ref(v_succ_x3f_382_);
lean_dec_ref(v_inst_377_);
v___x_383_ = lean_apply_1(v_succ_x3f_382_, v_val_381_);
v___x_384_ = lean_array_push(v_acc_379_, v_val_381_);
v___x_385_ = lean_apply_3(v_recur_380_, v___x_383_, v___x_384_, lean_box(0));
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rci_toList___redArg(lean_object* v_inst_386_, lean_object* v_r_387_){
_start:
{
lean_object* v___f_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___f_388_ = lean_alloc_closure((void*)(l_Std_Rci_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_388_, 0, v_inst_386_);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v_r_387_);
v___x_390_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_391_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_388_, v___x_389_, v___x_390_);
v___x_392_ = lean_array_to_list(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_toList(lean_object* v_00_u03b1_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_r_397_){
_start:
{
lean_object* v___f_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___f_398_ = lean_alloc_closure((void*)(l_Std_Rci_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_398_, 0, v_inst_394_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_r_397_);
v___x_400_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_401_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_398_, v___x_399_, v___x_400_);
v___x_402_ = lean_array_to_list(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_toArray___redArg(lean_object* v_inst_403_, lean_object* v_r_404_){
_start:
{
lean_object* v___f_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___f_405_ = lean_alloc_closure((void*)(l_Std_Rci_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_405_, 0, v_inst_403_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v_r_404_);
v___x_407_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_408_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_405_, v___x_406_, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_toArray(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_r_413_){
_start:
{
lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___f_414_ = lean_alloc_closure((void*)(l_Std_Rci_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_414_, 0, v_inst_410_);
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v_r_413_);
v___x_416_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_417_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_414_, v___x_415_, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_size___redArg(lean_object* v_inst_418_, lean_object* v_r_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_apply_1(v_inst_418_, v_r_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_size(lean_object* v_00_u03b1_421_, lean_object* v_inst_422_, lean_object* v_r_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_apply_1(v_inst_422_, v_r_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2(lean_object* v_toPure_425_, lean_object* v_inst_426_, lean_object* v_f_427_, lean_object* v_toBind_428_, lean_object* v___f_429_, lean_object* v_next_430_, lean_object* v_acc_431_, lean_object* v_h_432_, lean_object* v_G_433_){
_start:
{
lean_object* v___f_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_inc(v_next_430_);
v___f_434_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1), 5, 4);
lean_closure_set(v___f_434_, 0, v_toPure_425_);
lean_closure_set(v___f_434_, 1, v_inst_426_);
lean_closure_set(v___f_434_, 2, v_next_430_);
lean_closure_set(v___f_434_, 3, v_G_433_);
v___x_435_ = lean_apply_3(v_f_427_, v_next_430_, lean_box(0), v_acc_431_);
lean_inc(v_toBind_428_);
v___x_436_ = lean_apply_4(v_toBind_428_, lean_box(0), lean_box(0), v___x_435_, v___f_429_);
v___x_437_ = lean_apply_4(v_toBind_428_, lean_box(0), lean_box(0), v___x_436_, v___f_434_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0(lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_00_u03b2_440_, lean_object* v_r_441_, lean_object* v_init_442_, lean_object* v_f_443_){
_start:
{
lean_object* v_toApplicative_444_; lean_object* v_toBind_445_; lean_object* v_toPure_446_; lean_object* v___f_447_; lean_object* v___f_448_; lean_object* v___x_449_; 
v_toApplicative_444_ = lean_ctor_get(v_inst_438_, 0);
lean_inc_ref(v_toApplicative_444_);
v_toBind_445_ = lean_ctor_get(v_inst_438_, 1);
lean_inc(v_toBind_445_);
lean_dec_ref(v_inst_438_);
v_toPure_446_ = lean_ctor_get(v_toApplicative_444_, 1);
lean_inc_n(v_toPure_446_, 2);
lean_dec_ref(v_toApplicative_444_);
v___f_447_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_447_, 0, v_toPure_446_);
v___f_448_ = lean_alloc_closure((void*)(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2), 9, 5);
lean_closure_set(v___f_448_, 0, v_toPure_446_);
lean_closure_set(v___f_448_, 1, v_inst_439_);
lean_closure_set(v___f_448_, 2, v_f_443_);
lean_closure_set(v___f_448_, 3, v_toBind_445_);
lean_closure_set(v___f_448_, 4, v___f_447_);
v___x_449_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_448_, v_r_441_, v_init_442_, lean_box(0));
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg(lean_object* v_inst_450_, lean_object* v_inst_451_){
_start:
{
lean_object* v___f_452_; 
v___f_452_ = lean_alloc_closure((void*)(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0), 6, 2);
lean_closure_set(v___f_452_, 0, v_inst_451_);
lean_closure_set(v___f_452_, 1, v_inst_450_);
return v___f_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId(lean_object* v_00_u03b1_453_, lean_object* v_m_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v___f_461_; 
v___f_461_ = lean_alloc_closure((void*)(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0), 6, 2);
lean_closure_set(v___f_461_, 0, v_inst_459_);
lean_closure_set(v___f_461_, 1, v_inst_455_);
return v___f_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_Internal_iter___redArg(lean_object* v_inst_462_, lean_object* v_r_463_){
_start:
{
lean_object* v_succ_x3f_464_; lean_object* v_lower_465_; lean_object* v_upper_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_succ_x3f_464_ = lean_ctor_get(v_inst_462_, 0);
lean_inc_ref(v_succ_x3f_464_);
lean_dec_ref(v_inst_462_);
v_lower_465_ = lean_ctor_get(v_r_463_, 0);
v_upper_466_ = lean_ctor_get(v_r_463_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_r_463_);
if (v_isSharedCheck_474_ == 0)
{
v___x_468_ = v_r_463_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_upper_466_);
lean_inc(v_lower_465_);
lean_dec(v_r_463_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_apply_1(v_succ_x3f_464_, v_lower_465_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_upper_466_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_Internal_iter(lean_object* v_00_u03b1_475_, lean_object* v_inst_476_, lean_object* v_r_477_){
_start:
{
lean_object* v_succ_x3f_478_; lean_object* v_lower_479_; lean_object* v_upper_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_488_; 
v_succ_x3f_478_ = lean_ctor_get(v_inst_476_, 0);
lean_inc_ref(v_succ_x3f_478_);
lean_dec_ref(v_inst_476_);
v_lower_479_ = lean_ctor_get(v_r_477_, 0);
v_upper_480_ = lean_ctor_get(v_r_477_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_r_477_);
if (v_isSharedCheck_488_ == 0)
{
v___x_482_ = v_r_477_;
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_upper_480_);
lean_inc(v_lower_479_);
lean_dec(v_r_477_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_apply_1(v_succ_x3f_478_, v_lower_479_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_upper_480_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_toList___redArg___lam__0(lean_object* v_inst_489_, lean_object* v_succ_x3f_490_, lean_object* v_it_491_, lean_object* v_acc_492_, lean_object* v_recur_493_){
_start:
{
lean_object* v_next_494_; 
v_next_494_ = lean_ctor_get(v_it_491_, 0);
lean_inc(v_next_494_);
if (lean_obj_tag(v_next_494_) == 0)
{
lean_dec_ref(v_recur_493_);
lean_dec_ref(v_it_491_);
lean_dec_ref(v_succ_x3f_490_);
lean_dec_ref(v_inst_489_);
return v_acc_492_;
}
else
{
lean_object* v_upperBound_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_508_; 
v_upperBound_495_ = lean_ctor_get(v_it_491_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_it_491_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v_it_491_, 0);
lean_dec(v_unused_509_);
v___x_497_ = v_it_491_;
v_isShared_498_ = v_isSharedCheck_508_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_upperBound_495_);
lean_dec(v_it_491_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_508_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_val_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_val_499_ = lean_ctor_get(v_next_494_, 0);
lean_inc_n(v_val_499_, 2);
lean_dec_ref(v_next_494_);
lean_inc(v_upperBound_495_);
v___x_500_ = lean_apply_2(v_inst_489_, v_val_499_, v_upperBound_495_);
v___x_501_ = lean_unbox(v___x_500_);
if (v___x_501_ == 0)
{
lean_dec(v_val_499_);
lean_del_object(v___x_497_);
lean_dec(v_upperBound_495_);
lean_dec_ref(v_recur_493_);
lean_dec_ref(v_succ_x3f_490_);
return v_acc_492_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_inc(v_val_499_);
v___x_502_ = lean_apply_1(v_succ_x3f_490_, v_val_499_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_502_);
v___x_504_ = v___x_497_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_upperBound_495_);
v___x_504_ = v_reuseFailAlloc_507_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_array_push(v_acc_492_, v_val_499_);
v___x_506_ = lean_apply_3(v_recur_493_, v___x_504_, v___x_505_, lean_box(0));
return v___x_506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_toList___redArg(lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_r_512_){
_start:
{
lean_object* v_succ_x3f_513_; lean_object* v_lower_514_; lean_object* v_upper_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_527_; 
v_succ_x3f_513_ = lean_ctor_get(v_inst_511_, 0);
lean_inc_ref(v_succ_x3f_513_);
lean_dec_ref(v_inst_511_);
v_lower_514_ = lean_ctor_get(v_r_512_, 0);
v_upper_515_ = lean_ctor_get(v_r_512_, 1);
v_isSharedCheck_527_ = !lean_is_exclusive(v_r_512_);
if (v_isSharedCheck_527_ == 0)
{
v___x_517_ = v_r_512_;
v_isShared_518_ = v_isSharedCheck_527_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_upper_515_);
lean_inc(v_lower_514_);
lean_dec(v_r_512_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_527_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___f_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
lean_inc_ref(v_succ_x3f_513_);
v___f_519_ = lean_alloc_closure((void*)(l_Std_Roc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_519_, 0, v_inst_510_);
lean_closure_set(v___f_519_, 1, v_succ_x3f_513_);
v___x_520_ = lean_apply_1(v_succ_x3f_513_, v_lower_514_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_520_);
v___x_522_ = v___x_517_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_upper_515_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_524_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_519_, v___x_522_, v___x_523_);
v___x_525_ = lean_array_to_list(v___x_524_);
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_toList(lean_object* v_00_u03b1_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_r_534_){
_start:
{
lean_object* v_succ_x3f_535_; lean_object* v_lower_536_; lean_object* v_upper_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_549_; 
v_succ_x3f_535_ = lean_ctor_get(v_inst_531_, 0);
lean_inc_ref(v_succ_x3f_535_);
lean_dec_ref(v_inst_531_);
v_lower_536_ = lean_ctor_get(v_r_534_, 0);
v_upper_537_ = lean_ctor_get(v_r_534_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_r_534_);
if (v_isSharedCheck_549_ == 0)
{
v___x_539_ = v_r_534_;
v_isShared_540_ = v_isSharedCheck_549_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_upper_537_);
lean_inc(v_lower_536_);
lean_dec(v_r_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_549_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
lean_inc_ref(v_succ_x3f_535_);
v___f_541_ = lean_alloc_closure((void*)(l_Std_Roc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_541_, 0, v_inst_530_);
lean_closure_set(v___f_541_, 1, v_succ_x3f_535_);
v___x_542_ = lean_apply_1(v_succ_x3f_535_, v_lower_536_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_upper_537_);
v___x_544_ = v_reuseFailAlloc_548_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_546_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_541_, v___x_544_, v___x_545_);
v___x_547_ = lean_array_to_list(v___x_546_);
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_toArray___redArg(lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_r_552_){
_start:
{
lean_object* v_succ_x3f_553_; lean_object* v_lower_554_; lean_object* v_upper_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_566_; 
v_succ_x3f_553_ = lean_ctor_get(v_inst_551_, 0);
lean_inc_ref(v_succ_x3f_553_);
lean_dec_ref(v_inst_551_);
v_lower_554_ = lean_ctor_get(v_r_552_, 0);
v_upper_555_ = lean_ctor_get(v_r_552_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_r_552_);
if (v_isSharedCheck_566_ == 0)
{
v___x_557_ = v_r_552_;
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_upper_555_);
lean_inc(v_lower_554_);
lean_dec(v_r_552_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___f_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
lean_inc_ref(v_succ_x3f_553_);
v___f_559_ = lean_alloc_closure((void*)(l_Std_Roc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_559_, 0, v_inst_550_);
lean_closure_set(v___f_559_, 1, v_succ_x3f_553_);
v___x_560_ = lean_apply_1(v_succ_x3f_553_, v_lower_554_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_560_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_upper_555_);
v___x_562_ = v_reuseFailAlloc_565_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_564_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_559_, v___x_562_, v___x_563_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_toArray(lean_object* v_00_u03b1_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_r_573_){
_start:
{
lean_object* v_succ_x3f_574_; lean_object* v_lower_575_; lean_object* v_upper_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_587_; 
v_succ_x3f_574_ = lean_ctor_get(v_inst_570_, 0);
lean_inc_ref(v_succ_x3f_574_);
lean_dec_ref(v_inst_570_);
v_lower_575_ = lean_ctor_get(v_r_573_, 0);
v_upper_576_ = lean_ctor_get(v_r_573_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_r_573_);
if (v_isSharedCheck_587_ == 0)
{
v___x_578_ = v_r_573_;
v_isShared_579_ = v_isSharedCheck_587_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_upper_576_);
lean_inc(v_lower_575_);
lean_dec(v_r_573_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_587_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
lean_inc_ref(v_succ_x3f_574_);
v___f_580_ = lean_alloc_closure((void*)(l_Std_Roc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_580_, 0, v_inst_569_);
lean_closure_set(v___f_580_, 1, v_succ_x3f_574_);
v___x_581_ = lean_apply_1(v_succ_x3f_574_, v_lower_575_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_581_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_upper_576_);
v___x_583_ = v_reuseFailAlloc_586_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_585_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_580_, v___x_583_, v___x_584_);
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_size___redArg(lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_r_590_){
_start:
{
lean_object* v_succ_x3f_591_; lean_object* v_lower_592_; lean_object* v_upper_593_; lean_object* v___x_594_; 
v_succ_x3f_591_ = lean_ctor_get(v_inst_589_, 0);
lean_inc_ref(v_succ_x3f_591_);
lean_dec_ref(v_inst_589_);
v_lower_592_ = lean_ctor_get(v_r_590_, 0);
lean_inc(v_lower_592_);
v_upper_593_ = lean_ctor_get(v_r_590_, 1);
lean_inc(v_upper_593_);
lean_dec_ref(v_r_590_);
v___x_594_ = lean_apply_1(v_succ_x3f_591_, v_lower_592_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_595_; 
lean_dec(v_upper_593_);
lean_dec_ref(v_inst_588_);
v___x_595_ = lean_unsigned_to_nat(0u);
return v___x_595_;
}
else
{
lean_object* v_val_596_; lean_object* v___x_597_; 
v_val_596_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_val_596_);
lean_dec_ref(v___x_594_);
v___x_597_ = lean_apply_2(v_inst_588_, v_val_596_, v_upper_593_);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_size(lean_object* v_00_u03b1_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_r_601_){
_start:
{
lean_object* v_succ_x3f_602_; lean_object* v_lower_603_; lean_object* v_upper_604_; lean_object* v___x_605_; 
v_succ_x3f_602_ = lean_ctor_get(v_inst_600_, 0);
lean_inc_ref(v_succ_x3f_602_);
lean_dec_ref(v_inst_600_);
v_lower_603_ = lean_ctor_get(v_r_601_, 0);
lean_inc(v_lower_603_);
v_upper_604_ = lean_ctor_get(v_r_601_, 1);
lean_inc(v_upper_604_);
lean_dec_ref(v_r_601_);
v___x_605_ = lean_apply_1(v_succ_x3f_602_, v_lower_603_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v___x_606_; 
lean_dec(v_upper_604_);
lean_dec_ref(v_inst_599_);
v___x_606_ = lean_unsigned_to_nat(0u);
return v___x_606_;
}
else
{
lean_object* v_val_607_; lean_object* v___x_608_; 
v_val_607_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_607_);
lean_dec_ref(v___x_605_);
v___x_608_ = lean_apply_2(v_inst_599_, v_val_607_, v_upper_604_);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__1(lean_object* v_toPure_609_, lean_object* v_succ_x3f_610_, lean_object* v_next_611_, lean_object* v_G_612_, lean_object* v_____do__lift_613_){
_start:
{
if (lean_obj_tag(v_____do__lift_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_615_; 
lean_dec(v_G_612_);
lean_dec(v_next_611_);
lean_dec_ref(v_succ_x3f_610_);
v_a_614_ = lean_ctor_get(v_____do__lift_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref(v_____do__lift_613_);
v___x_615_ = lean_apply_2(v_toPure_609_, lean_box(0), v_a_614_);
return v___x_615_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_617_; 
v_a_616_ = lean_ctor_get(v_____do__lift_613_, 0);
lean_inc(v_a_616_);
lean_dec_ref(v_____do__lift_613_);
v___x_617_ = lean_apply_1(v_succ_x3f_610_, v_next_611_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; 
lean_dec(v_G_612_);
v___x_618_ = lean_apply_2(v_toPure_609_, lean_box(0), v_a_616_);
return v___x_618_;
}
else
{
lean_object* v_val_619_; lean_object* v___x_620_; 
lean_dec(v_toPure_609_);
v_val_619_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_val_619_);
lean_dec_ref(v___x_617_);
v___x_620_ = lean_apply_4(v_G_612_, v_val_619_, v_a_616_, lean_box(0), lean_box(0));
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0(lean_object* v_inst_621_, lean_object* v_upper_622_, lean_object* v_toPure_623_, lean_object* v_succ_x3f_624_, lean_object* v_f_625_, lean_object* v_toBind_626_, lean_object* v___f_627_, lean_object* v_next_628_, lean_object* v_acc_629_, lean_object* v_h_630_, lean_object* v_G_631_){
_start:
{
lean_object* v___x_632_; uint8_t v___x_633_; 
lean_inc(v_next_628_);
v___x_632_ = lean_apply_2(v_inst_621_, v_next_628_, v_upper_622_);
v___x_633_ = lean_unbox(v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
lean_dec(v_G_631_);
lean_dec(v_next_628_);
lean_dec(v___f_627_);
lean_dec(v_toBind_626_);
lean_dec(v_f_625_);
lean_dec_ref(v_succ_x3f_624_);
v___x_634_ = lean_apply_2(v_toPure_623_, lean_box(0), v_acc_629_);
return v___x_634_;
}
else
{
lean_object* v___f_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_inc(v_next_628_);
v___f_635_ = lean_alloc_closure((void*)(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__1), 5, 4);
lean_closure_set(v___f_635_, 0, v_toPure_623_);
lean_closure_set(v___f_635_, 1, v_succ_x3f_624_);
lean_closure_set(v___f_635_, 2, v_next_628_);
lean_closure_set(v___f_635_, 3, v_G_631_);
v___x_636_ = lean_apply_3(v_f_625_, v_next_628_, lean_box(0), v_acc_629_);
lean_inc(v_toBind_626_);
v___x_637_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_636_, v___f_627_);
v___x_638_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_637_, v___f_635_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2(lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_00_u03b2_642_, lean_object* v_r_643_, lean_object* v_init_644_, lean_object* v_f_645_){
_start:
{
lean_object* v_toApplicative_646_; lean_object* v_succ_x3f_647_; lean_object* v_lower_648_; lean_object* v_upper_649_; lean_object* v_toBind_650_; lean_object* v_toPure_651_; lean_object* v___x_652_; 
v_toApplicative_646_ = lean_ctor_get(v_inst_640_, 0);
lean_inc_ref(v_toApplicative_646_);
v_succ_x3f_647_ = lean_ctor_get(v_inst_639_, 0);
lean_inc_ref_n(v_succ_x3f_647_, 2);
lean_dec_ref(v_inst_639_);
v_lower_648_ = lean_ctor_get(v_r_643_, 0);
lean_inc(v_lower_648_);
v_upper_649_ = lean_ctor_get(v_r_643_, 1);
lean_inc(v_upper_649_);
lean_dec_ref(v_r_643_);
v_toBind_650_ = lean_ctor_get(v_inst_640_, 1);
lean_inc(v_toBind_650_);
lean_dec_ref(v_inst_640_);
v_toPure_651_ = lean_ctor_get(v_toApplicative_646_, 1);
lean_inc(v_toPure_651_);
lean_dec_ref(v_toApplicative_646_);
v___x_652_ = lean_apply_1(v_succ_x3f_647_, v_lower_648_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; 
lean_dec(v_toBind_650_);
lean_dec(v_upper_649_);
lean_dec_ref(v_succ_x3f_647_);
lean_dec(v_f_645_);
lean_dec_ref(v_inst_641_);
v___x_653_ = lean_apply_2(v_toPure_651_, lean_box(0), v_init_644_);
return v___x_653_;
}
else
{
lean_object* v_val_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___x_657_; 
v_val_654_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_654_);
lean_dec_ref(v___x_652_);
lean_inc(v_toPure_651_);
v___f_655_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_655_, 0, v_toPure_651_);
v___f_656_ = lean_alloc_closure((void*)(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0), 11, 7);
lean_closure_set(v___f_656_, 0, v_inst_641_);
lean_closure_set(v___f_656_, 1, v_upper_649_);
lean_closure_set(v___f_656_, 2, v_toPure_651_);
lean_closure_set(v___f_656_, 3, v_succ_x3f_647_);
lean_closure_set(v___f_656_, 4, v_f_645_);
lean_closure_set(v___f_656_, 5, v_toBind_650_);
lean_closure_set(v___f_656_, 6, v___f_655_);
v___x_657_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_656_, v_val_654_, v_init_644_, lean_box(0));
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_inst_660_){
_start:
{
lean_object* v___f_661_; 
v___f_661_ = lean_alloc_closure((void*)(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2), 7, 3);
lean_closure_set(v___f_661_, 0, v_inst_658_);
lean_closure_set(v___f_661_, 1, v_inst_660_);
lean_closure_set(v___f_661_, 2, v_inst_659_);
return v___f_661_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(lean_object* v_00_u03b1_662_, lean_object* v_m_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_inst_672_){
_start:
{
lean_object* v___f_673_; 
v___f_673_ = lean_alloc_closure((void*)(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2), 7, 3);
lean_closure_set(v___f_673_, 0, v_inst_664_);
lean_closure_set(v___f_673_, 1, v_inst_671_);
lean_closure_set(v___f_673_, 2, v_inst_666_);
return v___f_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_Internal_iter___redArg(lean_object* v_inst_674_, lean_object* v_r_675_){
_start:
{
lean_object* v_succ_x3f_676_; lean_object* v_lower_677_; lean_object* v_upper_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_686_; 
v_succ_x3f_676_ = lean_ctor_get(v_inst_674_, 0);
lean_inc_ref(v_succ_x3f_676_);
lean_dec_ref(v_inst_674_);
v_lower_677_ = lean_ctor_get(v_r_675_, 0);
v_upper_678_ = lean_ctor_get(v_r_675_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_r_675_);
if (v_isSharedCheck_686_ == 0)
{
v___x_680_ = v_r_675_;
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_upper_678_);
lean_inc(v_lower_677_);
lean_dec(v_r_675_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = lean_apply_1(v_succ_x3f_676_, v_lower_677_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_upper_678_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_Internal_iter(lean_object* v_00_u03b1_687_, lean_object* v_inst_688_, lean_object* v_r_689_){
_start:
{
lean_object* v_succ_x3f_690_; lean_object* v_lower_691_; lean_object* v_upper_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
v_succ_x3f_690_ = lean_ctor_get(v_inst_688_, 0);
lean_inc_ref(v_succ_x3f_690_);
lean_dec_ref(v_inst_688_);
v_lower_691_ = lean_ctor_get(v_r_689_, 0);
v_upper_692_ = lean_ctor_get(v_r_689_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_r_689_);
if (v_isSharedCheck_700_ == 0)
{
v___x_694_ = v_r_689_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_upper_692_);
lean_inc(v_lower_691_);
lean_dec(v_r_689_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_apply_1(v_succ_x3f_690_, v_lower_691_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_upper_692_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_toList___redArg___lam__0(lean_object* v_inst_701_, lean_object* v_succ_x3f_702_, lean_object* v_it_703_, lean_object* v_acc_704_, lean_object* v_recur_705_){
_start:
{
lean_object* v_next_706_; 
v_next_706_ = lean_ctor_get(v_it_703_, 0);
lean_inc(v_next_706_);
if (lean_obj_tag(v_next_706_) == 0)
{
lean_dec_ref(v_recur_705_);
lean_dec_ref(v_it_703_);
lean_dec_ref(v_succ_x3f_702_);
lean_dec_ref(v_inst_701_);
return v_acc_704_;
}
else
{
lean_object* v_upperBound_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_720_; 
v_upperBound_707_ = lean_ctor_get(v_it_703_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_it_703_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_it_703_, 0);
lean_dec(v_unused_721_);
v___x_709_ = v_it_703_;
v_isShared_710_ = v_isSharedCheck_720_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_upperBound_707_);
lean_dec(v_it_703_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_720_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_val_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v_val_711_ = lean_ctor_get(v_next_706_, 0);
lean_inc_n(v_val_711_, 2);
lean_dec_ref(v_next_706_);
lean_inc(v_upperBound_707_);
v___x_712_ = lean_apply_2(v_inst_701_, v_val_711_, v_upperBound_707_);
v___x_713_ = lean_unbox(v___x_712_);
if (v___x_713_ == 0)
{
lean_dec(v_val_711_);
lean_del_object(v___x_709_);
lean_dec(v_upperBound_707_);
lean_dec_ref(v_recur_705_);
lean_dec_ref(v_succ_x3f_702_);
return v_acc_704_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_716_; 
lean_inc(v_val_711_);
v___x_714_ = lean_apply_1(v_succ_x3f_702_, v_val_711_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_714_);
v___x_716_ = v___x_709_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_upperBound_707_);
v___x_716_ = v_reuseFailAlloc_719_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_array_push(v_acc_704_, v_val_711_);
v___x_718_ = lean_apply_3(v_recur_705_, v___x_716_, v___x_717_, lean_box(0));
return v___x_718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_toList___redArg(lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_r_724_){
_start:
{
lean_object* v_succ_x3f_725_; lean_object* v_lower_726_; lean_object* v_upper_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_739_; 
v_succ_x3f_725_ = lean_ctor_get(v_inst_723_, 0);
lean_inc_ref(v_succ_x3f_725_);
lean_dec_ref(v_inst_723_);
v_lower_726_ = lean_ctor_get(v_r_724_, 0);
v_upper_727_ = lean_ctor_get(v_r_724_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_r_724_);
if (v_isSharedCheck_739_ == 0)
{
v___x_729_ = v_r_724_;
v_isShared_730_ = v_isSharedCheck_739_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_upper_727_);
lean_inc(v_lower_726_);
lean_dec(v_r_724_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_739_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
lean_inc_ref(v_succ_x3f_725_);
v___f_731_ = lean_alloc_closure((void*)(l_Std_Roo_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_731_, 0, v_inst_722_);
lean_closure_set(v___f_731_, 1, v_succ_x3f_725_);
v___x_732_ = lean_apply_1(v_succ_x3f_725_, v_lower_726_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_732_);
v___x_734_ = v___x_729_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_upper_727_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_736_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_731_, v___x_734_, v___x_735_);
v___x_737_ = lean_array_to_list(v___x_736_);
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_toList(lean_object* v_00_u03b1_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_r_746_){
_start:
{
lean_object* v_succ_x3f_747_; lean_object* v_lower_748_; lean_object* v_upper_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_761_; 
v_succ_x3f_747_ = lean_ctor_get(v_inst_743_, 0);
lean_inc_ref(v_succ_x3f_747_);
lean_dec_ref(v_inst_743_);
v_lower_748_ = lean_ctor_get(v_r_746_, 0);
v_upper_749_ = lean_ctor_get(v_r_746_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_r_746_);
if (v_isSharedCheck_761_ == 0)
{
v___x_751_ = v_r_746_;
v_isShared_752_ = v_isSharedCheck_761_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_upper_749_);
lean_inc(v_lower_748_);
lean_dec(v_r_746_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_761_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
lean_inc_ref(v_succ_x3f_747_);
v___f_753_ = lean_alloc_closure((void*)(l_Std_Roo_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_753_, 0, v_inst_742_);
lean_closure_set(v___f_753_, 1, v_succ_x3f_747_);
v___x_754_ = lean_apply_1(v_succ_x3f_747_, v_lower_748_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_754_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_upper_749_);
v___x_756_ = v_reuseFailAlloc_760_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_758_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_753_, v___x_756_, v___x_757_);
v___x_759_ = lean_array_to_list(v___x_758_);
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_toArray___redArg(lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_r_764_){
_start:
{
lean_object* v_succ_x3f_765_; lean_object* v_lower_766_; lean_object* v_upper_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_778_; 
v_succ_x3f_765_ = lean_ctor_get(v_inst_763_, 0);
lean_inc_ref(v_succ_x3f_765_);
lean_dec_ref(v_inst_763_);
v_lower_766_ = lean_ctor_get(v_r_764_, 0);
v_upper_767_ = lean_ctor_get(v_r_764_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_r_764_);
if (v_isSharedCheck_778_ == 0)
{
v___x_769_ = v_r_764_;
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_upper_767_);
lean_inc(v_lower_766_);
lean_dec(v_r_764_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
lean_inc_ref(v_succ_x3f_765_);
v___f_771_ = lean_alloc_closure((void*)(l_Std_Roo_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_771_, 0, v_inst_762_);
lean_closure_set(v___f_771_, 1, v_succ_x3f_765_);
v___x_772_ = lean_apply_1(v_succ_x3f_765_, v_lower_766_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_772_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_upper_767_);
v___x_774_ = v_reuseFailAlloc_777_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_776_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_771_, v___x_774_, v___x_775_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_toArray(lean_object* v_00_u03b1_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_r_785_){
_start:
{
lean_object* v_succ_x3f_786_; lean_object* v_lower_787_; lean_object* v_upper_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_799_; 
v_succ_x3f_786_ = lean_ctor_get(v_inst_782_, 0);
lean_inc_ref(v_succ_x3f_786_);
lean_dec_ref(v_inst_782_);
v_lower_787_ = lean_ctor_get(v_r_785_, 0);
v_upper_788_ = lean_ctor_get(v_r_785_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_r_785_);
if (v_isSharedCheck_799_ == 0)
{
v___x_790_ = v_r_785_;
v_isShared_791_ = v_isSharedCheck_799_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_upper_788_);
lean_inc(v_lower_787_);
lean_dec(v_r_785_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_799_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
lean_inc_ref(v_succ_x3f_786_);
v___f_792_ = lean_alloc_closure((void*)(l_Std_Roo_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_792_, 0, v_inst_781_);
lean_closure_set(v___f_792_, 1, v_succ_x3f_786_);
v___x_793_ = lean_apply_1(v_succ_x3f_786_, v_lower_787_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_793_);
v___x_795_ = v___x_790_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_upper_788_);
v___x_795_ = v_reuseFailAlloc_798_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_797_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_792_, v___x_795_, v___x_796_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_size___redArg(lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_r_802_){
_start:
{
lean_object* v_succ_x3f_803_; lean_object* v_lower_804_; lean_object* v_upper_805_; lean_object* v___x_806_; 
v_succ_x3f_803_ = lean_ctor_get(v_inst_801_, 0);
lean_inc_ref(v_succ_x3f_803_);
lean_dec_ref(v_inst_801_);
v_lower_804_ = lean_ctor_get(v_r_802_, 0);
lean_inc(v_lower_804_);
v_upper_805_ = lean_ctor_get(v_r_802_, 1);
lean_inc(v_upper_805_);
lean_dec_ref(v_r_802_);
v___x_806_ = lean_apply_1(v_succ_x3f_803_, v_lower_804_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v___x_807_; 
lean_dec(v_upper_805_);
lean_dec_ref(v_inst_800_);
v___x_807_ = lean_unsigned_to_nat(0u);
return v___x_807_;
}
else
{
lean_object* v_val_808_; lean_object* v___x_809_; 
v_val_808_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_val_808_);
lean_dec_ref(v___x_806_);
v___x_809_ = lean_apply_2(v_inst_800_, v_val_808_, v_upper_805_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_size(lean_object* v_00_u03b1_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_r_813_){
_start:
{
lean_object* v_succ_x3f_814_; lean_object* v_lower_815_; lean_object* v_upper_816_; lean_object* v___x_817_; 
v_succ_x3f_814_ = lean_ctor_get(v_inst_812_, 0);
lean_inc_ref(v_succ_x3f_814_);
lean_dec_ref(v_inst_812_);
v_lower_815_ = lean_ctor_get(v_r_813_, 0);
lean_inc(v_lower_815_);
v_upper_816_ = lean_ctor_get(v_r_813_, 1);
lean_inc(v_upper_816_);
lean_dec_ref(v_r_813_);
v___x_817_ = lean_apply_1(v_succ_x3f_814_, v_lower_815_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_818_; 
lean_dec(v_upper_816_);
lean_dec_ref(v_inst_811_);
v___x_818_ = lean_unsigned_to_nat(0u);
return v___x_818_;
}
else
{
lean_object* v_val_819_; lean_object* v___x_820_; 
v_val_819_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_val_819_);
lean_dec_ref(v___x_817_);
v___x_820_ = lean_apply_2(v_inst_811_, v_val_819_, v_upper_816_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3(lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_00_u03b2_824_, lean_object* v_r_825_, lean_object* v_init_826_, lean_object* v_f_827_){
_start:
{
lean_object* v_toApplicative_828_; lean_object* v_succ_x3f_829_; lean_object* v_lower_830_; lean_object* v_upper_831_; lean_object* v_toBind_832_; lean_object* v_toPure_833_; lean_object* v___x_834_; 
v_toApplicative_828_ = lean_ctor_get(v_inst_822_, 0);
lean_inc_ref(v_toApplicative_828_);
v_succ_x3f_829_ = lean_ctor_get(v_inst_821_, 0);
lean_inc_ref_n(v_succ_x3f_829_, 2);
lean_dec_ref(v_inst_821_);
v_lower_830_ = lean_ctor_get(v_r_825_, 0);
lean_inc(v_lower_830_);
v_upper_831_ = lean_ctor_get(v_r_825_, 1);
lean_inc(v_upper_831_);
lean_dec_ref(v_r_825_);
v_toBind_832_ = lean_ctor_get(v_inst_822_, 1);
lean_inc(v_toBind_832_);
lean_dec_ref(v_inst_822_);
v_toPure_833_ = lean_ctor_get(v_toApplicative_828_, 1);
lean_inc(v_toPure_833_);
lean_dec_ref(v_toApplicative_828_);
v___x_834_ = lean_apply_1(v_succ_x3f_829_, v_lower_830_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v___x_835_; 
lean_dec(v_toBind_832_);
lean_dec(v_upper_831_);
lean_dec_ref(v_succ_x3f_829_);
lean_dec(v_f_827_);
lean_dec_ref(v_inst_823_);
v___x_835_ = lean_apply_2(v_toPure_833_, lean_box(0), v_init_826_);
return v___x_835_;
}
else
{
lean_object* v_val_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___x_839_; 
v_val_836_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_val_836_);
lean_dec_ref(v___x_834_);
lean_inc(v_toPure_833_);
v___f_837_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_837_, 0, v_toPure_833_);
v___f_838_ = lean_alloc_closure((void*)(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0), 11, 7);
lean_closure_set(v___f_838_, 0, v_inst_823_);
lean_closure_set(v___f_838_, 1, v_upper_831_);
lean_closure_set(v___f_838_, 2, v_toPure_833_);
lean_closure_set(v___f_838_, 3, v_succ_x3f_829_);
lean_closure_set(v___f_838_, 4, v_f_827_);
lean_closure_set(v___f_838_, 5, v_toBind_832_);
lean_closure_set(v___f_838_, 6, v___f_837_);
v___x_839_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_838_, v_val_836_, v_init_826_, lean_box(0));
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_inst_842_){
_start:
{
lean_object* v___f_843_; 
v___f_843_ = lean_alloc_closure((void*)(l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3), 7, 3);
lean_closure_set(v___f_843_, 0, v_inst_840_);
lean_closure_set(v___f_843_, 1, v_inst_842_);
lean_closure_set(v___f_843_, 2, v_inst_841_);
return v___f_843_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(lean_object* v_00_u03b1_844_, lean_object* v_m_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_inst_852_){
_start:
{
lean_object* v___f_853_; 
v___f_853_ = lean_alloc_closure((void*)(l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3), 7, 3);
lean_closure_set(v___f_853_, 0, v_inst_846_);
lean_closure_set(v___f_853_, 1, v_inst_851_);
lean_closure_set(v___f_853_, 2, v_inst_848_);
return v___f_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_Internal_iter___redArg(lean_object* v_inst_854_, lean_object* v_r_855_){
_start:
{
lean_object* v_succ_x3f_856_; lean_object* v___x_857_; 
v_succ_x3f_856_ = lean_ctor_get(v_inst_854_, 0);
lean_inc_ref(v_succ_x3f_856_);
lean_dec_ref(v_inst_854_);
v___x_857_ = lean_apply_1(v_succ_x3f_856_, v_r_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_Internal_iter(lean_object* v_00_u03b1_858_, lean_object* v_inst_859_, lean_object* v_r_860_){
_start:
{
lean_object* v_succ_x3f_861_; lean_object* v___x_862_; 
v_succ_x3f_861_ = lean_ctor_get(v_inst_859_, 0);
lean_inc_ref(v_succ_x3f_861_);
lean_dec_ref(v_inst_859_);
v___x_862_ = lean_apply_1(v_succ_x3f_861_, v_r_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_toList___redArg___lam__0(lean_object* v_succ_x3f_863_, lean_object* v_it_864_, lean_object* v_acc_865_, lean_object* v_recur_866_){
_start:
{
if (lean_obj_tag(v_it_864_) == 0)
{
lean_dec_ref(v_recur_866_);
lean_dec_ref(v_succ_x3f_863_);
return v_acc_865_;
}
else
{
lean_object* v_val_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_val_867_ = lean_ctor_get(v_it_864_, 0);
lean_inc_n(v_val_867_, 2);
lean_dec_ref(v_it_864_);
v___x_868_ = lean_apply_1(v_succ_x3f_863_, v_val_867_);
v___x_869_ = lean_array_push(v_acc_865_, v_val_867_);
v___x_870_ = lean_apply_3(v_recur_866_, v___x_868_, v___x_869_, lean_box(0));
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roi_toList___redArg(lean_object* v_inst_871_, lean_object* v_r_872_){
_start:
{
lean_object* v_succ_x3f_873_; lean_object* v___f_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_succ_x3f_873_ = lean_ctor_get(v_inst_871_, 0);
lean_inc_ref_n(v_succ_x3f_873_, 2);
lean_dec_ref(v_inst_871_);
v___f_874_ = lean_alloc_closure((void*)(l_Std_Roi_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_874_, 0, v_succ_x3f_873_);
v___x_875_ = lean_apply_1(v_succ_x3f_873_, v_r_872_);
v___x_876_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_877_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_874_, v___x_875_, v___x_876_);
v___x_878_ = lean_array_to_list(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_toList(lean_object* v_00_u03b1_879_, lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_r_883_){
_start:
{
lean_object* v_succ_x3f_884_; lean_object* v___f_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_succ_x3f_884_ = lean_ctor_get(v_inst_880_, 0);
lean_inc_ref_n(v_succ_x3f_884_, 2);
lean_dec_ref(v_inst_880_);
v___f_885_ = lean_alloc_closure((void*)(l_Std_Roi_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_885_, 0, v_succ_x3f_884_);
v___x_886_ = lean_apply_1(v_succ_x3f_884_, v_r_883_);
v___x_887_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_888_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_885_, v___x_886_, v___x_887_);
v___x_889_ = lean_array_to_list(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_toArray___redArg(lean_object* v_inst_890_, lean_object* v_r_891_){
_start:
{
lean_object* v_succ_x3f_892_; lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_succ_x3f_892_ = lean_ctor_get(v_inst_890_, 0);
lean_inc_ref_n(v_succ_x3f_892_, 2);
lean_dec_ref(v_inst_890_);
v___f_893_ = lean_alloc_closure((void*)(l_Std_Roi_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_893_, 0, v_succ_x3f_892_);
v___x_894_ = lean_apply_1(v_succ_x3f_892_, v_r_891_);
v___x_895_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_896_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_893_, v___x_894_, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_toArray(lean_object* v_00_u03b1_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_inst_900_, lean_object* v_r_901_){
_start:
{
lean_object* v_succ_x3f_902_; lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_succ_x3f_902_ = lean_ctor_get(v_inst_898_, 0);
lean_inc_ref_n(v_succ_x3f_902_, 2);
lean_dec_ref(v_inst_898_);
v___f_903_ = lean_alloc_closure((void*)(l_Std_Roi_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_903_, 0, v_succ_x3f_902_);
v___x_904_ = lean_apply_1(v_succ_x3f_902_, v_r_901_);
v___x_905_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_906_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_903_, v___x_904_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_size___redArg(lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_r_909_){
_start:
{
lean_object* v_succ_x3f_910_; lean_object* v___x_911_; 
v_succ_x3f_910_ = lean_ctor_get(v_inst_908_, 0);
lean_inc_ref(v_succ_x3f_910_);
lean_dec_ref(v_inst_908_);
v___x_911_ = lean_apply_1(v_succ_x3f_910_, v_r_909_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_912_; 
lean_dec_ref(v_inst_907_);
v___x_912_ = lean_unsigned_to_nat(0u);
return v___x_912_;
}
else
{
lean_object* v_val_913_; lean_object* v___x_914_; 
v_val_913_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_val_913_);
lean_dec_ref(v___x_911_);
v___x_914_ = lean_apply_1(v_inst_907_, v_val_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roi_size(lean_object* v_00_u03b1_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_r_918_){
_start:
{
lean_object* v_succ_x3f_919_; lean_object* v___x_920_; 
v_succ_x3f_919_ = lean_ctor_get(v_inst_917_, 0);
lean_inc_ref(v_succ_x3f_919_);
lean_dec_ref(v_inst_917_);
v___x_920_ = lean_apply_1(v_succ_x3f_919_, v_r_918_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v___x_921_; 
lean_dec_ref(v_inst_916_);
v___x_921_ = lean_unsigned_to_nat(0u);
return v___x_921_;
}
else
{
lean_object* v_val_922_; lean_object* v___x_923_; 
v_val_922_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_val_922_);
lean_dec_ref(v___x_920_);
v___x_923_ = lean_apply_1(v_inst_916_, v_val_922_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2(lean_object* v_toPure_924_, lean_object* v_succ_x3f_925_, lean_object* v_f_926_, lean_object* v_toBind_927_, lean_object* v___f_928_, lean_object* v_next_929_, lean_object* v_acc_930_, lean_object* v_h_931_, lean_object* v_G_932_){
_start:
{
lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_inc(v_next_929_);
v___f_933_ = lean_alloc_closure((void*)(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__1), 5, 4);
lean_closure_set(v___f_933_, 0, v_toPure_924_);
lean_closure_set(v___f_933_, 1, v_succ_x3f_925_);
lean_closure_set(v___f_933_, 2, v_next_929_);
lean_closure_set(v___f_933_, 3, v_G_932_);
v___x_934_ = lean_apply_3(v_f_926_, v_next_929_, lean_box(0), v_acc_930_);
lean_inc(v_toBind_927_);
v___x_935_ = lean_apply_4(v_toBind_927_, lean_box(0), lean_box(0), v___x_934_, v___f_928_);
v___x_936_ = lean_apply_4(v_toBind_927_, lean_box(0), lean_box(0), v___x_935_, v___f_933_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0(lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_00_u03b2_939_, lean_object* v_r_940_, lean_object* v_init_941_, lean_object* v_f_942_){
_start:
{
lean_object* v_toApplicative_943_; lean_object* v_succ_x3f_944_; lean_object* v_toBind_945_; lean_object* v_toPure_946_; lean_object* v_next_947_; 
v_toApplicative_943_ = lean_ctor_get(v_inst_938_, 0);
lean_inc_ref(v_toApplicative_943_);
v_succ_x3f_944_ = lean_ctor_get(v_inst_937_, 0);
lean_inc_ref_n(v_succ_x3f_944_, 2);
lean_dec_ref(v_inst_937_);
v_toBind_945_ = lean_ctor_get(v_inst_938_, 1);
lean_inc(v_toBind_945_);
lean_dec_ref(v_inst_938_);
v_toPure_946_ = lean_ctor_get(v_toApplicative_943_, 1);
lean_inc(v_toPure_946_);
lean_dec_ref(v_toApplicative_943_);
v_next_947_ = lean_apply_1(v_succ_x3f_944_, v_r_940_);
if (lean_obj_tag(v_next_947_) == 0)
{
lean_object* v___x_948_; 
lean_dec(v_toBind_945_);
lean_dec_ref(v_succ_x3f_944_);
lean_dec(v_f_942_);
v___x_948_ = lean_apply_2(v_toPure_946_, lean_box(0), v_init_941_);
return v___x_948_;
}
else
{
lean_object* v_val_949_; lean_object* v___f_950_; lean_object* v___f_951_; lean_object* v___x_952_; 
v_val_949_ = lean_ctor_get(v_next_947_, 0);
lean_inc(v_val_949_);
lean_dec_ref(v_next_947_);
lean_inc(v_toPure_946_);
v___f_950_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_950_, 0, v_toPure_946_);
v___f_951_ = lean_alloc_closure((void*)(l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2), 9, 5);
lean_closure_set(v___f_951_, 0, v_toPure_946_);
lean_closure_set(v___f_951_, 1, v_succ_x3f_944_);
lean_closure_set(v___f_951_, 2, v_f_942_);
lean_closure_set(v___f_951_, 3, v_toBind_945_);
lean_closure_set(v___f_951_, 4, v___f_950_);
v___x_952_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_951_, v_val_949_, v_init_941_, lean_box(0));
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(lean_object* v_inst_953_, lean_object* v_inst_954_){
_start:
{
lean_object* v___f_955_; 
v___f_955_ = lean_alloc_closure((void*)(l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0), 6, 2);
lean_closure_set(v___f_955_, 0, v_inst_953_);
lean_closure_set(v___f_955_, 1, v_inst_954_);
return v___f_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(lean_object* v_00_u03b1_956_, lean_object* v_m_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_inst_963_){
_start:
{
lean_object* v___f_964_; 
v___f_964_ = lean_alloc_closure((void*)(l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0), 6, 2);
lean_closure_set(v___f_964_, 0, v_inst_958_);
lean_closure_set(v___f_964_, 1, v_inst_962_);
return v___f_964_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_Internal_iter___redArg(lean_object* v_inst_965_, lean_object* v_r_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v_inst_965_);
lean_ctor_set(v___x_967_, 1, v_r_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_Internal_iter(lean_object* v_00_u03b1_968_, lean_object* v_inst_969_, lean_object* v_r_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_inst_969_);
lean_ctor_set(v___x_971_, 1, v_r_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_toList___redArg(lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_r_975_){
_start:
{
lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___f_976_ = lean_alloc_closure((void*)(l_Std_Rcc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_976_, 0, v_inst_973_);
lean_closure_set(v___f_976_, 1, v_inst_974_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v_inst_972_);
lean_ctor_set(v___x_977_, 1, v_r_975_);
v___x_978_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_979_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_976_, v___x_977_, v___x_978_);
v___x_980_ = lean_array_to_list(v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_toList(lean_object* v_00_u03b1_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_r_988_){
_start:
{
lean_object* v___f_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___f_989_ = lean_alloc_closure((void*)(l_Std_Rcc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_989_, 0, v_inst_984_);
lean_closure_set(v___f_989_, 1, v_inst_985_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v_inst_982_);
lean_ctor_set(v___x_990_, 1, v_r_988_);
v___x_991_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_992_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_989_, v___x_990_, v___x_991_);
v___x_993_ = lean_array_to_list(v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_toArray___redArg(lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_inst_996_, lean_object* v_r_997_){
_start:
{
lean_object* v___f_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___f_998_ = lean_alloc_closure((void*)(l_Std_Rcc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_998_, 0, v_inst_995_);
lean_closure_set(v___f_998_, 1, v_inst_996_);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v_inst_994_);
lean_ctor_set(v___x_999_, 1, v_r_997_);
v___x_1000_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_1001_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_998_, v___x_999_, v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_toArray(lean_object* v_00_u03b1_1002_, lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_inst_1008_, lean_object* v_r_1009_){
_start:
{
lean_object* v___f_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___f_1010_ = lean_alloc_closure((void*)(l_Std_Rcc_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1010_, 0, v_inst_1005_);
lean_closure_set(v___f_1010_, 1, v_inst_1006_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_inst_1003_);
lean_ctor_set(v___x_1011_, 1, v_r_1009_);
v___x_1012_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_1013_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_1010_, v___x_1011_, v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_size___redArg(lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_r_1016_){
_start:
{
if (lean_obj_tag(v_inst_1015_) == 0)
{
lean_object* v___x_1017_; 
lean_dec(v_r_1016_);
lean_dec_ref(v_inst_1014_);
v___x_1017_ = lean_unsigned_to_nat(0u);
return v___x_1017_;
}
else
{
lean_object* v_val_1018_; lean_object* v___x_1019_; 
v_val_1018_ = lean_ctor_get(v_inst_1015_, 0);
lean_inc(v_val_1018_);
lean_dec_ref(v_inst_1015_);
v___x_1019_ = lean_apply_2(v_inst_1014_, v_val_1018_, v_r_1016_);
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Ric_size(lean_object* v_00_u03b1_1020_, lean_object* v_inst_1021_, lean_object* v_inst_1022_, lean_object* v_r_1023_){
_start:
{
if (lean_obj_tag(v_inst_1022_) == 0)
{
lean_object* v___x_1024_; 
lean_dec(v_r_1023_);
lean_dec_ref(v_inst_1021_);
v___x_1024_ = lean_unsigned_to_nat(0u);
return v___x_1024_;
}
else
{
lean_object* v_val_1025_; lean_object* v___x_1026_; 
v_val_1025_ = lean_ctor_get(v_inst_1022_, 0);
lean_inc(v_val_1025_);
lean_dec_ref(v_inst_1022_);
v___x_1026_ = lean_apply_2(v_inst_1021_, v_val_1025_, v_r_1023_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__2(lean_object* v_inst_1027_, lean_object* v_r_1028_, lean_object* v_toPure_1029_, lean_object* v_inst_1030_, lean_object* v_f_1031_, lean_object* v_toBind_1032_, lean_object* v___f_1033_, lean_object* v_next_1034_, lean_object* v_acc_1035_, lean_object* v_h_1036_, lean_object* v_G_1037_){
_start:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
lean_inc(v_next_1034_);
v___x_1038_ = lean_apply_2(v_inst_1027_, v_next_1034_, v_r_1028_);
v___x_1039_ = lean_unbox(v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec(v_G_1037_);
lean_dec(v_next_1034_);
lean_dec(v___f_1033_);
lean_dec(v_toBind_1032_);
lean_dec(v_f_1031_);
lean_dec_ref(v_inst_1030_);
v___x_1040_ = lean_apply_2(v_toPure_1029_, lean_box(0), v_acc_1035_);
return v___x_1040_;
}
else
{
lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_inc(v_next_1034_);
v___f_1041_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1041_, 0, v_toPure_1029_);
lean_closure_set(v___f_1041_, 1, v_inst_1030_);
lean_closure_set(v___f_1041_, 2, v_next_1034_);
lean_closure_set(v___f_1041_, 3, v_G_1037_);
v___x_1042_ = lean_apply_3(v_f_1031_, v_next_1034_, lean_box(0), v_acc_1035_);
lean_inc(v_toBind_1032_);
v___x_1043_ = lean_apply_4(v_toBind_1032_, lean_box(0), lean_box(0), v___x_1042_, v___f_1033_);
v___x_1044_ = lean_apply_4(v_toBind_1032_, lean_box(0), lean_box(0), v___x_1043_, v___f_1041_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0(lean_object* v_inst_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_r_1050_, lean_object* v_init_1051_, lean_object* v_f_1052_){
_start:
{
lean_object* v_toApplicative_1053_; 
v_toApplicative_1053_ = lean_ctor_get(v_inst_1045_, 0);
lean_inc_ref(v_toApplicative_1053_);
if (lean_obj_tag(v_inst_1046_) == 0)
{
lean_object* v_toPure_1054_; lean_object* v___x_1055_; 
lean_dec(v_f_1052_);
lean_dec(v_r_1050_);
lean_dec_ref(v_inst_1048_);
lean_dec_ref(v_inst_1047_);
lean_dec_ref(v_inst_1045_);
v_toPure_1054_ = lean_ctor_get(v_toApplicative_1053_, 1);
lean_inc(v_toPure_1054_);
lean_dec_ref(v_toApplicative_1053_);
v___x_1055_ = lean_apply_2(v_toPure_1054_, lean_box(0), v_init_1051_);
return v___x_1055_;
}
else
{
lean_object* v_toBind_1056_; lean_object* v_toPure_1057_; lean_object* v_val_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; 
v_toBind_1056_ = lean_ctor_get(v_inst_1045_, 1);
lean_inc(v_toBind_1056_);
lean_dec_ref(v_inst_1045_);
v_toPure_1057_ = lean_ctor_get(v_toApplicative_1053_, 1);
lean_inc_n(v_toPure_1057_, 2);
lean_dec_ref(v_toApplicative_1053_);
v_val_1058_ = lean_ctor_get(v_inst_1046_, 0);
lean_inc(v_val_1058_);
lean_dec_ref(v_inst_1046_);
v___f_1059_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1059_, 0, v_toPure_1057_);
v___f_1060_ = lean_alloc_closure((void*)(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__2), 11, 7);
lean_closure_set(v___f_1060_, 0, v_inst_1047_);
lean_closure_set(v___f_1060_, 1, v_r_1050_);
lean_closure_set(v___f_1060_, 2, v_toPure_1057_);
lean_closure_set(v___f_1060_, 3, v_inst_1048_);
lean_closure_set(v___f_1060_, 4, v_f_1052_);
lean_closure_set(v___f_1060_, 5, v_toBind_1056_);
lean_closure_set(v___f_1060_, 6, v___f_1059_);
v___x_1061_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1060_, v_val_1058_, v_init_1051_, lean_box(0));
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_){
_start:
{
lean_object* v___f_1066_; 
v___f_1066_ = lean_alloc_closure((void*)(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0), 8, 4);
lean_closure_set(v___f_1066_, 0, v_inst_1065_);
lean_closure_set(v___f_1066_, 1, v_inst_1064_);
lean_closure_set(v___f_1066_, 2, v_inst_1063_);
lean_closure_set(v___f_1066_, 3, v_inst_1062_);
return v___f_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(lean_object* v_00_u03b1_1067_, lean_object* v_m_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_){
_start:
{
lean_object* v___f_1078_; 
v___f_1078_ = lean_alloc_closure((void*)(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0), 8, 4);
lean_closure_set(v___f_1078_, 0, v_inst_1076_);
lean_closure_set(v___f_1078_, 1, v_inst_1072_);
lean_closure_set(v___f_1078_, 2, v_inst_1071_);
lean_closure_set(v___f_1078_, 3, v_inst_1069_);
return v___f_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_Internal_iter___redArg(lean_object* v_inst_1079_, lean_object* v_r_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_inst_1079_);
lean_ctor_set(v___x_1081_, 1, v_r_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_Internal_iter(lean_object* v_00_u03b1_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_r_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_inst_1084_);
lean_ctor_set(v___x_1086_, 1, v_r_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_Internal_iter___boxed(lean_object* v_00_u03b1_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_r_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_Rio_Internal_iter(v_00_u03b1_1087_, v_inst_1088_, v_inst_1089_, v_r_1090_);
lean_dec_ref(v_inst_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_toList___redArg(lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_r_1095_){
_start:
{
lean_object* v___f_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___f_1096_ = lean_alloc_closure((void*)(l_Std_Rco_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1096_, 0, v_inst_1093_);
lean_closure_set(v___f_1096_, 1, v_inst_1094_);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v_inst_1092_);
lean_ctor_set(v___x_1097_, 1, v_r_1095_);
v___x_1098_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_1099_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_1096_, v___x_1097_, v___x_1098_);
v___x_1100_ = lean_array_to_list(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_toList(lean_object* v_00_u03b1_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_r_1108_){
_start:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___f_1109_ = lean_alloc_closure((void*)(l_Std_Rco_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1109_, 0, v_inst_1104_);
lean_closure_set(v___f_1109_, 1, v_inst_1105_);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v_inst_1102_);
lean_ctor_set(v___x_1110_, 1, v_r_1108_);
v___x_1111_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_1112_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_1109_, v___x_1110_, v___x_1111_);
v___x_1113_ = lean_array_to_list(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_toArray___redArg(lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_r_1117_){
_start:
{
lean_object* v___f_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___f_1118_ = lean_alloc_closure((void*)(l_Std_Rco_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1118_, 0, v_inst_1115_);
lean_closure_set(v___f_1118_, 1, v_inst_1116_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v_inst_1114_);
lean_ctor_set(v___x_1119_, 1, v_r_1117_);
v___x_1120_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_1121_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_1118_, v___x_1119_, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_toArray(lean_object* v_00_u03b1_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_r_1129_){
_start:
{
lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___f_1130_ = lean_alloc_closure((void*)(l_Std_Rco_toList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1130_, 0, v_inst_1125_);
lean_closure_set(v___f_1130_, 1, v_inst_1126_);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_inst_1123_);
lean_ctor_set(v___x_1131_, 1, v_r_1129_);
v___x_1132_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_1133_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_1130_, v___x_1131_, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_size___redArg(lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_r_1136_){
_start:
{
if (lean_obj_tag(v_inst_1135_) == 0)
{
lean_object* v___x_1137_; 
lean_dec(v_r_1136_);
lean_dec_ref(v_inst_1134_);
v___x_1137_ = lean_unsigned_to_nat(0u);
return v___x_1137_;
}
else
{
lean_object* v_val_1138_; lean_object* v___x_1139_; 
v_val_1138_ = lean_ctor_get(v_inst_1135_, 0);
lean_inc(v_val_1138_);
lean_dec_ref(v_inst_1135_);
v___x_1139_ = lean_apply_2(v_inst_1134_, v_val_1138_, v_r_1136_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rio_size(lean_object* v_00_u03b1_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_r_1143_){
_start:
{
if (lean_obj_tag(v_inst_1142_) == 0)
{
lean_object* v___x_1144_; 
lean_dec(v_r_1143_);
lean_dec_ref(v_inst_1141_);
v___x_1144_ = lean_unsigned_to_nat(0u);
return v___x_1144_;
}
else
{
lean_object* v_val_1145_; lean_object* v___x_1146_; 
v_val_1145_ = lean_ctor_get(v_inst_1142_, 0);
lean_inc(v_val_1145_);
lean_dec_ref(v_inst_1142_);
v___x_1146_ = lean_apply_2(v_inst_1141_, v_val_1145_, v_r_1143_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_){
_start:
{
lean_object* v___f_1151_; 
v___f_1151_ = lean_alloc_closure((void*)(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0), 8, 4);
lean_closure_set(v___f_1151_, 0, v_inst_1150_);
lean_closure_set(v___f_1151_, 1, v_inst_1149_);
lean_closure_set(v___f_1151_, 2, v_inst_1148_);
lean_closure_set(v___f_1151_, 3, v_inst_1147_);
return v___f_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(lean_object* v_00_u03b1_1152_, lean_object* v_m_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_){
_start:
{
lean_object* v___f_1163_; 
v___f_1163_ = lean_alloc_closure((void*)(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0), 8, 4);
lean_closure_set(v___f_1163_, 0, v_inst_1161_);
lean_closure_set(v___f_1163_, 1, v_inst_1157_);
lean_closure_set(v___f_1163_, 2, v_inst_1156_);
lean_closure_set(v___f_1163_, 3, v_inst_1154_);
return v___f_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_Internal_iter___redArg(lean_object* v_inst_1164_){
_start:
{
lean_inc(v_inst_1164_);
return v_inst_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_Internal_iter___redArg___boxed(lean_object* v_inst_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Std_Rii_Internal_iter___redArg(v_inst_1165_);
lean_dec(v_inst_1165_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_Internal_iter(lean_object* v_00_u03b1_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_x_1170_){
_start:
{
lean_inc(v_inst_1169_);
return v_inst_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_Internal_iter___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_Rii_Internal_iter(v_00_u03b1_1171_, v_inst_1172_, v_inst_1173_, v_x_1174_);
lean_dec(v_inst_1173_);
lean_dec_ref(v_inst_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_toList___redArg___lam__0(lean_object* v_inst_1176_, lean_object* v_it_1177_, lean_object* v_acc_1178_, lean_object* v_recur_1179_){
_start:
{
lean_object* v_val_1180_; 
v_val_1180_ = lean_apply_1(v_inst_1176_, v_it_1177_);
switch(lean_obj_tag(v_val_1180_))
{
case 0:
{
lean_object* v_it_1181_; lean_object* v_out_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_it_1181_ = lean_ctor_get(v_val_1180_, 0);
lean_inc(v_it_1181_);
v_out_1182_ = lean_ctor_get(v_val_1180_, 1);
lean_inc(v_out_1182_);
lean_dec_ref(v_val_1180_);
v___x_1183_ = lean_array_push(v_acc_1178_, v_out_1182_);
v___x_1184_ = lean_apply_3(v_recur_1179_, v_it_1181_, v___x_1183_, lean_box(0));
return v___x_1184_;
}
case 1:
{
lean_object* v_it_1185_; lean_object* v___x_1186_; 
v_it_1185_ = lean_ctor_get(v_val_1180_, 0);
lean_inc(v_it_1185_);
lean_dec_ref(v_val_1180_);
v___x_1186_ = lean_apply_3(v_recur_1179_, v_it_1185_, v_acc_1178_, lean_box(0));
return v___x_1186_;
}
default: 
{
lean_dec_ref(v_recur_1179_);
return v_acc_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rii_toList___redArg(lean_object* v_inst_1187_, lean_object* v_inst_1188_){
_start:
{
lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___f_1189_ = lean_alloc_closure((void*)(l_Std_Rii_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1189_, 0, v_inst_1188_);
v___x_1190_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_1191_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_1189_, v_inst_1187_, v___x_1190_);
v___x_1192_ = lean_array_to_list(v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_toList(lean_object* v_00_u03b1_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_r_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_){
_start:
{
lean_object* v___f_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___f_1199_ = lean_alloc_closure((void*)(l_Std_Rii_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1199_, 0, v_inst_1197_);
v___x_1200_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_1201_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_1199_, v_inst_1195_, v___x_1200_);
v___x_1202_ = lean_array_to_list(v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_toList___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_r_1206_, lean_object* v_inst_1207_, lean_object* v_inst_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Std_Rii_toList(v_00_u03b1_1203_, v_inst_1204_, v_inst_1205_, v_r_1206_, v_inst_1207_, v_inst_1208_);
lean_dec_ref(v_inst_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_toArray___redArg(lean_object* v_inst_1210_, lean_object* v_inst_1211_){
_start:
{
lean_object* v___f_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___f_1212_ = lean_alloc_closure((void*)(l_Std_Rii_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1212_, 0, v_inst_1211_);
v___x_1213_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_1214_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_1212_, v_inst_1210_, v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_toArray(lean_object* v_00_u03b1_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_r_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_){
_start:
{
lean_object* v___f_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___f_1221_ = lean_alloc_closure((void*)(l_Std_Rii_toList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1221_, 0, v_inst_1219_);
v___x_1222_ = ((lean_object*)(l_Std_Rcc_toList___redArg___closed__0));
v___x_1223_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_1221_, v_inst_1217_, v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_toArray___boxed(lean_object* v_00_u03b1_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_r_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Std_Rii_toArray(v_00_u03b1_1224_, v_inst_1225_, v_inst_1226_, v_r_1227_, v_inst_1228_, v_inst_1229_);
lean_dec_ref(v_inst_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_size___redArg(lean_object* v_inst_1231_, lean_object* v_inst_1232_){
_start:
{
if (lean_obj_tag(v_inst_1231_) == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref(v_inst_1232_);
v___x_1233_ = lean_unsigned_to_nat(0u);
return v___x_1233_;
}
else
{
lean_object* v_val_1234_; lean_object* v___x_1235_; 
v_val_1234_ = lean_ctor_get(v_inst_1231_, 0);
lean_inc(v_val_1234_);
lean_dec_ref(v_inst_1231_);
v___x_1235_ = lean_apply_1(v_inst_1232_, v_val_1234_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rii_size(lean_object* v_00_u03b1_1236_, lean_object* v_x_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_){
_start:
{
if (lean_obj_tag(v_inst_1238_) == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref(v_inst_1239_);
v___x_1240_ = lean_unsigned_to_nat(0u);
return v___x_1240_;
}
else
{
lean_object* v_val_1241_; lean_object* v___x_1242_; 
v_val_1241_ = lean_ctor_get(v_inst_1238_, 0);
lean_inc(v_val_1241_);
lean_dec_ref(v_inst_1238_);
v___x_1242_ = lean_apply_1(v_inst_1239_, v_val_1241_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__3(lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_00_u03b2_1246_, lean_object* v_r_1247_, lean_object* v_init_1248_, lean_object* v_f_1249_){
_start:
{
lean_object* v_toApplicative_1250_; 
v_toApplicative_1250_ = lean_ctor_get(v_inst_1243_, 0);
lean_inc_ref(v_toApplicative_1250_);
if (lean_obj_tag(v_inst_1244_) == 0)
{
lean_object* v_toPure_1251_; lean_object* v___x_1252_; 
lean_dec(v_f_1249_);
lean_dec_ref(v_inst_1245_);
lean_dec_ref(v_inst_1243_);
v_toPure_1251_ = lean_ctor_get(v_toApplicative_1250_, 1);
lean_inc(v_toPure_1251_);
lean_dec_ref(v_toApplicative_1250_);
v___x_1252_ = lean_apply_2(v_toPure_1251_, lean_box(0), v_init_1248_);
return v___x_1252_;
}
else
{
lean_object* v_toBind_1253_; lean_object* v_toPure_1254_; lean_object* v_val_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; 
v_toBind_1253_ = lean_ctor_get(v_inst_1243_, 1);
lean_inc(v_toBind_1253_);
lean_dec_ref(v_inst_1243_);
v_toPure_1254_ = lean_ctor_get(v_toApplicative_1250_, 1);
lean_inc_n(v_toPure_1254_, 2);
lean_dec_ref(v_toApplicative_1250_);
v_val_1255_ = lean_ctor_get(v_inst_1244_, 0);
lean_inc(v_val_1255_);
lean_dec_ref(v_inst_1244_);
v___f_1256_ = lean_alloc_closure((void*)(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1256_, 0, v_toPure_1254_);
v___f_1257_ = lean_alloc_closure((void*)(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2), 9, 5);
lean_closure_set(v___f_1257_, 0, v_toPure_1254_);
lean_closure_set(v___f_1257_, 1, v_inst_1245_);
lean_closure_set(v___f_1257_, 2, v_f_1249_);
lean_closure_set(v___f_1257_, 3, v_toBind_1253_);
lean_closure_set(v___f_1257_, 4, v___f_1256_);
v___x_1258_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1257_, v_val_1255_, v_init_1248_, lean_box(0));
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_){
_start:
{
lean_object* v___f_1262_; 
v___f_1262_ = lean_alloc_closure((void*)(l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__3), 7, 3);
lean_closure_set(v___f_1262_, 0, v_inst_1261_);
lean_closure_set(v___f_1262_, 1, v_inst_1260_);
lean_closure_set(v___f_1262_, 2, v_inst_1259_);
return v___f_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(lean_object* v_00_u03b1_1263_, lean_object* v_m_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_){
_start:
{
lean_object* v___f_1271_; 
v___f_1271_ = lean_alloc_closure((void*)(l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__3), 7, 3);
lean_closure_set(v___f_1271_, 0, v_inst_1269_);
lean_closure_set(v___f_1271_, 1, v_inst_1266_);
lean_closure_set(v___f_1271_, 2, v_inst_1265_);
return v___f_1271_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
}
#ifdef __cplusplus
}
#endif
