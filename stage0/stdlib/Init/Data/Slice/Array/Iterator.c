// Lean compiler output
// Module: Init.Data.Slice.Array.Iterator
// Imports: public import Init.Data.Slice.Operations import all Init.Data.Range.Polymorphic.Basic import Init.Omega public import Init.Data.Array.Subarray public import Init.Data.ToString.Extra
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SubarrayIterator_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l_SubarrayIterator_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___lam__0(lean_object*);
static const lean_closure_object l_instIteratorSubarrayIteratorId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instIteratorSubarrayIteratorId___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instIteratorSubarrayIteratorId___closed__0 = (const lean_object*)&l_instIteratorSubarrayIteratorId___closed__0_value;
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instToIterator___lam__0___boxed(lean_object*);
static const lean_closure_object l_Subarray_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Subarray_instToIterator___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_instToIterator___closed__0 = (const lean_object*)&l_Subarray_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Subarray_instToIterator(lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l_Subarray_copy___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Subarray_copy___redArg___closed__0 = (const lean_object*)&l_Subarray_copy___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Subarray_copy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_copy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instCoeSubarrayArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Subarray_copy, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instCoeSubarrayArray___closed__0 = (const lean_object*)&l_instCoeSubarrayArray___closed__0_value;
LEAN_EXPORT lean_object* l_instCoeSubarrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_ofSubarray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instAppendSubarray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instAppendSubarray___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instAppendSubarray___closed__0 = (const lean_object*)&l_Array_instAppendSubarray___closed__0_value;
static const lean_closure_object l_Array_instAppendSubarray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instAppendSubarray___lam__2, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Array_instAppendSubarray___closed__0_value),((lean_object*)&l_Array_instAppendSubarray___closed__0_value)} };
static const lean_object* l_Array_instAppendSubarray___closed__1 = (const lean_object*)&l_Array_instAppendSubarray___closed__1_value;
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object*);
static const lean_string_object l_Array_Subarray_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ".toSubarray"};
static const lean_object* l_Array_Subarray_repr___redArg___closed__0 = (const lean_object*)&l_Array_Subarray_repr___redArg___closed__0_value;
static const lean_ctor_object l_Array_Subarray_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_Subarray_repr___redArg___closed__0_value)}};
static const lean_object* l_Array_Subarray_repr___redArg___closed__1 = (const lean_object*)&l_Array_Subarray_repr___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_Subarray_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_Subarray_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray(lean_object*, lean_object*);
static const lean_string_object l_Array_instToStringSubarray___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Array_instToStringSubarray___redArg___lam__1___closed__0 = (const lean_object*)&l_Array_instToStringSubarray___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instToStringSubarray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SubarrayIterator_step___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v_array_2_; lean_object* v_start_3_; lean_object* v_stop_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_17_; 
v_array_2_ = lean_ctor_get(v_x_1_, 0);
v_start_3_ = lean_ctor_get(v_x_1_, 1);
v_stop_4_ = lean_ctor_get(v_x_1_, 2);
v_isSharedCheck_17_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_17_ == 0)
{
v___x_6_ = v_x_1_;
v_isShared_7_ = v_isSharedCheck_17_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_stop_4_);
lean_inc(v_start_3_);
lean_inc(v_array_2_);
lean_dec(v_x_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_17_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_lt(v_start_3_, v_stop_4_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_del_object(v___x_6_);
lean_dec(v_stop_4_);
lean_dec(v_start_3_);
lean_dec_ref(v_array_2_);
v___x_9_ = lean_box(2);
return v___x_9_;
}
else
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_13_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_start_3_, v___x_10_);
lean_inc_ref(v_array_2_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___x_11_);
v___x_13_ = v___x_6_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_array_2_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___x_11_);
lean_ctor_set(v_reuseFailAlloc_16_, 2, v_stop_4_);
v___x_13_ = v_reuseFailAlloc_16_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_array_fget(v_array_2_, v_start_3_);
lean_dec(v_start_3_);
lean_dec_ref(v_array_2_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_13_);
lean_ctor_set(v___x_15_, 1, v___x_14_);
return v___x_15_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_SubarrayIterator_step(lean_object* v_00_u03b1_18_, lean_object* v_m_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_array_21_; lean_object* v_start_22_; lean_object* v_stop_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_36_; 
v_array_21_ = lean_ctor_get(v_x_20_, 0);
v_start_22_ = lean_ctor_get(v_x_20_, 1);
v_stop_23_ = lean_ctor_get(v_x_20_, 2);
v_isSharedCheck_36_ = !lean_is_exclusive(v_x_20_);
if (v_isSharedCheck_36_ == 0)
{
v___x_25_ = v_x_20_;
v_isShared_26_ = v_isSharedCheck_36_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_stop_23_);
lean_inc(v_start_22_);
lean_inc(v_array_21_);
lean_dec(v_x_20_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_36_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
uint8_t v___x_27_; 
v___x_27_ = lean_nat_dec_lt(v_start_22_, v_stop_23_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
lean_del_object(v___x_25_);
lean_dec(v_stop_23_);
lean_dec(v_start_22_);
lean_dec_ref(v_array_21_);
v___x_28_ = lean_box(2);
return v___x_28_;
}
else
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_add(v_start_22_, v___x_29_);
lean_inc_ref(v_array_21_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v___x_30_);
v___x_32_ = v___x_25_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_array_21_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_35_, 2, v_stop_23_);
v___x_32_ = v_reuseFailAlloc_35_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_array_fget(v_array_21_, v_start_22_);
lean_dec(v_start_22_);
lean_dec_ref(v_array_21_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_32_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
return v___x_34_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___lam__0(lean_object* v_it_37_){
_start:
{
lean_object* v_array_38_; lean_object* v_start_39_; lean_object* v_stop_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_53_; 
v_array_38_ = lean_ctor_get(v_it_37_, 0);
v_start_39_ = lean_ctor_get(v_it_37_, 1);
v_stop_40_ = lean_ctor_get(v_it_37_, 2);
v_isSharedCheck_53_ = !lean_is_exclusive(v_it_37_);
if (v_isSharedCheck_53_ == 0)
{
v___x_42_ = v_it_37_;
v_isShared_43_ = v_isSharedCheck_53_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_stop_40_);
lean_inc(v_start_39_);
lean_inc(v_array_38_);
lean_dec(v_it_37_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_53_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
uint8_t v___x_44_; 
v___x_44_ = lean_nat_dec_lt(v_start_39_, v_stop_40_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; 
lean_del_object(v___x_42_);
lean_dec(v_stop_40_);
lean_dec(v_start_39_);
lean_dec_ref(v_array_38_);
v___x_45_ = lean_box(2);
return v___x_45_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_add(v_start_39_, v___x_46_);
lean_inc_ref(v_array_38_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_47_);
v___x_49_ = v___x_42_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_array_38_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_52_, 2, v_stop_40_);
v___x_49_ = v_reuseFailAlloc_52_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_array_fget(v_array_38_, v_start_39_);
lean_dec(v_start_39_);
lean_dec_ref(v_array_38_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
return v___x_51_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId(lean_object* v_00_u03b1_55_){
_start:
{
lean_object* v___f_56_; 
v___f_56_ = ((lean_object*)(l_instIteratorSubarrayIteratorId___closed__0));
return v___f_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter___redArg(lean_object* v_x_57_, lean_object* v_h__1_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_apply_1(v_h__1_58_, v_x_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter(lean_object* v_00_u03b1_60_, lean_object* v_motive_61_, lean_object* v_x_62_, lean_object* v_h__1_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_apply_1(v_h__1_63_, v_x_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation(lean_object* v_00_u03b1_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object* v_toPure_67_, lean_object* v_recur_68_, lean_object* v_it_69_, lean_object* v_____do__lift_70_){
_start:
{
if (lean_obj_tag(v_____do__lift_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_72_; 
lean_dec_ref(v_it_69_);
lean_dec(v_recur_68_);
v_a_71_ = lean_ctor_get(v_____do__lift_70_, 0);
lean_inc(v_a_71_);
lean_dec_ref(v_____do__lift_70_);
v___x_72_ = lean_apply_2(v_toPure_67_, lean_box(0), v_a_71_);
return v___x_72_;
}
else
{
lean_object* v_a_73_; lean_object* v___x_74_; 
lean_dec(v_toPure_67_);
v_a_73_ = lean_ctor_get(v_____do__lift_70_, 0);
lean_inc(v_a_73_);
lean_dec_ref(v_____do__lift_70_);
v___x_74_ = lean_apply_4(v_recur_68_, v_it_69_, v_a_73_, lean_box(0), lean_box(0));
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1(lean_object* v_toPure_75_, lean_object* v_recur_76_, lean_object* v___y_77_, lean_object* v_acc_78_, lean_object* v_toBind_79_, lean_object* v_s_80_){
_start:
{
switch(lean_obj_tag(v_s_80_))
{
case 0:
{
lean_object* v_it_81_; lean_object* v_out_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_it_81_ = lean_ctor_get(v_s_80_, 0);
lean_inc(v_it_81_);
v_out_82_ = lean_ctor_get(v_s_80_, 1);
lean_inc(v_out_82_);
lean_dec_ref(v_s_80_);
v___f_83_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_83_, 0, v_toPure_75_);
lean_closure_set(v___f_83_, 1, v_recur_76_);
lean_closure_set(v___f_83_, 2, v_it_81_);
v___x_84_ = lean_apply_3(v___y_77_, v_out_82_, lean_box(0), v_acc_78_);
v___x_85_ = lean_apply_4(v_toBind_79_, lean_box(0), lean_box(0), v___x_84_, v___f_83_);
return v___x_85_;
}
case 1:
{
lean_object* v_it_86_; lean_object* v___x_87_; 
lean_dec(v_toBind_79_);
lean_dec(v___y_77_);
lean_dec(v_toPure_75_);
v_it_86_ = lean_ctor_get(v_s_80_, 0);
lean_inc(v_it_86_);
lean_dec_ref(v_s_80_);
v___x_87_ = lean_apply_4(v_recur_76_, v_it_86_, v_acc_78_, lean_box(0), lean_box(0));
return v___x_87_;
}
default: 
{
lean_object* v___x_88_; 
lean_dec(v_toBind_79_);
lean_dec(v___y_77_);
lean_dec(v_recur_76_);
v___x_88_ = lean_apply_2(v_toPure_75_, lean_box(0), v_acc_78_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2(lean_object* v_toPure_89_, lean_object* v___y_90_, lean_object* v_toBind_91_, lean_object* v_lift_92_, lean_object* v_it_93_, lean_object* v_acc_94_, lean_object* v_hP_95_, lean_object* v_recur_96_){
_start:
{
lean_object* v_array_97_; lean_object* v_start_98_; lean_object* v_stop_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_115_; 
v_array_97_ = lean_ctor_get(v_it_93_, 0);
v_start_98_ = lean_ctor_get(v_it_93_, 1);
v_stop_99_ = lean_ctor_get(v_it_93_, 2);
v_isSharedCheck_115_ = !lean_is_exclusive(v_it_93_);
if (v_isSharedCheck_115_ == 0)
{
v___x_101_ = v_it_93_;
v_isShared_102_ = v_isSharedCheck_115_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_stop_99_);
lean_inc(v_start_98_);
lean_inc(v_array_97_);
lean_dec(v_it_93_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_115_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___f_103_; uint8_t v___x_104_; 
v___f_103_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_103_, 0, v_toPure_89_);
lean_closure_set(v___f_103_, 1, v_recur_96_);
lean_closure_set(v___f_103_, 2, v___y_90_);
lean_closure_set(v___f_103_, 3, v_acc_94_);
lean_closure_set(v___f_103_, 4, v_toBind_91_);
v___x_104_ = lean_nat_dec_lt(v_start_98_, v_stop_99_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_del_object(v___x_101_);
lean_dec(v_stop_99_);
lean_dec(v_start_98_);
lean_dec_ref(v_array_97_);
v___x_105_ = lean_box(2);
v___x_106_ = lean_apply_4(v_lift_92_, lean_box(0), lean_box(0), v___f_103_, v___x_105_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = lean_nat_add(v_start_98_, v___x_107_);
lean_inc_ref(v_array_97_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_108_);
v___x_110_ = v___x_101_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_array_97_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_stop_99_);
v___x_110_ = v_reuseFailAlloc_114_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_array_fget(v_array_97_, v_start_98_);
lean_dec(v_start_98_);
lean_dec_ref(v_array_97_);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = lean_apply_4(v_lift_92_, lean_box(0), lean_box(0), v___f_103_, v___x_112_);
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3(lean_object* v_inst_116_, lean_object* v_lift_117_, lean_object* v_00_u03b3_118_, lean_object* v_Pl_119_, lean_object* v_it_120_, lean_object* v_init_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_toApplicative_123_; lean_object* v_toBind_124_; lean_object* v_toPure_125_; lean_object* v___f_126_; lean_object* v___x_127_; 
v_toApplicative_123_ = lean_ctor_get(v_inst_116_, 0);
lean_inc_ref(v_toApplicative_123_);
v_toBind_124_ = lean_ctor_get(v_inst_116_, 1);
lean_inc(v_toBind_124_);
lean_dec_ref(v_inst_116_);
v_toPure_125_ = lean_ctor_get(v_toApplicative_123_, 1);
lean_inc(v_toPure_125_);
lean_dec_ref(v_toApplicative_123_);
v___f_126_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2), 8, 4);
lean_closure_set(v___f_126_, 0, v_toPure_125_);
lean_closure_set(v___f_126_, 1, v___y_122_);
lean_closure_set(v___f_126_, 2, v_toBind_124_);
lean_closure_set(v___f_126_, 3, v_lift_117_);
v___x_127_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_126_, v_it_120_, v_init_121_, lean_box(0));
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(lean_object* v_inst_128_){
_start:
{
lean_object* v___f_129_; 
v___f_129_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_129_, 0, v_inst_128_);
return v___f_129_;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad(lean_object* v_00_u03b1_130_, lean_object* v_m_131_, lean_object* v_inst_132_){
_start:
{
lean_object* v___f_133_; 
v___f_133_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_133_, 0, v_inst_132_);
return v___f_133_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___lam__0(lean_object* v_x_134_){
_start:
{
lean_inc_ref(v_x_134_);
return v_x_134_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___lam__0___boxed(lean_object* v_x_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Subarray_instToIterator___lam__0(v_x_135_);
lean_dec_ref(v_x_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator(lean_object* v_00_u03b1_138_){
_start:
{
lean_object* v___f_139_; 
v___f_139_ = ((lean_object*)(l_Subarray_instToIterator___closed__0));
return v___f_139_;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad___redArg(lean_object* v_inst_140_){
_start:
{
lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; 
v___f_141_ = ((lean_object*)(l_Subarray_instToIterator___closed__0));
lean_inc_ref(v_inst_140_);
v___f_142_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_142_, 0, v_inst_140_);
v___x_143_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(v_inst_140_, v___f_141_, v___f_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad(lean_object* v_00_u03b1_144_, lean_object* v_m_145_, lean_object* v_inst_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_instForInSubarrayOfMonad___redArg(v_inst_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__0(lean_object* v_toPure_148_, lean_object* v_____do__lift_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_apply_2(v_toPure_148_, lean_box(0), v_____do__lift_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__1(lean_object* v_toPure_151_, lean_object* v_recur_152_, lean_object* v___x_153_, lean_object* v_____do__lift_154_){
_start:
{
if (lean_obj_tag(v_____do__lift_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; 
lean_dec_ref(v___x_153_);
lean_dec(v_recur_152_);
v_a_155_ = lean_ctor_get(v_____do__lift_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v_____do__lift_154_);
v___x_156_ = lean_apply_2(v_toPure_151_, lean_box(0), v_a_155_);
return v___x_156_;
}
else
{
lean_object* v_a_157_; lean_object* v___x_158_; 
lean_dec(v_toPure_151_);
v_a_157_ = lean_ctor_get(v_____do__lift_154_, 0);
lean_inc(v_a_157_);
lean_dec_ref(v_____do__lift_154_);
v___x_158_ = lean_apply_4(v_recur_152_, v___x_153_, v_a_157_, lean_box(0), lean_box(0));
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__2(lean_object* v_toPure_159_, lean_object* v_f_160_, lean_object* v_toBind_161_, lean_object* v___f_162_, lean_object* v_it_163_, lean_object* v_acc_164_, lean_object* v_hP_165_, lean_object* v_recur_166_){
_start:
{
lean_object* v_array_167_; lean_object* v_start_168_; lean_object* v_stop_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_185_; 
v_array_167_ = lean_ctor_get(v_it_163_, 0);
v_start_168_ = lean_ctor_get(v_it_163_, 1);
v_stop_169_ = lean_ctor_get(v_it_163_, 2);
v_isSharedCheck_185_ = !lean_is_exclusive(v_it_163_);
if (v_isSharedCheck_185_ == 0)
{
v___x_171_ = v_it_163_;
v_isShared_172_ = v_isSharedCheck_185_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_stop_169_);
lean_inc(v_start_168_);
lean_inc(v_array_167_);
lean_dec(v_it_163_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_185_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
uint8_t v___x_173_; 
v___x_173_ = lean_nat_dec_lt(v_start_168_, v_stop_169_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
lean_del_object(v___x_171_);
lean_dec(v_stop_169_);
lean_dec(v_start_168_);
lean_dec_ref(v_array_167_);
lean_dec(v_recur_166_);
lean_dec(v___f_162_);
lean_dec(v_toBind_161_);
lean_dec(v_f_160_);
v___x_174_ = lean_apply_2(v_toPure_159_, lean_box(0), v_acc_164_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_add(v_start_168_, v___x_175_);
lean_inc_ref(v_array_167_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_176_);
v___x_178_ = v___x_171_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_array_167_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_stop_169_);
v___x_178_ = v_reuseFailAlloc_184_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___f_179_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_179_, 0, v_toPure_159_);
lean_closure_set(v___f_179_, 1, v_recur_166_);
lean_closure_set(v___f_179_, 2, v___x_178_);
v___x_180_ = lean_array_fget(v_array_167_, v_start_168_);
lean_dec(v_start_168_);
lean_dec_ref(v_array_167_);
v___x_181_ = lean_apply_2(v_f_160_, v___x_180_, v_acc_164_);
lean_inc(v_toBind_161_);
v___x_182_ = lean_apply_4(v_toBind_161_, lean_box(0), lean_box(0), v___x_181_, v___f_162_);
v___x_183_ = lean_apply_4(v_toBind_161_, lean_box(0), lean_box(0), v___x_182_, v___f_179_);
return v___x_183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object* v_inst_186_, lean_object* v_s_187_, lean_object* v_b_188_, lean_object* v_f_189_){
_start:
{
lean_object* v_toApplicative_190_; lean_object* v_toBind_191_; lean_object* v_toPure_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___x_195_; 
v_toApplicative_190_ = lean_ctor_get(v_inst_186_, 0);
lean_inc_ref(v_toApplicative_190_);
v_toBind_191_ = lean_ctor_get(v_inst_186_, 1);
lean_inc(v_toBind_191_);
lean_dec_ref(v_inst_186_);
v_toPure_192_ = lean_ctor_get(v_toApplicative_190_, 1);
lean_inc_n(v_toPure_192_, 2);
lean_dec_ref(v_toApplicative_190_);
v___f_193_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_193_, 0, v_toPure_192_);
v___f_194_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__2), 8, 4);
lean_closure_set(v___f_194_, 0, v_toPure_192_);
lean_closure_set(v___f_194_, 1, v_f_189_);
lean_closure_set(v___f_194_, 2, v_toBind_191_);
lean_closure_set(v___f_194_, 3, v___f_193_);
v___x_195_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_194_, v_s_187_, v_b_188_, lean_box(0));
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_m_198_, lean_object* v_inst_199_, lean_object* v_s_200_, lean_object* v_b_201_, lean_object* v_f_202_){
_start:
{
lean_object* v_toApplicative_203_; lean_object* v_toBind_204_; lean_object* v_toPure_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___x_208_; 
v_toApplicative_203_ = lean_ctor_get(v_inst_199_, 0);
lean_inc_ref(v_toApplicative_203_);
v_toBind_204_ = lean_ctor_get(v_inst_199_, 1);
lean_inc(v_toBind_204_);
lean_dec_ref(v_inst_199_);
v_toPure_205_ = lean_ctor_get(v_toApplicative_203_, 1);
lean_inc_n(v_toPure_205_, 2);
lean_dec_ref(v_toApplicative_203_);
v___f_206_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_206_, 0, v_toPure_205_);
v___f_207_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__2), 8, 4);
lean_closure_set(v___f_207_, 0, v_toPure_205_);
lean_closure_set(v___f_207_, 1, v_f_202_);
lean_closure_set(v___f_207_, 2, v_toBind_204_);
lean_closure_set(v___f_207_, 3, v___f_206_);
v___x_208_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_207_, v_s_200_, v_b_201_, lean_box(0));
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(lean_object* v_a_209_, lean_object* v_b_210_){
_start:
{
lean_object* v_array_211_; lean_object* v_start_212_; lean_object* v_stop_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_226_; 
v_array_211_ = lean_ctor_get(v_a_209_, 0);
v_start_212_ = lean_ctor_get(v_a_209_, 1);
v_stop_213_ = lean_ctor_get(v_a_209_, 2);
v_isSharedCheck_226_ = !lean_is_exclusive(v_a_209_);
if (v_isSharedCheck_226_ == 0)
{
v___x_215_ = v_a_209_;
v_isShared_216_ = v_isSharedCheck_226_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_stop_213_);
lean_inc(v_start_212_);
lean_inc(v_array_211_);
lean_dec(v_a_209_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_226_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_lt(v_start_212_, v_stop_213_);
if (v___x_217_ == 0)
{
lean_del_object(v___x_215_);
lean_dec(v_stop_213_);
lean_dec(v_start_212_);
lean_dec_ref(v_array_211_);
return v_b_210_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_add(v_start_212_, v___x_218_);
lean_inc_ref(v_array_211_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_219_);
v___x_221_ = v___x_215_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_array_211_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_stop_213_);
v___x_221_ = v_reuseFailAlloc_225_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_array_fget(v_array_211_, v_start_212_);
lean_dec(v_start_212_);
lean_dec_ref(v_array_211_);
v___x_223_ = lean_array_push(v_b_210_, v___x_222_);
v_a_209_ = v___x_221_;
v_b_210_ = v___x_223_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_copy___redArg(lean_object* v_s_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_231_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Subarray_copy(lean_object* v_00_u03b1_232_, lean_object* v_s_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Subarray_copy___redArg(v_s_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0(lean_object* v_00_u03b1_235_, lean_object* v_inst_236_, lean_object* v_R_237_, lean_object* v_a_238_, lean_object* v_b_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_a_238_, v_b_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_instCoeSubarrayArray(lean_object* v_00_u03b1_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = ((lean_object*)(l_instCoeSubarrayArray___closed__0));
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object* v_s_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_246_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_244_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray(lean_object* v_00_u03b1_247_, lean_object* v_s_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Array_ofSubarray___redArg(v_s_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__0(lean_object* v_it_250_, lean_object* v_acc_251_, lean_object* v_recur_252_){
_start:
{
lean_object* v_array_253_; lean_object* v_start_254_; lean_object* v_stop_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_268_; 
v_array_253_ = lean_ctor_get(v_it_250_, 0);
v_start_254_ = lean_ctor_get(v_it_250_, 1);
v_stop_255_ = lean_ctor_get(v_it_250_, 2);
v_isSharedCheck_268_ = !lean_is_exclusive(v_it_250_);
if (v_isSharedCheck_268_ == 0)
{
v___x_257_ = v_it_250_;
v_isShared_258_ = v_isSharedCheck_268_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_stop_255_);
lean_inc(v_start_254_);
lean_inc(v_array_253_);
lean_dec(v_it_250_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_268_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
uint8_t v___x_259_; 
v___x_259_ = lean_nat_dec_lt(v_start_254_, v_stop_255_);
if (v___x_259_ == 0)
{
lean_del_object(v___x_257_);
lean_dec(v_stop_255_);
lean_dec(v_start_254_);
lean_dec_ref(v_array_253_);
lean_dec_ref(v_recur_252_);
return v_acc_251_;
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_add(v_start_254_, v___x_260_);
lean_inc_ref(v_array_253_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_261_);
v___x_263_ = v___x_257_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_array_253_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v_stop_255_);
v___x_263_ = v_reuseFailAlloc_267_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_array_fget(v_array_253_, v_start_254_);
lean_dec(v_start_254_);
lean_dec_ref(v_array_253_);
v___x_265_ = lean_array_push(v_acc_251_, v___x_264_);
v___x_266_ = lean_apply_3(v_recur_252_, v___x_263_, v___x_265_, lean_box(0));
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__2(lean_object* v___f_269_, lean_object* v___f_270_, lean_object* v_x_271_, lean_object* v_y_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_275_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_269_, v_x_271_, v___x_274_);
v___x_276_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_270_, v_y_272_, v___x_274_);
v_a_277_ = l_Array_append___redArg(v___x_275_, v___x_276_);
lean_dec(v___x_276_);
v___x_278_ = lean_array_get_size(v_a_277_);
v___x_279_ = l_Array_toSubarray___redArg(v_a_277_, v___x_273_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object* v_00_u03b1_283_){
_start:
{
lean_object* v___f_284_; 
v___f_284_ = ((lean_object*)(l_Array_instAppendSubarray___closed__1));
return v___f_284_;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr___redArg(lean_object* v_inst_288_, lean_object* v_s_289_){
_start:
{
lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___f_290_ = ((lean_object*)(l_Array_instAppendSubarray___closed__0));
v___x_291_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_292_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_290_, v_s_289_, v___x_291_);
v___x_293_ = l_Array_repr___redArg(v_inst_288_, v___x_292_);
v___x_294_ = ((lean_object*)(l_Array_Subarray_repr___redArg___closed__1));
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr(lean_object* v_00_u03b1_296_, lean_object* v_inst_297_, lean_object* v_s_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Array_Subarray_repr___redArg(v_inst_297_, v_s_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0(lean_object* v_inst_300_, lean_object* v_s_301_, lean_object* v_x_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Array_Subarray_repr___redArg(v_inst_300_, v_s_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0___boxed(lean_object* v_inst_304_, lean_object* v_s_305_, lean_object* v_x_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Array_instReprSubarray___redArg___lam__0(v_inst_304_, v_s_305_, v_x_306_);
lean_dec(v_x_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg(lean_object* v_inst_308_){
_start:
{
lean_object* v___f_309_; 
v___f_309_ = lean_alloc_closure((void*)(l_Array_instReprSubarray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_309_, 0, v_inst_308_);
return v___f_309_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray(lean_object* v_00_u03b1_310_, lean_object* v_inst_311_){
_start:
{
lean_object* v___f_312_; 
v___f_312_ = lean_alloc_closure((void*)(l_Array_instReprSubarray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_312_, 0, v_inst_311_);
return v___f_312_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__1(lean_object* v___f_314_, lean_object* v_inst_315_, lean_object* v_s_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_317_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_318_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_314_, v_s_316_, v___x_317_);
v___x_319_ = ((lean_object*)(l_Array_instToStringSubarray___redArg___lam__1___closed__0));
v___x_320_ = lean_array_to_list(v___x_318_);
v___x_321_ = l_List_toString___redArg(v_inst_315_, v___x_320_);
v___x_322_ = lean_string_append(v___x_319_, v___x_321_);
lean_dec_ref(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object* v_inst_323_){
_start:
{
lean_object* v___f_324_; lean_object* v___f_325_; 
v___f_324_ = ((lean_object*)(l_Array_instAppendSubarray___closed__0));
v___f_325_ = lean_alloc_closure((void*)(l_Array_instToStringSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_325_, 0, v___f_324_);
lean_closure_set(v___f_325_, 1, v_inst_323_);
return v___f_325_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray(lean_object* v_00_u03b1_326_, lean_object* v_inst_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Array_instToStringSubarray___redArg(v_inst_327_);
return v___x_328_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Slice_Array_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Slice_Array_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif
