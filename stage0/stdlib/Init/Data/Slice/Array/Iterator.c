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
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SubarrayIterator_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l_SubarrayIterator_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___redArg___lam__0(lean_object*);
static const lean_closure_object l_instIteratorSubarrayIteratorId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instIteratorSubarrayIteratorId___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instIteratorSubarrayIteratorId___redArg___closed__0 = (const lean_object*)&l_instIteratorSubarrayIteratorId___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___redArg();
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Subarray_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Subarray_instToIterator___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Subarray_instToIterator___redArg___closed__0 = (const lean_object*)&l_Subarray_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___boxed(lean_object*);
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
static const lean_closure_object l_instCoeSubarrayArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Subarray_copy, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instCoeSubarrayArray___redArg___closed__0 = (const lean_object*)&l_instCoeSubarrayArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instCoeSubarrayArray___redArg();
LEAN_EXPORT lean_object* l_instCoeSubarrayArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instCoeSubarrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_ofSubarray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instAppendSubarray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instAppendSubarray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instAppendSubarray___redArg___closed__0 = (const lean_object*)&l_Array_instAppendSubarray___redArg___closed__0_value;
static const lean_closure_object l_Array_instAppendSubarray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instAppendSubarray___redArg___lam__2, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Array_instAppendSubarray___redArg___closed__0_value),((lean_object*)&l_Array_instAppendSubarray___redArg___closed__0_value)} };
static const lean_object* l_Array_instAppendSubarray___redArg___closed__1 = (const lean_object*)&l_Array_instAppendSubarray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg();
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___boxed(lean_object*);
static lean_once_cell_t l_Array_instAppendSubarray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_instAppendSubarray___closed__0;
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
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___redArg___lam__0(lean_object* v_it_37_){
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
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___redArg(){
_start:
{
lean_object* v___f_56_; 
v___f_56_ = ((lean_object*)(l_instIteratorSubarrayIteratorId___redArg___closed__0));
return v___f_56_;
}
}
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___redArg___boxed(lean_object* v___dummy_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_instIteratorSubarrayIteratorId___redArg();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId(lean_object* v_00_u03b1_59_){
_start:
{
lean_object* v___f_60_; 
v___f_60_ = ((lean_object*)(l_instIteratorSubarrayIteratorId___redArg___closed__0));
return v___f_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter___redArg(lean_object* v_x_61_, lean_object* v_h__1_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_apply_1(v_h__1_62_, v_x_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter(lean_object* v_00_u03b1_64_, lean_object* v_motive_65_, lean_object* v_x_66_, lean_object* v_h__1_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_apply_1(v_h__1_67_, v_x_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg(){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg___boxed(lean_object* v___dummy_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg();
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation(lean_object* v_00_u03b1_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object* v_toPure_75_, lean_object* v_recur_76_, lean_object* v_it_77_, lean_object* v_____do__lift_78_){
_start:
{
if (lean_obj_tag(v_____do__lift_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; 
lean_dec_ref(v_it_77_);
lean_dec(v_recur_76_);
v_a_79_ = lean_ctor_get(v_____do__lift_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v_____do__lift_78_, 1);
v___x_80_ = lean_apply_2(v_toPure_75_, lean_box(0), v_a_79_);
return v___x_80_;
}
else
{
lean_object* v_a_81_; lean_object* v___x_82_; 
lean_dec(v_toPure_75_);
v_a_81_ = lean_ctor_get(v_____do__lift_78_, 0);
lean_inc(v_a_81_);
lean_dec_ref_known(v_____do__lift_78_, 1);
v___x_82_ = lean_apply_4(v_recur_76_, v_it_77_, v_a_81_, lean_box(0), lean_box(0));
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1(lean_object* v_toPure_83_, lean_object* v_recur_84_, lean_object* v___y_85_, lean_object* v_acc_86_, lean_object* v_toBind_87_, lean_object* v_s_88_){
_start:
{
switch(lean_obj_tag(v_s_88_))
{
case 0:
{
lean_object* v_it_89_; lean_object* v_out_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_it_89_ = lean_ctor_get(v_s_88_, 0);
lean_inc(v_it_89_);
v_out_90_ = lean_ctor_get(v_s_88_, 1);
lean_inc(v_out_90_);
lean_dec_ref_known(v_s_88_, 2);
v___f_91_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_91_, 0, v_toPure_83_);
lean_closure_set(v___f_91_, 1, v_recur_84_);
lean_closure_set(v___f_91_, 2, v_it_89_);
v___x_92_ = lean_apply_3(v___y_85_, v_out_90_, lean_box(0), v_acc_86_);
v___x_93_ = lean_apply_4(v_toBind_87_, lean_box(0), lean_box(0), v___x_92_, v___f_91_);
return v___x_93_;
}
case 1:
{
lean_object* v_it_94_; lean_object* v___x_95_; 
lean_dec(v_toBind_87_);
lean_dec(v___y_85_);
lean_dec(v_toPure_83_);
v_it_94_ = lean_ctor_get(v_s_88_, 0);
lean_inc(v_it_94_);
lean_dec_ref_known(v_s_88_, 1);
v___x_95_ = lean_apply_4(v_recur_84_, v_it_94_, v_acc_86_, lean_box(0), lean_box(0));
return v___x_95_;
}
default: 
{
lean_object* v___x_96_; 
lean_dec(v_toBind_87_);
lean_dec(v___y_85_);
lean_dec(v_recur_84_);
v___x_96_ = lean_apply_2(v_toPure_83_, lean_box(0), v_acc_86_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2(lean_object* v_toPure_97_, lean_object* v___y_98_, lean_object* v_toBind_99_, lean_object* v_lift_100_, lean_object* v_it_101_, lean_object* v_acc_102_, lean_object* v_hP_103_, lean_object* v_recur_104_){
_start:
{
lean_object* v_array_105_; lean_object* v_start_106_; lean_object* v_stop_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_123_; 
v_array_105_ = lean_ctor_get(v_it_101_, 0);
v_start_106_ = lean_ctor_get(v_it_101_, 1);
v_stop_107_ = lean_ctor_get(v_it_101_, 2);
v_isSharedCheck_123_ = !lean_is_exclusive(v_it_101_);
if (v_isSharedCheck_123_ == 0)
{
v___x_109_ = v_it_101_;
v_isShared_110_ = v_isSharedCheck_123_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_stop_107_);
lean_inc(v_start_106_);
lean_inc(v_array_105_);
lean_dec(v_it_101_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_123_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___f_111_; uint8_t v___x_112_; 
v___f_111_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_111_, 0, v_toPure_97_);
lean_closure_set(v___f_111_, 1, v_recur_104_);
lean_closure_set(v___f_111_, 2, v___y_98_);
lean_closure_set(v___f_111_, 3, v_acc_102_);
lean_closure_set(v___f_111_, 4, v_toBind_99_);
v___x_112_ = lean_nat_dec_lt(v_start_106_, v_stop_107_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_del_object(v___x_109_);
lean_dec(v_stop_107_);
lean_dec(v_start_106_);
lean_dec_ref(v_array_105_);
v___x_113_ = lean_box(2);
v___x_114_ = lean_apply_4(v_lift_100_, lean_box(0), lean_box(0), v___f_111_, v___x_113_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_add(v_start_106_, v___x_115_);
lean_inc_ref(v_array_105_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_116_);
v___x_118_ = v___x_109_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_array_105_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_122_, 2, v_stop_107_);
v___x_118_ = v_reuseFailAlloc_122_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_array_fget(v_array_105_, v_start_106_);
lean_dec(v_start_106_);
lean_dec_ref(v_array_105_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = lean_apply_4(v_lift_100_, lean_box(0), lean_box(0), v___f_111_, v___x_120_);
return v___x_121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3(lean_object* v_inst_124_, lean_object* v_lift_125_, lean_object* v_00_u03b3_126_, lean_object* v_Pl_127_, lean_object* v_it_128_, lean_object* v_init_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_toApplicative_131_; lean_object* v_toBind_132_; lean_object* v_toPure_133_; lean_object* v___f_134_; lean_object* v___x_135_; 
v_toApplicative_131_ = lean_ctor_get(v_inst_124_, 0);
lean_inc_ref(v_toApplicative_131_);
v_toBind_132_ = lean_ctor_get(v_inst_124_, 1);
lean_inc(v_toBind_132_);
lean_dec_ref(v_inst_124_);
v_toPure_133_ = lean_ctor_get(v_toApplicative_131_, 1);
lean_inc(v_toPure_133_);
lean_dec_ref(v_toApplicative_131_);
v___f_134_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2), 8, 4);
lean_closure_set(v___f_134_, 0, v_toPure_133_);
lean_closure_set(v___f_134_, 1, v___y_130_);
lean_closure_set(v___f_134_, 2, v_toBind_132_);
lean_closure_set(v___f_134_, 3, v_lift_125_);
v___x_135_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_134_, v_it_128_, v_init_129_, lean_box(0));
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(lean_object* v_inst_136_){
_start:
{
lean_object* v___f_137_; 
v___f_137_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_137_, 0, v_inst_136_);
return v___f_137_;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad(lean_object* v_00_u03b1_138_, lean_object* v_m_139_, lean_object* v_inst_140_){
_start:
{
lean_object* v___f_141_; 
v___f_141_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_141_, 0, v_inst_140_);
return v___f_141_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___lam__0(lean_object* v_x_142_){
_start:
{
lean_inc_ref(v_x_142_);
return v_x_142_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___lam__0___boxed(lean_object* v_x_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Subarray_instToIterator___redArg___lam__0(v_x_143_);
lean_dec_ref(v_x_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg(){
_start:
{
lean_object* v___f_147_; 
v___f_147_ = ((lean_object*)(l_Subarray_instToIterator___redArg___closed__0));
return v___f_147_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___boxed(lean_object* v___dummy_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Subarray_instToIterator___redArg();
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator(lean_object* v_00_u03b1_150_){
_start:
{
lean_object* v___f_151_; 
v___f_151_ = ((lean_object*)(l_Subarray_instToIterator___redArg___closed__0));
return v___f_151_;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad___redArg(lean_object* v_inst_152_){
_start:
{
lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___x_155_; 
v___f_153_ = ((lean_object*)(l_Subarray_instToIterator___redArg___closed__0));
lean_inc_ref(v_inst_152_);
v___f_154_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_154_, 0, v_inst_152_);
v___x_155_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(v_inst_152_, v___f_153_, v___f_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad(lean_object* v_00_u03b1_156_, lean_object* v_m_157_, lean_object* v_inst_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_instForInSubarrayOfMonad___redArg(v_inst_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__0(lean_object* v_toPure_160_, lean_object* v_____do__lift_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_apply_2(v_toPure_160_, lean_box(0), v_____do__lift_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__1(lean_object* v_toPure_163_, lean_object* v_recur_164_, lean_object* v___x_165_, lean_object* v_____do__lift_166_){
_start:
{
if (lean_obj_tag(v_____do__lift_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; 
lean_dec_ref(v___x_165_);
lean_dec(v_recur_164_);
v_a_167_ = lean_ctor_get(v_____do__lift_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v_____do__lift_166_, 1);
v___x_168_ = lean_apply_2(v_toPure_163_, lean_box(0), v_a_167_);
return v___x_168_;
}
else
{
lean_object* v_a_169_; lean_object* v___x_170_; 
lean_dec(v_toPure_163_);
v_a_169_ = lean_ctor_get(v_____do__lift_166_, 0);
lean_inc(v_a_169_);
lean_dec_ref_known(v_____do__lift_166_, 1);
v___x_170_ = lean_apply_4(v_recur_164_, v___x_165_, v_a_169_, lean_box(0), lean_box(0));
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__2(lean_object* v_toPure_171_, lean_object* v_f_172_, lean_object* v_toBind_173_, lean_object* v___f_174_, lean_object* v_it_175_, lean_object* v_acc_176_, lean_object* v_hP_177_, lean_object* v_recur_178_){
_start:
{
lean_object* v_array_179_; lean_object* v_start_180_; lean_object* v_stop_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_197_; 
v_array_179_ = lean_ctor_get(v_it_175_, 0);
v_start_180_ = lean_ctor_get(v_it_175_, 1);
v_stop_181_ = lean_ctor_get(v_it_175_, 2);
v_isSharedCheck_197_ = !lean_is_exclusive(v_it_175_);
if (v_isSharedCheck_197_ == 0)
{
v___x_183_ = v_it_175_;
v_isShared_184_ = v_isSharedCheck_197_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_stop_181_);
lean_inc(v_start_180_);
lean_inc(v_array_179_);
lean_dec(v_it_175_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_197_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
uint8_t v___x_185_; 
v___x_185_ = lean_nat_dec_lt(v_start_180_, v_stop_181_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
lean_del_object(v___x_183_);
lean_dec(v_stop_181_);
lean_dec(v_start_180_);
lean_dec_ref(v_array_179_);
lean_dec(v_recur_178_);
lean_dec(v___f_174_);
lean_dec(v_toBind_173_);
lean_dec(v_f_172_);
v___x_186_ = lean_apply_2(v_toPure_171_, lean_box(0), v_acc_176_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_start_180_, v___x_187_);
lean_inc_ref(v_array_179_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_188_);
v___x_190_ = v___x_183_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_array_179_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_stop_181_);
v___x_190_ = v_reuseFailAlloc_196_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___f_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___f_191_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_191_, 0, v_toPure_171_);
lean_closure_set(v___f_191_, 1, v_recur_178_);
lean_closure_set(v___f_191_, 2, v___x_190_);
v___x_192_ = lean_array_fget(v_array_179_, v_start_180_);
lean_dec(v_start_180_);
lean_dec_ref(v_array_179_);
v___x_193_ = lean_apply_2(v_f_172_, v___x_192_, v_acc_176_);
lean_inc(v_toBind_173_);
v___x_194_ = lean_apply_4(v_toBind_173_, lean_box(0), lean_box(0), v___x_193_, v___f_174_);
v___x_195_ = lean_apply_4(v_toBind_173_, lean_box(0), lean_box(0), v___x_194_, v___f_191_);
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object* v_inst_198_, lean_object* v_s_199_, lean_object* v_b_200_, lean_object* v_f_201_){
_start:
{
lean_object* v_toApplicative_202_; lean_object* v_toBind_203_; lean_object* v_toPure_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___x_207_; 
v_toApplicative_202_ = lean_ctor_get(v_inst_198_, 0);
lean_inc_ref(v_toApplicative_202_);
v_toBind_203_ = lean_ctor_get(v_inst_198_, 1);
lean_inc(v_toBind_203_);
lean_dec_ref(v_inst_198_);
v_toPure_204_ = lean_ctor_get(v_toApplicative_202_, 1);
lean_inc_n(v_toPure_204_, 2);
lean_dec_ref(v_toApplicative_202_);
v___f_205_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_205_, 0, v_toPure_204_);
v___f_206_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__2), 8, 4);
lean_closure_set(v___f_206_, 0, v_toPure_204_);
lean_closure_set(v___f_206_, 1, v_f_201_);
lean_closure_set(v___f_206_, 2, v_toBind_203_);
lean_closure_set(v___f_206_, 3, v___f_205_);
v___x_207_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_206_, v_s_199_, v_b_200_, lean_box(0));
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_m_210_, lean_object* v_inst_211_, lean_object* v_s_212_, lean_object* v_b_213_, lean_object* v_f_214_){
_start:
{
lean_object* v_toApplicative_215_; lean_object* v_toBind_216_; lean_object* v_toPure_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___x_220_; 
v_toApplicative_215_ = lean_ctor_get(v_inst_211_, 0);
lean_inc_ref(v_toApplicative_215_);
v_toBind_216_ = lean_ctor_get(v_inst_211_, 1);
lean_inc(v_toBind_216_);
lean_dec_ref(v_inst_211_);
v_toPure_217_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc_n(v_toPure_217_, 2);
lean_dec_ref(v_toApplicative_215_);
v___f_218_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_218_, 0, v_toPure_217_);
v___f_219_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__2), 8, 4);
lean_closure_set(v___f_219_, 0, v_toPure_217_);
lean_closure_set(v___f_219_, 1, v_f_214_);
lean_closure_set(v___f_219_, 2, v_toBind_216_);
lean_closure_set(v___f_219_, 3, v___f_218_);
v___x_220_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_219_, v_s_212_, v_b_213_, lean_box(0));
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
lean_object* v_array_223_; lean_object* v_start_224_; lean_object* v_stop_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_238_; 
v_array_223_ = lean_ctor_get(v_a_221_, 0);
v_start_224_ = lean_ctor_get(v_a_221_, 1);
v_stop_225_ = lean_ctor_get(v_a_221_, 2);
v_isSharedCheck_238_ = !lean_is_exclusive(v_a_221_);
if (v_isSharedCheck_238_ == 0)
{
v___x_227_ = v_a_221_;
v_isShared_228_ = v_isSharedCheck_238_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_stop_225_);
lean_inc(v_start_224_);
lean_inc(v_array_223_);
lean_dec(v_a_221_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_238_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
uint8_t v___x_229_; 
v___x_229_ = lean_nat_dec_lt(v_start_224_, v_stop_225_);
if (v___x_229_ == 0)
{
lean_del_object(v___x_227_);
lean_dec(v_stop_225_);
lean_dec(v_start_224_);
lean_dec_ref(v_array_223_);
return v_b_222_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = lean_nat_add(v_start_224_, v___x_230_);
lean_inc_ref(v_array_223_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 1, v___x_231_);
v___x_233_ = v___x_227_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_array_223_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_stop_225_);
v___x_233_ = v_reuseFailAlloc_237_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_array_fget(v_array_223_, v_start_224_);
lean_dec(v_start_224_);
lean_dec_ref(v_array_223_);
v___x_235_ = lean_array_push(v_b_222_, v___x_234_);
v_a_221_ = v___x_233_;
v_b_222_ = v___x_235_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_copy___redArg(lean_object* v_s_241_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_243_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_241_, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Subarray_copy(lean_object* v_00_u03b1_244_, lean_object* v_s_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Subarray_copy___redArg(v_s_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0(lean_object* v_00_u03b1_247_, lean_object* v_inst_248_, lean_object* v_R_249_, lean_object* v_a_250_, lean_object* v_b_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_a_250_, v_b_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_instCoeSubarrayArray___redArg(){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = ((lean_object*)(l_instCoeSubarrayArray___redArg___closed__0));
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_instCoeSubarrayArray___redArg___boxed(lean_object* v___dummy_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_instCoeSubarrayArray___redArg();
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_instCoeSubarrayArray(lean_object* v_00_u03b1_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = ((lean_object*)(l_instCoeSubarrayArray___redArg___closed__0));
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object* v_s_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_262_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_260_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray(lean_object* v_00_u03b1_263_, lean_object* v_s_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Array_ofSubarray___redArg(v_s_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___lam__0(lean_object* v_it_266_, lean_object* v_acc_267_, lean_object* v_recur_268_){
_start:
{
lean_object* v_array_269_; lean_object* v_start_270_; lean_object* v_stop_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_284_; 
v_array_269_ = lean_ctor_get(v_it_266_, 0);
v_start_270_ = lean_ctor_get(v_it_266_, 1);
v_stop_271_ = lean_ctor_get(v_it_266_, 2);
v_isSharedCheck_284_ = !lean_is_exclusive(v_it_266_);
if (v_isSharedCheck_284_ == 0)
{
v___x_273_ = v_it_266_;
v_isShared_274_ = v_isSharedCheck_284_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_stop_271_);
lean_inc(v_start_270_);
lean_inc(v_array_269_);
lean_dec(v_it_266_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_284_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_lt(v_start_270_, v_stop_271_);
if (v___x_275_ == 0)
{
lean_del_object(v___x_273_);
lean_dec(v_stop_271_);
lean_dec(v_start_270_);
lean_dec_ref(v_array_269_);
lean_dec_ref(v_recur_268_);
return v_acc_267_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_add(v_start_270_, v___x_276_);
lean_inc_ref(v_array_269_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___x_277_);
v___x_279_ = v___x_273_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_array_269_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_stop_271_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_array_fget(v_array_269_, v_start_270_);
lean_dec(v_start_270_);
lean_dec_ref(v_array_269_);
v___x_281_ = lean_array_push(v_acc_267_, v___x_280_);
v___x_282_ = lean_apply_3(v_recur_268_, v___x_279_, v___x_281_, lean_box(0));
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___lam__2(lean_object* v___f_285_, lean_object* v___f_286_, lean_object* v_x_287_, lean_object* v_y_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_a_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_291_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_285_, v_x_287_, v___x_290_);
v___x_292_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_286_, v_y_288_, v___x_290_);
v_a_293_ = l_Array_append___redArg(v___x_291_, v___x_292_);
lean_dec(v___x_292_);
v___x_294_ = lean_array_get_size(v_a_293_);
v___x_295_ = l_Array_toSubarray___redArg(v_a_293_, v___x_289_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg(){
_start:
{
lean_object* v___f_300_; 
v___f_300_ = ((lean_object*)(l_Array_instAppendSubarray___redArg___closed__1));
return v___f_300_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___boxed(lean_object* v___dummy_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Array_instAppendSubarray___redArg();
return v_res_302_;
}
}
static lean_object* _init_l_Array_instAppendSubarray___closed__0(void){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Array_instAppendSubarray___redArg();
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object* v_00_u03b1_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Array_instAppendSubarray___closed__0, &l_Array_instAppendSubarray___closed__0_once, _init_l_Array_instAppendSubarray___closed__0);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr___redArg(lean_object* v_inst_309_, lean_object* v_s_310_){
_start:
{
lean_object* v___f_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___f_311_ = ((lean_object*)(l_Array_instAppendSubarray___redArg___closed__0));
v___x_312_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_313_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_311_, v_s_310_, v___x_312_);
v___x_314_ = l_Array_repr___redArg(v_inst_309_, v___x_313_);
v___x_315_ = ((lean_object*)(l_Array_Subarray_repr___redArg___closed__1));
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr(lean_object* v_00_u03b1_317_, lean_object* v_inst_318_, lean_object* v_s_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Array_Subarray_repr___redArg(v_inst_318_, v_s_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0(lean_object* v_inst_321_, lean_object* v_s_322_, lean_object* v_x_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Array_Subarray_repr___redArg(v_inst_321_, v_s_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0___boxed(lean_object* v_inst_325_, lean_object* v_s_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Array_instReprSubarray___redArg___lam__0(v_inst_325_, v_s_326_, v_x_327_);
lean_dec(v_x_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg(lean_object* v_inst_329_){
_start:
{
lean_object* v___f_330_; 
v___f_330_ = lean_alloc_closure((void*)(l_Array_instReprSubarray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_330_, 0, v_inst_329_);
return v___f_330_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray(lean_object* v_00_u03b1_331_, lean_object* v_inst_332_){
_start:
{
lean_object* v___f_333_; 
v___f_333_ = lean_alloc_closure((void*)(l_Array_instReprSubarray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_333_, 0, v_inst_332_);
return v___f_333_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__1(lean_object* v___f_335_, lean_object* v_inst_336_, lean_object* v_s_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_338_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_339_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_335_, v_s_337_, v___x_338_);
v___x_340_ = ((lean_object*)(l_Array_instToStringSubarray___redArg___lam__1___closed__0));
v___x_341_ = lean_array_to_list(v___x_339_);
v___x_342_ = l_List_toString___redArg(v_inst_336_, v___x_341_);
v___x_343_ = lean_string_append(v___x_340_, v___x_342_);
lean_dec_ref(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object* v_inst_344_){
_start:
{
lean_object* v___f_345_; lean_object* v___f_346_; 
v___f_345_ = ((lean_object*)(l_Array_instAppendSubarray___redArg___closed__0));
v___f_346_ = lean_alloc_closure((void*)(l_Array_instToStringSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_346_, 0, v___f_345_);
lean_closure_set(v___f_346_, 1, v_inst_344_);
return v___f_346_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray(lean_object* v_00_u03b1_347_, lean_object* v_inst_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Array_instToStringSubarray___redArg(v_inst_348_);
return v___x_349_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
