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
lean_object* l_instIteratorSubarrayIteratorId___redArg(){
_start:
{
lean_object* v___f_56_; 
v___f_56_ = ((lean_object*)(l_instIteratorSubarrayIteratorId___redArg___closed__0));
return v___f_56_;
}
}
LEAN_EXPORT void l_instIteratorSubarrayIteratorId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_57_;
v_res_57_ = l_instIteratorSubarrayIteratorId___redArg();
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___redArg___boxed(lean_object* v___dummy_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_instIteratorSubarrayIteratorId___redArg();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId(lean_object* v_00_u03b1_60_){
_start:
{
lean_object* v___f_61_; 
v___f_61_ = ((lean_object*)(l_instIteratorSubarrayIteratorId___redArg___closed__0));
return v___f_61_;
}
}
lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg(){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT void l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_64_;
v_res_64_ = l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg();
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg___boxed(lean_object* v___dummy_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg();
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation(lean_object* v_00_u03b1_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_box(0);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object* v_toPure_69_, lean_object* v_recur_70_, lean_object* v_it_71_, lean_object* v_____do__lift_72_){
_start:
{
if (lean_obj_tag(v_____do__lift_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
lean_dec_ref(v_it_71_);
lean_dec(v_recur_70_);
v_a_73_ = lean_ctor_get(v_____do__lift_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v_____do__lift_72_, 1);
v___x_74_ = lean_apply_2(v_toPure_69_, lean_box(0), v_a_73_);
return v___x_74_;
}
else
{
lean_object* v_a_75_; lean_object* v___x_76_; 
lean_dec(v_toPure_69_);
v_a_75_ = lean_ctor_get(v_____do__lift_72_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v_____do__lift_72_, 1);
v___x_76_ = lean_apply_4(v_recur_70_, v_it_71_, v_a_75_, lean_box(0), lean_box(0));
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1(lean_object* v_toPure_77_, lean_object* v_recur_78_, lean_object* v___y_79_, lean_object* v_acc_80_, lean_object* v_toBind_81_, lean_object* v_s_82_){
_start:
{
switch(lean_obj_tag(v_s_82_))
{
case 0:
{
lean_object* v_it_83_; lean_object* v_out_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_it_83_ = lean_ctor_get(v_s_82_, 0);
lean_inc(v_it_83_);
v_out_84_ = lean_ctor_get(v_s_82_, 1);
lean_inc(v_out_84_);
lean_dec_ref_known(v_s_82_, 2);
v___f_85_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_85_, 0, v_toPure_77_);
lean_closure_set(v___f_85_, 1, v_recur_78_);
lean_closure_set(v___f_85_, 2, v_it_83_);
v___x_86_ = lean_apply_3(v___y_79_, v_out_84_, lean_box(0), v_acc_80_);
v___x_87_ = lean_apply_4(v_toBind_81_, lean_box(0), lean_box(0), v___x_86_, v___f_85_);
return v___x_87_;
}
case 1:
{
lean_object* v_it_88_; lean_object* v___x_89_; 
lean_dec(v_toBind_81_);
lean_dec(v___y_79_);
lean_dec(v_toPure_77_);
v_it_88_ = lean_ctor_get(v_s_82_, 0);
lean_inc(v_it_88_);
lean_dec_ref_known(v_s_82_, 1);
v___x_89_ = lean_apply_4(v_recur_78_, v_it_88_, v_acc_80_, lean_box(0), lean_box(0));
return v___x_89_;
}
default: 
{
lean_object* v___x_90_; 
lean_dec(v_toBind_81_);
lean_dec(v___y_79_);
lean_dec(v_recur_78_);
v___x_90_ = lean_apply_2(v_toPure_77_, lean_box(0), v_acc_80_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2(lean_object* v_toPure_91_, lean_object* v___y_92_, lean_object* v_toBind_93_, lean_object* v_lift_94_, lean_object* v_it_95_, lean_object* v_acc_96_, lean_object* v_hP_97_, lean_object* v_recur_98_){
_start:
{
lean_object* v_array_99_; lean_object* v_start_100_; lean_object* v_stop_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_117_; 
v_array_99_ = lean_ctor_get(v_it_95_, 0);
v_start_100_ = lean_ctor_get(v_it_95_, 1);
v_stop_101_ = lean_ctor_get(v_it_95_, 2);
v_isSharedCheck_117_ = !lean_is_exclusive(v_it_95_);
if (v_isSharedCheck_117_ == 0)
{
v___x_103_ = v_it_95_;
v_isShared_104_ = v_isSharedCheck_117_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_stop_101_);
lean_inc(v_start_100_);
lean_inc(v_array_99_);
lean_dec(v_it_95_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_117_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___f_105_; uint8_t v___x_106_; 
v___f_105_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_105_, 0, v_toPure_91_);
lean_closure_set(v___f_105_, 1, v_recur_98_);
lean_closure_set(v___f_105_, 2, v___y_92_);
lean_closure_set(v___f_105_, 3, v_acc_96_);
lean_closure_set(v___f_105_, 4, v_toBind_93_);
v___x_106_ = lean_nat_dec_lt(v_start_100_, v_stop_101_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_del_object(v___x_103_);
lean_dec(v_stop_101_);
lean_dec(v_start_100_);
lean_dec_ref(v_array_99_);
v___x_107_ = lean_box(2);
v___x_108_ = lean_apply_4(v_lift_94_, lean_box(0), lean_box(0), v___f_105_, v___x_107_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_add(v_start_100_, v___x_109_);
lean_inc_ref(v_array_99_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v___x_110_);
v___x_112_ = v___x_103_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_array_99_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_stop_101_);
v___x_112_ = v_reuseFailAlloc_116_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_array_fget(v_array_99_, v_start_100_);
lean_dec(v_start_100_);
lean_dec_ref(v_array_99_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_apply_4(v_lift_94_, lean_box(0), lean_box(0), v___f_105_, v___x_114_);
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3(lean_object* v_inst_118_, lean_object* v_lift_119_, lean_object* v_00_u03b3_120_, lean_object* v_Pl_121_, lean_object* v_it_122_, lean_object* v_init_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_toApplicative_125_; lean_object* v_toBind_126_; lean_object* v_toPure_127_; lean_object* v___f_128_; lean_object* v___x_129_; 
v_toApplicative_125_ = lean_ctor_get(v_inst_118_, 0);
lean_inc_ref(v_toApplicative_125_);
v_toBind_126_ = lean_ctor_get(v_inst_118_, 1);
lean_inc(v_toBind_126_);
lean_dec_ref(v_inst_118_);
v_toPure_127_ = lean_ctor_get(v_toApplicative_125_, 1);
lean_inc(v_toPure_127_);
lean_dec_ref(v_toApplicative_125_);
v___f_128_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2), 8, 4);
lean_closure_set(v___f_128_, 0, v_toPure_127_);
lean_closure_set(v___f_128_, 1, v___y_124_);
lean_closure_set(v___f_128_, 2, v_toBind_126_);
lean_closure_set(v___f_128_, 3, v_lift_119_);
v___x_129_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_128_, v_it_122_, v_init_123_, lean_box(0));
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(lean_object* v_inst_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_131_, 0, v_inst_130_);
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad(lean_object* v_00_u03b1_132_, lean_object* v_m_133_, lean_object* v_inst_134_){
_start:
{
lean_object* v___f_135_; 
v___f_135_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_135_, 0, v_inst_134_);
return v___f_135_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___lam__0(lean_object* v_x_136_){
_start:
{
lean_inc_ref(v_x_136_);
return v_x_136_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___lam__0___boxed(lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Subarray_instToIterator___redArg___lam__0(v_x_137_);
lean_dec_ref(v_x_137_);
return v_res_138_;
}
}
lean_object* l_Subarray_instToIterator___redArg(){
_start:
{
lean_object* v___f_141_; 
v___f_141_ = ((lean_object*)(l_Subarray_instToIterator___redArg___closed__0));
return v___f_141_;
}
}
LEAN_EXPORT void l_Subarray_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_142_;
v_res_142_ = l_Subarray_instToIterator___redArg();
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___boxed(lean_object* v___dummy_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Subarray_instToIterator___redArg();
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator(lean_object* v_00_u03b1_145_){
_start:
{
lean_object* v___f_146_; 
v___f_146_ = ((lean_object*)(l_Subarray_instToIterator___redArg___closed__0));
return v___f_146_;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad___redArg(lean_object* v_inst_147_){
_start:
{
lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_150_; 
v___f_148_ = ((lean_object*)(l_Subarray_instToIterator___redArg___closed__0));
lean_inc_ref(v_inst_147_);
v___f_149_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_149_, 0, v_inst_147_);
v___x_150_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(v_inst_147_, v___f_148_, v___f_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad(lean_object* v_00_u03b1_151_, lean_object* v_m_152_, lean_object* v_inst_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_instForInSubarrayOfMonad___redArg(v_inst_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__0(lean_object* v_toPure_155_, lean_object* v_____do__lift_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lean_apply_2(v_toPure_155_, lean_box(0), v_____do__lift_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__1(lean_object* v_toPure_158_, lean_object* v_recur_159_, lean_object* v___x_160_, lean_object* v_____do__lift_161_){
_start:
{
if (lean_obj_tag(v_____do__lift_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_163_; 
lean_dec_ref(v___x_160_);
lean_dec(v_recur_159_);
v_a_162_ = lean_ctor_get(v_____do__lift_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref_known(v_____do__lift_161_, 1);
v___x_163_ = lean_apply_2(v_toPure_158_, lean_box(0), v_a_162_);
return v___x_163_;
}
else
{
lean_object* v_a_164_; lean_object* v___x_165_; 
lean_dec(v_toPure_158_);
v_a_164_ = lean_ctor_get(v_____do__lift_161_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v_____do__lift_161_, 1);
v___x_165_ = lean_apply_4(v_recur_159_, v___x_160_, v_a_164_, lean_box(0), lean_box(0));
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__2(lean_object* v_toPure_166_, lean_object* v_f_167_, lean_object* v_toBind_168_, lean_object* v___f_169_, lean_object* v_it_170_, lean_object* v_acc_171_, lean_object* v_hP_172_, lean_object* v_recur_173_){
_start:
{
lean_object* v_array_174_; lean_object* v_start_175_; lean_object* v_stop_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_192_; 
v_array_174_ = lean_ctor_get(v_it_170_, 0);
v_start_175_ = lean_ctor_get(v_it_170_, 1);
v_stop_176_ = lean_ctor_get(v_it_170_, 2);
v_isSharedCheck_192_ = !lean_is_exclusive(v_it_170_);
if (v_isSharedCheck_192_ == 0)
{
v___x_178_ = v_it_170_;
v_isShared_179_ = v_isSharedCheck_192_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_stop_176_);
lean_inc(v_start_175_);
lean_inc(v_array_174_);
lean_dec(v_it_170_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_192_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
uint8_t v___x_180_; 
v___x_180_ = lean_nat_dec_lt(v_start_175_, v_stop_176_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_del_object(v___x_178_);
lean_dec(v_stop_176_);
lean_dec(v_start_175_);
lean_dec_ref(v_array_174_);
lean_dec(v_recur_173_);
lean_dec(v___f_169_);
lean_dec(v_toBind_168_);
lean_dec(v_f_167_);
v___x_181_ = lean_apply_2(v_toPure_166_, lean_box(0), v_acc_171_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_add(v_start_175_, v___x_182_);
lean_inc_ref(v_array_174_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_183_);
v___x_185_ = v___x_178_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_array_174_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_stop_176_);
v___x_185_ = v_reuseFailAlloc_191_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___f_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___f_186_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_186_, 0, v_toPure_166_);
lean_closure_set(v___f_186_, 1, v_recur_173_);
lean_closure_set(v___f_186_, 2, v___x_185_);
v___x_187_ = lean_array_fget(v_array_174_, v_start_175_);
lean_dec(v_start_175_);
lean_dec_ref(v_array_174_);
v___x_188_ = lean_apply_2(v_f_167_, v___x_187_, v_acc_171_);
lean_inc(v_toBind_168_);
v___x_189_ = lean_apply_4(v_toBind_168_, lean_box(0), lean_box(0), v___x_188_, v___f_169_);
v___x_190_ = lean_apply_4(v_toBind_168_, lean_box(0), lean_box(0), v___x_189_, v___f_186_);
return v___x_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object* v_inst_193_, lean_object* v_s_194_, lean_object* v_b_195_, lean_object* v_f_196_){
_start:
{
lean_object* v_toApplicative_197_; lean_object* v_toBind_198_; lean_object* v_toPure_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___x_202_; 
v_toApplicative_197_ = lean_ctor_get(v_inst_193_, 0);
lean_inc_ref(v_toApplicative_197_);
v_toBind_198_ = lean_ctor_get(v_inst_193_, 1);
lean_inc(v_toBind_198_);
lean_dec_ref(v_inst_193_);
v_toPure_199_ = lean_ctor_get(v_toApplicative_197_, 1);
lean_inc_n(v_toPure_199_, 2);
lean_dec_ref(v_toApplicative_197_);
v___f_200_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_200_, 0, v_toPure_199_);
v___f_201_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__2), 8, 4);
lean_closure_set(v___f_201_, 0, v_toPure_199_);
lean_closure_set(v___f_201_, 1, v_f_196_);
lean_closure_set(v___f_201_, 2, v_toBind_198_);
lean_closure_set(v___f_201_, 3, v___f_200_);
v___x_202_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_201_, v_s_194_, v_b_195_, lean_box(0));
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_m_205_, lean_object* v_inst_206_, lean_object* v_s_207_, lean_object* v_b_208_, lean_object* v_f_209_){
_start:
{
lean_object* v_toApplicative_210_; lean_object* v_toBind_211_; lean_object* v_toPure_212_; lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___x_215_; 
v_toApplicative_210_ = lean_ctor_get(v_inst_206_, 0);
lean_inc_ref(v_toApplicative_210_);
v_toBind_211_ = lean_ctor_get(v_inst_206_, 1);
lean_inc(v_toBind_211_);
lean_dec_ref(v_inst_206_);
v_toPure_212_ = lean_ctor_get(v_toApplicative_210_, 1);
lean_inc_n(v_toPure_212_, 2);
lean_dec_ref(v_toApplicative_210_);
v___f_213_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_213_, 0, v_toPure_212_);
v___f_214_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__2), 8, 4);
lean_closure_set(v___f_214_, 0, v_toPure_212_);
lean_closure_set(v___f_214_, 1, v_f_209_);
lean_closure_set(v___f_214_, 2, v_toBind_211_);
lean_closure_set(v___f_214_, 3, v___f_213_);
v___x_215_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_214_, v_s_207_, v_b_208_, lean_box(0));
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(lean_object* v_a_216_, lean_object* v_b_217_){
_start:
{
lean_object* v_array_218_; lean_object* v_start_219_; lean_object* v_stop_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_233_; 
v_array_218_ = lean_ctor_get(v_a_216_, 0);
v_start_219_ = lean_ctor_get(v_a_216_, 1);
v_stop_220_ = lean_ctor_get(v_a_216_, 2);
v_isSharedCheck_233_ = !lean_is_exclusive(v_a_216_);
if (v_isSharedCheck_233_ == 0)
{
v___x_222_ = v_a_216_;
v_isShared_223_ = v_isSharedCheck_233_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_stop_220_);
lean_inc(v_start_219_);
lean_inc(v_array_218_);
lean_dec(v_a_216_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_233_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
uint8_t v___x_224_; 
v___x_224_ = lean_nat_dec_lt(v_start_219_, v_stop_220_);
if (v___x_224_ == 0)
{
lean_del_object(v___x_222_);
lean_dec(v_stop_220_);
lean_dec(v_start_219_);
lean_dec_ref(v_array_218_);
return v_b_217_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_start_219_, v___x_225_);
lean_inc_ref(v_array_218_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_226_);
v___x_228_ = v___x_222_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_array_218_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_stop_220_);
v___x_228_ = v_reuseFailAlloc_232_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_array_fget(v_array_218_, v_start_219_);
lean_dec(v_start_219_);
lean_dec_ref(v_array_218_);
v___x_230_ = lean_array_push(v_b_217_, v___x_229_);
v_a_216_ = v___x_228_;
v_b_217_ = v___x_230_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_copy___redArg(lean_object* v_s_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_238_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_236_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Subarray_copy(lean_object* v_00_u03b1_239_, lean_object* v_s_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Subarray_copy___redArg(v_s_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0(lean_object* v_00_u03b1_242_, lean_object* v_inst_243_, lean_object* v_R_244_, lean_object* v_a_245_, lean_object* v_b_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_a_245_, v_b_246_);
return v___x_247_;
}
}
lean_object* l_instCoeSubarrayArray___redArg(){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = ((lean_object*)(l_instCoeSubarrayArray___redArg___closed__0));
return v___x_250_;
}
}
LEAN_EXPORT void l_instCoeSubarrayArray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_251_;
v_res_251_ = l_instCoeSubarrayArray___redArg();
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_instCoeSubarrayArray___redArg___boxed(lean_object* v___dummy_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_instCoeSubarrayArray___redArg();
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_instCoeSubarrayArray(lean_object* v_00_u03b1_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = ((lean_object*)(l_instCoeSubarrayArray___redArg___closed__0));
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object* v_s_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_258_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray(lean_object* v_00_u03b1_259_, lean_object* v_s_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Array_ofSubarray___redArg(v_s_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___lam__0(lean_object* v_it_262_, lean_object* v_acc_263_, lean_object* v_recur_264_){
_start:
{
lean_object* v_array_265_; lean_object* v_start_266_; lean_object* v_stop_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_280_; 
v_array_265_ = lean_ctor_get(v_it_262_, 0);
v_start_266_ = lean_ctor_get(v_it_262_, 1);
v_stop_267_ = lean_ctor_get(v_it_262_, 2);
v_isSharedCheck_280_ = !lean_is_exclusive(v_it_262_);
if (v_isSharedCheck_280_ == 0)
{
v___x_269_ = v_it_262_;
v_isShared_270_ = v_isSharedCheck_280_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_stop_267_);
lean_inc(v_start_266_);
lean_inc(v_array_265_);
lean_dec(v_it_262_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_280_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
uint8_t v___x_271_; 
v___x_271_ = lean_nat_dec_lt(v_start_266_, v_stop_267_);
if (v___x_271_ == 0)
{
lean_del_object(v___x_269_);
lean_dec(v_stop_267_);
lean_dec(v_start_266_);
lean_dec_ref(v_array_265_);
lean_dec_ref(v_recur_264_);
return v_acc_263_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_start_266_, v___x_272_);
lean_inc_ref(v_array_265_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_273_);
v___x_275_ = v___x_269_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_array_265_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_stop_267_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_array_fget(v_array_265_, v_start_266_);
lean_dec(v_start_266_);
lean_dec_ref(v_array_265_);
v___x_277_ = lean_array_push(v_acc_263_, v___x_276_);
v___x_278_ = lean_apply_3(v_recur_264_, v___x_275_, v___x_277_, lean_box(0));
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___lam__2(lean_object* v___f_281_, lean_object* v___f_282_, lean_object* v_x_283_, lean_object* v_y_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_a_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_287_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_281_, v_x_283_, v___x_286_);
v___x_288_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_282_, v_y_284_, v___x_286_);
v_a_289_ = l_Array_append___redArg(v___x_287_, v___x_288_);
lean_dec(v___x_288_);
v___x_290_ = lean_array_get_size(v_a_289_);
v___x_291_ = l_Array_toSubarray___redArg(v_a_289_, v___x_285_, v___x_290_);
return v___x_291_;
}
}
lean_object* l_Array_instAppendSubarray___redArg(){
_start:
{
lean_object* v___f_296_; 
v___f_296_ = ((lean_object*)(l_Array_instAppendSubarray___redArg___closed__1));
return v___f_296_;
}
}
LEAN_EXPORT void l_Array_instAppendSubarray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_297_;
v_res_297_ = l_Array_instAppendSubarray___redArg();
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___boxed(lean_object* v___dummy_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Array_instAppendSubarray___redArg();
return v_res_299_;
}
}
static lean_object* _init_l_Array_instAppendSubarray___closed__0(void){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Array_instAppendSubarray___redArg();
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object* v_00_u03b1_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Array_instAppendSubarray___closed__0, &l_Array_instAppendSubarray___closed__0_once, _init_l_Array_instAppendSubarray___closed__0);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr___redArg(lean_object* v_inst_306_, lean_object* v_s_307_){
_start:
{
lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___f_308_ = ((lean_object*)(l_Array_instAppendSubarray___redArg___closed__0));
v___x_309_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_310_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_308_, v_s_307_, v___x_309_);
v___x_311_ = l_Array_repr___redArg(v_inst_306_, v___x_310_);
v___x_312_ = ((lean_object*)(l_Array_Subarray_repr___redArg___closed__1));
v___x_313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr(lean_object* v_00_u03b1_314_, lean_object* v_inst_315_, lean_object* v_s_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Array_Subarray_repr___redArg(v_inst_315_, v_s_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0(lean_object* v_inst_318_, lean_object* v_s_319_, lean_object* v_x_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Array_Subarray_repr___redArg(v_inst_318_, v_s_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0___boxed(lean_object* v_inst_322_, lean_object* v_s_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Array_instReprSubarray___redArg___lam__0(v_inst_322_, v_s_323_, v_x_324_);
lean_dec(v_x_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg(lean_object* v_inst_326_){
_start:
{
lean_object* v___f_327_; 
v___f_327_ = lean_alloc_closure((void*)(l_Array_instReprSubarray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_327_, 0, v_inst_326_);
return v___f_327_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray(lean_object* v_00_u03b1_328_, lean_object* v_inst_329_){
_start:
{
lean_object* v___f_330_; 
v___f_330_ = lean_alloc_closure((void*)(l_Array_instReprSubarray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_330_, 0, v_inst_329_);
return v___f_330_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__1(lean_object* v___f_332_, lean_object* v_inst_333_, lean_object* v_s_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_335_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_336_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_332_, v_s_334_, v___x_335_);
v___x_337_ = ((lean_object*)(l_Array_instToStringSubarray___redArg___lam__1___closed__0));
v___x_338_ = lean_array_to_list(v___x_336_);
v___x_339_ = l_List_toString___redArg(v_inst_333_, v___x_338_);
v___x_340_ = lean_string_append(v___x_337_, v___x_339_);
lean_dec_ref(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object* v_inst_341_){
_start:
{
lean_object* v___f_342_; lean_object* v___f_343_; 
v___f_342_ = ((lean_object*)(l_Array_instAppendSubarray___redArg___closed__0));
v___f_343_ = lean_alloc_closure((void*)(l_Array_instToStringSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_343_, 0, v___f_342_);
lean_closure_set(v___f_343_, 1, v_inst_341_);
return v___f_343_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray(lean_object* v_00_u03b1_344_, lean_object* v_inst_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Array_instToStringSubarray___redArg(v_inst_345_);
return v___x_346_;
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
