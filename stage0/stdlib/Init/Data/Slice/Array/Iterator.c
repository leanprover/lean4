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
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg(){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(0);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg___boxed(lean_object* v___dummy_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation___redArg();
return v_res_64_;
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
lean_dec_ref_known(v_____do__lift_70_, 1);
v___x_72_ = lean_apply_2(v_toPure_67_, lean_box(0), v_a_71_);
return v___x_72_;
}
else
{
lean_object* v_a_73_; lean_object* v___x_74_; 
lean_dec(v_toPure_67_);
v_a_73_ = lean_ctor_get(v_____do__lift_70_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v_____do__lift_70_, 1);
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
lean_dec_ref_known(v_s_80_, 2);
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
lean_dec_ref_known(v_s_80_, 1);
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
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___lam__0(lean_object* v_x_134_){
_start:
{
lean_inc_ref(v_x_134_);
return v_x_134_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___lam__0___boxed(lean_object* v_x_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Subarray_instToIterator___redArg___lam__0(v_x_135_);
lean_dec_ref(v_x_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg(){
_start:
{
lean_object* v___f_139_; 
v___f_139_ = ((lean_object*)(l_Subarray_instToIterator___redArg___closed__0));
return v___f_139_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___redArg___boxed(lean_object* v___dummy_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Subarray_instToIterator___redArg();
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator(lean_object* v_00_u03b1_142_){
_start:
{
lean_object* v___f_143_; 
v___f_143_ = ((lean_object*)(l_Subarray_instToIterator___redArg___closed__0));
return v___f_143_;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad___redArg(lean_object* v_inst_144_){
_start:
{
lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___x_147_; 
v___f_145_ = ((lean_object*)(l_Subarray_instToIterator___redArg___closed__0));
lean_inc_ref(v_inst_144_);
v___f_146_ = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_146_, 0, v_inst_144_);
v___x_147_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(v_inst_144_, v___f_145_, v___f_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad(lean_object* v_00_u03b1_148_, lean_object* v_m_149_, lean_object* v_inst_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_instForInSubarrayOfMonad___redArg(v_inst_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__0(lean_object* v_toPure_152_, lean_object* v_____do__lift_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_apply_2(v_toPure_152_, lean_box(0), v_____do__lift_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__1(lean_object* v_toPure_155_, lean_object* v_recur_156_, lean_object* v___x_157_, lean_object* v_____do__lift_158_){
_start:
{
if (lean_obj_tag(v_____do__lift_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
lean_dec_ref(v___x_157_);
lean_dec(v_recur_156_);
v_a_159_ = lean_ctor_get(v_____do__lift_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v_____do__lift_158_, 1);
v___x_160_ = lean_apply_2(v_toPure_155_, lean_box(0), v_a_159_);
return v___x_160_;
}
else
{
lean_object* v_a_161_; lean_object* v___x_162_; 
lean_dec(v_toPure_155_);
v_a_161_ = lean_ctor_get(v_____do__lift_158_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v_____do__lift_158_, 1);
v___x_162_ = lean_apply_4(v_recur_156_, v___x_157_, v_a_161_, lean_box(0), lean_box(0));
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__2(lean_object* v_toPure_163_, lean_object* v_f_164_, lean_object* v_toBind_165_, lean_object* v___f_166_, lean_object* v_it_167_, lean_object* v_acc_168_, lean_object* v_hP_169_, lean_object* v_recur_170_){
_start:
{
lean_object* v_array_171_; lean_object* v_start_172_; lean_object* v_stop_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_189_; 
v_array_171_ = lean_ctor_get(v_it_167_, 0);
v_start_172_ = lean_ctor_get(v_it_167_, 1);
v_stop_173_ = lean_ctor_get(v_it_167_, 2);
v_isSharedCheck_189_ = !lean_is_exclusive(v_it_167_);
if (v_isSharedCheck_189_ == 0)
{
v___x_175_ = v_it_167_;
v_isShared_176_ = v_isSharedCheck_189_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_stop_173_);
lean_inc(v_start_172_);
lean_inc(v_array_171_);
lean_dec(v_it_167_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_189_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
uint8_t v___x_177_; 
v___x_177_ = lean_nat_dec_lt(v_start_172_, v_stop_173_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
lean_del_object(v___x_175_);
lean_dec(v_stop_173_);
lean_dec(v_start_172_);
lean_dec_ref(v_array_171_);
lean_dec(v_recur_170_);
lean_dec(v___f_166_);
lean_dec(v_toBind_165_);
lean_dec(v_f_164_);
v___x_178_ = lean_apply_2(v_toPure_163_, lean_box(0), v_acc_168_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v_start_172_, v___x_179_);
lean_inc_ref(v_array_171_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_180_);
v___x_182_ = v___x_175_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_array_171_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_stop_173_);
v___x_182_ = v_reuseFailAlloc_188_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___f_183_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_183_, 0, v_toPure_163_);
lean_closure_set(v___f_183_, 1, v_recur_170_);
lean_closure_set(v___f_183_, 2, v___x_182_);
v___x_184_ = lean_array_fget(v_array_171_, v_start_172_);
lean_dec(v_start_172_);
lean_dec_ref(v_array_171_);
v___x_185_ = lean_apply_2(v_f_164_, v___x_184_, v_acc_168_);
lean_inc(v_toBind_165_);
v___x_186_ = lean_apply_4(v_toBind_165_, lean_box(0), lean_box(0), v___x_185_, v___f_166_);
v___x_187_ = lean_apply_4(v_toBind_165_, lean_box(0), lean_box(0), v___x_186_, v___f_183_);
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object* v_inst_190_, lean_object* v_s_191_, lean_object* v_b_192_, lean_object* v_f_193_){
_start:
{
lean_object* v_toApplicative_194_; lean_object* v_toBind_195_; lean_object* v_toPure_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___x_199_; 
v_toApplicative_194_ = lean_ctor_get(v_inst_190_, 0);
lean_inc_ref(v_toApplicative_194_);
v_toBind_195_ = lean_ctor_get(v_inst_190_, 1);
lean_inc(v_toBind_195_);
lean_dec_ref(v_inst_190_);
v_toPure_196_ = lean_ctor_get(v_toApplicative_194_, 1);
lean_inc_n(v_toPure_196_, 2);
lean_dec_ref(v_toApplicative_194_);
v___f_197_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_197_, 0, v_toPure_196_);
v___f_198_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__2), 8, 4);
lean_closure_set(v___f_198_, 0, v_toPure_196_);
lean_closure_set(v___f_198_, 1, v_f_193_);
lean_closure_set(v___f_198_, 2, v_toBind_195_);
lean_closure_set(v___f_198_, 3, v___f_197_);
v___x_199_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_198_, v_s_191_, v_b_192_, lean_box(0));
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object* v_00_u03b1_200_, lean_object* v_00_u03b2_201_, lean_object* v_m_202_, lean_object* v_inst_203_, lean_object* v_s_204_, lean_object* v_b_205_, lean_object* v_f_206_){
_start:
{
lean_object* v_toApplicative_207_; lean_object* v_toBind_208_; lean_object* v_toPure_209_; lean_object* v___f_210_; lean_object* v___f_211_; lean_object* v___x_212_; 
v_toApplicative_207_ = lean_ctor_get(v_inst_203_, 0);
lean_inc_ref(v_toApplicative_207_);
v_toBind_208_ = lean_ctor_get(v_inst_203_, 1);
lean_inc(v_toBind_208_);
lean_dec_ref(v_inst_203_);
v_toPure_209_ = lean_ctor_get(v_toApplicative_207_, 1);
lean_inc_n(v_toPure_209_, 2);
lean_dec_ref(v_toApplicative_207_);
v___f_210_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_210_, 0, v_toPure_209_);
v___f_211_ = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__2), 8, 4);
lean_closure_set(v___f_211_, 0, v_toPure_209_);
lean_closure_set(v___f_211_, 1, v_f_206_);
lean_closure_set(v___f_211_, 2, v_toBind_208_);
lean_closure_set(v___f_211_, 3, v___f_210_);
v___x_212_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_211_, v_s_204_, v_b_205_, lean_box(0));
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(lean_object* v_a_213_, lean_object* v_b_214_){
_start:
{
lean_object* v_array_215_; lean_object* v_start_216_; lean_object* v_stop_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_230_; 
v_array_215_ = lean_ctor_get(v_a_213_, 0);
v_start_216_ = lean_ctor_get(v_a_213_, 1);
v_stop_217_ = lean_ctor_get(v_a_213_, 2);
v_isSharedCheck_230_ = !lean_is_exclusive(v_a_213_);
if (v_isSharedCheck_230_ == 0)
{
v___x_219_ = v_a_213_;
v_isShared_220_ = v_isSharedCheck_230_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_stop_217_);
lean_inc(v_start_216_);
lean_inc(v_array_215_);
lean_dec(v_a_213_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_230_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint8_t v___x_221_; 
v___x_221_ = lean_nat_dec_lt(v_start_216_, v_stop_217_);
if (v___x_221_ == 0)
{
lean_del_object(v___x_219_);
lean_dec(v_stop_217_);
lean_dec(v_start_216_);
lean_dec_ref(v_array_215_);
return v_b_214_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_add(v_start_216_, v___x_222_);
lean_inc_ref(v_array_215_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_223_);
v___x_225_ = v___x_219_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_array_215_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_stop_217_);
v___x_225_ = v_reuseFailAlloc_229_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_array_fget(v_array_215_, v_start_216_);
lean_dec(v_start_216_);
lean_dec_ref(v_array_215_);
v___x_227_ = lean_array_push(v_b_214_, v___x_226_);
v_a_213_ = v___x_225_;
v_b_214_ = v___x_227_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_copy___redArg(lean_object* v_s_233_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_235_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_233_, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Subarray_copy(lean_object* v_00_u03b1_236_, lean_object* v_s_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Subarray_copy___redArg(v_s_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0(lean_object* v_00_u03b1_239_, lean_object* v_inst_240_, lean_object* v_R_241_, lean_object* v_a_242_, lean_object* v_b_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_a_242_, v_b_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_instCoeSubarrayArray___redArg(){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = ((lean_object*)(l_instCoeSubarrayArray___redArg___closed__0));
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_instCoeSubarrayArray___redArg___boxed(lean_object* v___dummy_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_instCoeSubarrayArray___redArg();
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_instCoeSubarrayArray(lean_object* v_00_u03b1_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = ((lean_object*)(l_instCoeSubarrayArray___redArg___closed__0));
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object* v_s_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_254_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_252_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray(lean_object* v_00_u03b1_255_, lean_object* v_s_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Array_ofSubarray___redArg(v_s_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___lam__0(lean_object* v_it_258_, lean_object* v_acc_259_, lean_object* v_recur_260_){
_start:
{
lean_object* v_array_261_; lean_object* v_start_262_; lean_object* v_stop_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_276_; 
v_array_261_ = lean_ctor_get(v_it_258_, 0);
v_start_262_ = lean_ctor_get(v_it_258_, 1);
v_stop_263_ = lean_ctor_get(v_it_258_, 2);
v_isSharedCheck_276_ = !lean_is_exclusive(v_it_258_);
if (v_isSharedCheck_276_ == 0)
{
v___x_265_ = v_it_258_;
v_isShared_266_ = v_isSharedCheck_276_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_stop_263_);
lean_inc(v_start_262_);
lean_inc(v_array_261_);
lean_dec(v_it_258_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_276_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
uint8_t v___x_267_; 
v___x_267_ = lean_nat_dec_lt(v_start_262_, v_stop_263_);
if (v___x_267_ == 0)
{
lean_del_object(v___x_265_);
lean_dec(v_stop_263_);
lean_dec(v_start_262_);
lean_dec_ref(v_array_261_);
lean_dec_ref(v_recur_260_);
return v_acc_259_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_start_262_, v___x_268_);
lean_inc_ref(v_array_261_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_269_);
v___x_271_ = v___x_265_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_array_261_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_stop_263_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_array_fget(v_array_261_, v_start_262_);
lean_dec(v_start_262_);
lean_dec_ref(v_array_261_);
v___x_273_ = lean_array_push(v_acc_259_, v___x_272_);
v___x_274_ = lean_apply_3(v_recur_260_, v___x_271_, v___x_273_, lean_box(0));
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___lam__2(lean_object* v___f_277_, lean_object* v___f_278_, lean_object* v_x_279_, lean_object* v_y_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v_a_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_283_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_277_, v_x_279_, v___x_282_);
v___x_284_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_278_, v_y_280_, v___x_282_);
v_a_285_ = l_Array_append___redArg(v___x_283_, v___x_284_);
lean_dec(v___x_284_);
v___x_286_ = lean_array_get_size(v_a_285_);
v___x_287_ = l_Array_toSubarray___redArg(v_a_285_, v___x_281_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg(){
_start:
{
lean_object* v___f_292_; 
v___f_292_ = ((lean_object*)(l_Array_instAppendSubarray___redArg___closed__1));
return v___f_292_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___redArg___boxed(lean_object* v___dummy_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Array_instAppendSubarray___redArg();
return v_res_294_;
}
}
static lean_object* _init_l_Array_instAppendSubarray___closed__0(void){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Array_instAppendSubarray___redArg();
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object* v_00_u03b1_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Array_instAppendSubarray___closed__0, &l_Array_instAppendSubarray___closed__0_once, _init_l_Array_instAppendSubarray___closed__0);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr___redArg(lean_object* v_inst_301_, lean_object* v_s_302_){
_start:
{
lean_object* v___f_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___f_303_ = ((lean_object*)(l_Array_instAppendSubarray___redArg___closed__0));
v___x_304_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_305_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_303_, v_s_302_, v___x_304_);
v___x_306_ = l_Array_repr___redArg(v_inst_301_, v___x_305_);
v___x_307_ = ((lean_object*)(l_Array_Subarray_repr___redArg___closed__1));
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr(lean_object* v_00_u03b1_309_, lean_object* v_inst_310_, lean_object* v_s_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Array_Subarray_repr___redArg(v_inst_310_, v_s_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0(lean_object* v_inst_313_, lean_object* v_s_314_, lean_object* v_x_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Array_Subarray_repr___redArg(v_inst_313_, v_s_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0___boxed(lean_object* v_inst_317_, lean_object* v_s_318_, lean_object* v_x_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Array_instReprSubarray___redArg___lam__0(v_inst_317_, v_s_318_, v_x_319_);
lean_dec(v_x_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg(lean_object* v_inst_321_){
_start:
{
lean_object* v___f_322_; 
v___f_322_ = lean_alloc_closure((void*)(l_Array_instReprSubarray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_322_, 0, v_inst_321_);
return v___f_322_;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray(lean_object* v_00_u03b1_323_, lean_object* v_inst_324_){
_start:
{
lean_object* v___f_325_; 
v___f_325_ = lean_alloc_closure((void*)(l_Array_instReprSubarray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_325_, 0, v_inst_324_);
return v___f_325_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__1(lean_object* v___f_327_, lean_object* v_inst_328_, lean_object* v_s_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_330_ = ((lean_object*)(l_Subarray_copy___redArg___closed__0));
v___x_331_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_327_, v_s_329_, v___x_330_);
v___x_332_ = ((lean_object*)(l_Array_instToStringSubarray___redArg___lam__1___closed__0));
v___x_333_ = lean_array_to_list(v___x_331_);
v___x_334_ = l_List_toString___redArg(v_inst_328_, v___x_333_);
v___x_335_ = lean_string_append(v___x_332_, v___x_334_);
lean_dec_ref(v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object* v_inst_336_){
_start:
{
lean_object* v___f_337_; lean_object* v___f_338_; 
v___f_337_ = ((lean_object*)(l_Array_instAppendSubarray___redArg___closed__0));
v___f_338_ = lean_alloc_closure((void*)(l_Array_instToStringSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_338_, 0, v___f_337_);
lean_closure_set(v___f_338_, 1, v_inst_336_);
return v___f_338_;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray(lean_object* v_00_u03b1_339_, lean_object* v_inst_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Array_instToStringSubarray___redArg(v_inst_340_);
return v___x_341_;
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
