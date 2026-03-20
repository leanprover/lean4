// Lean compiler output
// Module: Lean.Data.Iterators.Producers.PersistentHashMap
// Imports: public import Init.Data.Array.Subarray public import Init.Data.Array.Subarray.Split public import Lean.Data.PersistentHashMap import Init.Data.Iterators.Consumers import Init.Omega import Init.Data.Slice.Array.Lemmas import Init.Data.Array.Mem import Init.Data.List.TakeDrop
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
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_done_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consEntries_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consEntries_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consCollision_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consCollision_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_prependNode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_prependNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___lam__0(lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_instIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_instIterator___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_instIterator___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_instIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx(lean_object* v_00_u03b1_7_, lean_object* v_00_u03b2_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___boxed(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_PersistentHashMap_Zipper_ctorIdx(v_00_u03b1_11_, v_00_u03b2_12_, v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(lean_object* v_t_15_, lean_object* v_k_16_){
_start:
{
switch(lean_obj_tag(v_t_15_))
{
case 0:
{
return v_k_16_;
}
case 1:
{
lean_object* v_a_17_; lean_object* v_a_18_; lean_object* v___x_19_; 
v_a_17_ = lean_ctor_get(v_t_15_, 0);
lean_inc_ref(v_a_17_);
v_a_18_ = lean_ctor_get(v_t_15_, 1);
lean_inc(v_a_18_);
lean_dec_ref(v_t_15_);
v___x_19_ = lean_apply_2(v_k_16_, v_a_17_, v_a_18_);
return v___x_19_;
}
default: 
{
lean_object* v_keys_20_; lean_object* v_vals_21_; lean_object* v_a_22_; lean_object* v___x_23_; 
v_keys_20_ = lean_ctor_get(v_t_15_, 0);
lean_inc_ref(v_keys_20_);
v_vals_21_ = lean_ctor_get(v_t_15_, 1);
lean_inc_ref(v_vals_21_);
v_a_22_ = lean_ctor_get(v_t_15_, 2);
lean_inc(v_a_22_);
lean_dec_ref(v_t_15_);
v___x_23_ = lean_apply_4(v_k_16_, v_keys_20_, v_vals_21_, lean_box(0), v_a_22_);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorElim(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_28_, v_k_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorElim___boxed(lean_object* v_00_u03b1_32_, lean_object* v_00_u03b2_33_, lean_object* v_motive_34_, lean_object* v_ctorIdx_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_k_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_PersistentHashMap_Zipper_ctorElim(v_00_u03b1_32_, v_00_u03b2_33_, v_motive_34_, v_ctorIdx_35_, v_t_36_, v_h_37_, v_k_38_);
lean_dec(v_ctorIdx_35_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_done_elim___redArg(lean_object* v_t_40_, lean_object* v_done_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_40_, v_done_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_done_elim(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_done_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_46_, v_done_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consEntries_elim___redArg(lean_object* v_t_50_, lean_object* v_consEntries_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_50_, v_consEntries_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consEntries_elim(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_consEntries_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_56_, v_consEntries_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consCollision_elim___redArg(lean_object* v_t_60_, lean_object* v_consCollision_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_60_, v_consCollision_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consCollision_elim(lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_consCollision_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_66_, v_consCollision_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_prependNode___redArg(lean_object* v_node_70_, lean_object* v_z_71_){
_start:
{
if (lean_obj_tag(v_node_70_) == 0)
{
lean_object* v_es_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_es_72_ = lean_ctor_get(v_node_70_, 0);
lean_inc_ref(v_es_72_);
lean_dec_ref(v_node_70_);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_array_get_size(v_es_72_);
v___x_75_ = l_Array_toSubarray___redArg(v_es_72_, v___x_73_, v___x_74_);
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v_z_71_);
return v___x_76_;
}
else
{
lean_object* v_ks_77_; lean_object* v_vs_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_ks_77_ = lean_ctor_get(v_node_70_, 0);
lean_inc_ref(v_ks_77_);
v_vs_78_ = lean_ctor_get(v_node_70_, 1);
lean_inc_ref(v_vs_78_);
lean_dec_ref(v_node_70_);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_array_get_size(v_ks_77_);
v___x_81_ = l_Array_toSubarray___redArg(v_ks_77_, v___x_79_, v___x_80_);
v___x_82_ = lean_array_get_size(v_vs_78_);
v___x_83_ = l_Array_toSubarray___redArg(v_vs_78_, v___x_79_, v___x_82_);
v___x_84_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_84_, 0, v___x_81_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
lean_ctor_set(v___x_84_, 2, v_z_71_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_prependNode(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_node_87_, lean_object* v_z_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_87_, v_z_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_step___redArg(lean_object* v_it_90_){
_start:
{
switch(lean_obj_tag(v_it_90_))
{
case 0:
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(2);
return v___x_91_;
}
case 1:
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_129_; 
v_a_92_ = lean_ctor_get(v_it_90_, 0);
v_a_93_ = lean_ctor_get(v_it_90_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_it_90_);
if (v_isSharedCheck_129_ == 0)
{
v___x_95_ = v_it_90_;
v_isShared_96_ = v_isSharedCheck_129_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_inc(v_a_92_);
lean_dec(v_it_90_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_129_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v_start_97_; lean_object* v_stop_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_start_97_ = lean_ctor_get(v_a_92_, 1);
v_stop_98_ = lean_ctor_get(v_a_92_, 2);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_nat_sub(v_stop_98_, v_start_97_);
v___x_101_ = lean_nat_dec_lt(v___x_99_, v___x_100_);
lean_dec(v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
lean_del_object(v___x_95_);
lean_dec_ref(v_a_92_);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_a_93_);
return v___x_102_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_z_106_; 
v___x_103_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_92_);
v___x_104_ = l_Subarray_drop___redArg(v_a_92_, v___x_103_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_104_);
v_z_106_ = v___x_95_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_a_93_);
v_z_106_ = v_reuseFailAlloc_128_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; 
v___x_107_ = l_Subarray_get___redArg(v_a_92_, v___x_99_);
lean_dec_ref(v_a_92_);
switch(lean_obj_tag(v___x_107_))
{
case 0:
{
lean_object* v_key_108_; lean_object* v_val_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_117_; 
v_key_108_ = lean_ctor_get(v___x_107_, 0);
v_val_109_ = lean_ctor_get(v___x_107_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_117_ == 0)
{
v___x_111_ = v___x_107_;
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_val_109_);
lean_inc(v_key_108_);
lean_dec(v___x_107_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_key_108_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_val_109_);
v___x_114_ = v_reuseFailAlloc_116_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; 
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v_z_106_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
return v___x_115_;
}
}
}
case 1:
{
lean_object* v_node_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_node_118_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_126_ == 0)
{
v___x_120_ = v___x_107_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_node_118_);
lean_dec(v___x_107_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_118_, v_z_106_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
default: 
{
lean_object* v___x_127_; 
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v_z_106_);
return v___x_127_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_130_; lean_object* v_keys_131_; lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_152_; 
v_vals_130_ = lean_ctor_get(v_it_90_, 1);
v_keys_131_ = lean_ctor_get(v_it_90_, 0);
v_a_132_ = lean_ctor_get(v_it_90_, 2);
v_isSharedCheck_152_ = !lean_is_exclusive(v_it_90_);
if (v_isSharedCheck_152_ == 0)
{
v___x_134_ = v_it_90_;
v_isShared_135_ = v_isSharedCheck_152_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_inc(v_vals_130_);
lean_inc(v_keys_131_);
lean_dec(v_it_90_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_152_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_start_136_; lean_object* v_stop_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_start_136_ = lean_ctor_get(v_vals_130_, 1);
v_stop_137_ = lean_ctor_get(v_vals_130_, 2);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_nat_sub(v_stop_137_, v_start_136_);
v___x_140_ = lean_nat_dec_lt(v___x_138_, v___x_139_);
lean_dec(v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
lean_del_object(v___x_134_);
lean_dec_ref(v_keys_131_);
lean_dec_ref(v_vals_130_);
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v_a_132_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_142_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_131_);
v___x_143_ = l_Subarray_drop___redArg(v_keys_131_, v___x_142_);
lean_inc_ref(v_vals_130_);
v___x_144_ = l_Subarray_drop___redArg(v_vals_130_, v___x_142_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_144_);
lean_ctor_set(v___x_134_, 0, v___x_143_);
v___x_146_ = v___x_134_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_151_, 2, v_a_132_);
v___x_146_ = v_reuseFailAlloc_151_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = l_Subarray_get___redArg(v_keys_131_, v___x_138_);
lean_dec_ref(v_keys_131_);
v___x_148_ = l_Subarray_get___redArg(v_vals_130_, v___x_138_);
lean_dec_ref(v_vals_130_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_146_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
return v___x_150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_step(lean_object* v_00_u03b1_153_, lean_object* v_00_u03b2_154_, lean_object* v_it_155_){
_start:
{
switch(lean_obj_tag(v_it_155_))
{
case 0:
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(2);
return v___x_156_;
}
case 1:
{
lean_object* v_a_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_194_; 
v_a_157_ = lean_ctor_get(v_it_155_, 0);
v_a_158_ = lean_ctor_get(v_it_155_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_it_155_);
if (v_isSharedCheck_194_ == 0)
{
v___x_160_ = v_it_155_;
v_isShared_161_ = v_isSharedCheck_194_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_inc(v_a_157_);
lean_dec(v_it_155_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_194_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_start_162_; lean_object* v_stop_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v_start_162_ = lean_ctor_get(v_a_157_, 1);
v_stop_163_ = lean_ctor_get(v_a_157_, 2);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_nat_sub(v_stop_163_, v_start_162_);
v___x_166_ = lean_nat_dec_lt(v___x_164_, v___x_165_);
lean_dec(v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
lean_del_object(v___x_160_);
lean_dec_ref(v_a_157_);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v_a_158_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_z_171_; 
v___x_168_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_157_);
v___x_169_ = l_Subarray_drop___redArg(v_a_157_, v___x_168_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_169_);
v_z_171_ = v___x_160_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_a_158_);
v_z_171_ = v_reuseFailAlloc_193_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; 
v___x_172_ = l_Subarray_get___redArg(v_a_157_, v___x_164_);
lean_dec_ref(v_a_157_);
switch(lean_obj_tag(v___x_172_))
{
case 0:
{
lean_object* v_key_173_; lean_object* v_val_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_182_; 
v_key_173_ = lean_ctor_get(v___x_172_, 0);
v_val_174_ = lean_ctor_get(v___x_172_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_182_ == 0)
{
v___x_176_ = v___x_172_;
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_val_174_);
lean_inc(v_key_173_);
lean_dec(v___x_172_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_key_173_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_val_174_);
v___x_179_ = v_reuseFailAlloc_181_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_z_171_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
return v___x_180_;
}
}
}
case 1:
{
lean_object* v_node_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_node_183_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_191_ == 0)
{
v___x_185_ = v___x_172_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_node_183_);
lean_dec(v___x_172_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_183_, v_z_171_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
default: 
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_z_171_);
return v___x_192_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_195_; lean_object* v_keys_196_; lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_217_; 
v_vals_195_ = lean_ctor_get(v_it_155_, 1);
v_keys_196_ = lean_ctor_get(v_it_155_, 0);
v_a_197_ = lean_ctor_get(v_it_155_, 2);
v_isSharedCheck_217_ = !lean_is_exclusive(v_it_155_);
if (v_isSharedCheck_217_ == 0)
{
v___x_199_ = v_it_155_;
v_isShared_200_ = v_isSharedCheck_217_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_inc(v_vals_195_);
lean_inc(v_keys_196_);
lean_dec(v_it_155_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_217_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_start_201_; lean_object* v_stop_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_start_201_ = lean_ctor_get(v_vals_195_, 1);
v_stop_202_ = lean_ctor_get(v_vals_195_, 2);
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = lean_nat_sub(v_stop_202_, v_start_201_);
v___x_205_ = lean_nat_dec_lt(v___x_203_, v___x_204_);
lean_dec(v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_del_object(v___x_199_);
lean_dec_ref(v_keys_196_);
lean_dec_ref(v_vals_195_);
v___x_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_206_, 0, v_a_197_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_207_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_196_);
v___x_208_ = l_Subarray_drop___redArg(v_keys_196_, v___x_207_);
lean_inc_ref(v_vals_195_);
v___x_209_ = l_Subarray_drop___redArg(v_vals_195_, v___x_207_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v___x_209_);
lean_ctor_set(v___x_199_, 0, v___x_208_);
v___x_211_ = v___x_199_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_a_197_);
v___x_211_ = v_reuseFailAlloc_216_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_212_ = l_Subarray_get___redArg(v_keys_196_, v___x_203_);
lean_dec_ref(v_keys_196_);
v___x_213_ = l_Subarray_get___redArg(v_vals_195_, v___x_203_);
lean_dec_ref(v_vals_195_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_211_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
return v___x_215_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___lam__0(lean_object* v_it_218_){
_start:
{
switch(lean_obj_tag(v_it_218_))
{
case 0:
{
lean_object* v___x_219_; 
v___x_219_ = lean_box(2);
return v___x_219_;
}
case 1:
{
lean_object* v_a_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_257_; 
v_a_220_ = lean_ctor_get(v_it_218_, 0);
v_a_221_ = lean_ctor_get(v_it_218_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_it_218_);
if (v_isSharedCheck_257_ == 0)
{
v___x_223_ = v_it_218_;
v_isShared_224_ = v_isSharedCheck_257_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_inc(v_a_220_);
lean_dec(v_it_218_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_257_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_start_225_; lean_object* v_stop_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_start_225_ = lean_ctor_get(v_a_220_, 1);
v_stop_226_ = lean_ctor_get(v_a_220_, 2);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_nat_sub(v_stop_226_, v_start_225_);
v___x_229_ = lean_nat_dec_lt(v___x_227_, v___x_228_);
lean_dec(v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
lean_del_object(v___x_223_);
lean_dec_ref(v_a_220_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v_a_221_);
return v___x_230_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_z_234_; 
v___x_231_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_220_);
v___x_232_ = l_Subarray_drop___redArg(v_a_220_, v___x_231_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_232_);
v_z_234_ = v___x_223_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_a_221_);
v_z_234_ = v_reuseFailAlloc_256_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; 
v___x_235_ = l_Subarray_get___redArg(v_a_220_, v___x_227_);
lean_dec_ref(v_a_220_);
switch(lean_obj_tag(v___x_235_))
{
case 0:
{
lean_object* v_key_236_; lean_object* v_val_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_245_; 
v_key_236_ = lean_ctor_get(v___x_235_, 0);
v_val_237_ = lean_ctor_get(v___x_235_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_245_ == 0)
{
v___x_239_ = v___x_235_;
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_val_237_);
lean_inc(v_key_236_);
lean_dec(v___x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_key_236_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_val_237_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_z_234_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
return v___x_243_;
}
}
}
case 1:
{
lean_object* v_node_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_254_; 
v_node_246_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_254_ == 0)
{
v___x_248_ = v___x_235_;
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_node_246_);
lean_dec(v___x_235_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_246_, v_z_234_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_250_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
default: 
{
lean_object* v___x_255_; 
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v_z_234_);
return v___x_255_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_258_; lean_object* v_keys_259_; lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_280_; 
v_vals_258_ = lean_ctor_get(v_it_218_, 1);
v_keys_259_ = lean_ctor_get(v_it_218_, 0);
v_a_260_ = lean_ctor_get(v_it_218_, 2);
v_isSharedCheck_280_ = !lean_is_exclusive(v_it_218_);
if (v_isSharedCheck_280_ == 0)
{
v___x_262_ = v_it_218_;
v_isShared_263_ = v_isSharedCheck_280_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_inc(v_vals_258_);
lean_inc(v_keys_259_);
lean_dec(v_it_218_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_280_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_start_264_; lean_object* v_stop_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_start_264_ = lean_ctor_get(v_vals_258_, 1);
v_stop_265_ = lean_ctor_get(v_vals_258_, 2);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_nat_sub(v_stop_265_, v_start_264_);
v___x_268_ = lean_nat_dec_lt(v___x_266_, v___x_267_);
lean_dec(v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_del_object(v___x_262_);
lean_dec_ref(v_keys_259_);
lean_dec_ref(v_vals_258_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_a_260_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_270_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_259_);
v___x_271_ = l_Subarray_drop___redArg(v_keys_259_, v___x_270_);
lean_inc_ref(v_vals_258_);
v___x_272_ = l_Subarray_drop___redArg(v_vals_258_, v___x_270_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_272_);
lean_ctor_set(v___x_262_, 0, v___x_271_);
v___x_274_ = v___x_262_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_a_260_);
v___x_274_ = v_reuseFailAlloc_279_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = l_Subarray_get___redArg(v_keys_259_, v___x_266_);
lean_dec_ref(v_keys_259_);
v___x_276_ = l_Subarray_get___redArg(v_vals_258_, v___x_266_);
lean_dec_ref(v_vals_258_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_274_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
return v___x_278_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator(lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_){
_start:
{
lean_object* v___f_284_; 
v___f_284_ = ((lean_object*)(l_Lean_PersistentHashMap_instIterator___closed__0));
return v___f_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(lean_object* v_es_285_, lean_object* v_i_286_){
_start:
{
lean_object* v___y_288_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_array_get_size(v_es_285_);
v___x_294_ = lean_nat_dec_lt(v_i_286_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_unsigned_to_nat(0u);
return v___x_295_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_array_fget_borrowed(v_es_285_, v_i_286_);
if (lean_obj_tag(v___x_296_) == 1)
{
lean_object* v_node_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_node_297_ = lean_ctor_get(v___x_296_, 0);
v___x_298_ = lean_unsigned_to_nat(2u);
v___x_299_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_297_);
v___x_300_ = lean_nat_add(v___x_298_, v___x_299_);
lean_dec(v___x_299_);
v___y_288_ = v___x_300_;
goto v___jp_287_;
}
else
{
lean_object* v___x_301_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___y_288_ = v___x_301_;
goto v___jp_287_;
}
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_i_286_, v___x_289_);
v___x_291_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_285_, v___x_290_);
lean_dec(v___x_290_);
v___x_292_ = lean_nat_add(v___y_288_, v___x_291_);
lean_dec(v___x_291_);
lean_dec(v___y_288_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___redArg(lean_object* v_node_302_){
_start:
{
if (lean_obj_tag(v_node_302_) == 0)
{
lean_object* v_es_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_es_303_ = lean_ctor_get(v_node_302_, 0);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_303_, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v_vs_306_; lean_object* v___x_307_; 
v_vs_306_ = lean_ctor_get(v_node_302_, 1);
v___x_307_ = lean_array_get_size(v_vs_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___redArg___boxed(lean_object* v_node_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_308_);
lean_dec_ref(v_node_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg___boxed(lean_object* v_es_310_, lean_object* v_i_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_310_, v_i_311_);
lean_dec(v_i_311_);
lean_dec_ref(v_es_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(lean_object* v_00_u03b1_313_, lean_object* v_00_u03b2_314_, lean_object* v_es_315_, lean_object* v_i_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_315_, v_i_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___boxed(lean_object* v_00_u03b1_318_, lean_object* v_00_u03b2_319_, lean_object* v_es_320_, lean_object* v_i_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(v_00_u03b1_318_, v_00_u03b2_319_, v_es_320_, v_i_321_);
lean_dec(v_i_321_);
lean_dec_ref(v_es_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure(lean_object* v_00_u03b1_323_, lean_object* v_00_u03b2_324_, lean_object* v_node_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___boxed(lean_object* v_00_u03b1_327_, lean_object* v_00_u03b2_328_, lean_object* v_node_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_PersistentHashMap_Node_measure(v_00_u03b1_327_, v_00_u03b2_328_, v_node_329_);
lean_dec_ref(v_node_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter___redArg(lean_object* v_x_331_, lean_object* v_h__1_332_, lean_object* v_h__2_333_, lean_object* v_h__3_334_){
_start:
{
switch(lean_obj_tag(v_x_331_))
{
case 0:
{
lean_object* v_key_335_; lean_object* v_val_336_; lean_object* v___x_337_; 
lean_dec(v_h__3_334_);
lean_dec(v_h__1_332_);
v_key_335_ = lean_ctor_get(v_x_331_, 0);
lean_inc(v_key_335_);
v_val_336_ = lean_ctor_get(v_x_331_, 1);
lean_inc(v_val_336_);
lean_dec_ref(v_x_331_);
v___x_337_ = lean_apply_3(v_h__2_333_, v_key_335_, v_val_336_, lean_box(0));
return v___x_337_;
}
case 1:
{
lean_object* v_node_338_; lean_object* v___x_339_; 
lean_dec(v_h__2_333_);
lean_dec(v_h__1_332_);
v_node_338_ = lean_ctor_get(v_x_331_, 0);
lean_inc(v_node_338_);
lean_dec_ref(v_x_331_);
v___x_339_ = lean_apply_2(v_h__3_334_, v_node_338_, lean_box(0));
return v___x_339_;
}
default: 
{
lean_object* v___x_340_; 
lean_dec(v_h__3_334_);
lean_dec(v_h__2_333_);
v___x_340_ = lean_apply_1(v_h__1_332_, lean_box(0));
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_motive_343_, lean_object* v_x_344_, lean_object* v_h__1_345_, lean_object* v_h__2_346_, lean_object* v_h__3_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter___redArg(v_x_344_, v_h__1_345_, v_h__2_346_, v_h__3_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter___redArg(lean_object* v_node_349_, lean_object* v_h__1_350_, lean_object* v_h__2_351_){
_start:
{
if (lean_obj_tag(v_node_349_) == 0)
{
lean_object* v_es_352_; lean_object* v___x_353_; 
lean_dec(v_h__2_351_);
v_es_352_ = lean_ctor_get(v_node_349_, 0);
lean_inc_ref(v_es_352_);
lean_dec_ref(v_node_349_);
v___x_353_ = lean_apply_1(v_h__1_350_, v_es_352_);
return v___x_353_;
}
else
{
lean_object* v_ks_354_; lean_object* v_vs_355_; lean_object* v___x_356_; 
lean_dec(v_h__1_350_);
v_ks_354_ = lean_ctor_get(v_node_349_, 0);
lean_inc_ref(v_ks_354_);
v_vs_355_ = lean_ctor_get(v_node_349_, 1);
lean_inc_ref(v_vs_355_);
lean_dec_ref(v_node_349_);
v___x_356_ = lean_apply_3(v_h__2_351_, v_ks_354_, v_vs_355_, lean_box(0));
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter(lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_motive_359_, lean_object* v_node_360_, lean_object* v_h__1_361_, lean_object* v_h__2_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter___redArg(v_node_360_, v_h__1_361_, v_h__2_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg(lean_object* v_entry_364_){
_start:
{
if (lean_obj_tag(v_entry_364_) == 1)
{
lean_object* v_node_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_node_365_ = lean_ctor_get(v_entry_364_, 0);
v___x_366_ = lean_unsigned_to_nat(2u);
v___x_367_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_365_);
v___x_368_ = lean_nat_add(v___x_366_, v___x_367_);
lean_dec(v___x_367_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = lean_unsigned_to_nat(1u);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg___boxed(lean_object* v_entry_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_370_);
lean_dec(v_entry_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_entry_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___boxed(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v_entry_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_PersistentHashMap_Entry_measure(v_00_u03b1_376_, v_00_u03b2_377_, v_entry_378_);
lean_dec(v_entry_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(lean_object* v_init_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_inc(v_init_380_);
return v_init_380_;
}
else
{
lean_object* v_head_382_; lean_object* v_tail_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_head_382_ = lean_ctor_get(v_x_381_, 0);
v_tail_383_ = lean_ctor_get(v_x_381_, 1);
v___x_384_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_380_, v_tail_383_);
v___x_385_ = lean_nat_add(v_head_382_, v___x_384_);
lean_dec(v___x_384_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2___boxed(lean_object* v_init_386_, lean_object* v_x_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_386_, v_x_387_);
lean_dec(v_x_387_);
lean_dec(v_init_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(lean_object* v_l_389_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v___x_390_, v_l_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2___boxed(lean_object* v_l_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v_l_392_);
lean_dec(v_l_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
if (lean_obj_tag(v_a_394_) == 0)
{
lean_object* v___x_396_; 
v___x_396_ = l_List_reverse___redArg(v_a_395_);
return v___x_396_;
}
else
{
lean_object* v_head_397_; lean_object* v_tail_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_407_; 
v_head_397_ = lean_ctor_get(v_a_394_, 0);
v_tail_398_ = lean_ctor_get(v_a_394_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_a_394_);
if (v_isSharedCheck_407_ == 0)
{
v___x_400_ = v_a_394_;
v_isShared_401_ = v_isSharedCheck_407_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_tail_398_);
lean_inc(v_head_397_);
lean_dec(v_a_394_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_407_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_head_397_);
lean_dec(v_head_397_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v_a_395_);
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_a_395_);
v___x_404_ = v_reuseFailAlloc_406_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
v_a_394_ = v_tail_398_;
v_a_395_ = v___x_404_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(lean_object* v_a_408_, lean_object* v_b_409_){
_start:
{
lean_object* v_array_410_; lean_object* v_start_411_; lean_object* v_stop_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_425_; 
v_array_410_ = lean_ctor_get(v_a_408_, 0);
v_start_411_ = lean_ctor_get(v_a_408_, 1);
v_stop_412_ = lean_ctor_get(v_a_408_, 2);
v_isSharedCheck_425_ = !lean_is_exclusive(v_a_408_);
if (v_isSharedCheck_425_ == 0)
{
v___x_414_ = v_a_408_;
v_isShared_415_ = v_isSharedCheck_425_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_stop_412_);
lean_inc(v_start_411_);
lean_inc(v_array_410_);
lean_dec(v_a_408_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_425_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint8_t v___x_416_; 
v___x_416_ = lean_nat_dec_lt(v_start_411_, v_stop_412_);
if (v___x_416_ == 0)
{
lean_del_object(v___x_414_);
lean_dec(v_stop_412_);
lean_dec(v_start_411_);
lean_dec_ref(v_array_410_);
return v_b_409_;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_add(v_start_411_, v___x_417_);
lean_inc_ref(v_array_410_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___x_418_);
v___x_420_ = v___x_414_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_array_410_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_stop_412_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_array_fget(v_array_410_, v_start_411_);
lean_dec(v_start_411_);
lean_dec_ref(v_array_410_);
v___x_422_ = lean_array_push(v_b_409_, v___x_421_);
v_a_408_ = v___x_420_;
v_b_409_ = v___x_422_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure___redArg(lean_object* v_es_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_429_ = ((lean_object*)(l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0));
v___x_430_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_es_428_, v___x_429_);
v___x_431_ = lean_array_to_list(v___x_430_);
v___x_432_ = lean_box(0);
v___x_433_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v___x_431_, v___x_432_);
v___x_434_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v___x_433_);
lean_dec(v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure(lean_object* v_00_u03b1_435_, lean_object* v_00_u03b2_436_, lean_object* v_es_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_es_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_inst_441_, lean_object* v_R_442_, lean_object* v_a_443_, lean_object* v_b_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_a_443_, v_b_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v_a_448_, v_a_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure___redArg(lean_object* v_x_451_){
_start:
{
switch(lean_obj_tag(v_x_451_))
{
case 0:
{
lean_object* v___x_452_; 
v___x_452_ = lean_unsigned_to_nat(0u);
return v___x_452_;
}
case 1:
{
lean_object* v_a_453_; lean_object* v_a_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_a_453_ = lean_ctor_get(v_x_451_, 0);
lean_inc_ref(v_a_453_);
v_a_454_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_a_454_);
lean_dec_ref(v_x_451_);
v___x_455_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_a_453_);
v___x_456_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_454_);
v___x_457_ = lean_nat_add(v___x_455_, v___x_456_);
lean_dec(v___x_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_add(v___x_457_, v___x_458_);
lean_dec(v___x_457_);
return v___x_459_;
}
default: 
{
lean_object* v_vals_460_; lean_object* v_a_461_; lean_object* v_start_462_; lean_object* v_stop_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_vals_460_ = lean_ctor_get(v_x_451_, 1);
lean_inc_ref(v_vals_460_);
v_a_461_ = lean_ctor_get(v_x_451_, 2);
lean_inc(v_a_461_);
lean_dec_ref(v_x_451_);
v_start_462_ = lean_ctor_get(v_vals_460_, 1);
lean_inc(v_start_462_);
v_stop_463_ = lean_ctor_get(v_vals_460_, 2);
lean_inc(v_stop_463_);
lean_dec_ref(v_vals_460_);
v___x_464_ = lean_nat_sub(v_stop_463_, v_start_462_);
lean_dec(v_start_462_);
lean_dec(v_stop_463_);
v___x_465_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_461_);
v___x_466_ = lean_nat_add(v___x_464_, v___x_465_);
lean_dec(v___x_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_add(v___x_466_, v___x_467_);
lean_dec(v___x_466_);
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_x_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(lean_object* v_x_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_, lean_object* v_h__3_476_){
_start:
{
switch(lean_obj_tag(v_x_473_))
{
case 0:
{
lean_object* v_key_477_; lean_object* v_val_478_; lean_object* v___x_479_; 
lean_dec(v_h__3_476_);
lean_dec(v_h__1_474_);
v_key_477_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_key_477_);
v_val_478_ = lean_ctor_get(v_x_473_, 1);
lean_inc(v_val_478_);
lean_dec_ref(v_x_473_);
v___x_479_ = lean_apply_2(v_h__2_475_, v_key_477_, v_val_478_);
return v___x_479_;
}
case 1:
{
lean_object* v_node_480_; lean_object* v___x_481_; 
lean_dec(v_h__2_475_);
lean_dec(v_h__1_474_);
v_node_480_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_node_480_);
lean_dec_ref(v_x_473_);
v___x_481_ = lean_apply_1(v_h__3_476_, v_node_480_);
return v___x_481_;
}
default: 
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v_h__3_476_);
lean_dec(v_h__2_475_);
v___x_482_ = lean_box(0);
v___x_483_ = lean_apply_1(v_h__1_474_, v___x_482_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_motive_486_, lean_object* v_x_487_, lean_object* v_h__1_488_, lean_object* v_h__2_489_, lean_object* v_h__3_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(v_x_487_, v_h__1_488_, v_h__2_489_, v_h__3_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(lean_object* v_x_492_, lean_object* v_h__1_493_, lean_object* v_h__2_494_, lean_object* v_h__3_495_){
_start:
{
switch(lean_obj_tag(v_x_492_))
{
case 0:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v_h__3_495_);
lean_dec(v_h__2_494_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_apply_1(v_h__1_493_, v___x_496_);
return v___x_497_;
}
case 1:
{
lean_object* v_a_498_; lean_object* v_a_499_; lean_object* v___x_500_; 
lean_dec(v_h__3_495_);
lean_dec(v_h__1_493_);
v_a_498_ = lean_ctor_get(v_x_492_, 0);
lean_inc_ref(v_a_498_);
v_a_499_ = lean_ctor_get(v_x_492_, 1);
lean_inc(v_a_499_);
lean_dec_ref(v_x_492_);
v___x_500_ = lean_apply_2(v_h__2_494_, v_a_498_, v_a_499_);
return v___x_500_;
}
default: 
{
lean_object* v_keys_501_; lean_object* v_vals_502_; lean_object* v_a_503_; lean_object* v___x_504_; 
lean_dec(v_h__2_494_);
lean_dec(v_h__1_493_);
v_keys_501_ = lean_ctor_get(v_x_492_, 0);
lean_inc_ref(v_keys_501_);
v_vals_502_ = lean_ctor_get(v_x_492_, 1);
lean_inc_ref(v_vals_502_);
v_a_503_ = lean_ctor_get(v_x_492_, 2);
lean_inc(v_a_503_);
lean_dec_ref(v_x_492_);
v___x_504_ = lean_apply_4(v_h__3_495_, v_keys_501_, v_vals_502_, lean_box(0), v_a_503_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter(lean_object* v_00_u03b1_505_, lean_object* v_00_u03b2_506_, lean_object* v_motive_507_, lean_object* v_x_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_, lean_object* v_h__3_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(v_x_508_, v_h__1_509_, v_h__2_510_, v_h__3_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation(lean_object* v_00_u03b1_513_, lean_object* v_00_u03b2_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_box(0);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_516_, lean_object* v_recur_517_, lean_object* v_it_518_, lean_object* v_____do__lift_519_){
_start:
{
if (lean_obj_tag(v_____do__lift_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
lean_dec(v_it_518_);
lean_dec(v_recur_517_);
v_a_520_ = lean_ctor_get(v_____do__lift_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref(v_____do__lift_519_);
v___x_521_ = lean_apply_2(v_toPure_516_, lean_box(0), v_a_520_);
return v___x_521_;
}
else
{
lean_object* v_a_522_; lean_object* v___x_523_; 
lean_dec(v_toPure_516_);
v_a_522_ = lean_ctor_get(v_____do__lift_519_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v_____do__lift_519_);
v___x_523_ = lean_apply_4(v_recur_517_, v_it_518_, v_a_522_, lean_box(0), lean_box(0));
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_524_, lean_object* v_recur_525_, lean_object* v___y_526_, lean_object* v_acc_527_, lean_object* v_toBind_528_, lean_object* v_s_529_){
_start:
{
switch(lean_obj_tag(v_s_529_))
{
case 0:
{
lean_object* v_it_530_; lean_object* v_out_531_; lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_it_530_ = lean_ctor_get(v_s_529_, 0);
lean_inc(v_it_530_);
v_out_531_ = lean_ctor_get(v_s_529_, 1);
lean_inc(v_out_531_);
lean_dec_ref(v_s_529_);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_532_, 0, v_toPure_524_);
lean_closure_set(v___f_532_, 1, v_recur_525_);
lean_closure_set(v___f_532_, 2, v_it_530_);
v___x_533_ = lean_apply_3(v___y_526_, v_out_531_, lean_box(0), v_acc_527_);
v___x_534_ = lean_apply_4(v_toBind_528_, lean_box(0), lean_box(0), v___x_533_, v___f_532_);
return v___x_534_;
}
case 1:
{
lean_object* v_it_535_; lean_object* v___x_536_; 
lean_dec(v_toBind_528_);
lean_dec(v___y_526_);
lean_dec(v_toPure_524_);
v_it_535_ = lean_ctor_get(v_s_529_, 0);
lean_inc(v_it_535_);
lean_dec_ref(v_s_529_);
v___x_536_ = lean_apply_4(v_recur_525_, v_it_535_, v_acc_527_, lean_box(0), lean_box(0));
return v___x_536_;
}
default: 
{
lean_object* v___x_537_; 
lean_dec(v_toBind_528_);
lean_dec(v___y_526_);
lean_dec(v_recur_525_);
v___x_537_ = lean_apply_2(v_toPure_524_, lean_box(0), v_acc_527_);
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_538_, lean_object* v___y_539_, lean_object* v_toBind_540_, lean_object* v_lift_541_, lean_object* v_it_542_, lean_object* v_acc_543_, lean_object* v_hP_544_, lean_object* v_recur_545_){
_start:
{
lean_object* v___f_546_; 
v___f_546_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_546_, 0, v_toPure_538_);
lean_closure_set(v___f_546_, 1, v_recur_545_);
lean_closure_set(v___f_546_, 2, v___y_539_);
lean_closure_set(v___f_546_, 3, v_acc_543_);
lean_closure_set(v___f_546_, 4, v_toBind_540_);
switch(lean_obj_tag(v_it_542_))
{
case 0:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_box(2);
v___x_548_ = lean_apply_4(v_lift_541_, lean_box(0), lean_box(0), v___f_546_, v___x_547_);
return v___x_548_;
}
case 1:
{
lean_object* v_a_549_; lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_590_; 
v_a_549_ = lean_ctor_get(v_it_542_, 0);
v_a_550_ = lean_ctor_get(v_it_542_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_it_542_);
if (v_isSharedCheck_590_ == 0)
{
v___x_552_ = v_it_542_;
v_isShared_553_ = v_isSharedCheck_590_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_inc(v_a_549_);
lean_dec(v_it_542_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_590_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v_start_554_; lean_object* v_stop_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_start_554_ = lean_ctor_get(v_a_549_, 1);
v_stop_555_ = lean_ctor_get(v_a_549_, 2);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_nat_sub(v_stop_555_, v_start_554_);
v___x_558_ = lean_nat_dec_lt(v___x_556_, v___x_557_);
lean_dec(v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_del_object(v___x_552_);
lean_dec_ref(v_a_549_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_a_550_);
v___x_560_ = lean_apply_4(v_lift_541_, lean_box(0), lean_box(0), v___f_546_, v___x_559_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_z_564_; 
v___x_561_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_549_);
v___x_562_ = l_Subarray_drop___redArg(v_a_549_, v___x_561_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_562_);
v_z_564_ = v___x_552_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_a_550_);
v_z_564_ = v_reuseFailAlloc_589_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; 
v___x_565_ = l_Subarray_get___redArg(v_a_549_, v___x_556_);
lean_dec_ref(v_a_549_);
switch(lean_obj_tag(v___x_565_))
{
case 0:
{
lean_object* v_key_566_; lean_object* v_val_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_576_; 
v_key_566_ = lean_ctor_get(v___x_565_, 0);
v_val_567_ = lean_ctor_get(v___x_565_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_576_ == 0)
{
v___x_569_ = v___x_565_;
v_isShared_570_ = v_isSharedCheck_576_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_val_567_);
lean_inc(v_key_566_);
lean_dec(v___x_565_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_576_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_key_566_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_val_567_);
v___x_572_ = v_reuseFailAlloc_575_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_z_564_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_apply_4(v_lift_541_, lean_box(0), lean_box(0), v___f_546_, v___x_573_);
return v___x_574_;
}
}
}
case 1:
{
lean_object* v_node_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_586_; 
v_node_577_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_586_ == 0)
{
v___x_579_ = v___x_565_;
v_isShared_580_ = v_isSharedCheck_586_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_node_577_);
lean_dec(v___x_565_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_586_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_577_, v_z_564_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_581_);
v___x_583_ = v___x_579_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_585_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; 
v___x_584_ = lean_apply_4(v_lift_541_, lean_box(0), lean_box(0), v___f_546_, v___x_583_);
return v___x_584_;
}
}
}
default: 
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v_z_564_);
v___x_588_ = lean_apply_4(v_lift_541_, lean_box(0), lean_box(0), v___f_546_, v___x_587_);
return v___x_588_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_591_; lean_object* v_keys_592_; lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_615_; 
v_vals_591_ = lean_ctor_get(v_it_542_, 1);
v_keys_592_ = lean_ctor_get(v_it_542_, 0);
v_a_593_ = lean_ctor_get(v_it_542_, 2);
v_isSharedCheck_615_ = !lean_is_exclusive(v_it_542_);
if (v_isSharedCheck_615_ == 0)
{
v___x_595_ = v_it_542_;
v_isShared_596_ = v_isSharedCheck_615_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_inc(v_vals_591_);
lean_inc(v_keys_592_);
lean_dec(v_it_542_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_615_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_start_597_; lean_object* v_stop_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_start_597_ = lean_ctor_get(v_vals_591_, 1);
v_stop_598_ = lean_ctor_get(v_vals_591_, 2);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_nat_sub(v_stop_598_, v_start_597_);
v___x_601_ = lean_nat_dec_lt(v___x_599_, v___x_600_);
lean_dec(v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_del_object(v___x_595_);
lean_dec_ref(v_keys_592_);
lean_dec_ref(v_vals_591_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v_a_593_);
v___x_603_ = lean_apply_4(v_lift_541_, lean_box(0), lean_box(0), v___f_546_, v___x_602_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_604_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_592_);
v___x_605_ = l_Subarray_drop___redArg(v_keys_592_, v___x_604_);
lean_inc_ref(v_vals_591_);
v___x_606_ = l_Subarray_drop___redArg(v_vals_591_, v___x_604_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___x_606_);
lean_ctor_set(v___x_595_, 0, v___x_605_);
v___x_608_ = v___x_595_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_a_593_);
v___x_608_ = v_reuseFailAlloc_614_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_609_ = l_Subarray_get___redArg(v_keys_592_, v___x_599_);
lean_dec_ref(v_keys_592_);
v___x_610_ = l_Subarray_get___redArg(v_vals_591_, v___x_599_);
lean_dec_ref(v_vals_591_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_608_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_apply_4(v_lift_541_, lean_box(0), lean_box(0), v___f_546_, v___x_612_);
return v___x_613_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3(lean_object* v_inst_616_, lean_object* v_lift_617_, lean_object* v_00_u03b3_618_, lean_object* v_Pl_619_, lean_object* v_it_620_, lean_object* v_init_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_toApplicative_623_; lean_object* v_toBind_624_; lean_object* v_toPure_625_; lean_object* v___f_626_; lean_object* v___x_627_; 
v_toApplicative_623_ = lean_ctor_get(v_inst_616_, 0);
lean_inc_ref(v_toApplicative_623_);
v_toBind_624_ = lean_ctor_get(v_inst_616_, 1);
lean_inc(v_toBind_624_);
lean_dec_ref(v_inst_616_);
v_toPure_625_ = lean_ctor_get(v_toApplicative_623_, 1);
lean_inc(v_toPure_625_);
lean_dec_ref(v_toApplicative_623_);
v___f_626_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_626_, 0, v_toPure_625_);
lean_closure_set(v___f_626_, 1, v___y_622_);
lean_closure_set(v___f_626_, 2, v_toBind_624_);
lean_closure_set(v___f_626_, 3, v_lift_617_);
v___x_627_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_626_, v_it_620_, v_init_621_, lean_box(0));
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg(lean_object* v_inst_628_){
_start:
{
lean_object* v___f_629_; 
v___f_629_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_629_, 0, v_inst_628_);
return v___f_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop(lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_n_632_, lean_object* v_inst_633_){
_start:
{
lean_object* v___f_634_; 
v___f_634_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_634_, 0, v_inst_633_);
return v___f_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___redArg(lean_object* v_map_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(0);
v___x_637_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_635_, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter(lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_map_642_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_box(0);
v___x_644_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_642_, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___boxed(lean_object* v_00_u03b1_645_, lean_object* v_00_u03b2_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_map_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_PersistentHashMap_iter(v_00_u03b1_645_, v_00_u03b2_646_, v_inst_647_, v_inst_648_, v_map_649_);
lean_dec_ref(v_inst_648_);
lean_dec_ref(v_inst_647_);
return v_res_650_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Iterators_Producers_PersistentHashMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
}
#ifdef __cplusplus
}
#endif
