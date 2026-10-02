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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_instIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_instIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_instIterator___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_instIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg___boxed(lean_object*);
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
lean_dec_ref_known(v_t_15_, 2);
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
lean_dec_ref_known(v_t_15_, 3);
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
lean_dec_ref_known(v_node_70_, 1);
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
lean_dec_ref_known(v_node_70_, 2);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___redArg___lam__0(lean_object* v_it_218_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___redArg(){
_start:
{
lean_object* v___f_283_; 
v___f_283_ = ((lean_object*)(l_Lean_PersistentHashMap_instIterator___redArg___closed__0));
return v___f_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___redArg___boxed(lean_object* v___dummy_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_PersistentHashMap_instIterator___redArg();
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator(lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_){
_start:
{
lean_object* v___f_288_; 
v___f_288_ = ((lean_object*)(l_Lean_PersistentHashMap_instIterator___redArg___closed__0));
return v___f_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(lean_object* v_es_289_, lean_object* v_i_290_){
_start:
{
lean_object* v___y_292_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_array_get_size(v_es_289_);
v___x_298_ = lean_nat_dec_lt(v_i_290_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_unsigned_to_nat(0u);
return v___x_299_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_array_fget_borrowed(v_es_289_, v_i_290_);
if (lean_obj_tag(v___x_300_) == 1)
{
lean_object* v_node_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_node_301_ = lean_ctor_get(v___x_300_, 0);
v___x_302_ = lean_unsigned_to_nat(2u);
v___x_303_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_301_);
v___x_304_ = lean_nat_add(v___x_302_, v___x_303_);
lean_dec(v___x_303_);
v___y_292_ = v___x_304_;
goto v___jp_291_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = lean_unsigned_to_nat(1u);
v___y_292_ = v___x_305_;
goto v___jp_291_;
}
}
v___jp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_i_290_, v___x_293_);
v___x_295_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_289_, v___x_294_);
lean_dec(v___x_294_);
v___x_296_ = lean_nat_add(v___y_292_, v___x_295_);
lean_dec(v___x_295_);
lean_dec(v___y_292_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___redArg(lean_object* v_node_306_){
_start:
{
if (lean_obj_tag(v_node_306_) == 0)
{
lean_object* v_es_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_es_307_ = lean_ctor_get(v_node_306_, 0);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_307_, v___x_308_);
return v___x_309_;
}
else
{
lean_object* v_vs_310_; lean_object* v___x_311_; 
v_vs_310_ = lean_ctor_get(v_node_306_, 1);
v___x_311_ = lean_array_get_size(v_vs_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___redArg___boxed(lean_object* v_node_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_312_);
lean_dec_ref(v_node_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg___boxed(lean_object* v_es_314_, lean_object* v_i_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_314_, v_i_315_);
lean_dec(v_i_315_);
lean_dec_ref(v_es_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(lean_object* v_00_u03b1_317_, lean_object* v_00_u03b2_318_, lean_object* v_es_319_, lean_object* v_i_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_319_, v_i_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___boxed(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_es_324_, lean_object* v_i_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(v_00_u03b1_322_, v_00_u03b2_323_, v_es_324_, v_i_325_);
lean_dec(v_i_325_);
lean_dec_ref(v_es_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure(lean_object* v_00_u03b1_327_, lean_object* v_00_u03b2_328_, lean_object* v_node_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___boxed(lean_object* v_00_u03b1_331_, lean_object* v_00_u03b2_332_, lean_object* v_node_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_PersistentHashMap_Node_measure(v_00_u03b1_331_, v_00_u03b2_332_, v_node_333_);
lean_dec_ref(v_node_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter___redArg(lean_object* v_x_335_, lean_object* v_h__1_336_, lean_object* v_h__2_337_, lean_object* v_h__3_338_){
_start:
{
switch(lean_obj_tag(v_x_335_))
{
case 0:
{
lean_object* v_key_339_; lean_object* v_val_340_; lean_object* v___x_341_; 
lean_dec(v_h__3_338_);
lean_dec(v_h__1_336_);
v_key_339_ = lean_ctor_get(v_x_335_, 0);
lean_inc(v_key_339_);
v_val_340_ = lean_ctor_get(v_x_335_, 1);
lean_inc(v_val_340_);
lean_dec_ref_known(v_x_335_, 2);
v___x_341_ = lean_apply_3(v_h__2_337_, v_key_339_, v_val_340_, lean_box(0));
return v___x_341_;
}
case 1:
{
lean_object* v_node_342_; lean_object* v___x_343_; 
lean_dec(v_h__2_337_);
lean_dec(v_h__1_336_);
v_node_342_ = lean_ctor_get(v_x_335_, 0);
lean_inc(v_node_342_);
lean_dec_ref_known(v_x_335_, 1);
v___x_343_ = lean_apply_2(v_h__3_338_, v_node_342_, lean_box(0));
return v___x_343_;
}
default: 
{
lean_object* v___x_344_; 
lean_dec(v_h__3_338_);
lean_dec(v_h__2_337_);
v___x_344_ = lean_apply_1(v_h__1_336_, lean_box(0));
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter(lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_motive_347_, lean_object* v_x_348_, lean_object* v_h__1_349_, lean_object* v_h__2_350_, lean_object* v_h__3_351_){
_start:
{
switch(lean_obj_tag(v_x_348_))
{
case 0:
{
lean_object* v_key_352_; lean_object* v_val_353_; lean_object* v___x_354_; 
lean_dec(v_h__3_351_);
lean_dec(v_h__1_349_);
v_key_352_ = lean_ctor_get(v_x_348_, 0);
lean_inc(v_key_352_);
v_val_353_ = lean_ctor_get(v_x_348_, 1);
lean_inc(v_val_353_);
lean_dec_ref_known(v_x_348_, 2);
v___x_354_ = lean_apply_3(v_h__2_350_, v_key_352_, v_val_353_, lean_box(0));
return v___x_354_;
}
case 1:
{
lean_object* v_node_355_; lean_object* v___x_356_; 
lean_dec(v_h__2_350_);
lean_dec(v_h__1_349_);
v_node_355_ = lean_ctor_get(v_x_348_, 0);
lean_inc(v_node_355_);
lean_dec_ref_known(v_x_348_, 1);
v___x_356_ = lean_apply_2(v_h__3_351_, v_node_355_, lean_box(0));
return v___x_356_;
}
default: 
{
lean_object* v___x_357_; 
lean_dec(v_h__3_351_);
lean_dec(v_h__2_350_);
v___x_357_ = lean_apply_1(v_h__1_349_, lean_box(0));
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter___redArg(lean_object* v_node_358_, lean_object* v_h__1_359_, lean_object* v_h__2_360_){
_start:
{
if (lean_obj_tag(v_node_358_) == 0)
{
lean_object* v_es_361_; lean_object* v___x_362_; 
lean_dec(v_h__2_360_);
v_es_361_ = lean_ctor_get(v_node_358_, 0);
lean_inc_ref(v_es_361_);
lean_dec_ref_known(v_node_358_, 1);
v___x_362_ = lean_apply_1(v_h__1_359_, v_es_361_);
return v___x_362_;
}
else
{
lean_object* v_ks_363_; lean_object* v_vs_364_; lean_object* v___x_365_; 
lean_dec(v_h__1_359_);
v_ks_363_ = lean_ctor_get(v_node_358_, 0);
lean_inc_ref(v_ks_363_);
v_vs_364_ = lean_ctor_get(v_node_358_, 1);
lean_inc_ref(v_vs_364_);
lean_dec_ref_known(v_node_358_, 2);
v___x_365_ = lean_apply_3(v_h__2_360_, v_ks_363_, v_vs_364_, lean_box(0));
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter(lean_object* v_00_u03b1_366_, lean_object* v_00_u03b2_367_, lean_object* v_motive_368_, lean_object* v_node_369_, lean_object* v_h__1_370_, lean_object* v_h__2_371_){
_start:
{
if (lean_obj_tag(v_node_369_) == 0)
{
lean_object* v_es_372_; lean_object* v___x_373_; 
lean_dec(v_h__2_371_);
v_es_372_ = lean_ctor_get(v_node_369_, 0);
lean_inc_ref(v_es_372_);
lean_dec_ref_known(v_node_369_, 1);
v___x_373_ = lean_apply_1(v_h__1_370_, v_es_372_);
return v___x_373_;
}
else
{
lean_object* v_ks_374_; lean_object* v_vs_375_; lean_object* v___x_376_; 
lean_dec(v_h__1_370_);
v_ks_374_ = lean_ctor_get(v_node_369_, 0);
lean_inc_ref(v_ks_374_);
v_vs_375_ = lean_ctor_get(v_node_369_, 1);
lean_inc_ref(v_vs_375_);
lean_dec_ref_known(v_node_369_, 2);
v___x_376_ = lean_apply_3(v_h__2_371_, v_ks_374_, v_vs_375_, lean_box(0));
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg(lean_object* v_entry_377_){
_start:
{
if (lean_obj_tag(v_entry_377_) == 1)
{
lean_object* v_node_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_node_378_ = lean_ctor_get(v_entry_377_, 0);
v___x_379_ = lean_unsigned_to_nat(2u);
v___x_380_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_378_);
v___x_381_ = lean_nat_add(v___x_379_, v___x_380_);
lean_dec(v___x_380_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(1u);
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg___boxed(lean_object* v_entry_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_383_);
lean_dec(v_entry_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure(lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_entry_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___boxed(lean_object* v_00_u03b1_389_, lean_object* v_00_u03b2_390_, lean_object* v_entry_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_PersistentHashMap_Entry_measure(v_00_u03b1_389_, v_00_u03b2_390_, v_entry_391_);
lean_dec(v_entry_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(lean_object* v_init_393_, lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_inc(v_init_393_);
return v_init_393_;
}
else
{
lean_object* v_head_395_; lean_object* v_tail_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_head_395_ = lean_ctor_get(v_x_394_, 0);
v_tail_396_ = lean_ctor_get(v_x_394_, 1);
v___x_397_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_393_, v_tail_396_);
v___x_398_ = lean_nat_add(v_head_395_, v___x_397_);
lean_dec(v___x_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2___boxed(lean_object* v_init_399_, lean_object* v_x_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_399_, v_x_400_);
lean_dec(v_x_400_);
lean_dec(v_init_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(lean_object* v_l_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v___x_403_, v_l_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2___boxed(lean_object* v_l_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v_l_405_);
lean_dec(v_l_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
if (lean_obj_tag(v_a_407_) == 0)
{
lean_object* v___x_409_; 
v___x_409_ = l_List_reverse___redArg(v_a_408_);
return v___x_409_;
}
else
{
lean_object* v_head_410_; lean_object* v_tail_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_420_; 
v_head_410_ = lean_ctor_get(v_a_407_, 0);
v_tail_411_ = lean_ctor_get(v_a_407_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_a_407_);
if (v_isSharedCheck_420_ == 0)
{
v___x_413_ = v_a_407_;
v_isShared_414_ = v_isSharedCheck_420_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_tail_411_);
lean_inc(v_head_410_);
lean_dec(v_a_407_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_420_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_head_410_);
lean_dec(v_head_410_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v_a_408_);
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_a_408_);
v___x_417_ = v_reuseFailAlloc_419_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
v_a_407_ = v_tail_411_;
v_a_408_ = v___x_417_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(lean_object* v_a_421_, lean_object* v_b_422_){
_start:
{
lean_object* v_array_423_; lean_object* v_start_424_; lean_object* v_stop_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_438_; 
v_array_423_ = lean_ctor_get(v_a_421_, 0);
v_start_424_ = lean_ctor_get(v_a_421_, 1);
v_stop_425_ = lean_ctor_get(v_a_421_, 2);
v_isSharedCheck_438_ = !lean_is_exclusive(v_a_421_);
if (v_isSharedCheck_438_ == 0)
{
v___x_427_ = v_a_421_;
v_isShared_428_ = v_isSharedCheck_438_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_stop_425_);
lean_inc(v_start_424_);
lean_inc(v_array_423_);
lean_dec(v_a_421_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_438_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
uint8_t v___x_429_; 
v___x_429_ = lean_nat_dec_lt(v_start_424_, v_stop_425_);
if (v___x_429_ == 0)
{
lean_del_object(v___x_427_);
lean_dec(v_stop_425_);
lean_dec(v_start_424_);
lean_dec_ref(v_array_423_);
return v_b_422_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_add(v_start_424_, v___x_430_);
lean_inc_ref(v_array_423_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 1, v___x_431_);
v___x_433_ = v___x_427_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_array_423_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_stop_425_);
v___x_433_ = v_reuseFailAlloc_437_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_array_fget(v_array_423_, v_start_424_);
lean_dec(v_start_424_);
lean_dec_ref(v_array_423_);
v___x_435_ = lean_array_push(v_b_422_, v___x_434_);
v_a_421_ = v___x_433_;
v_b_422_ = v___x_435_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure___redArg(lean_object* v_es_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_442_ = ((lean_object*)(l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0));
v___x_443_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_es_441_, v___x_442_);
v___x_444_ = lean_array_to_list(v___x_443_);
v___x_445_ = lean_box(0);
v___x_446_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v___x_444_, v___x_445_);
v___x_447_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v___x_446_);
lean_dec(v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure(lean_object* v_00_u03b1_448_, lean_object* v_00_u03b2_449_, lean_object* v_es_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_es_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0(lean_object* v_00_u03b1_452_, lean_object* v_00_u03b2_453_, lean_object* v_inst_454_, lean_object* v_R_455_, lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_a_456_, v_b_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1(lean_object* v_00_u03b1_459_, lean_object* v_00_u03b2_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v_a_461_, v_a_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure___redArg(lean_object* v_x_464_){
_start:
{
switch(lean_obj_tag(v_x_464_))
{
case 0:
{
lean_object* v___x_465_; 
v___x_465_ = lean_unsigned_to_nat(0u);
return v___x_465_;
}
case 1:
{
lean_object* v_a_466_; lean_object* v_a_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_a_466_ = lean_ctor_get(v_x_464_, 0);
lean_inc_ref(v_a_466_);
v_a_467_ = lean_ctor_get(v_x_464_, 1);
lean_inc(v_a_467_);
lean_dec_ref_known(v_x_464_, 2);
v___x_468_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_a_466_);
v___x_469_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_467_);
v___x_470_ = lean_nat_add(v___x_468_, v___x_469_);
lean_dec(v___x_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_add(v___x_470_, v___x_471_);
lean_dec(v___x_470_);
return v___x_472_;
}
default: 
{
lean_object* v_vals_473_; lean_object* v_a_474_; lean_object* v_start_475_; lean_object* v_stop_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_vals_473_ = lean_ctor_get(v_x_464_, 1);
lean_inc_ref(v_vals_473_);
v_a_474_ = lean_ctor_get(v_x_464_, 2);
lean_inc(v_a_474_);
lean_dec_ref_known(v_x_464_, 3);
v_start_475_ = lean_ctor_get(v_vals_473_, 1);
lean_inc(v_start_475_);
v_stop_476_ = lean_ctor_get(v_vals_473_, 2);
lean_inc(v_stop_476_);
lean_dec_ref(v_vals_473_);
v___x_477_ = lean_nat_sub(v_stop_476_, v_start_475_);
lean_dec(v_start_475_);
lean_dec(v_stop_476_);
v___x_478_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_474_);
v___x_479_ = lean_nat_add(v___x_477_, v___x_478_);
lean_dec(v___x_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_add(v___x_479_, v___x_480_);
lean_dec(v___x_479_);
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure(lean_object* v_00_u03b1_482_, lean_object* v_00_u03b2_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(lean_object* v_x_486_, lean_object* v_h__1_487_, lean_object* v_h__2_488_, lean_object* v_h__3_489_){
_start:
{
switch(lean_obj_tag(v_x_486_))
{
case 0:
{
lean_object* v_key_490_; lean_object* v_val_491_; lean_object* v___x_492_; 
lean_dec(v_h__3_489_);
lean_dec(v_h__1_487_);
v_key_490_ = lean_ctor_get(v_x_486_, 0);
lean_inc(v_key_490_);
v_val_491_ = lean_ctor_get(v_x_486_, 1);
lean_inc(v_val_491_);
lean_dec_ref_known(v_x_486_, 2);
v___x_492_ = lean_apply_2(v_h__2_488_, v_key_490_, v_val_491_);
return v___x_492_;
}
case 1:
{
lean_object* v_node_493_; lean_object* v___x_494_; 
lean_dec(v_h__2_488_);
lean_dec(v_h__1_487_);
v_node_493_ = lean_ctor_get(v_x_486_, 0);
lean_inc(v_node_493_);
lean_dec_ref_known(v_x_486_, 1);
v___x_494_ = lean_apply_1(v_h__3_489_, v_node_493_);
return v___x_494_;
}
default: 
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v_h__3_489_);
lean_dec(v_h__2_488_);
v___x_495_ = lean_box(0);
v___x_496_ = lean_apply_1(v_h__1_487_, v___x_495_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter(lean_object* v_00_u03b1_497_, lean_object* v_00_u03b2_498_, lean_object* v_motive_499_, lean_object* v_x_500_, lean_object* v_h__1_501_, lean_object* v_h__2_502_, lean_object* v_h__3_503_){
_start:
{
switch(lean_obj_tag(v_x_500_))
{
case 0:
{
lean_object* v_key_504_; lean_object* v_val_505_; lean_object* v___x_506_; 
lean_dec(v_h__3_503_);
lean_dec(v_h__1_501_);
v_key_504_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_key_504_);
v_val_505_ = lean_ctor_get(v_x_500_, 1);
lean_inc(v_val_505_);
lean_dec_ref_known(v_x_500_, 2);
v___x_506_ = lean_apply_2(v_h__2_502_, v_key_504_, v_val_505_);
return v___x_506_;
}
case 1:
{
lean_object* v_node_507_; lean_object* v___x_508_; 
lean_dec(v_h__2_502_);
lean_dec(v_h__1_501_);
v_node_507_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_node_507_);
lean_dec_ref_known(v_x_500_, 1);
v___x_508_ = lean_apply_1(v_h__3_503_, v_node_507_);
return v___x_508_;
}
default: 
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v_h__3_503_);
lean_dec(v_h__2_502_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_apply_1(v_h__1_501_, v___x_509_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(lean_object* v_x_511_, lean_object* v_h__1_512_, lean_object* v_h__2_513_, lean_object* v_h__3_514_){
_start:
{
switch(lean_obj_tag(v_x_511_))
{
case 0:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_h__3_514_);
lean_dec(v_h__2_513_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_apply_1(v_h__1_512_, v___x_515_);
return v___x_516_;
}
case 1:
{
lean_object* v_a_517_; lean_object* v_a_518_; lean_object* v___x_519_; 
lean_dec(v_h__3_514_);
lean_dec(v_h__1_512_);
v_a_517_ = lean_ctor_get(v_x_511_, 0);
lean_inc_ref(v_a_517_);
v_a_518_ = lean_ctor_get(v_x_511_, 1);
lean_inc(v_a_518_);
lean_dec_ref_known(v_x_511_, 2);
v___x_519_ = lean_apply_2(v_h__2_513_, v_a_517_, v_a_518_);
return v___x_519_;
}
default: 
{
lean_object* v_keys_520_; lean_object* v_vals_521_; lean_object* v_a_522_; lean_object* v___x_523_; 
lean_dec(v_h__2_513_);
lean_dec(v_h__1_512_);
v_keys_520_ = lean_ctor_get(v_x_511_, 0);
lean_inc_ref(v_keys_520_);
v_vals_521_ = lean_ctor_get(v_x_511_, 1);
lean_inc_ref(v_vals_521_);
v_a_522_ = lean_ctor_get(v_x_511_, 2);
lean_inc(v_a_522_);
lean_dec_ref_known(v_x_511_, 3);
v___x_523_ = lean_apply_4(v_h__3_514_, v_keys_520_, v_vals_521_, lean_box(0), v_a_522_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_motive_526_, lean_object* v_x_527_, lean_object* v_h__1_528_, lean_object* v_h__2_529_, lean_object* v_h__3_530_){
_start:
{
switch(lean_obj_tag(v_x_527_))
{
case 0:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v_h__3_530_);
lean_dec(v_h__2_529_);
v___x_531_ = lean_box(0);
v___x_532_ = lean_apply_1(v_h__1_528_, v___x_531_);
return v___x_532_;
}
case 1:
{
lean_object* v_a_533_; lean_object* v_a_534_; lean_object* v___x_535_; 
lean_dec(v_h__3_530_);
lean_dec(v_h__1_528_);
v_a_533_ = lean_ctor_get(v_x_527_, 0);
lean_inc_ref(v_a_533_);
v_a_534_ = lean_ctor_get(v_x_527_, 1);
lean_inc(v_a_534_);
lean_dec_ref_known(v_x_527_, 2);
v___x_535_ = lean_apply_2(v_h__2_529_, v_a_533_, v_a_534_);
return v___x_535_;
}
default: 
{
lean_object* v_keys_536_; lean_object* v_vals_537_; lean_object* v_a_538_; lean_object* v___x_539_; 
lean_dec(v_h__2_529_);
lean_dec(v_h__1_528_);
v_keys_536_ = lean_ctor_get(v_x_527_, 0);
lean_inc_ref(v_keys_536_);
v_vals_537_ = lean_ctor_get(v_x_527_, 1);
lean_inc_ref(v_vals_537_);
v_a_538_ = lean_ctor_get(v_x_527_, 2);
lean_inc(v_a_538_);
lean_dec_ref_known(v_x_527_, 3);
v___x_539_ = lean_apply_4(v_h__3_530_, v_keys_536_, v_vals_537_, lean_box(0), v_a_538_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_box(0);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg();
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_box(0);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_547_, lean_object* v_recur_548_, lean_object* v_it_549_, lean_object* v_____do__lift_550_){
_start:
{
if (lean_obj_tag(v_____do__lift_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; 
lean_dec(v_it_549_);
lean_dec(v_recur_548_);
v_a_551_ = lean_ctor_get(v_____do__lift_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v_____do__lift_550_, 1);
v___x_552_ = lean_apply_2(v_toPure_547_, lean_box(0), v_a_551_);
return v___x_552_;
}
else
{
lean_object* v_a_553_; lean_object* v___x_554_; 
lean_dec(v_toPure_547_);
v_a_553_ = lean_ctor_get(v_____do__lift_550_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v_____do__lift_550_, 1);
v___x_554_ = lean_apply_4(v_recur_548_, v_it_549_, v_a_553_, lean_box(0), lean_box(0));
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_555_, lean_object* v_recur_556_, lean_object* v___y_557_, lean_object* v_acc_558_, lean_object* v_toBind_559_, lean_object* v_s_560_){
_start:
{
switch(lean_obj_tag(v_s_560_))
{
case 0:
{
lean_object* v_it_561_; lean_object* v_out_562_; lean_object* v___f_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_it_561_ = lean_ctor_get(v_s_560_, 0);
lean_inc(v_it_561_);
v_out_562_ = lean_ctor_get(v_s_560_, 1);
lean_inc(v_out_562_);
lean_dec_ref_known(v_s_560_, 2);
v___f_563_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_563_, 0, v_toPure_555_);
lean_closure_set(v___f_563_, 1, v_recur_556_);
lean_closure_set(v___f_563_, 2, v_it_561_);
v___x_564_ = lean_apply_3(v___y_557_, v_out_562_, lean_box(0), v_acc_558_);
v___x_565_ = lean_apply_4(v_toBind_559_, lean_box(0), lean_box(0), v___x_564_, v___f_563_);
return v___x_565_;
}
case 1:
{
lean_object* v_it_566_; lean_object* v___x_567_; 
lean_dec(v_toBind_559_);
lean_dec(v___y_557_);
lean_dec(v_toPure_555_);
v_it_566_ = lean_ctor_get(v_s_560_, 0);
lean_inc(v_it_566_);
lean_dec_ref_known(v_s_560_, 1);
v___x_567_ = lean_apply_4(v_recur_556_, v_it_566_, v_acc_558_, lean_box(0), lean_box(0));
return v___x_567_;
}
default: 
{
lean_object* v___x_568_; 
lean_dec(v_toBind_559_);
lean_dec(v___y_557_);
lean_dec(v_recur_556_);
v___x_568_ = lean_apply_2(v_toPure_555_, lean_box(0), v_acc_558_);
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_569_, lean_object* v___y_570_, lean_object* v_toBind_571_, lean_object* v_lift_572_, lean_object* v_it_573_, lean_object* v_acc_574_, lean_object* v_hP_575_, lean_object* v_recur_576_){
_start:
{
lean_object* v___f_577_; 
v___f_577_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_577_, 0, v_toPure_569_);
lean_closure_set(v___f_577_, 1, v_recur_576_);
lean_closure_set(v___f_577_, 2, v___y_570_);
lean_closure_set(v___f_577_, 3, v_acc_574_);
lean_closure_set(v___f_577_, 4, v_toBind_571_);
switch(lean_obj_tag(v_it_573_))
{
case 0:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_box(2);
v___x_579_ = lean_apply_4(v_lift_572_, lean_box(0), lean_box(0), v___f_577_, v___x_578_);
return v___x_579_;
}
case 1:
{
lean_object* v_a_580_; lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_621_; 
v_a_580_ = lean_ctor_get(v_it_573_, 0);
v_a_581_ = lean_ctor_get(v_it_573_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_it_573_);
if (v_isSharedCheck_621_ == 0)
{
v___x_583_ = v_it_573_;
v_isShared_584_ = v_isSharedCheck_621_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_inc(v_a_580_);
lean_dec(v_it_573_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_621_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_start_585_; lean_object* v_stop_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_start_585_ = lean_ctor_get(v_a_580_, 1);
v_stop_586_ = lean_ctor_get(v_a_580_, 2);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_nat_sub(v_stop_586_, v_start_585_);
v___x_589_ = lean_nat_dec_lt(v___x_587_, v___x_588_);
lean_dec(v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_del_object(v___x_583_);
lean_dec_ref(v_a_580_);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v_a_581_);
v___x_591_ = lean_apply_4(v_lift_572_, lean_box(0), lean_box(0), v___f_577_, v___x_590_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_z_595_; 
v___x_592_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_580_);
v___x_593_ = l_Subarray_drop___redArg(v_a_580_, v___x_592_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_593_);
v_z_595_ = v___x_583_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_a_581_);
v_z_595_ = v_reuseFailAlloc_620_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = l_Subarray_get___redArg(v_a_580_, v___x_587_);
lean_dec_ref(v_a_580_);
switch(lean_obj_tag(v___x_596_))
{
case 0:
{
lean_object* v_key_597_; lean_object* v_val_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_607_; 
v_key_597_ = lean_ctor_get(v___x_596_, 0);
v_val_598_ = lean_ctor_get(v___x_596_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_607_ == 0)
{
v___x_600_ = v___x_596_;
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_val_598_);
lean_inc(v_key_597_);
lean_dec(v___x_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_key_597_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_val_598_);
v___x_603_ = v_reuseFailAlloc_606_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v_z_595_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_apply_4(v_lift_572_, lean_box(0), lean_box(0), v___f_577_, v___x_604_);
return v___x_605_;
}
}
}
case 1:
{
lean_object* v_node_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_617_; 
v_node_608_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_617_ == 0)
{
v___x_610_ = v___x_596_;
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_node_608_);
lean_dec(v___x_596_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_608_, v_z_595_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = lean_apply_4(v_lift_572_, lean_box(0), lean_box(0), v___f_577_, v___x_614_);
return v___x_615_;
}
}
}
default: 
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v_z_595_);
v___x_619_ = lean_apply_4(v_lift_572_, lean_box(0), lean_box(0), v___f_577_, v___x_618_);
return v___x_619_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_622_; lean_object* v_keys_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_646_; 
v_vals_622_ = lean_ctor_get(v_it_573_, 1);
v_keys_623_ = lean_ctor_get(v_it_573_, 0);
v_a_624_ = lean_ctor_get(v_it_573_, 2);
v_isSharedCheck_646_ = !lean_is_exclusive(v_it_573_);
if (v_isSharedCheck_646_ == 0)
{
v___x_626_ = v_it_573_;
v_isShared_627_ = v_isSharedCheck_646_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_inc(v_vals_622_);
lean_inc(v_keys_623_);
lean_dec(v_it_573_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_646_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_start_628_; lean_object* v_stop_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_start_628_ = lean_ctor_get(v_vals_622_, 1);
v_stop_629_ = lean_ctor_get(v_vals_622_, 2);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_nat_sub(v_stop_629_, v_start_628_);
v___x_632_ = lean_nat_dec_lt(v___x_630_, v___x_631_);
lean_dec(v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_del_object(v___x_626_);
lean_dec_ref(v_keys_623_);
lean_dec_ref(v_vals_622_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v_a_624_);
v___x_634_ = lean_apply_4(v_lift_572_, lean_box(0), lean_box(0), v___f_577_, v___x_633_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_635_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_623_);
v___x_636_ = l_Subarray_drop___redArg(v_keys_623_, v___x_635_);
lean_inc_ref(v_vals_622_);
v___x_637_ = l_Subarray_drop___redArg(v_vals_622_, v___x_635_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_637_);
lean_ctor_set(v___x_626_, 0, v___x_636_);
v___x_639_ = v___x_626_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_a_624_);
v___x_639_ = v_reuseFailAlloc_645_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_640_ = l_Subarray_get___redArg(v_keys_623_, v___x_630_);
lean_dec_ref(v_keys_623_);
v___x_641_ = l_Subarray_get___redArg(v_vals_622_, v___x_630_);
lean_dec_ref(v_vals_622_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_639_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = lean_apply_4(v_lift_572_, lean_box(0), lean_box(0), v___f_577_, v___x_643_);
return v___x_644_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3(lean_object* v_inst_647_, lean_object* v_lift_648_, lean_object* v_00_u03b3_649_, lean_object* v_Pl_650_, lean_object* v_it_651_, lean_object* v_init_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_toApplicative_654_; lean_object* v_toBind_655_; lean_object* v_toPure_656_; lean_object* v___f_657_; lean_object* v___x_658_; 
v_toApplicative_654_ = lean_ctor_get(v_inst_647_, 0);
lean_inc_ref(v_toApplicative_654_);
v_toBind_655_ = lean_ctor_get(v_inst_647_, 1);
lean_inc(v_toBind_655_);
lean_dec_ref(v_inst_647_);
v_toPure_656_ = lean_ctor_get(v_toApplicative_654_, 1);
lean_inc(v_toPure_656_);
lean_dec_ref(v_toApplicative_654_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_657_, 0, v_toPure_656_);
lean_closure_set(v___f_657_, 1, v___y_653_);
lean_closure_set(v___f_657_, 2, v_toBind_655_);
lean_closure_set(v___f_657_, 3, v_lift_648_);
v___x_658_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_657_, v_it_651_, v_init_652_, lean_box(0));
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg(lean_object* v_inst_659_){
_start:
{
lean_object* v___f_660_; 
v___f_660_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_660_, 0, v_inst_659_);
return v___f_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_n_663_, lean_object* v_inst_664_){
_start:
{
lean_object* v___f_665_; 
v___f_665_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_665_, 0, v_inst_664_);
return v___f_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___redArg(lean_object* v_map_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_box(0);
v___x_668_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_666_, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter(lean_object* v_00_u03b1_669_, lean_object* v_00_u03b2_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_map_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_box(0);
v___x_675_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_673_, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___boxed(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_map_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_PersistentHashMap_iter(v_00_u03b1_676_, v_00_u03b2_677_, v_inst_678_, v_inst_679_, v_map_680_);
lean_dec_ref(v_inst_679_);
lean_dec_ref(v_inst_678_);
return v_res_681_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
