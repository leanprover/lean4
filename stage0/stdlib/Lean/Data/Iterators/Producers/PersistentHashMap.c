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
switch(lean_obj_tag(v_x_344_))
{
case 0:
{
lean_object* v_key_348_; lean_object* v_val_349_; lean_object* v___x_350_; 
lean_dec(v_h__3_347_);
lean_dec(v_h__1_345_);
v_key_348_ = lean_ctor_get(v_x_344_, 0);
lean_inc(v_key_348_);
v_val_349_ = lean_ctor_get(v_x_344_, 1);
lean_inc(v_val_349_);
lean_dec_ref(v_x_344_);
v___x_350_ = lean_apply_3(v_h__2_346_, v_key_348_, v_val_349_, lean_box(0));
return v___x_350_;
}
case 1:
{
lean_object* v_node_351_; lean_object* v___x_352_; 
lean_dec(v_h__2_346_);
lean_dec(v_h__1_345_);
v_node_351_ = lean_ctor_get(v_x_344_, 0);
lean_inc(v_node_351_);
lean_dec_ref(v_x_344_);
v___x_352_ = lean_apply_2(v_h__3_347_, v_node_351_, lean_box(0));
return v___x_352_;
}
default: 
{
lean_object* v___x_353_; 
lean_dec(v_h__3_347_);
lean_dec(v_h__2_346_);
v___x_353_ = lean_apply_1(v_h__1_345_, lean_box(0));
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter___redArg(lean_object* v_node_354_, lean_object* v_h__1_355_, lean_object* v_h__2_356_){
_start:
{
if (lean_obj_tag(v_node_354_) == 0)
{
lean_object* v_es_357_; lean_object* v___x_358_; 
lean_dec(v_h__2_356_);
v_es_357_ = lean_ctor_get(v_node_354_, 0);
lean_inc_ref(v_es_357_);
lean_dec_ref(v_node_354_);
v___x_358_ = lean_apply_1(v_h__1_355_, v_es_357_);
return v___x_358_;
}
else
{
lean_object* v_ks_359_; lean_object* v_vs_360_; lean_object* v___x_361_; 
lean_dec(v_h__1_355_);
v_ks_359_ = lean_ctor_get(v_node_354_, 0);
lean_inc_ref(v_ks_359_);
v_vs_360_ = lean_ctor_get(v_node_354_, 1);
lean_inc_ref(v_vs_360_);
lean_dec_ref(v_node_354_);
v___x_361_ = lean_apply_3(v_h__2_356_, v_ks_359_, v_vs_360_, lean_box(0));
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter(lean_object* v_00_u03b1_362_, lean_object* v_00_u03b2_363_, lean_object* v_motive_364_, lean_object* v_node_365_, lean_object* v_h__1_366_, lean_object* v_h__2_367_){
_start:
{
if (lean_obj_tag(v_node_365_) == 0)
{
lean_object* v_es_368_; lean_object* v___x_369_; 
lean_dec(v_h__2_367_);
v_es_368_ = lean_ctor_get(v_node_365_, 0);
lean_inc_ref(v_es_368_);
lean_dec_ref(v_node_365_);
v___x_369_ = lean_apply_1(v_h__1_366_, v_es_368_);
return v___x_369_;
}
else
{
lean_object* v_ks_370_; lean_object* v_vs_371_; lean_object* v___x_372_; 
lean_dec(v_h__1_366_);
v_ks_370_ = lean_ctor_get(v_node_365_, 0);
lean_inc_ref(v_ks_370_);
v_vs_371_ = lean_ctor_get(v_node_365_, 1);
lean_inc_ref(v_vs_371_);
lean_dec_ref(v_node_365_);
v___x_372_ = lean_apply_3(v_h__2_367_, v_ks_370_, v_vs_371_, lean_box(0));
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg(lean_object* v_entry_373_){
_start:
{
if (lean_obj_tag(v_entry_373_) == 1)
{
lean_object* v_node_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_node_374_ = lean_ctor_get(v_entry_373_, 0);
v___x_375_ = lean_unsigned_to_nat(2u);
v___x_376_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_374_);
v___x_377_ = lean_nat_add(v___x_375_, v___x_376_);
lean_dec(v___x_376_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(1u);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg___boxed(lean_object* v_entry_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_379_);
lean_dec(v_entry_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_entry_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___boxed(lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_entry_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_PersistentHashMap_Entry_measure(v_00_u03b1_385_, v_00_u03b2_386_, v_entry_387_);
lean_dec(v_entry_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(lean_object* v_init_389_, lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_inc(v_init_389_);
return v_init_389_;
}
else
{
lean_object* v_head_391_; lean_object* v_tail_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_head_391_ = lean_ctor_get(v_x_390_, 0);
v_tail_392_ = lean_ctor_get(v_x_390_, 1);
v___x_393_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_389_, v_tail_392_);
v___x_394_ = lean_nat_add(v_head_391_, v___x_393_);
lean_dec(v___x_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2___boxed(lean_object* v_init_395_, lean_object* v_x_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_395_, v_x_396_);
lean_dec(v_x_396_);
lean_dec(v_init_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(lean_object* v_l_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v___x_399_, v_l_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2___boxed(lean_object* v_l_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v_l_401_);
lean_dec(v_l_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
if (lean_obj_tag(v_a_403_) == 0)
{
lean_object* v___x_405_; 
v___x_405_ = l_List_reverse___redArg(v_a_404_);
return v___x_405_;
}
else
{
lean_object* v_head_406_; lean_object* v_tail_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_416_; 
v_head_406_ = lean_ctor_get(v_a_403_, 0);
v_tail_407_ = lean_ctor_get(v_a_403_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_a_403_);
if (v_isSharedCheck_416_ == 0)
{
v___x_409_ = v_a_403_;
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_tail_407_);
lean_inc(v_head_406_);
lean_dec(v_a_403_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_head_406_);
lean_dec(v_head_406_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v_a_404_);
lean_ctor_set(v___x_409_, 0, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_a_404_);
v___x_413_ = v_reuseFailAlloc_415_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
v_a_403_ = v_tail_407_;
v_a_404_ = v___x_413_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(lean_object* v_a_417_, lean_object* v_b_418_){
_start:
{
lean_object* v_array_419_; lean_object* v_start_420_; lean_object* v_stop_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_434_; 
v_array_419_ = lean_ctor_get(v_a_417_, 0);
v_start_420_ = lean_ctor_get(v_a_417_, 1);
v_stop_421_ = lean_ctor_get(v_a_417_, 2);
v_isSharedCheck_434_ = !lean_is_exclusive(v_a_417_);
if (v_isSharedCheck_434_ == 0)
{
v___x_423_ = v_a_417_;
v_isShared_424_ = v_isSharedCheck_434_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_stop_421_);
lean_inc(v_start_420_);
lean_inc(v_array_419_);
lean_dec(v_a_417_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_434_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
uint8_t v___x_425_; 
v___x_425_ = lean_nat_dec_lt(v_start_420_, v_stop_421_);
if (v___x_425_ == 0)
{
lean_del_object(v___x_423_);
lean_dec(v_stop_421_);
lean_dec(v_start_420_);
lean_dec_ref(v_array_419_);
return v_b_418_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_add(v_start_420_, v___x_426_);
lean_inc_ref(v_array_419_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_427_);
v___x_429_ = v___x_423_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_array_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_stop_421_);
v___x_429_ = v_reuseFailAlloc_433_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_array_fget(v_array_419_, v_start_420_);
lean_dec(v_start_420_);
lean_dec_ref(v_array_419_);
v___x_431_ = lean_array_push(v_b_418_, v___x_430_);
v_a_417_ = v___x_429_;
v_b_418_ = v___x_431_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure___redArg(lean_object* v_es_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_438_ = ((lean_object*)(l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0));
v___x_439_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_es_437_, v___x_438_);
v___x_440_ = lean_array_to_list(v___x_439_);
v___x_441_ = lean_box(0);
v___x_442_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v___x_440_, v___x_441_);
v___x_443_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v___x_442_);
lean_dec(v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure(lean_object* v_00_u03b1_444_, lean_object* v_00_u03b2_445_, lean_object* v_es_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_es_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0(lean_object* v_00_u03b1_448_, lean_object* v_00_u03b2_449_, lean_object* v_inst_450_, lean_object* v_R_451_, lean_object* v_a_452_, lean_object* v_b_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_a_452_, v_b_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1(lean_object* v_00_u03b1_455_, lean_object* v_00_u03b2_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v_a_457_, v_a_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure___redArg(lean_object* v_x_460_){
_start:
{
switch(lean_obj_tag(v_x_460_))
{
case 0:
{
lean_object* v___x_461_; 
v___x_461_ = lean_unsigned_to_nat(0u);
return v___x_461_;
}
case 1:
{
lean_object* v_a_462_; lean_object* v_a_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_a_462_ = lean_ctor_get(v_x_460_, 0);
lean_inc_ref(v_a_462_);
v_a_463_ = lean_ctor_get(v_x_460_, 1);
lean_inc(v_a_463_);
lean_dec_ref(v_x_460_);
v___x_464_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_a_462_);
v___x_465_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_463_);
v___x_466_ = lean_nat_add(v___x_464_, v___x_465_);
lean_dec(v___x_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_add(v___x_466_, v___x_467_);
lean_dec(v___x_466_);
return v___x_468_;
}
default: 
{
lean_object* v_vals_469_; lean_object* v_a_470_; lean_object* v_start_471_; lean_object* v_stop_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_vals_469_ = lean_ctor_get(v_x_460_, 1);
lean_inc_ref(v_vals_469_);
v_a_470_ = lean_ctor_get(v_x_460_, 2);
lean_inc(v_a_470_);
lean_dec_ref(v_x_460_);
v_start_471_ = lean_ctor_get(v_vals_469_, 1);
lean_inc(v_start_471_);
v_stop_472_ = lean_ctor_get(v_vals_469_, 2);
lean_inc(v_stop_472_);
lean_dec_ref(v_vals_469_);
v___x_473_ = lean_nat_sub(v_stop_472_, v_start_471_);
lean_dec(v_start_471_);
lean_dec(v_stop_472_);
v___x_474_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_470_);
v___x_475_ = lean_nat_add(v___x_473_, v___x_474_);
lean_dec(v___x_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v___x_475_, v___x_476_);
lean_dec(v___x_475_);
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure(lean_object* v_00_u03b1_478_, lean_object* v_00_u03b2_479_, lean_object* v_x_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(lean_object* v_x_482_, lean_object* v_h__1_483_, lean_object* v_h__2_484_, lean_object* v_h__3_485_){
_start:
{
switch(lean_obj_tag(v_x_482_))
{
case 0:
{
lean_object* v_key_486_; lean_object* v_val_487_; lean_object* v___x_488_; 
lean_dec(v_h__3_485_);
lean_dec(v_h__1_483_);
v_key_486_ = lean_ctor_get(v_x_482_, 0);
lean_inc(v_key_486_);
v_val_487_ = lean_ctor_get(v_x_482_, 1);
lean_inc(v_val_487_);
lean_dec_ref(v_x_482_);
v___x_488_ = lean_apply_2(v_h__2_484_, v_key_486_, v_val_487_);
return v___x_488_;
}
case 1:
{
lean_object* v_node_489_; lean_object* v___x_490_; 
lean_dec(v_h__2_484_);
lean_dec(v_h__1_483_);
v_node_489_ = lean_ctor_get(v_x_482_, 0);
lean_inc(v_node_489_);
lean_dec_ref(v_x_482_);
v___x_490_ = lean_apply_1(v_h__3_485_, v_node_489_);
return v___x_490_;
}
default: 
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_h__3_485_);
lean_dec(v_h__2_484_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_apply_1(v_h__1_483_, v___x_491_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_motive_495_, lean_object* v_x_496_, lean_object* v_h__1_497_, lean_object* v_h__2_498_, lean_object* v_h__3_499_){
_start:
{
switch(lean_obj_tag(v_x_496_))
{
case 0:
{
lean_object* v_key_500_; lean_object* v_val_501_; lean_object* v___x_502_; 
lean_dec(v_h__3_499_);
lean_dec(v_h__1_497_);
v_key_500_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_key_500_);
v_val_501_ = lean_ctor_get(v_x_496_, 1);
lean_inc(v_val_501_);
lean_dec_ref(v_x_496_);
v___x_502_ = lean_apply_2(v_h__2_498_, v_key_500_, v_val_501_);
return v___x_502_;
}
case 1:
{
lean_object* v_node_503_; lean_object* v___x_504_; 
lean_dec(v_h__2_498_);
lean_dec(v_h__1_497_);
v_node_503_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_node_503_);
lean_dec_ref(v_x_496_);
v___x_504_ = lean_apply_1(v_h__3_499_, v_node_503_);
return v___x_504_;
}
default: 
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v_h__3_499_);
lean_dec(v_h__2_498_);
v___x_505_ = lean_box(0);
v___x_506_ = lean_apply_1(v_h__1_497_, v___x_505_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(lean_object* v_x_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_, lean_object* v_h__3_510_){
_start:
{
switch(lean_obj_tag(v_x_507_))
{
case 0:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_h__3_510_);
lean_dec(v_h__2_509_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_apply_1(v_h__1_508_, v___x_511_);
return v___x_512_;
}
case 1:
{
lean_object* v_a_513_; lean_object* v_a_514_; lean_object* v___x_515_; 
lean_dec(v_h__3_510_);
lean_dec(v_h__1_508_);
v_a_513_ = lean_ctor_get(v_x_507_, 0);
lean_inc_ref(v_a_513_);
v_a_514_ = lean_ctor_get(v_x_507_, 1);
lean_inc(v_a_514_);
lean_dec_ref(v_x_507_);
v___x_515_ = lean_apply_2(v_h__2_509_, v_a_513_, v_a_514_);
return v___x_515_;
}
default: 
{
lean_object* v_keys_516_; lean_object* v_vals_517_; lean_object* v_a_518_; lean_object* v___x_519_; 
lean_dec(v_h__2_509_);
lean_dec(v_h__1_508_);
v_keys_516_ = lean_ctor_get(v_x_507_, 0);
lean_inc_ref(v_keys_516_);
v_vals_517_ = lean_ctor_get(v_x_507_, 1);
lean_inc_ref(v_vals_517_);
v_a_518_ = lean_ctor_get(v_x_507_, 2);
lean_inc(v_a_518_);
lean_dec_ref(v_x_507_);
v___x_519_ = lean_apply_4(v_h__3_510_, v_keys_516_, v_vals_517_, lean_box(0), v_a_518_);
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_motive_522_, lean_object* v_x_523_, lean_object* v_h__1_524_, lean_object* v_h__2_525_, lean_object* v_h__3_526_){
_start:
{
switch(lean_obj_tag(v_x_523_))
{
case 0:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_h__3_526_);
lean_dec(v_h__2_525_);
v___x_527_ = lean_box(0);
v___x_528_ = lean_apply_1(v_h__1_524_, v___x_527_);
return v___x_528_;
}
case 1:
{
lean_object* v_a_529_; lean_object* v_a_530_; lean_object* v___x_531_; 
lean_dec(v_h__3_526_);
lean_dec(v_h__1_524_);
v_a_529_ = lean_ctor_get(v_x_523_, 0);
lean_inc_ref(v_a_529_);
v_a_530_ = lean_ctor_get(v_x_523_, 1);
lean_inc(v_a_530_);
lean_dec_ref(v_x_523_);
v___x_531_ = lean_apply_2(v_h__2_525_, v_a_529_, v_a_530_);
return v___x_531_;
}
default: 
{
lean_object* v_keys_532_; lean_object* v_vals_533_; lean_object* v_a_534_; lean_object* v___x_535_; 
lean_dec(v_h__2_525_);
lean_dec(v_h__1_524_);
v_keys_532_ = lean_ctor_get(v_x_523_, 0);
lean_inc_ref(v_keys_532_);
v_vals_533_ = lean_ctor_get(v_x_523_, 1);
lean_inc_ref(v_vals_533_);
v_a_534_ = lean_ctor_get(v_x_523_, 2);
lean_inc(v_a_534_);
lean_dec_ref(v_x_523_);
v___x_535_ = lean_apply_4(v_h__3_526_, v_keys_532_, v_vals_533_, lean_box(0), v_a_534_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(0);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_539_, lean_object* v_recur_540_, lean_object* v_it_541_, lean_object* v_____do__lift_542_){
_start:
{
if (lean_obj_tag(v_____do__lift_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; 
lean_dec(v_it_541_);
lean_dec(v_recur_540_);
v_a_543_ = lean_ctor_get(v_____do__lift_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref(v_____do__lift_542_);
v___x_544_ = lean_apply_2(v_toPure_539_, lean_box(0), v_a_543_);
return v___x_544_;
}
else
{
lean_object* v_a_545_; lean_object* v___x_546_; 
lean_dec(v_toPure_539_);
v_a_545_ = lean_ctor_get(v_____do__lift_542_, 0);
lean_inc(v_a_545_);
lean_dec_ref(v_____do__lift_542_);
v___x_546_ = lean_apply_4(v_recur_540_, v_it_541_, v_a_545_, lean_box(0), lean_box(0));
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_547_, lean_object* v_recur_548_, lean_object* v___y_549_, lean_object* v_acc_550_, lean_object* v_toBind_551_, lean_object* v_s_552_){
_start:
{
switch(lean_obj_tag(v_s_552_))
{
case 0:
{
lean_object* v_it_553_; lean_object* v_out_554_; lean_object* v___f_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_it_553_ = lean_ctor_get(v_s_552_, 0);
lean_inc(v_it_553_);
v_out_554_ = lean_ctor_get(v_s_552_, 1);
lean_inc(v_out_554_);
lean_dec_ref(v_s_552_);
v___f_555_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_555_, 0, v_toPure_547_);
lean_closure_set(v___f_555_, 1, v_recur_548_);
lean_closure_set(v___f_555_, 2, v_it_553_);
v___x_556_ = lean_apply_3(v___y_549_, v_out_554_, lean_box(0), v_acc_550_);
v___x_557_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_556_, v___f_555_);
return v___x_557_;
}
case 1:
{
lean_object* v_it_558_; lean_object* v___x_559_; 
lean_dec(v_toBind_551_);
lean_dec(v___y_549_);
lean_dec(v_toPure_547_);
v_it_558_ = lean_ctor_get(v_s_552_, 0);
lean_inc(v_it_558_);
lean_dec_ref(v_s_552_);
v___x_559_ = lean_apply_4(v_recur_548_, v_it_558_, v_acc_550_, lean_box(0), lean_box(0));
return v___x_559_;
}
default: 
{
lean_object* v___x_560_; 
lean_dec(v_toBind_551_);
lean_dec(v___y_549_);
lean_dec(v_recur_548_);
v___x_560_ = lean_apply_2(v_toPure_547_, lean_box(0), v_acc_550_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_561_, lean_object* v___y_562_, lean_object* v_toBind_563_, lean_object* v_lift_564_, lean_object* v_it_565_, lean_object* v_acc_566_, lean_object* v_hP_567_, lean_object* v_recur_568_){
_start:
{
lean_object* v___f_569_; 
v___f_569_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_569_, 0, v_toPure_561_);
lean_closure_set(v___f_569_, 1, v_recur_568_);
lean_closure_set(v___f_569_, 2, v___y_562_);
lean_closure_set(v___f_569_, 3, v_acc_566_);
lean_closure_set(v___f_569_, 4, v_toBind_563_);
switch(lean_obj_tag(v_it_565_))
{
case 0:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_box(2);
v___x_571_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_570_);
return v___x_571_;
}
case 1:
{
lean_object* v_a_572_; lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_613_; 
v_a_572_ = lean_ctor_get(v_it_565_, 0);
v_a_573_ = lean_ctor_get(v_it_565_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_it_565_);
if (v_isSharedCheck_613_ == 0)
{
v___x_575_ = v_it_565_;
v_isShared_576_ = v_isSharedCheck_613_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_inc(v_a_572_);
lean_dec(v_it_565_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_613_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_start_577_; lean_object* v_stop_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_start_577_ = lean_ctor_get(v_a_572_, 1);
v_stop_578_ = lean_ctor_get(v_a_572_, 2);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_nat_sub(v_stop_578_, v_start_577_);
v___x_581_ = lean_nat_dec_lt(v___x_579_, v___x_580_);
lean_dec(v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_del_object(v___x_575_);
lean_dec_ref(v_a_572_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v_a_573_);
v___x_583_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_582_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v_z_587_; 
v___x_584_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_572_);
v___x_585_ = l_Subarray_drop___redArg(v_a_572_, v___x_584_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_585_);
v_z_587_ = v___x_575_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_a_573_);
v_z_587_ = v_reuseFailAlloc_612_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; 
v___x_588_ = l_Subarray_get___redArg(v_a_572_, v___x_579_);
lean_dec_ref(v_a_572_);
switch(lean_obj_tag(v___x_588_))
{
case 0:
{
lean_object* v_key_589_; lean_object* v_val_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_599_; 
v_key_589_ = lean_ctor_get(v___x_588_, 0);
v_val_590_ = lean_ctor_get(v___x_588_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_599_ == 0)
{
v___x_592_ = v___x_588_;
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_val_590_);
lean_inc(v_key_589_);
lean_dec(v___x_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_key_589_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_val_590_);
v___x_595_ = v_reuseFailAlloc_598_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_z_587_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_596_);
return v___x_597_;
}
}
}
case 1:
{
lean_object* v_node_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_609_; 
v_node_600_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_609_ == 0)
{
v___x_602_ = v___x_588_;
v_isShared_603_ = v_isSharedCheck_609_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_node_600_);
lean_dec(v___x_588_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_609_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_600_, v_z_587_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; 
v___x_607_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_606_);
return v___x_607_;
}
}
}
default: 
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v_z_587_);
v___x_611_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_610_);
return v___x_611_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_614_; lean_object* v_keys_615_; lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_638_; 
v_vals_614_ = lean_ctor_get(v_it_565_, 1);
v_keys_615_ = lean_ctor_get(v_it_565_, 0);
v_a_616_ = lean_ctor_get(v_it_565_, 2);
v_isSharedCheck_638_ = !lean_is_exclusive(v_it_565_);
if (v_isSharedCheck_638_ == 0)
{
v___x_618_ = v_it_565_;
v_isShared_619_ = v_isSharedCheck_638_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_inc(v_vals_614_);
lean_inc(v_keys_615_);
lean_dec(v_it_565_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_638_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v_start_620_; lean_object* v_stop_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_start_620_ = lean_ctor_get(v_vals_614_, 1);
v_stop_621_ = lean_ctor_get(v_vals_614_, 2);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_nat_sub(v_stop_621_, v_start_620_);
v___x_624_ = lean_nat_dec_lt(v___x_622_, v___x_623_);
lean_dec(v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_del_object(v___x_618_);
lean_dec_ref(v_keys_615_);
lean_dec_ref(v_vals_614_);
v___x_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_625_, 0, v_a_616_);
v___x_626_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_625_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_627_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_615_);
v___x_628_ = l_Subarray_drop___redArg(v_keys_615_, v___x_627_);
lean_inc_ref(v_vals_614_);
v___x_629_ = l_Subarray_drop___redArg(v_vals_614_, v___x_627_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_629_);
lean_ctor_set(v___x_618_, 0, v___x_628_);
v___x_631_ = v___x_618_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_a_616_);
v___x_631_ = v_reuseFailAlloc_637_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_632_ = l_Subarray_get___redArg(v_keys_615_, v___x_622_);
lean_dec_ref(v_keys_615_);
v___x_633_ = l_Subarray_get___redArg(v_vals_614_, v___x_622_);
lean_dec_ref(v_vals_614_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_631_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_635_);
return v___x_636_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3(lean_object* v_inst_639_, lean_object* v_lift_640_, lean_object* v_00_u03b3_641_, lean_object* v_Pl_642_, lean_object* v_it_643_, lean_object* v_init_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_toApplicative_646_; lean_object* v_toBind_647_; lean_object* v_toPure_648_; lean_object* v___f_649_; lean_object* v___x_650_; 
v_toApplicative_646_ = lean_ctor_get(v_inst_639_, 0);
lean_inc_ref(v_toApplicative_646_);
v_toBind_647_ = lean_ctor_get(v_inst_639_, 1);
lean_inc(v_toBind_647_);
lean_dec_ref(v_inst_639_);
v_toPure_648_ = lean_ctor_get(v_toApplicative_646_, 1);
lean_inc(v_toPure_648_);
lean_dec_ref(v_toApplicative_646_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_649_, 0, v_toPure_648_);
lean_closure_set(v___f_649_, 1, v___y_645_);
lean_closure_set(v___f_649_, 2, v_toBind_647_);
lean_closure_set(v___f_649_, 3, v_lift_640_);
v___x_650_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_649_, v_it_643_, v_init_644_, lean_box(0));
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg(lean_object* v_inst_651_){
_start:
{
lean_object* v___f_652_; 
v___f_652_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_652_, 0, v_inst_651_);
return v___f_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_n_655_, lean_object* v_inst_656_){
_start:
{
lean_object* v___f_657_; 
v___f_657_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_657_, 0, v_inst_656_);
return v___f_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___redArg(lean_object* v_map_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_box(0);
v___x_660_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_658_, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_map_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box(0);
v___x_667_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_665_, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___boxed(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_map_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_PersistentHashMap_iter(v_00_u03b1_668_, v_00_u03b2_669_, v_inst_670_, v_inst_671_, v_map_672_);
lean_dec_ref(v_inst_671_);
lean_dec_ref(v_inst_670_);
return v_res_673_;
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
