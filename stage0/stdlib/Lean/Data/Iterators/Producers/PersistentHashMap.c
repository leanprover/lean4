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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_PersistentHashMap_Zipper_ctorIdx___impl___redArg(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_00_u03b2_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_tag_nat(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorIdx___impl___boxed(lean_object* v_00_u03b1_9_, lean_object* v_00_u03b2_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_PersistentHashMap_Zipper_ctorIdx___impl(v_00_u03b1_9_, v_00_u03b2_10_, v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
switch(lean_obj_tag(v_t_13_))
{
case 0:
{
return v_k_14_;
}
case 1:
{
lean_object* v_a_15_; lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_a_15_);
v_a_16_ = lean_ctor_get(v_t_13_, 1);
lean_inc(v_a_16_);
lean_dec_ref_known(v_t_13_, 2);
v___x_17_ = lean_apply_2(v_k_14_, v_a_15_, v_a_16_);
return v___x_17_;
}
default: 
{
lean_object* v_keys_18_; lean_object* v_vals_19_; lean_object* v_a_20_; lean_object* v___x_21_; 
v_keys_18_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_keys_18_);
v_vals_19_ = lean_ctor_get(v_t_13_, 1);
lean_inc_ref(v_vals_19_);
v_a_20_ = lean_ctor_get(v_t_13_, 2);
lean_inc(v_a_20_);
lean_dec_ref_known(v_t_13_, 3);
v___x_21_ = lean_apply_4(v_k_14_, v_keys_18_, v_vals_19_, lean_box(0), v_a_20_);
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorElim(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_26_, v_k_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_ctorElim___boxed(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_motive_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_PersistentHashMap_Zipper_ctorElim(v_00_u03b1_30_, v_00_u03b2_31_, v_motive_32_, v_ctorIdx_33_, v_t_34_, v_h_35_, v_k_36_);
lean_dec(v_ctorIdx_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_done_elim___redArg(lean_object* v_t_38_, lean_object* v_done_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_38_, v_done_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_done_elim(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_done_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_44_, v_done_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consEntries_elim___redArg(lean_object* v_t_48_, lean_object* v_consEntries_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_48_, v_consEntries_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consEntries_elim(lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_motive_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_consEntries_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_54_, v_consEntries_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consCollision_elim___redArg(lean_object* v_t_58_, lean_object* v_consCollision_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_58_, v_consCollision_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_consCollision_elim(lean_object* v_00_u03b1_61_, lean_object* v_00_u03b2_62_, lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_consCollision_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_64_, v_consCollision_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_prependNode___redArg(lean_object* v_node_68_, lean_object* v_z_69_){
_start:
{
if (lean_obj_tag(v_node_68_) == 0)
{
lean_object* v_es_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_es_70_ = lean_ctor_get(v_node_68_, 0);
lean_inc_ref(v_es_70_);
lean_dec_ref_known(v_node_68_, 1);
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_array_get_size(v_es_70_);
v___x_73_ = l_Array_toSubarray___redArg(v_es_70_, v___x_71_, v___x_72_);
v___x_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v_z_69_);
return v___x_74_;
}
else
{
lean_object* v_ks_75_; lean_object* v_vs_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_ks_75_ = lean_ctor_get(v_node_68_, 0);
lean_inc_ref(v_ks_75_);
v_vs_76_ = lean_ctor_get(v_node_68_, 1);
lean_inc_ref(v_vs_76_);
lean_dec_ref_known(v_node_68_, 2);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_array_get_size(v_ks_75_);
v___x_79_ = l_Array_toSubarray___redArg(v_ks_75_, v___x_77_, v___x_78_);
v___x_80_ = lean_array_get_size(v_vs_76_);
v___x_81_ = l_Array_toSubarray___redArg(v_vs_76_, v___x_77_, v___x_80_);
v___x_82_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_82_, 0, v___x_79_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
lean_ctor_set(v___x_82_, 2, v_z_69_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_prependNode(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_node_85_, lean_object* v_z_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_85_, v_z_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_step___redArg(lean_object* v_it_88_){
_start:
{
switch(lean_obj_tag(v_it_88_))
{
case 0:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(2);
return v___x_89_;
}
case 1:
{
lean_object* v_a_90_; lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_127_; 
v_a_90_ = lean_ctor_get(v_it_88_, 0);
v_a_91_ = lean_ctor_get(v_it_88_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v_it_88_);
if (v_isSharedCheck_127_ == 0)
{
v___x_93_ = v_it_88_;
v_isShared_94_ = v_isSharedCheck_127_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_inc(v_a_90_);
lean_dec(v_it_88_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_127_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_start_95_; lean_object* v_stop_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_start_95_ = lean_ctor_get(v_a_90_, 1);
v_stop_96_ = lean_ctor_get(v_a_90_, 2);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_nat_sub(v_stop_96_, v_start_95_);
v___x_99_ = lean_nat_dec_lt(v___x_97_, v___x_98_);
lean_dec(v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_del_object(v___x_93_);
lean_dec_ref(v_a_90_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v_a_91_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_z_104_; 
v___x_101_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_90_);
v___x_102_ = l_Subarray_drop___redArg(v_a_90_, v___x_101_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_102_);
v_z_104_ = v___x_93_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_a_91_);
v_z_104_ = v_reuseFailAlloc_126_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; 
v___x_105_ = l_Subarray_get___redArg(v_a_90_, v___x_97_);
lean_dec_ref(v_a_90_);
switch(lean_obj_tag(v___x_105_))
{
case 0:
{
lean_object* v_key_106_; lean_object* v_val_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
v_key_106_ = lean_ctor_get(v___x_105_, 0);
v_val_107_ = lean_ctor_get(v___x_105_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_115_ == 0)
{
v___x_109_ = v___x_105_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_val_107_);
lean_inc(v_key_106_);
lean_dec(v___x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_key_106_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_val_107_);
v___x_112_ = v_reuseFailAlloc_114_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_z_104_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
return v___x_113_;
}
}
}
case 1:
{
lean_object* v_node_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_124_; 
v_node_116_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_124_ == 0)
{
v___x_118_ = v___x_105_;
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_node_116_);
lean_dec(v___x_105_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_120_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_116_, v_z_104_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_120_);
v___x_122_ = v___x_118_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
default: 
{
lean_object* v___x_125_; 
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v_z_104_);
return v___x_125_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_128_; lean_object* v_keys_129_; lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_150_; 
v_vals_128_ = lean_ctor_get(v_it_88_, 1);
v_keys_129_ = lean_ctor_get(v_it_88_, 0);
v_a_130_ = lean_ctor_get(v_it_88_, 2);
v_isSharedCheck_150_ = !lean_is_exclusive(v_it_88_);
if (v_isSharedCheck_150_ == 0)
{
v___x_132_ = v_it_88_;
v_isShared_133_ = v_isSharedCheck_150_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_inc(v_vals_128_);
lean_inc(v_keys_129_);
lean_dec(v_it_88_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_150_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_start_134_; lean_object* v_stop_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_start_134_ = lean_ctor_get(v_vals_128_, 1);
v_stop_135_ = lean_ctor_get(v_vals_128_, 2);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_nat_sub(v_stop_135_, v_start_134_);
v___x_138_ = lean_nat_dec_lt(v___x_136_, v___x_137_);
lean_dec(v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
lean_del_object(v___x_132_);
lean_dec_ref(v_keys_129_);
lean_dec_ref(v_vals_128_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v_a_130_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_140_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_129_);
v___x_141_ = l_Subarray_drop___redArg(v_keys_129_, v___x_140_);
lean_inc_ref(v_vals_128_);
v___x_142_ = l_Subarray_drop___redArg(v_vals_128_, v___x_140_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_142_);
lean_ctor_set(v___x_132_, 0, v___x_141_);
v___x_144_ = v___x_132_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v_a_130_);
v___x_144_ = v_reuseFailAlloc_149_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = l_Subarray_get___redArg(v_keys_129_, v___x_136_);
lean_dec_ref(v_keys_129_);
v___x_146_ = l_Subarray_get___redArg(v_vals_128_, v___x_136_);
lean_dec_ref(v_vals_128_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_144_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
return v___x_148_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_step(lean_object* v_00_u03b1_151_, lean_object* v_00_u03b2_152_, lean_object* v_it_153_){
_start:
{
switch(lean_obj_tag(v_it_153_))
{
case 0:
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(2);
return v___x_154_;
}
case 1:
{
lean_object* v_a_155_; lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_192_; 
v_a_155_ = lean_ctor_get(v_it_153_, 0);
v_a_156_ = lean_ctor_get(v_it_153_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_it_153_);
if (v_isSharedCheck_192_ == 0)
{
v___x_158_ = v_it_153_;
v_isShared_159_ = v_isSharedCheck_192_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_inc(v_a_155_);
lean_dec(v_it_153_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_192_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_start_160_; lean_object* v_stop_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_start_160_ = lean_ctor_get(v_a_155_, 1);
v_stop_161_ = lean_ctor_get(v_a_155_, 2);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_nat_sub(v_stop_161_, v_start_160_);
v___x_164_ = lean_nat_dec_lt(v___x_162_, v___x_163_);
lean_dec(v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
lean_del_object(v___x_158_);
lean_dec_ref(v_a_155_);
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_a_156_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_z_169_; 
v___x_166_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_155_);
v___x_167_ = l_Subarray_drop___redArg(v_a_155_, v___x_166_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_167_);
v_z_169_ = v___x_158_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_a_156_);
v_z_169_ = v_reuseFailAlloc_191_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; 
v___x_170_ = l_Subarray_get___redArg(v_a_155_, v___x_162_);
lean_dec_ref(v_a_155_);
switch(lean_obj_tag(v___x_170_))
{
case 0:
{
lean_object* v_key_171_; lean_object* v_val_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_180_; 
v_key_171_ = lean_ctor_get(v___x_170_, 0);
v_val_172_ = lean_ctor_get(v___x_170_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_180_ == 0)
{
v___x_174_ = v___x_170_;
v_isShared_175_ = v_isSharedCheck_180_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_val_172_);
lean_inc(v_key_171_);
lean_dec(v___x_170_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_180_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_key_171_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_val_172_);
v___x_177_ = v_reuseFailAlloc_179_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; 
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_z_169_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
return v___x_178_;
}
}
}
case 1:
{
lean_object* v_node_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_189_; 
v_node_181_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_189_ == 0)
{
v___x_183_ = v___x_170_;
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_node_181_);
lean_dec(v___x_170_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_185_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_181_, v_z_169_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_185_);
v___x_187_ = v___x_183_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
default: 
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_z_169_);
return v___x_190_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_193_; lean_object* v_keys_194_; lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_215_; 
v_vals_193_ = lean_ctor_get(v_it_153_, 1);
v_keys_194_ = lean_ctor_get(v_it_153_, 0);
v_a_195_ = lean_ctor_get(v_it_153_, 2);
v_isSharedCheck_215_ = !lean_is_exclusive(v_it_153_);
if (v_isSharedCheck_215_ == 0)
{
v___x_197_ = v_it_153_;
v_isShared_198_ = v_isSharedCheck_215_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_inc(v_vals_193_);
lean_inc(v_keys_194_);
lean_dec(v_it_153_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_215_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v_start_199_; lean_object* v_stop_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_start_199_ = lean_ctor_get(v_vals_193_, 1);
v_stop_200_ = lean_ctor_get(v_vals_193_, 2);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_nat_sub(v_stop_200_, v_start_199_);
v___x_203_ = lean_nat_dec_lt(v___x_201_, v___x_202_);
lean_dec(v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
lean_del_object(v___x_197_);
lean_dec_ref(v_keys_194_);
lean_dec_ref(v_vals_193_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v_a_195_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_205_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_194_);
v___x_206_ = l_Subarray_drop___redArg(v_keys_194_, v___x_205_);
lean_inc_ref(v_vals_193_);
v___x_207_ = l_Subarray_drop___redArg(v_vals_193_, v___x_205_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_207_);
lean_ctor_set(v___x_197_, 0, v___x_206_);
v___x_209_ = v___x_197_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_a_195_);
v___x_209_ = v_reuseFailAlloc_214_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = l_Subarray_get___redArg(v_keys_194_, v___x_201_);
lean_dec_ref(v_keys_194_);
v___x_211_ = l_Subarray_get___redArg(v_vals_193_, v___x_201_);
lean_dec_ref(v_vals_193_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_209_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
return v___x_213_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___redArg___lam__0(lean_object* v_it_216_){
_start:
{
switch(lean_obj_tag(v_it_216_))
{
case 0:
{
lean_object* v___x_217_; 
v___x_217_ = lean_box(2);
return v___x_217_;
}
case 1:
{
lean_object* v_a_218_; lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_255_; 
v_a_218_ = lean_ctor_get(v_it_216_, 0);
v_a_219_ = lean_ctor_get(v_it_216_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_it_216_);
if (v_isSharedCheck_255_ == 0)
{
v___x_221_ = v_it_216_;
v_isShared_222_ = v_isSharedCheck_255_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_inc(v_a_218_);
lean_dec(v_it_216_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_255_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v_start_223_; lean_object* v_stop_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_start_223_ = lean_ctor_get(v_a_218_, 1);
v_stop_224_ = lean_ctor_get(v_a_218_, 2);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_nat_sub(v_stop_224_, v_start_223_);
v___x_227_ = lean_nat_dec_lt(v___x_225_, v___x_226_);
lean_dec(v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_del_object(v___x_221_);
lean_dec_ref(v_a_218_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v_a_219_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_z_232_; 
v___x_229_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_218_);
v___x_230_ = l_Subarray_drop___redArg(v_a_218_, v___x_229_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_230_);
v_z_232_ = v___x_221_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_a_219_);
v_z_232_ = v_reuseFailAlloc_254_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; 
v___x_233_ = l_Subarray_get___redArg(v_a_218_, v___x_225_);
lean_dec_ref(v_a_218_);
switch(lean_obj_tag(v___x_233_))
{
case 0:
{
lean_object* v_key_234_; lean_object* v_val_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
v_key_234_ = lean_ctor_get(v___x_233_, 0);
v_val_235_ = lean_ctor_get(v___x_233_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v___x_233_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_val_235_);
lean_inc(v_key_234_);
lean_dec(v___x_233_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_key_234_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_val_235_);
v___x_240_ = v_reuseFailAlloc_242_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_z_232_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
return v___x_241_;
}
}
}
case 1:
{
lean_object* v_node_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
v_node_244_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_252_ == 0)
{
v___x_246_ = v___x_233_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_node_244_);
lean_dec(v___x_233_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_244_, v_z_232_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
default: 
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v_z_232_);
return v___x_253_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_256_; lean_object* v_keys_257_; lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_278_; 
v_vals_256_ = lean_ctor_get(v_it_216_, 1);
v_keys_257_ = lean_ctor_get(v_it_216_, 0);
v_a_258_ = lean_ctor_get(v_it_216_, 2);
v_isSharedCheck_278_ = !lean_is_exclusive(v_it_216_);
if (v_isSharedCheck_278_ == 0)
{
v___x_260_ = v_it_216_;
v_isShared_261_ = v_isSharedCheck_278_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_inc(v_vals_256_);
lean_inc(v_keys_257_);
lean_dec(v_it_216_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_278_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v_start_262_; lean_object* v_stop_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_start_262_ = lean_ctor_get(v_vals_256_, 1);
v_stop_263_ = lean_ctor_get(v_vals_256_, 2);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_nat_sub(v_stop_263_, v_start_262_);
v___x_266_ = lean_nat_dec_lt(v___x_264_, v___x_265_);
lean_dec(v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
lean_del_object(v___x_260_);
lean_dec_ref(v_keys_257_);
lean_dec_ref(v_vals_256_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v_a_258_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_268_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_257_);
v___x_269_ = l_Subarray_drop___redArg(v_keys_257_, v___x_268_);
lean_inc_ref(v_vals_256_);
v___x_270_ = l_Subarray_drop___redArg(v_vals_256_, v___x_268_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v___x_270_);
lean_ctor_set(v___x_260_, 0, v___x_269_);
v___x_272_ = v___x_260_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_a_258_);
v___x_272_ = v_reuseFailAlloc_277_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_273_ = l_Subarray_get___redArg(v_keys_257_, v___x_264_);
lean_dec_ref(v_keys_257_);
v___x_274_ = l_Subarray_get___redArg(v_vals_256_, v___x_264_);
lean_dec_ref(v_vals_256_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_272_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
return v___x_276_;
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
lean_object* v___f_281_; 
v___f_281_ = ((lean_object*)(l_Lean_PersistentHashMap_instIterator___redArg___closed__0));
return v___f_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___redArg___boxed(lean_object* v___dummy_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_PersistentHashMap_instIterator___redArg();
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator(lean_object* v_00_u03b1_284_, lean_object* v_00_u03b2_285_){
_start:
{
lean_object* v___f_286_; 
v___f_286_ = ((lean_object*)(l_Lean_PersistentHashMap_instIterator___redArg___closed__0));
return v___f_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(lean_object* v_es_287_, lean_object* v_i_288_){
_start:
{
lean_object* v___y_290_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_array_get_size(v_es_287_);
v___x_296_ = lean_nat_dec_lt(v_i_288_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(0u);
return v___x_297_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_array_fget_borrowed(v_es_287_, v_i_288_);
if (lean_obj_tag(v___x_298_) == 1)
{
lean_object* v_node_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_node_299_ = lean_ctor_get(v___x_298_, 0);
v___x_300_ = lean_unsigned_to_nat(2u);
v___x_301_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_299_);
v___x_302_ = lean_nat_add(v___x_300_, v___x_301_);
lean_dec(v___x_301_);
v___y_290_ = v___x_302_;
goto v___jp_289_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_unsigned_to_nat(1u);
v___y_290_ = v___x_303_;
goto v___jp_289_;
}
}
v___jp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_i_288_, v___x_291_);
v___x_293_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_287_, v___x_292_);
lean_dec(v___x_292_);
v___x_294_ = lean_nat_add(v___y_290_, v___x_293_);
lean_dec(v___x_293_);
lean_dec(v___y_290_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___redArg(lean_object* v_node_304_){
_start:
{
if (lean_obj_tag(v_node_304_) == 0)
{
lean_object* v_es_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_es_305_ = lean_ctor_get(v_node_304_, 0);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_305_, v___x_306_);
return v___x_307_;
}
else
{
lean_object* v_vs_308_; lean_object* v___x_309_; 
v_vs_308_ = lean_ctor_get(v_node_304_, 1);
v___x_309_ = lean_array_get_size(v_vs_308_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___redArg___boxed(lean_object* v_node_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_310_);
lean_dec_ref(v_node_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg___boxed(lean_object* v_es_312_, lean_object* v_i_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_312_, v_i_313_);
lean_dec(v_i_313_);
lean_dec_ref(v_es_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(lean_object* v_00_u03b1_315_, lean_object* v_00_u03b2_316_, lean_object* v_es_317_, lean_object* v_i_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_317_, v_i_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___boxed(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_es_322_, lean_object* v_i_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(v_00_u03b1_320_, v_00_u03b2_321_, v_es_322_, v_i_323_);
lean_dec(v_i_323_);
lean_dec_ref(v_es_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure(lean_object* v_00_u03b1_325_, lean_object* v_00_u03b2_326_, lean_object* v_node_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___boxed(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_node_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_PersistentHashMap_Node_measure(v_00_u03b1_329_, v_00_u03b2_330_, v_node_331_);
lean_dec_ref(v_node_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter___redArg(lean_object* v_x_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_, lean_object* v_h__3_336_){
_start:
{
switch(lean_obj_tag(v_x_333_))
{
case 0:
{
lean_object* v_key_337_; lean_object* v_val_338_; lean_object* v___x_339_; 
lean_dec(v_h__3_336_);
lean_dec(v_h__1_334_);
v_key_337_ = lean_ctor_get(v_x_333_, 0);
lean_inc(v_key_337_);
v_val_338_ = lean_ctor_get(v_x_333_, 1);
lean_inc(v_val_338_);
lean_dec_ref_known(v_x_333_, 2);
v___x_339_ = lean_apply_3(v_h__2_335_, v_key_337_, v_val_338_, lean_box(0));
return v___x_339_;
}
case 1:
{
lean_object* v_node_340_; lean_object* v___x_341_; 
lean_dec(v_h__2_335_);
lean_dec(v_h__1_334_);
v_node_340_ = lean_ctor_get(v_x_333_, 0);
lean_inc(v_node_340_);
lean_dec_ref_known(v_x_333_, 1);
v___x_341_ = lean_apply_2(v_h__3_336_, v_node_340_, lean_box(0));
return v___x_341_;
}
default: 
{
lean_object* v___x_342_; 
lean_dec(v_h__3_336_);
lean_dec(v_h__2_335_);
v___x_342_ = lean_apply_1(v_h__1_334_, lean_box(0));
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_motive_345_, lean_object* v_x_346_, lean_object* v_h__1_347_, lean_object* v_h__2_348_, lean_object* v_h__3_349_){
_start:
{
switch(lean_obj_tag(v_x_346_))
{
case 0:
{
lean_object* v_key_350_; lean_object* v_val_351_; lean_object* v___x_352_; 
lean_dec(v_h__3_349_);
lean_dec(v_h__1_347_);
v_key_350_ = lean_ctor_get(v_x_346_, 0);
lean_inc(v_key_350_);
v_val_351_ = lean_ctor_get(v_x_346_, 1);
lean_inc(v_val_351_);
lean_dec_ref_known(v_x_346_, 2);
v___x_352_ = lean_apply_3(v_h__2_348_, v_key_350_, v_val_351_, lean_box(0));
return v___x_352_;
}
case 1:
{
lean_object* v_node_353_; lean_object* v___x_354_; 
lean_dec(v_h__2_348_);
lean_dec(v_h__1_347_);
v_node_353_ = lean_ctor_get(v_x_346_, 0);
lean_inc(v_node_353_);
lean_dec_ref_known(v_x_346_, 1);
v___x_354_ = lean_apply_2(v_h__3_349_, v_node_353_, lean_box(0));
return v___x_354_;
}
default: 
{
lean_object* v___x_355_; 
lean_dec(v_h__3_349_);
lean_dec(v_h__2_348_);
v___x_355_ = lean_apply_1(v_h__1_347_, lean_box(0));
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter___redArg(lean_object* v_node_356_, lean_object* v_h__1_357_, lean_object* v_h__2_358_){
_start:
{
if (lean_obj_tag(v_node_356_) == 0)
{
lean_object* v_es_359_; lean_object* v___x_360_; 
lean_dec(v_h__2_358_);
v_es_359_ = lean_ctor_get(v_node_356_, 0);
lean_inc_ref(v_es_359_);
lean_dec_ref_known(v_node_356_, 1);
v___x_360_ = lean_apply_1(v_h__1_357_, v_es_359_);
return v___x_360_;
}
else
{
lean_object* v_ks_361_; lean_object* v_vs_362_; lean_object* v___x_363_; 
lean_dec(v_h__1_357_);
v_ks_361_ = lean_ctor_get(v_node_356_, 0);
lean_inc_ref(v_ks_361_);
v_vs_362_ = lean_ctor_get(v_node_356_, 1);
lean_inc_ref(v_vs_362_);
lean_dec_ref_known(v_node_356_, 2);
v___x_363_ = lean_apply_3(v_h__2_358_, v_ks_361_, v_vs_362_, lean_box(0));
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_motive_366_, lean_object* v_node_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_){
_start:
{
if (lean_obj_tag(v_node_367_) == 0)
{
lean_object* v_es_370_; lean_object* v___x_371_; 
lean_dec(v_h__2_369_);
v_es_370_ = lean_ctor_get(v_node_367_, 0);
lean_inc_ref(v_es_370_);
lean_dec_ref_known(v_node_367_, 1);
v___x_371_ = lean_apply_1(v_h__1_368_, v_es_370_);
return v___x_371_;
}
else
{
lean_object* v_ks_372_; lean_object* v_vs_373_; lean_object* v___x_374_; 
lean_dec(v_h__1_368_);
v_ks_372_ = lean_ctor_get(v_node_367_, 0);
lean_inc_ref(v_ks_372_);
v_vs_373_ = lean_ctor_get(v_node_367_, 1);
lean_inc_ref(v_vs_373_);
lean_dec_ref_known(v_node_367_, 2);
v___x_374_ = lean_apply_3(v_h__2_369_, v_ks_372_, v_vs_373_, lean_box(0));
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg(lean_object* v_entry_375_){
_start:
{
if (lean_obj_tag(v_entry_375_) == 1)
{
lean_object* v_node_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_node_376_ = lean_ctor_get(v_entry_375_, 0);
v___x_377_ = lean_unsigned_to_nat(2u);
v___x_378_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_376_);
v___x_379_ = lean_nat_add(v___x_377_, v___x_378_);
lean_dec(v___x_378_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(1u);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg___boxed(lean_object* v_entry_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_381_);
lean_dec(v_entry_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure(lean_object* v_00_u03b1_383_, lean_object* v_00_u03b2_384_, lean_object* v_entry_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___boxed(lean_object* v_00_u03b1_387_, lean_object* v_00_u03b2_388_, lean_object* v_entry_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_PersistentHashMap_Entry_measure(v_00_u03b1_387_, v_00_u03b2_388_, v_entry_389_);
lean_dec(v_entry_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(lean_object* v_init_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
lean_inc(v_init_391_);
return v_init_391_;
}
else
{
lean_object* v_head_393_; lean_object* v_tail_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_head_393_ = lean_ctor_get(v_x_392_, 0);
v_tail_394_ = lean_ctor_get(v_x_392_, 1);
v___x_395_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_391_, v_tail_394_);
v___x_396_ = lean_nat_add(v_head_393_, v___x_395_);
lean_dec(v___x_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2___boxed(lean_object* v_init_397_, lean_object* v_x_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_397_, v_x_398_);
lean_dec(v_x_398_);
lean_dec(v_init_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(lean_object* v_l_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v___x_401_, v_l_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2___boxed(lean_object* v_l_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v_l_403_);
lean_dec(v_l_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
if (lean_obj_tag(v_a_405_) == 0)
{
lean_object* v___x_407_; 
v___x_407_ = l_List_reverse___redArg(v_a_406_);
return v___x_407_;
}
else
{
lean_object* v_head_408_; lean_object* v_tail_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_418_; 
v_head_408_ = lean_ctor_get(v_a_405_, 0);
v_tail_409_ = lean_ctor_get(v_a_405_, 1);
v_isSharedCheck_418_ = !lean_is_exclusive(v_a_405_);
if (v_isSharedCheck_418_ == 0)
{
v___x_411_ = v_a_405_;
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_tail_409_);
lean_inc(v_head_408_);
lean_dec(v_a_405_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_head_408_);
lean_dec(v_head_408_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v_a_406_);
lean_ctor_set(v___x_411_, 0, v___x_413_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_a_406_);
v___x_415_ = v_reuseFailAlloc_417_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
v_a_405_ = v_tail_409_;
v_a_406_ = v___x_415_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(lean_object* v_a_419_, lean_object* v_b_420_){
_start:
{
lean_object* v_array_421_; lean_object* v_start_422_; lean_object* v_stop_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_436_; 
v_array_421_ = lean_ctor_get(v_a_419_, 0);
v_start_422_ = lean_ctor_get(v_a_419_, 1);
v_stop_423_ = lean_ctor_get(v_a_419_, 2);
v_isSharedCheck_436_ = !lean_is_exclusive(v_a_419_);
if (v_isSharedCheck_436_ == 0)
{
v___x_425_ = v_a_419_;
v_isShared_426_ = v_isSharedCheck_436_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_stop_423_);
lean_inc(v_start_422_);
lean_inc(v_array_421_);
lean_dec(v_a_419_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_436_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
uint8_t v___x_427_; 
v___x_427_ = lean_nat_dec_lt(v_start_422_, v_stop_423_);
if (v___x_427_ == 0)
{
lean_del_object(v___x_425_);
lean_dec(v_stop_423_);
lean_dec(v_start_422_);
lean_dec_ref(v_array_421_);
return v_b_420_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_add(v_start_422_, v___x_428_);
lean_inc_ref(v_array_421_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v___x_429_);
v___x_431_ = v___x_425_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_array_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_stop_423_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_array_fget(v_array_421_, v_start_422_);
lean_dec(v_start_422_);
lean_dec_ref(v_array_421_);
v___x_433_ = lean_array_push(v_b_420_, v___x_432_);
v_a_419_ = v___x_431_;
v_b_420_ = v___x_433_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure___redArg(lean_object* v_es_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_440_ = ((lean_object*)(l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0));
v___x_441_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_es_439_, v___x_440_);
v___x_442_ = lean_array_to_list(v___x_441_);
v___x_443_ = lean_box(0);
v___x_444_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v___x_442_, v___x_443_);
v___x_445_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v___x_444_);
lean_dec(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_es_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_es_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0(lean_object* v_00_u03b1_450_, lean_object* v_00_u03b2_451_, lean_object* v_inst_452_, lean_object* v_R_453_, lean_object* v_a_454_, lean_object* v_b_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_a_454_, v_b_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1(lean_object* v_00_u03b1_457_, lean_object* v_00_u03b2_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v_a_459_, v_a_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure___redArg(lean_object* v_x_462_){
_start:
{
switch(lean_obj_tag(v_x_462_))
{
case 0:
{
lean_object* v___x_463_; 
v___x_463_ = lean_unsigned_to_nat(0u);
return v___x_463_;
}
case 1:
{
lean_object* v_a_464_; lean_object* v_a_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_a_464_ = lean_ctor_get(v_x_462_, 0);
lean_inc_ref(v_a_464_);
v_a_465_ = lean_ctor_get(v_x_462_, 1);
lean_inc(v_a_465_);
lean_dec_ref_known(v_x_462_, 2);
v___x_466_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_a_464_);
v___x_467_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_465_);
v___x_468_ = lean_nat_add(v___x_466_, v___x_467_);
lean_dec(v___x_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v___x_468_, v___x_469_);
lean_dec(v___x_468_);
return v___x_470_;
}
default: 
{
lean_object* v_vals_471_; lean_object* v_a_472_; lean_object* v_start_473_; lean_object* v_stop_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_vals_471_ = lean_ctor_get(v_x_462_, 1);
lean_inc_ref(v_vals_471_);
v_a_472_ = lean_ctor_get(v_x_462_, 2);
lean_inc(v_a_472_);
lean_dec_ref_known(v_x_462_, 3);
v_start_473_ = lean_ctor_get(v_vals_471_, 1);
lean_inc(v_start_473_);
v_stop_474_ = lean_ctor_get(v_vals_471_, 2);
lean_inc(v_stop_474_);
lean_dec_ref(v_vals_471_);
v___x_475_ = lean_nat_sub(v_stop_474_, v_start_473_);
lean_dec(v_start_473_);
lean_dec(v_stop_474_);
v___x_476_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_472_);
v___x_477_ = lean_nat_add(v___x_475_, v___x_476_);
lean_dec(v___x_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_nat_add(v___x_477_, v___x_478_);
lean_dec(v___x_477_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure(lean_object* v_00_u03b1_480_, lean_object* v_00_u03b2_481_, lean_object* v_x_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(lean_object* v_x_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_, lean_object* v_h__3_487_){
_start:
{
switch(lean_obj_tag(v_x_484_))
{
case 0:
{
lean_object* v_key_488_; lean_object* v_val_489_; lean_object* v___x_490_; 
lean_dec(v_h__3_487_);
lean_dec(v_h__1_485_);
v_key_488_ = lean_ctor_get(v_x_484_, 0);
lean_inc(v_key_488_);
v_val_489_ = lean_ctor_get(v_x_484_, 1);
lean_inc(v_val_489_);
lean_dec_ref_known(v_x_484_, 2);
v___x_490_ = lean_apply_2(v_h__2_486_, v_key_488_, v_val_489_);
return v___x_490_;
}
case 1:
{
lean_object* v_node_491_; lean_object* v___x_492_; 
lean_dec(v_h__2_486_);
lean_dec(v_h__1_485_);
v_node_491_ = lean_ctor_get(v_x_484_, 0);
lean_inc(v_node_491_);
lean_dec_ref_known(v_x_484_, 1);
v___x_492_ = lean_apply_1(v_h__3_487_, v_node_491_);
return v___x_492_;
}
default: 
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v_h__3_487_);
lean_dec(v_h__2_486_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_apply_1(v_h__1_485_, v___x_493_);
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter(lean_object* v_00_u03b1_495_, lean_object* v_00_u03b2_496_, lean_object* v_motive_497_, lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_, lean_object* v_h__3_501_){
_start:
{
switch(lean_obj_tag(v_x_498_))
{
case 0:
{
lean_object* v_key_502_; lean_object* v_val_503_; lean_object* v___x_504_; 
lean_dec(v_h__3_501_);
lean_dec(v_h__1_499_);
v_key_502_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_key_502_);
v_val_503_ = lean_ctor_get(v_x_498_, 1);
lean_inc(v_val_503_);
lean_dec_ref_known(v_x_498_, 2);
v___x_504_ = lean_apply_2(v_h__2_500_, v_key_502_, v_val_503_);
return v___x_504_;
}
case 1:
{
lean_object* v_node_505_; lean_object* v___x_506_; 
lean_dec(v_h__2_500_);
lean_dec(v_h__1_499_);
v_node_505_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_node_505_);
lean_dec_ref_known(v_x_498_, 1);
v___x_506_ = lean_apply_1(v_h__3_501_, v_node_505_);
return v___x_506_;
}
default: 
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v_h__3_501_);
lean_dec(v_h__2_500_);
v___x_507_ = lean_box(0);
v___x_508_ = lean_apply_1(v_h__1_499_, v___x_507_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(lean_object* v_x_509_, lean_object* v_h__1_510_, lean_object* v_h__2_511_, lean_object* v_h__3_512_){
_start:
{
switch(lean_obj_tag(v_x_509_))
{
case 0:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v_h__3_512_);
lean_dec(v_h__2_511_);
v___x_513_ = lean_box(0);
v___x_514_ = lean_apply_1(v_h__1_510_, v___x_513_);
return v___x_514_;
}
case 1:
{
lean_object* v_a_515_; lean_object* v_a_516_; lean_object* v___x_517_; 
lean_dec(v_h__3_512_);
lean_dec(v_h__1_510_);
v_a_515_ = lean_ctor_get(v_x_509_, 0);
lean_inc_ref(v_a_515_);
v_a_516_ = lean_ctor_get(v_x_509_, 1);
lean_inc(v_a_516_);
lean_dec_ref_known(v_x_509_, 2);
v___x_517_ = lean_apply_2(v_h__2_511_, v_a_515_, v_a_516_);
return v___x_517_;
}
default: 
{
lean_object* v_keys_518_; lean_object* v_vals_519_; lean_object* v_a_520_; lean_object* v___x_521_; 
lean_dec(v_h__2_511_);
lean_dec(v_h__1_510_);
v_keys_518_ = lean_ctor_get(v_x_509_, 0);
lean_inc_ref(v_keys_518_);
v_vals_519_ = lean_ctor_get(v_x_509_, 1);
lean_inc_ref(v_vals_519_);
v_a_520_ = lean_ctor_get(v_x_509_, 2);
lean_inc(v_a_520_);
lean_dec_ref_known(v_x_509_, 3);
v___x_521_ = lean_apply_4(v_h__3_512_, v_keys_518_, v_vals_519_, lean_box(0), v_a_520_);
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter(lean_object* v_00_u03b1_522_, lean_object* v_00_u03b2_523_, lean_object* v_motive_524_, lean_object* v_x_525_, lean_object* v_h__1_526_, lean_object* v_h__2_527_, lean_object* v_h__3_528_){
_start:
{
switch(lean_obj_tag(v_x_525_))
{
case 0:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_h__3_528_);
lean_dec(v_h__2_527_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_apply_1(v_h__1_526_, v___x_529_);
return v___x_530_;
}
case 1:
{
lean_object* v_a_531_; lean_object* v_a_532_; lean_object* v___x_533_; 
lean_dec(v_h__3_528_);
lean_dec(v_h__1_526_);
v_a_531_ = lean_ctor_get(v_x_525_, 0);
lean_inc_ref(v_a_531_);
v_a_532_ = lean_ctor_get(v_x_525_, 1);
lean_inc(v_a_532_);
lean_dec_ref_known(v_x_525_, 2);
v___x_533_ = lean_apply_2(v_h__2_527_, v_a_531_, v_a_532_);
return v___x_533_;
}
default: 
{
lean_object* v_keys_534_; lean_object* v_vals_535_; lean_object* v_a_536_; lean_object* v___x_537_; 
lean_dec(v_h__2_527_);
lean_dec(v_h__1_526_);
v_keys_534_ = lean_ctor_get(v_x_525_, 0);
lean_inc_ref(v_keys_534_);
v_vals_535_ = lean_ctor_get(v_x_525_, 1);
lean_inc_ref(v_vals_535_);
v_a_536_ = lean_ctor_get(v_x_525_, 2);
lean_inc(v_a_536_);
lean_dec_ref_known(v_x_525_, 3);
v___x_537_ = lean_apply_4(v_h__3_528_, v_keys_534_, v_vals_535_, lean_box(0), v_a_536_);
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_box(0);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg();
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_box(0);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_545_, lean_object* v_recur_546_, lean_object* v_it_547_, lean_object* v_____do__lift_548_){
_start:
{
if (lean_obj_tag(v_____do__lift_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; 
lean_dec(v_it_547_);
lean_dec(v_recur_546_);
v_a_549_ = lean_ctor_get(v_____do__lift_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v_____do__lift_548_, 1);
v___x_550_ = lean_apply_2(v_toPure_545_, lean_box(0), v_a_549_);
return v___x_550_;
}
else
{
lean_object* v_a_551_; lean_object* v___x_552_; 
lean_dec(v_toPure_545_);
v_a_551_ = lean_ctor_get(v_____do__lift_548_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v_____do__lift_548_, 1);
v___x_552_ = lean_apply_4(v_recur_546_, v_it_547_, v_a_551_, lean_box(0), lean_box(0));
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_553_, lean_object* v_recur_554_, lean_object* v___y_555_, lean_object* v_acc_556_, lean_object* v_toBind_557_, lean_object* v_s_558_){
_start:
{
switch(lean_obj_tag(v_s_558_))
{
case 0:
{
lean_object* v_it_559_; lean_object* v_out_560_; lean_object* v___f_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_it_559_ = lean_ctor_get(v_s_558_, 0);
lean_inc(v_it_559_);
v_out_560_ = lean_ctor_get(v_s_558_, 1);
lean_inc(v_out_560_);
lean_dec_ref_known(v_s_558_, 2);
v___f_561_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_561_, 0, v_toPure_553_);
lean_closure_set(v___f_561_, 1, v_recur_554_);
lean_closure_set(v___f_561_, 2, v_it_559_);
v___x_562_ = lean_apply_3(v___y_555_, v_out_560_, lean_box(0), v_acc_556_);
v___x_563_ = lean_apply_4(v_toBind_557_, lean_box(0), lean_box(0), v___x_562_, v___f_561_);
return v___x_563_;
}
case 1:
{
lean_object* v_it_564_; lean_object* v___x_565_; 
lean_dec(v_toBind_557_);
lean_dec(v___y_555_);
lean_dec(v_toPure_553_);
v_it_564_ = lean_ctor_get(v_s_558_, 0);
lean_inc(v_it_564_);
lean_dec_ref_known(v_s_558_, 1);
v___x_565_ = lean_apply_4(v_recur_554_, v_it_564_, v_acc_556_, lean_box(0), lean_box(0));
return v___x_565_;
}
default: 
{
lean_object* v___x_566_; 
lean_dec(v_toBind_557_);
lean_dec(v___y_555_);
lean_dec(v_recur_554_);
v___x_566_ = lean_apply_2(v_toPure_553_, lean_box(0), v_acc_556_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_567_, lean_object* v___y_568_, lean_object* v_toBind_569_, lean_object* v_lift_570_, lean_object* v_it_571_, lean_object* v_acc_572_, lean_object* v_hP_573_, lean_object* v_recur_574_){
_start:
{
lean_object* v___f_575_; 
v___f_575_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_575_, 0, v_toPure_567_);
lean_closure_set(v___f_575_, 1, v_recur_574_);
lean_closure_set(v___f_575_, 2, v___y_568_);
lean_closure_set(v___f_575_, 3, v_acc_572_);
lean_closure_set(v___f_575_, 4, v_toBind_569_);
switch(lean_obj_tag(v_it_571_))
{
case 0:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_box(2);
v___x_577_ = lean_apply_4(v_lift_570_, lean_box(0), lean_box(0), v___f_575_, v___x_576_);
return v___x_577_;
}
case 1:
{
lean_object* v_a_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_619_; 
v_a_578_ = lean_ctor_get(v_it_571_, 0);
v_a_579_ = lean_ctor_get(v_it_571_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_it_571_);
if (v_isSharedCheck_619_ == 0)
{
v___x_581_ = v_it_571_;
v_isShared_582_ = v_isSharedCheck_619_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_inc(v_a_578_);
lean_dec(v_it_571_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_619_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_start_583_; lean_object* v_stop_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_start_583_ = lean_ctor_get(v_a_578_, 1);
v_stop_584_ = lean_ctor_get(v_a_578_, 2);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_nat_sub(v_stop_584_, v_start_583_);
v___x_587_ = lean_nat_dec_lt(v___x_585_, v___x_586_);
lean_dec(v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_del_object(v___x_581_);
lean_dec_ref(v_a_578_);
v___x_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_588_, 0, v_a_579_);
v___x_589_ = lean_apply_4(v_lift_570_, lean_box(0), lean_box(0), v___f_575_, v___x_588_);
return v___x_589_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_z_593_; 
v___x_590_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_578_);
v___x_591_ = l_Subarray_drop___redArg(v_a_578_, v___x_590_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_591_);
v_z_593_ = v___x_581_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_a_579_);
v_z_593_ = v_reuseFailAlloc_618_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; 
v___x_594_ = l_Subarray_get___redArg(v_a_578_, v___x_585_);
lean_dec_ref(v_a_578_);
switch(lean_obj_tag(v___x_594_))
{
case 0:
{
lean_object* v_key_595_; lean_object* v_val_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_605_; 
v_key_595_ = lean_ctor_get(v___x_594_, 0);
v_val_596_ = lean_ctor_get(v___x_594_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_605_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_val_596_);
lean_inc(v_key_595_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_key_595_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_val_596_);
v___x_601_ = v_reuseFailAlloc_604_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v_z_593_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = lean_apply_4(v_lift_570_, lean_box(0), lean_box(0), v___f_575_, v___x_602_);
return v___x_603_;
}
}
}
case 1:
{
lean_object* v_node_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_615_; 
v_node_606_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_615_ == 0)
{
v___x_608_ = v___x_594_;
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_node_606_);
lean_dec(v___x_594_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_606_, v_z_593_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_614_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; 
v___x_613_ = lean_apply_4(v_lift_570_, lean_box(0), lean_box(0), v___f_575_, v___x_612_);
return v___x_613_;
}
}
}
default: 
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v_z_593_);
v___x_617_ = lean_apply_4(v_lift_570_, lean_box(0), lean_box(0), v___f_575_, v___x_616_);
return v___x_617_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_620_; lean_object* v_keys_621_; lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_644_; 
v_vals_620_ = lean_ctor_get(v_it_571_, 1);
v_keys_621_ = lean_ctor_get(v_it_571_, 0);
v_a_622_ = lean_ctor_get(v_it_571_, 2);
v_isSharedCheck_644_ = !lean_is_exclusive(v_it_571_);
if (v_isSharedCheck_644_ == 0)
{
v___x_624_ = v_it_571_;
v_isShared_625_ = v_isSharedCheck_644_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_inc(v_vals_620_);
lean_inc(v_keys_621_);
lean_dec(v_it_571_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_644_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_start_626_; lean_object* v_stop_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_start_626_ = lean_ctor_get(v_vals_620_, 1);
v_stop_627_ = lean_ctor_get(v_vals_620_, 2);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_nat_sub(v_stop_627_, v_start_626_);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
lean_dec(v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_del_object(v___x_624_);
lean_dec_ref(v_keys_621_);
lean_dec_ref(v_vals_620_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v_a_622_);
v___x_632_ = lean_apply_4(v_lift_570_, lean_box(0), lean_box(0), v___f_575_, v___x_631_);
return v___x_632_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_633_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_621_);
v___x_634_ = l_Subarray_drop___redArg(v_keys_621_, v___x_633_);
lean_inc_ref(v_vals_620_);
v___x_635_ = l_Subarray_drop___redArg(v_vals_620_, v___x_633_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v___x_635_);
lean_ctor_set(v___x_624_, 0, v___x_634_);
v___x_637_ = v___x_624_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_a_622_);
v___x_637_ = v_reuseFailAlloc_643_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_638_ = l_Subarray_get___redArg(v_keys_621_, v___x_628_);
lean_dec_ref(v_keys_621_);
v___x_639_ = l_Subarray_get___redArg(v_vals_620_, v___x_628_);
lean_dec_ref(v_vals_620_);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_637_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_apply_4(v_lift_570_, lean_box(0), lean_box(0), v___f_575_, v___x_641_);
return v___x_642_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3(lean_object* v_inst_645_, lean_object* v_lift_646_, lean_object* v_00_u03b3_647_, lean_object* v_Pl_648_, lean_object* v_it_649_, lean_object* v_init_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_toApplicative_652_; lean_object* v_toBind_653_; lean_object* v_toPure_654_; lean_object* v___f_655_; lean_object* v___x_656_; 
v_toApplicative_652_ = lean_ctor_get(v_inst_645_, 0);
lean_inc_ref(v_toApplicative_652_);
v_toBind_653_ = lean_ctor_get(v_inst_645_, 1);
lean_inc(v_toBind_653_);
lean_dec_ref(v_inst_645_);
v_toPure_654_ = lean_ctor_get(v_toApplicative_652_, 1);
lean_inc(v_toPure_654_);
lean_dec_ref(v_toApplicative_652_);
v___f_655_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_655_, 0, v_toPure_654_);
lean_closure_set(v___f_655_, 1, v___y_651_);
lean_closure_set(v___f_655_, 2, v_toBind_653_);
lean_closure_set(v___f_655_, 3, v_lift_646_);
v___x_656_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_655_, v_it_649_, v_init_650_, lean_box(0));
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg(lean_object* v_inst_657_){
_start:
{
lean_object* v___f_658_; 
v___f_658_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_658_, 0, v_inst_657_);
return v___f_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_n_661_, lean_object* v_inst_662_){
_start:
{
lean_object* v___f_663_; 
v___f_663_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_663_, 0, v_inst_662_);
return v___f_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___redArg(lean_object* v_map_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_box(0);
v___x_666_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_664_, v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter(lean_object* v_00_u03b1_667_, lean_object* v_00_u03b2_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_map_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box(0);
v___x_673_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_671_, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___boxed(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_map_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_PersistentHashMap_iter(v_00_u03b1_674_, v_00_u03b2_675_, v_inst_676_, v_inst_677_, v_map_678_);
lean_dec_ref(v_inst_677_);
lean_dec_ref(v_inst_676_);
return v_res_679_;
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
