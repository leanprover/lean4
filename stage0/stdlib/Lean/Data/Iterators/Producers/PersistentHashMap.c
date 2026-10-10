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
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_instIterator___redArg(){
_start:
{
lean_object* v___f_281_; 
v___f_281_ = ((lean_object*)(l_Lean_PersistentHashMap_instIterator___redArg___closed__0));
return v___f_281_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_instIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_282_;
v_res_282_ = l_Lean_PersistentHashMap_instIterator___redArg();
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator___redArg___boxed(lean_object* v___dummy_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_PersistentHashMap_instIterator___redArg();
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIterator(lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_){
_start:
{
lean_object* v___f_287_; 
v___f_287_ = ((lean_object*)(l_Lean_PersistentHashMap_instIterator___redArg___closed__0));
return v___f_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(lean_object* v_es_288_, lean_object* v_i_289_){
_start:
{
lean_object* v___y_291_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_array_get_size(v_es_288_);
v___x_297_ = lean_nat_dec_lt(v_i_289_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_unsigned_to_nat(0u);
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_array_fget_borrowed(v_es_288_, v_i_289_);
if (lean_obj_tag(v___x_299_) == 1)
{
lean_object* v_node_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_node_300_ = lean_ctor_get(v___x_299_, 0);
v___x_301_ = lean_unsigned_to_nat(2u);
v___x_302_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_300_);
v___x_303_ = lean_nat_add(v___x_301_, v___x_302_);
lean_dec(v___x_302_);
v___y_291_ = v___x_303_;
goto v___jp_290_;
}
else
{
lean_object* v___x_304_; 
v___x_304_ = lean_unsigned_to_nat(1u);
v___y_291_ = v___x_304_;
goto v___jp_290_;
}
}
v___jp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_add(v_i_289_, v___x_292_);
v___x_294_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_288_, v___x_293_);
lean_dec(v___x_293_);
v___x_295_ = lean_nat_add(v___y_291_, v___x_294_);
lean_dec(v___x_294_);
lean_dec(v___y_291_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___redArg(lean_object* v_node_305_){
_start:
{
if (lean_obj_tag(v_node_305_) == 0)
{
lean_object* v_es_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_es_306_ = lean_ctor_get(v_node_305_, 0);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_306_, v___x_307_);
return v___x_308_;
}
else
{
lean_object* v_vs_309_; lean_object* v___x_310_; 
v_vs_309_ = lean_ctor_get(v_node_305_, 1);
v___x_310_ = lean_array_get_size(v_vs_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___redArg___boxed(lean_object* v_node_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_311_);
lean_dec_ref(v_node_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg___boxed(lean_object* v_es_313_, lean_object* v_i_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_313_, v_i_314_);
lean_dec(v_i_314_);
lean_dec_ref(v_es_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(lean_object* v_00_u03b1_316_, lean_object* v_00_u03b2_317_, lean_object* v_es_318_, lean_object* v_i_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_318_, v_i_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___boxed(lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_es_323_, lean_object* v_i_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(v_00_u03b1_321_, v_00_u03b2_322_, v_es_323_, v_i_324_);
lean_dec(v_i_324_);
lean_dec_ref(v_es_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure(lean_object* v_00_u03b1_326_, lean_object* v_00_u03b2_327_, lean_object* v_node_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_measure___boxed(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b2_331_, lean_object* v_node_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_PersistentHashMap_Node_measure(v_00_u03b1_330_, v_00_u03b2_331_, v_node_332_);
lean_dec_ref(v_node_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter___redArg(lean_object* v_x_334_, lean_object* v_h__1_335_, lean_object* v_h__2_336_, lean_object* v_h__3_337_){
_start:
{
switch(lean_obj_tag(v_x_334_))
{
case 0:
{
lean_object* v_key_338_; lean_object* v_val_339_; lean_object* v___x_340_; 
lean_dec(v_h__3_337_);
lean_dec(v_h__1_335_);
v_key_338_ = lean_ctor_get(v_x_334_, 0);
lean_inc(v_key_338_);
v_val_339_ = lean_ctor_get(v_x_334_, 1);
lean_inc(v_val_339_);
lean_dec_ref_known(v_x_334_, 2);
v___x_340_ = lean_apply_3(v_h__2_336_, v_key_338_, v_val_339_, lean_box(0));
return v___x_340_;
}
case 1:
{
lean_object* v_node_341_; lean_object* v___x_342_; 
lean_dec(v_h__2_336_);
lean_dec(v_h__1_335_);
v_node_341_ = lean_ctor_get(v_x_334_, 0);
lean_inc(v_node_341_);
lean_dec_ref_known(v_x_334_, 1);
v___x_342_ = lean_apply_2(v_h__3_337_, v_node_341_, lean_box(0));
return v___x_342_;
}
default: 
{
lean_object* v___x_343_; 
lean_dec(v_h__3_337_);
lean_dec(v_h__2_336_);
v___x_343_ = lean_apply_1(v_h__1_335_, lean_box(0));
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_motive_346_, lean_object* v_x_347_, lean_object* v_h__1_348_, lean_object* v_h__2_349_, lean_object* v_h__3_350_){
_start:
{
switch(lean_obj_tag(v_x_347_))
{
case 0:
{
lean_object* v_key_351_; lean_object* v_val_352_; lean_object* v___x_353_; 
lean_dec(v_h__3_350_);
lean_dec(v_h__1_348_);
v_key_351_ = lean_ctor_get(v_x_347_, 0);
lean_inc(v_key_351_);
v_val_352_ = lean_ctor_get(v_x_347_, 1);
lean_inc(v_val_352_);
lean_dec_ref_known(v_x_347_, 2);
v___x_353_ = lean_apply_3(v_h__2_349_, v_key_351_, v_val_352_, lean_box(0));
return v___x_353_;
}
case 1:
{
lean_object* v_node_354_; lean_object* v___x_355_; 
lean_dec(v_h__2_349_);
lean_dec(v_h__1_348_);
v_node_354_ = lean_ctor_get(v_x_347_, 0);
lean_inc(v_node_354_);
lean_dec_ref_known(v_x_347_, 1);
v___x_355_ = lean_apply_2(v_h__3_350_, v_node_354_, lean_box(0));
return v___x_355_;
}
default: 
{
lean_object* v___x_356_; 
lean_dec(v_h__3_350_);
lean_dec(v_h__2_349_);
v___x_356_ = lean_apply_1(v_h__1_348_, lean_box(0));
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter___redArg(lean_object* v_node_357_, lean_object* v_h__1_358_, lean_object* v_h__2_359_){
_start:
{
if (lean_obj_tag(v_node_357_) == 0)
{
lean_object* v_es_360_; lean_object* v___x_361_; 
lean_dec(v_h__2_359_);
v_es_360_ = lean_ctor_get(v_node_357_, 0);
lean_inc_ref(v_es_360_);
lean_dec_ref_known(v_node_357_, 1);
v___x_361_ = lean_apply_1(v_h__1_358_, v_es_360_);
return v___x_361_;
}
else
{
lean_object* v_ks_362_; lean_object* v_vs_363_; lean_object* v___x_364_; 
lean_dec(v_h__1_358_);
v_ks_362_ = lean_ctor_get(v_node_357_, 0);
lean_inc_ref(v_ks_362_);
v_vs_363_ = lean_ctor_get(v_node_357_, 1);
lean_inc_ref(v_vs_363_);
lean_dec_ref_known(v_node_357_, 2);
v___x_364_ = lean_apply_3(v_h__2_359_, v_ks_362_, v_vs_363_, lean_box(0));
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter(lean_object* v_00_u03b1_365_, lean_object* v_00_u03b2_366_, lean_object* v_motive_367_, lean_object* v_node_368_, lean_object* v_h__1_369_, lean_object* v_h__2_370_){
_start:
{
if (lean_obj_tag(v_node_368_) == 0)
{
lean_object* v_es_371_; lean_object* v___x_372_; 
lean_dec(v_h__2_370_);
v_es_371_ = lean_ctor_get(v_node_368_, 0);
lean_inc_ref(v_es_371_);
lean_dec_ref_known(v_node_368_, 1);
v___x_372_ = lean_apply_1(v_h__1_369_, v_es_371_);
return v___x_372_;
}
else
{
lean_object* v_ks_373_; lean_object* v_vs_374_; lean_object* v___x_375_; 
lean_dec(v_h__1_369_);
v_ks_373_ = lean_ctor_get(v_node_368_, 0);
lean_inc_ref(v_ks_373_);
v_vs_374_ = lean_ctor_get(v_node_368_, 1);
lean_inc_ref(v_vs_374_);
lean_dec_ref_known(v_node_368_, 2);
v___x_375_ = lean_apply_3(v_h__2_370_, v_ks_373_, v_vs_374_, lean_box(0));
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg(lean_object* v_entry_376_){
_start:
{
if (lean_obj_tag(v_entry_376_) == 1)
{
lean_object* v_node_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_node_377_ = lean_ctor_get(v_entry_376_, 0);
v___x_378_ = lean_unsigned_to_nat(2u);
v___x_379_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_377_);
v___x_380_ = lean_nat_add(v___x_378_, v___x_379_);
lean_dec(v___x_379_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; 
v___x_381_ = lean_unsigned_to_nat(1u);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___redArg___boxed(lean_object* v_entry_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_382_);
lean_dec(v_entry_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure(lean_object* v_00_u03b1_384_, lean_object* v_00_u03b2_385_, lean_object* v_entry_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_measure___boxed(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_entry_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_PersistentHashMap_Entry_measure(v_00_u03b1_388_, v_00_u03b2_389_, v_entry_390_);
lean_dec(v_entry_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(lean_object* v_init_392_, lean_object* v_x_393_){
_start:
{
if (lean_obj_tag(v_x_393_) == 0)
{
lean_inc(v_init_392_);
return v_init_392_;
}
else
{
lean_object* v_head_394_; lean_object* v_tail_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_head_394_ = lean_ctor_get(v_x_393_, 0);
v_tail_395_ = lean_ctor_get(v_x_393_, 1);
v___x_396_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_392_, v_tail_395_);
v___x_397_ = lean_nat_add(v_head_394_, v___x_396_);
lean_dec(v___x_396_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2___boxed(lean_object* v_init_398_, lean_object* v_x_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_398_, v_x_399_);
lean_dec(v_x_399_);
lean_dec(v_init_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(lean_object* v_l_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v___x_402_, v_l_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2___boxed(lean_object* v_l_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v_l_404_);
lean_dec(v_l_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
if (lean_obj_tag(v_a_406_) == 0)
{
lean_object* v___x_408_; 
v___x_408_ = l_List_reverse___redArg(v_a_407_);
return v___x_408_;
}
else
{
lean_object* v_head_409_; lean_object* v_tail_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_419_; 
v_head_409_ = lean_ctor_get(v_a_406_, 0);
v_tail_410_ = lean_ctor_get(v_a_406_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_419_ == 0)
{
v___x_412_ = v_a_406_;
v_isShared_413_ = v_isSharedCheck_419_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_tail_410_);
lean_inc(v_head_409_);
lean_dec(v_a_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_419_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_head_409_);
lean_dec(v_head_409_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_a_407_);
lean_ctor_set(v___x_412_, 0, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_a_407_);
v___x_416_ = v_reuseFailAlloc_418_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
v_a_406_ = v_tail_410_;
v_a_407_ = v___x_416_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(lean_object* v_a_420_, lean_object* v_b_421_){
_start:
{
lean_object* v_array_422_; lean_object* v_start_423_; lean_object* v_stop_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_437_; 
v_array_422_ = lean_ctor_get(v_a_420_, 0);
v_start_423_ = lean_ctor_get(v_a_420_, 1);
v_stop_424_ = lean_ctor_get(v_a_420_, 2);
v_isSharedCheck_437_ = !lean_is_exclusive(v_a_420_);
if (v_isSharedCheck_437_ == 0)
{
v___x_426_ = v_a_420_;
v_isShared_427_ = v_isSharedCheck_437_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_stop_424_);
lean_inc(v_start_423_);
lean_inc(v_array_422_);
lean_dec(v_a_420_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_437_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___x_428_; 
v___x_428_ = lean_nat_dec_lt(v_start_423_, v_stop_424_);
if (v___x_428_ == 0)
{
lean_del_object(v___x_426_);
lean_dec(v_stop_424_);
lean_dec(v_start_423_);
lean_dec_ref(v_array_422_);
return v_b_421_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_add(v_start_423_, v___x_429_);
lean_inc_ref(v_array_422_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_430_);
v___x_432_ = v___x_426_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_array_422_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_stop_424_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_array_fget(v_array_422_, v_start_423_);
lean_dec(v_start_423_);
lean_dec_ref(v_array_422_);
v___x_434_ = lean_array_push(v_b_421_, v___x_433_);
v_a_420_ = v___x_432_;
v_b_421_ = v___x_434_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure___redArg(lean_object* v_es_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_441_ = ((lean_object*)(l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0));
v___x_442_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_es_440_, v___x_441_);
v___x_443_ = lean_array_to_list(v___x_442_);
v___x_444_ = lean_box(0);
v___x_445_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v___x_443_, v___x_444_);
v___x_446_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v___x_445_);
lean_dec(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure(lean_object* v_00_u03b1_447_, lean_object* v_00_u03b2_448_, lean_object* v_es_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_es_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0(lean_object* v_00_u03b1_451_, lean_object* v_00_u03b2_452_, lean_object* v_inst_453_, lean_object* v_R_454_, lean_object* v_a_455_, lean_object* v_b_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_a_455_, v_b_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1(lean_object* v_00_u03b1_458_, lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v_a_460_, v_a_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure___redArg(lean_object* v_x_463_){
_start:
{
switch(lean_obj_tag(v_x_463_))
{
case 0:
{
lean_object* v___x_464_; 
v___x_464_ = lean_unsigned_to_nat(0u);
return v___x_464_;
}
case 1:
{
lean_object* v_a_465_; lean_object* v_a_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_a_465_ = lean_ctor_get(v_x_463_, 0);
lean_inc_ref(v_a_465_);
v_a_466_ = lean_ctor_get(v_x_463_, 1);
lean_inc(v_a_466_);
lean_dec_ref_known(v_x_463_, 2);
v___x_467_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_a_465_);
v___x_468_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_466_);
v___x_469_ = lean_nat_add(v___x_467_, v___x_468_);
lean_dec(v___x_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_nat_add(v___x_469_, v___x_470_);
lean_dec(v___x_469_);
return v___x_471_;
}
default: 
{
lean_object* v_vals_472_; lean_object* v_a_473_; lean_object* v_start_474_; lean_object* v_stop_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_vals_472_ = lean_ctor_get(v_x_463_, 1);
lean_inc_ref(v_vals_472_);
v_a_473_ = lean_ctor_get(v_x_463_, 2);
lean_inc(v_a_473_);
lean_dec_ref_known(v_x_463_, 3);
v_start_474_ = lean_ctor_get(v_vals_472_, 1);
lean_inc(v_start_474_);
v_stop_475_ = lean_ctor_get(v_vals_472_, 2);
lean_inc(v_stop_475_);
lean_dec_ref(v_vals_472_);
v___x_476_ = lean_nat_sub(v_stop_475_, v_start_474_);
lean_dec(v_start_474_);
lean_dec(v_stop_475_);
v___x_477_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_473_);
v___x_478_ = lean_nat_add(v___x_476_, v___x_477_);
lean_dec(v___x_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_add(v___x_478_, v___x_479_);
lean_dec(v___x_478_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure(lean_object* v_00_u03b1_481_, lean_object* v_00_u03b2_482_, lean_object* v_x_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(lean_object* v_x_485_, lean_object* v_h__1_486_, lean_object* v_h__2_487_, lean_object* v_h__3_488_){
_start:
{
switch(lean_obj_tag(v_x_485_))
{
case 0:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_h__3_488_);
lean_dec(v_h__2_487_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_apply_1(v_h__1_486_, v___x_489_);
return v___x_490_;
}
case 1:
{
lean_object* v_a_491_; lean_object* v_a_492_; lean_object* v___x_493_; 
lean_dec(v_h__3_488_);
lean_dec(v_h__1_486_);
v_a_491_ = lean_ctor_get(v_x_485_, 0);
lean_inc_ref(v_a_491_);
v_a_492_ = lean_ctor_get(v_x_485_, 1);
lean_inc(v_a_492_);
lean_dec_ref_known(v_x_485_, 2);
v___x_493_ = lean_apply_2(v_h__2_487_, v_a_491_, v_a_492_);
return v___x_493_;
}
default: 
{
lean_object* v_keys_494_; lean_object* v_vals_495_; lean_object* v_a_496_; lean_object* v___x_497_; 
lean_dec(v_h__2_487_);
lean_dec(v_h__1_486_);
v_keys_494_ = lean_ctor_get(v_x_485_, 0);
lean_inc_ref(v_keys_494_);
v_vals_495_ = lean_ctor_get(v_x_485_, 1);
lean_inc_ref(v_vals_495_);
v_a_496_ = lean_ctor_get(v_x_485_, 2);
lean_inc(v_a_496_);
lean_dec_ref_known(v_x_485_, 3);
v___x_497_ = lean_apply_4(v_h__3_488_, v_keys_494_, v_vals_495_, lean_box(0), v_a_496_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter(lean_object* v_00_u03b1_498_, lean_object* v_00_u03b2_499_, lean_object* v_motive_500_, lean_object* v_x_501_, lean_object* v_h__1_502_, lean_object* v_h__2_503_, lean_object* v_h__3_504_){
_start:
{
switch(lean_obj_tag(v_x_501_))
{
case 0:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v_h__3_504_);
lean_dec(v_h__2_503_);
v___x_505_ = lean_box(0);
v___x_506_ = lean_apply_1(v_h__1_502_, v___x_505_);
return v___x_506_;
}
case 1:
{
lean_object* v_a_507_; lean_object* v_a_508_; lean_object* v___x_509_; 
lean_dec(v_h__3_504_);
lean_dec(v_h__1_502_);
v_a_507_ = lean_ctor_get(v_x_501_, 0);
lean_inc_ref(v_a_507_);
v_a_508_ = lean_ctor_get(v_x_501_, 1);
lean_inc(v_a_508_);
lean_dec_ref_known(v_x_501_, 2);
v___x_509_ = lean_apply_2(v_h__2_503_, v_a_507_, v_a_508_);
return v___x_509_;
}
default: 
{
lean_object* v_keys_510_; lean_object* v_vals_511_; lean_object* v_a_512_; lean_object* v___x_513_; 
lean_dec(v_h__2_503_);
lean_dec(v_h__1_502_);
v_keys_510_ = lean_ctor_get(v_x_501_, 0);
lean_inc_ref(v_keys_510_);
v_vals_511_ = lean_ctor_get(v_x_501_, 1);
lean_inc_ref(v_vals_511_);
v_a_512_ = lean_ctor_get(v_x_501_, 2);
lean_inc(v_a_512_);
lean_dec_ref_known(v_x_501_, 3);
v___x_513_ = lean_apply_4(v_h__3_504_, v_keys_510_, v_vals_511_, lean_box(0), v_a_512_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(lean_object* v_x_514_, lean_object* v_h__1_515_, lean_object* v_h__2_516_, lean_object* v_h__3_517_){
_start:
{
switch(lean_obj_tag(v_x_514_))
{
case 0:
{
lean_object* v_key_518_; lean_object* v_val_519_; lean_object* v___x_520_; 
lean_dec(v_h__3_517_);
lean_dec(v_h__1_515_);
v_key_518_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_key_518_);
v_val_519_ = lean_ctor_get(v_x_514_, 1);
lean_inc(v_val_519_);
lean_dec_ref_known(v_x_514_, 2);
v___x_520_ = lean_apply_2(v_h__2_516_, v_key_518_, v_val_519_);
return v___x_520_;
}
case 1:
{
lean_object* v_node_521_; lean_object* v___x_522_; 
lean_dec(v_h__2_516_);
lean_dec(v_h__1_515_);
v_node_521_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_node_521_);
lean_dec_ref_known(v_x_514_, 1);
v___x_522_ = lean_apply_1(v_h__3_517_, v_node_521_);
return v___x_522_;
}
default: 
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec(v_h__3_517_);
lean_dec(v_h__2_516_);
v___x_523_ = lean_box(0);
v___x_524_ = lean_apply_1(v_h__1_515_, v___x_523_);
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter(lean_object* v_00_u03b1_525_, lean_object* v_00_u03b2_526_, lean_object* v_motive_527_, lean_object* v_x_528_, lean_object* v_h__1_529_, lean_object* v_h__2_530_, lean_object* v_h__3_531_){
_start:
{
switch(lean_obj_tag(v_x_528_))
{
case 0:
{
lean_object* v_key_532_; lean_object* v_val_533_; lean_object* v___x_534_; 
lean_dec(v_h__3_531_);
lean_dec(v_h__1_529_);
v_key_532_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_key_532_);
v_val_533_ = lean_ctor_get(v_x_528_, 1);
lean_inc(v_val_533_);
lean_dec_ref_known(v_x_528_, 2);
v___x_534_ = lean_apply_2(v_h__2_530_, v_key_532_, v_val_533_);
return v___x_534_;
}
case 1:
{
lean_object* v_node_535_; lean_object* v___x_536_; 
lean_dec(v_h__2_530_);
lean_dec(v_h__1_529_);
v_node_535_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_node_535_);
lean_dec_ref_known(v_x_528_, 1);
v___x_536_ = lean_apply_1(v_h__3_531_, v_node_535_);
return v___x_536_;
}
default: 
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_h__3_531_);
lean_dec(v_h__2_530_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_apply_1(v_h__1_529_, v___x_537_);
return v___x_538_;
}
}
}
}
lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_box(0);
return v___x_540_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_541_;
v_res_541_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg();
stack->m_obj
 = v_res_541_;
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
