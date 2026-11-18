// Lean compiler output
// Module: Lean.Data.Iterators.Producers.PersistentHashMap
// Imports: public import Init.Data.Array.Subarray public import Init.Data.Array.Subarray.Split public import Lean.Data.PersistentHashMap import Init.Data.Iterators.Consumers import Init.Omega import Init.Data.Slice.Array.Lemmas import Init.Data.Array.Mem import Init.Data.List.TakeDrop import Init.Data.List.Impl
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2_spec__3(lean_object* v_as_391_, size_t v_i_392_, size_t v_stop_393_, lean_object* v_b_394_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_eq(v_i_392_, v_stop_393_);
if (v___x_395_ == 0)
{
size_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_396_ = ((size_t)1ULL);
v___x_397_ = lean_usize_sub(v_i_392_, v___x_396_);
v___x_398_ = lean_array_uget_borrowed(v_as_391_, v___x_397_);
v___x_399_ = lean_nat_add(v___x_398_, v_b_394_);
lean_dec(v_b_394_);
v_i_392_ = v___x_397_;
v_b_394_ = v___x_399_;
goto _start;
}
else
{
return v_b_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2_spec__3___boxed(lean_object* v_as_401_, lean_object* v_i_402_, lean_object* v_stop_403_, lean_object* v_b_404_){
_start:
{
size_t v_i_boxed_405_; size_t v_stop_boxed_406_; lean_object* v_res_407_; 
v_i_boxed_405_ = lean_unbox_usize(v_i_402_);
lean_dec(v_i_402_);
v_stop_boxed_406_ = lean_unbox_usize(v_stop_403_);
lean_dec(v_stop_403_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2_spec__3(v_as_401_, v_i_boxed_405_, v_stop_boxed_406_, v_b_404_);
lean_dec_ref(v_as_401_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(lean_object* v_init_408_, lean_object* v_l_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_410_ = lean_array_mk(v_l_409_);
v___x_411_ = lean_array_get_size(v___x_410_);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_nat_dec_lt(v___x_412_, v___x_411_);
if (v___x_413_ == 0)
{
lean_dec_ref(v___x_410_);
return v_init_408_;
}
else
{
size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_usize_of_nat(v___x_411_);
v___x_415_ = ((size_t)0ULL);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2_spec__3(v___x_410_, v___x_414_, v___x_415_, v_init_408_);
lean_dec_ref(v___x_410_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(lean_object* v_l_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = l_List_foldrTR___at___00List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v___x_418_, v_l_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
if (lean_obj_tag(v_a_420_) == 0)
{
lean_object* v___x_422_; 
v___x_422_ = l_List_reverse___redArg(v_a_421_);
return v___x_422_;
}
else
{
lean_object* v_head_423_; lean_object* v_tail_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_433_; 
v_head_423_ = lean_ctor_get(v_a_420_, 0);
v_tail_424_ = lean_ctor_get(v_a_420_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_a_420_);
if (v_isSharedCheck_433_ == 0)
{
v___x_426_ = v_a_420_;
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_tail_424_);
lean_inc(v_head_423_);
lean_dec(v_a_420_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_head_423_);
lean_dec(v_head_423_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_a_421_);
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_a_421_);
v___x_430_ = v_reuseFailAlloc_432_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
v_a_420_ = v_tail_424_;
v_a_421_ = v___x_430_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(lean_object* v_a_434_, lean_object* v_b_435_){
_start:
{
lean_object* v_array_436_; lean_object* v_start_437_; lean_object* v_stop_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_451_; 
v_array_436_ = lean_ctor_get(v_a_434_, 0);
v_start_437_ = lean_ctor_get(v_a_434_, 1);
v_stop_438_ = lean_ctor_get(v_a_434_, 2);
v_isSharedCheck_451_ = !lean_is_exclusive(v_a_434_);
if (v_isSharedCheck_451_ == 0)
{
v___x_440_ = v_a_434_;
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_stop_438_);
lean_inc(v_start_437_);
lean_inc(v_array_436_);
lean_dec(v_a_434_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint8_t v___x_442_; 
v___x_442_ = lean_nat_dec_lt(v_start_437_, v_stop_438_);
if (v___x_442_ == 0)
{
lean_del_object(v___x_440_);
lean_dec(v_stop_438_);
lean_dec(v_start_437_);
lean_dec_ref(v_array_436_);
return v_b_435_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_start_437_, v___x_443_);
lean_inc_ref(v_array_436_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_444_);
v___x_446_ = v___x_440_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_array_436_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_stop_438_);
v___x_446_ = v_reuseFailAlloc_450_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_array_fget(v_array_436_, v_start_437_);
lean_dec(v_start_437_);
lean_dec_ref(v_array_436_);
v___x_448_ = lean_array_push(v_b_435_, v___x_447_);
v_a_434_ = v___x_446_;
v_b_435_ = v___x_448_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure___redArg(lean_object* v_es_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_455_ = ((lean_object*)(l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0));
v___x_456_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_es_454_, v___x_455_);
v___x_457_ = lean_array_to_list(v___x_456_);
v___x_458_ = lean_box(0);
v___x_459_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v___x_457_, v___x_458_);
v___x_460_ = l_List_sumTR___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_subarrayMeasure(lean_object* v_00_u03b1_461_, lean_object* v_00_u03b2_462_, lean_object* v_es_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_es_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0(lean_object* v_00_u03b1_465_, lean_object* v_00_u03b2_466_, lean_object* v_inst_467_, lean_object* v_R_468_, lean_object* v_a_469_, lean_object* v_b_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_a_469_, v_b_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1(lean_object* v_00_u03b1_472_, lean_object* v_00_u03b2_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(v_a_474_, v_a_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure___redArg(lean_object* v_x_477_){
_start:
{
switch(lean_obj_tag(v_x_477_))
{
case 0:
{
lean_object* v___x_478_; 
v___x_478_ = lean_unsigned_to_nat(0u);
return v___x_478_;
}
case 1:
{
lean_object* v_a_479_; lean_object* v_a_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_a_479_ = lean_ctor_get(v_x_477_, 0);
lean_inc_ref(v_a_479_);
v_a_480_ = lean_ctor_get(v_x_477_, 1);
lean_inc(v_a_480_);
lean_dec_ref_known(v_x_477_, 2);
v___x_481_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_a_479_);
v___x_482_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_480_);
v___x_483_ = lean_nat_add(v___x_481_, v___x_482_);
lean_dec(v___x_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v___x_483_, v___x_484_);
lean_dec(v___x_483_);
return v___x_485_;
}
default: 
{
lean_object* v_vals_486_; lean_object* v_a_487_; lean_object* v_start_488_; lean_object* v_stop_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_vals_486_ = lean_ctor_get(v_x_477_, 1);
lean_inc_ref(v_vals_486_);
v_a_487_ = lean_ctor_get(v_x_477_, 2);
lean_inc(v_a_487_);
lean_dec_ref_known(v_x_477_, 3);
v_start_488_ = lean_ctor_get(v_vals_486_, 1);
lean_inc(v_start_488_);
v_stop_489_ = lean_ctor_get(v_vals_486_, 2);
lean_inc(v_stop_489_);
lean_dec_ref(v_vals_486_);
v___x_490_ = lean_nat_sub(v_stop_489_, v_start_488_);
lean_dec(v_start_488_);
lean_dec(v_stop_489_);
v___x_491_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_487_);
v___x_492_ = lean_nat_add(v___x_490_, v___x_491_);
lean_dec(v___x_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_add(v___x_492_, v___x_493_);
lean_dec(v___x_492_);
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Zipper_measure(lean_object* v_00_u03b1_495_, lean_object* v_00_u03b2_496_, lean_object* v_x_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(lean_object* v_x_499_, lean_object* v_h__1_500_, lean_object* v_h__2_501_, lean_object* v_h__3_502_){
_start:
{
switch(lean_obj_tag(v_x_499_))
{
case 0:
{
lean_object* v_key_503_; lean_object* v_val_504_; lean_object* v___x_505_; 
lean_dec(v_h__3_502_);
lean_dec(v_h__1_500_);
v_key_503_ = lean_ctor_get(v_x_499_, 0);
lean_inc(v_key_503_);
v_val_504_ = lean_ctor_get(v_x_499_, 1);
lean_inc(v_val_504_);
lean_dec_ref_known(v_x_499_, 2);
v___x_505_ = lean_apply_2(v_h__2_501_, v_key_503_, v_val_504_);
return v___x_505_;
}
case 1:
{
lean_object* v_node_506_; lean_object* v___x_507_; 
lean_dec(v_h__2_501_);
lean_dec(v_h__1_500_);
v_node_506_ = lean_ctor_get(v_x_499_, 0);
lean_inc(v_node_506_);
lean_dec_ref_known(v_x_499_, 1);
v___x_507_ = lean_apply_1(v_h__3_502_, v_node_506_);
return v___x_507_;
}
default: 
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_h__3_502_);
lean_dec(v_h__2_501_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_apply_1(v_h__1_500_, v___x_508_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter(lean_object* v_00_u03b1_510_, lean_object* v_00_u03b2_511_, lean_object* v_motive_512_, lean_object* v_x_513_, lean_object* v_h__1_514_, lean_object* v_h__2_515_, lean_object* v_h__3_516_){
_start:
{
switch(lean_obj_tag(v_x_513_))
{
case 0:
{
lean_object* v_key_517_; lean_object* v_val_518_; lean_object* v___x_519_; 
lean_dec(v_h__3_516_);
lean_dec(v_h__1_514_);
v_key_517_ = lean_ctor_get(v_x_513_, 0);
lean_inc(v_key_517_);
v_val_518_ = lean_ctor_get(v_x_513_, 1);
lean_inc(v_val_518_);
lean_dec_ref_known(v_x_513_, 2);
v___x_519_ = lean_apply_2(v_h__2_515_, v_key_517_, v_val_518_);
return v___x_519_;
}
case 1:
{
lean_object* v_node_520_; lean_object* v___x_521_; 
lean_dec(v_h__2_515_);
lean_dec(v_h__1_514_);
v_node_520_ = lean_ctor_get(v_x_513_, 0);
lean_inc(v_node_520_);
lean_dec_ref_known(v_x_513_, 1);
v___x_521_ = lean_apply_1(v_h__3_516_, v_node_520_);
return v___x_521_;
}
default: 
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v_h__3_516_);
lean_dec(v_h__2_515_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_apply_1(v_h__1_514_, v___x_522_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(lean_object* v_x_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_, lean_object* v_h__3_527_){
_start:
{
switch(lean_obj_tag(v_x_524_))
{
case 0:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
v___x_528_ = lean_box(0);
v___x_529_ = lean_apply_1(v_h__1_525_, v___x_528_);
return v___x_529_;
}
case 1:
{
lean_object* v_a_530_; lean_object* v_a_531_; lean_object* v___x_532_; 
lean_dec(v_h__3_527_);
lean_dec(v_h__1_525_);
v_a_530_ = lean_ctor_get(v_x_524_, 0);
lean_inc_ref(v_a_530_);
v_a_531_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_a_531_);
lean_dec_ref_known(v_x_524_, 2);
v___x_532_ = lean_apply_2(v_h__2_526_, v_a_530_, v_a_531_);
return v___x_532_;
}
default: 
{
lean_object* v_keys_533_; lean_object* v_vals_534_; lean_object* v_a_535_; lean_object* v___x_536_; 
lean_dec(v_h__2_526_);
lean_dec(v_h__1_525_);
v_keys_533_ = lean_ctor_get(v_x_524_, 0);
lean_inc_ref(v_keys_533_);
v_vals_534_ = lean_ctor_get(v_x_524_, 1);
lean_inc_ref(v_vals_534_);
v_a_535_ = lean_ctor_get(v_x_524_, 2);
lean_inc(v_a_535_);
lean_dec_ref_known(v_x_524_, 3);
v___x_536_ = lean_apply_4(v_h__3_527_, v_keys_533_, v_vals_534_, lean_box(0), v_a_535_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter(lean_object* v_00_u03b1_537_, lean_object* v_00_u03b2_538_, lean_object* v_motive_539_, lean_object* v_x_540_, lean_object* v_h__1_541_, lean_object* v_h__2_542_, lean_object* v_h__3_543_){
_start:
{
switch(lean_obj_tag(v_x_540_))
{
case 0:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_h__3_543_);
lean_dec(v_h__2_542_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_apply_1(v_h__1_541_, v___x_544_);
return v___x_545_;
}
case 1:
{
lean_object* v_a_546_; lean_object* v_a_547_; lean_object* v___x_548_; 
lean_dec(v_h__3_543_);
lean_dec(v_h__1_541_);
v_a_546_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_a_546_);
v_a_547_ = lean_ctor_get(v_x_540_, 1);
lean_inc(v_a_547_);
lean_dec_ref_known(v_x_540_, 2);
v___x_548_ = lean_apply_2(v_h__2_542_, v_a_546_, v_a_547_);
return v___x_548_;
}
default: 
{
lean_object* v_keys_549_; lean_object* v_vals_550_; lean_object* v_a_551_; lean_object* v___x_552_; 
lean_dec(v_h__2_542_);
lean_dec(v_h__1_541_);
v_keys_549_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_keys_549_);
v_vals_550_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_vals_550_);
v_a_551_ = lean_ctor_get(v_x_540_, 2);
lean_inc(v_a_551_);
lean_dec_ref_known(v_x_540_, 3);
v___x_552_ = lean_apply_4(v_h__3_543_, v_keys_549_, v_vals_550_, lean_box(0), v_a_551_);
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = lean_box(0);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation___redArg();
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation(lean_object* v_00_u03b1_557_, lean_object* v_00_u03b2_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lean_box(0);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_560_, lean_object* v_recur_561_, lean_object* v_it_562_, lean_object* v_____do__lift_563_){
_start:
{
if (lean_obj_tag(v_____do__lift_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; 
lean_dec(v_it_562_);
lean_dec(v_recur_561_);
v_a_564_ = lean_ctor_get(v_____do__lift_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v_____do__lift_563_, 1);
v___x_565_ = lean_apply_2(v_toPure_560_, lean_box(0), v_a_564_);
return v___x_565_;
}
else
{
lean_object* v_a_566_; lean_object* v___x_567_; 
lean_dec(v_toPure_560_);
v_a_566_ = lean_ctor_get(v_____do__lift_563_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v_____do__lift_563_, 1);
v___x_567_ = lean_apply_4(v_recur_561_, v_it_562_, v_a_566_, lean_box(0), lean_box(0));
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_568_, lean_object* v_recur_569_, lean_object* v___y_570_, lean_object* v_acc_571_, lean_object* v_toBind_572_, lean_object* v_s_573_){
_start:
{
switch(lean_obj_tag(v_s_573_))
{
case 0:
{
lean_object* v_it_574_; lean_object* v_out_575_; lean_object* v___f_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_it_574_ = lean_ctor_get(v_s_573_, 0);
lean_inc(v_it_574_);
v_out_575_ = lean_ctor_get(v_s_573_, 1);
lean_inc(v_out_575_);
lean_dec_ref_known(v_s_573_, 2);
v___f_576_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_576_, 0, v_toPure_568_);
lean_closure_set(v___f_576_, 1, v_recur_569_);
lean_closure_set(v___f_576_, 2, v_it_574_);
v___x_577_ = lean_apply_3(v___y_570_, v_out_575_, lean_box(0), v_acc_571_);
v___x_578_ = lean_apply_4(v_toBind_572_, lean_box(0), lean_box(0), v___x_577_, v___f_576_);
return v___x_578_;
}
case 1:
{
lean_object* v_it_579_; lean_object* v___x_580_; 
lean_dec(v_toBind_572_);
lean_dec(v___y_570_);
lean_dec(v_toPure_568_);
v_it_579_ = lean_ctor_get(v_s_573_, 0);
lean_inc(v_it_579_);
lean_dec_ref_known(v_s_573_, 1);
v___x_580_ = lean_apply_4(v_recur_569_, v_it_579_, v_acc_571_, lean_box(0), lean_box(0));
return v___x_580_;
}
default: 
{
lean_object* v___x_581_; 
lean_dec(v_toBind_572_);
lean_dec(v___y_570_);
lean_dec(v_recur_569_);
v___x_581_ = lean_apply_2(v_toPure_568_, lean_box(0), v_acc_571_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_582_, lean_object* v___y_583_, lean_object* v_toBind_584_, lean_object* v_lift_585_, lean_object* v_it_586_, lean_object* v_acc_587_, lean_object* v_hP_588_, lean_object* v_recur_589_){
_start:
{
lean_object* v___f_590_; 
v___f_590_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_590_, 0, v_toPure_582_);
lean_closure_set(v___f_590_, 1, v_recur_589_);
lean_closure_set(v___f_590_, 2, v___y_583_);
lean_closure_set(v___f_590_, 3, v_acc_587_);
lean_closure_set(v___f_590_, 4, v_toBind_584_);
switch(lean_obj_tag(v_it_586_))
{
case 0:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_box(2);
v___x_592_ = lean_apply_4(v_lift_585_, lean_box(0), lean_box(0), v___f_590_, v___x_591_);
return v___x_592_;
}
case 1:
{
lean_object* v_a_593_; lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_634_; 
v_a_593_ = lean_ctor_get(v_it_586_, 0);
v_a_594_ = lean_ctor_get(v_it_586_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_it_586_);
if (v_isSharedCheck_634_ == 0)
{
v___x_596_ = v_it_586_;
v_isShared_597_ = v_isSharedCheck_634_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_inc(v_a_593_);
lean_dec(v_it_586_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_634_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v_start_598_; lean_object* v_stop_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_start_598_ = lean_ctor_get(v_a_593_, 1);
v_stop_599_ = lean_ctor_get(v_a_593_, 2);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_nat_sub(v_stop_599_, v_start_598_);
v___x_602_ = lean_nat_dec_lt(v___x_600_, v___x_601_);
lean_dec(v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_del_object(v___x_596_);
lean_dec_ref(v_a_593_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v_a_594_);
v___x_604_ = lean_apply_4(v_lift_585_, lean_box(0), lean_box(0), v___f_590_, v___x_603_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_z_608_; 
v___x_605_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_593_);
v___x_606_ = l_Subarray_drop___redArg(v_a_593_, v___x_605_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_606_);
v_z_608_ = v___x_596_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_a_594_);
v_z_608_ = v_reuseFailAlloc_633_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; 
v___x_609_ = l_Subarray_get___redArg(v_a_593_, v___x_600_);
lean_dec_ref(v_a_593_);
switch(lean_obj_tag(v___x_609_))
{
case 0:
{
lean_object* v_key_610_; lean_object* v_val_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_620_; 
v_key_610_ = lean_ctor_get(v___x_609_, 0);
v_val_611_ = lean_ctor_get(v___x_609_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_620_ == 0)
{
v___x_613_ = v___x_609_;
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_val_611_);
lean_inc(v_key_610_);
lean_dec(v___x_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_key_610_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_val_611_);
v___x_616_ = v_reuseFailAlloc_619_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v_z_608_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_apply_4(v_lift_585_, lean_box(0), lean_box(0), v___f_590_, v___x_617_);
return v___x_618_;
}
}
}
case 1:
{
lean_object* v_node_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_630_; 
v_node_621_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_630_ == 0)
{
v___x_623_ = v___x_609_;
v_isShared_624_ = v_isSharedCheck_630_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_node_621_);
lean_dec(v___x_609_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_630_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_625_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_621_, v_z_608_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_629_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; 
v___x_628_ = lean_apply_4(v_lift_585_, lean_box(0), lean_box(0), v___f_590_, v___x_627_);
return v___x_628_;
}
}
}
default: 
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v_z_608_);
v___x_632_ = lean_apply_4(v_lift_585_, lean_box(0), lean_box(0), v___f_590_, v___x_631_);
return v___x_632_;
}
}
}
}
}
}
default: 
{
lean_object* v_vals_635_; lean_object* v_keys_636_; lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_659_; 
v_vals_635_ = lean_ctor_get(v_it_586_, 1);
v_keys_636_ = lean_ctor_get(v_it_586_, 0);
v_a_637_ = lean_ctor_get(v_it_586_, 2);
v_isSharedCheck_659_ = !lean_is_exclusive(v_it_586_);
if (v_isSharedCheck_659_ == 0)
{
v___x_639_ = v_it_586_;
v_isShared_640_ = v_isSharedCheck_659_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_inc(v_vals_635_);
lean_inc(v_keys_636_);
lean_dec(v_it_586_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_659_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_start_641_; lean_object* v_stop_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_start_641_ = lean_ctor_get(v_vals_635_, 1);
v_stop_642_ = lean_ctor_get(v_vals_635_, 2);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_nat_sub(v_stop_642_, v_start_641_);
v___x_645_ = lean_nat_dec_lt(v___x_643_, v___x_644_);
lean_dec(v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_del_object(v___x_639_);
lean_dec_ref(v_keys_636_);
lean_dec_ref(v_vals_635_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v_a_637_);
v___x_647_ = lean_apply_4(v_lift_585_, lean_box(0), lean_box(0), v___f_590_, v___x_646_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_648_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_keys_636_);
v___x_649_ = l_Subarray_drop___redArg(v_keys_636_, v___x_648_);
lean_inc_ref(v_vals_635_);
v___x_650_ = l_Subarray_drop___redArg(v_vals_635_, v___x_648_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v___x_650_);
lean_ctor_set(v___x_639_, 0, v___x_649_);
v___x_652_ = v___x_639_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_a_637_);
v___x_652_ = v_reuseFailAlloc_658_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_653_ = l_Subarray_get___redArg(v_keys_636_, v___x_643_);
lean_dec_ref(v_keys_636_);
v___x_654_ = l_Subarray_get___redArg(v_vals_635_, v___x_643_);
lean_dec_ref(v_vals_635_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_652_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_apply_4(v_lift_585_, lean_box(0), lean_box(0), v___f_590_, v___x_656_);
return v___x_657_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3(lean_object* v_inst_660_, lean_object* v_lift_661_, lean_object* v_00_u03b3_662_, lean_object* v_Pl_663_, lean_object* v_it_664_, lean_object* v_init_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_toApplicative_667_; lean_object* v_toBind_668_; lean_object* v_toPure_669_; lean_object* v___f_670_; lean_object* v___x_671_; 
v_toApplicative_667_ = lean_ctor_get(v_inst_660_, 0);
lean_inc_ref(v_toApplicative_667_);
v_toBind_668_ = lean_ctor_get(v_inst_660_, 1);
lean_inc(v_toBind_668_);
lean_dec_ref(v_inst_660_);
v_toPure_669_ = lean_ctor_get(v_toApplicative_667_, 1);
lean_inc(v_toPure_669_);
lean_dec_ref(v_toApplicative_667_);
v___f_670_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_670_, 0, v_toPure_669_);
lean_closure_set(v___f_670_, 1, v___y_666_);
lean_closure_set(v___f_670_, 2, v_toBind_668_);
lean_closure_set(v___f_670_, 3, v_lift_661_);
v___x_671_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_670_, v_it_664_, v_init_665_, lean_box(0));
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop___redArg(lean_object* v_inst_672_){
_start:
{
lean_object* v___f_673_; 
v___f_673_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_673_, 0, v_inst_672_);
return v___f_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instIteratorLoop(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_n_676_, lean_object* v_inst_677_){
_start:
{
lean_object* v___f_678_; 
v___f_678_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_678_, 0, v_inst_677_);
return v___f_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___redArg(lean_object* v_map_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_679_, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_map_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_box(0);
v___x_688_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_686_, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_iter___boxed(lean_object* v_00_u03b1_689_, lean_object* v_00_u03b2_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_map_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_PersistentHashMap_iter(v_00_u03b1_689_, v_00_u03b2_690_, v_inst_691_, v_inst_692_, v_map_693_);
lean_dec_ref(v_inst_692_);
lean_dec_ref(v_inst_691_);
return v_res_694_;
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
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
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
res = runtime_initialize_Init_Data_List_Impl(builtin);
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
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
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
res = initialize_Init_Data_List_Impl(builtin);
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
