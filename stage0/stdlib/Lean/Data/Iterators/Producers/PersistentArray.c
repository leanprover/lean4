// Lean compiler output
// Module: Lean.Data.Iterators.Producers.PersistentArray
// Imports: public import Lean.Data.PersistentArray public import Init.Data.Iterators.Consumers.Monadic.Loop import Init.Data.Iterators.Consumers import Init.Omega import Init.Data.Array.Mem import Init.Data.List.TakeDrop
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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_done_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_consLeaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_consLeaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_consNodes_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_consNodes_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_done_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_consLeaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_consLeaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_consNodes_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_consNodes_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNode___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_prependNode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_prependNode___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_prependNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_prependNode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNodeFrom___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNodeFrom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNodeFrom(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNodeFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_prependNode_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_prependNode_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_step(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_step(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIterator___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_PersistentArray_Zipper_instIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_Zipper_instIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_Zipper_instIterator___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentArray_Zipper_instIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIterator___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIterator(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIterator___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_PersistentArray_RevZipper_instIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_RevZipper_instIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_RevZipper_instIterator___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentArray_RevZipper_instIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIterator___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIterator(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_nodeMeasure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_nodesMeasure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_nodeMeasure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_nodesMeasure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_nodesMeasure_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_nodesMeasure_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_measure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_measure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_nodeMeasure_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_nodeMeasure_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_measure_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_measure_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_instFinitenessRelation(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_instFinitenessRelation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iterFromIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iterFromIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iterFromIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iterFromIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_revIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_revIter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_revIter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_revIter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_PersistentArray_Zipper_ctorIdx___impl___redArg(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_PersistentArray_Zipper_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
if (lean_obj_tag(v_t_11_) == 0)
{
return v_k_12_;
}
else
{
lean_object* v_vs_13_; lean_object* v_i_14_; lean_object* v_a_15_; lean_object* v___x_16_; 
v_vs_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_vs_13_);
v_i_14_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_i_14_);
v_a_15_ = lean_ctor_get(v_t_11_, 2);
lean_inc(v_a_15_);
lean_dec(v_t_11_);
v___x_16_ = lean_apply_3(v_k_12_, v_vs_13_, v_i_14_, v_a_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorElim(lean_object* v_00_u03b1_17_, lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_PersistentArray_Zipper_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_ctorElim___boxed(lean_object* v_00_u03b1_24_, lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_PersistentArray_Zipper_ctorElim(v_00_u03b1_24_, v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_done_elim___redArg(lean_object* v_t_31_, lean_object* v_done_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_PersistentArray_Zipper_ctorElim___redArg(v_t_31_, v_done_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_done_elim(lean_object* v_00_u03b1_34_, lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_done_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_PersistentArray_Zipper_ctorElim___redArg(v_t_36_, v_done_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_consLeaf_elim___redArg(lean_object* v_t_40_, lean_object* v_consLeaf_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_PersistentArray_Zipper_ctorElim___redArg(v_t_40_, v_consLeaf_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_consLeaf_elim(lean_object* v_00_u03b1_43_, lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_consLeaf_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_PersistentArray_Zipper_ctorElim___redArg(v_t_45_, v_consLeaf_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_consNodes_elim___redArg(lean_object* v_t_49_, lean_object* v_consNodes_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_PersistentArray_Zipper_ctorElim___redArg(v_t_49_, v_consNodes_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_consNodes_elim(lean_object* v_00_u03b1_52_, lean_object* v_motive_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_consNodes_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_PersistentArray_Zipper_ctorElim___redArg(v_t_54_, v_consNodes_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorIdx___impl___redArg(lean_object* v_x_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_obj_tag_nat(v_x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorIdx___impl___redArg___boxed(lean_object* v_x_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_PersistentArray_RevZipper_ctorIdx___impl___redArg(v_x_60_);
lean_dec(v_x_60_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorIdx___impl(lean_object* v_00_u03b1_62_, lean_object* v_x_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_tag_nat(v_x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorIdx___impl___boxed(lean_object* v_00_u03b1_65_, lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_PersistentArray_RevZipper_ctorIdx___impl(v_00_u03b1_65_, v_x_66_);
lean_dec(v_x_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorElim___redArg(lean_object* v_t_68_, lean_object* v_k_69_){
_start:
{
if (lean_obj_tag(v_t_68_) == 0)
{
return v_k_69_;
}
else
{
lean_object* v_vs_70_; lean_object* v_i_71_; lean_object* v_a_72_; lean_object* v___x_73_; 
v_vs_70_ = lean_ctor_get(v_t_68_, 0);
lean_inc_ref(v_vs_70_);
v_i_71_ = lean_ctor_get(v_t_68_, 1);
lean_inc(v_i_71_);
v_a_72_ = lean_ctor_get(v_t_68_, 2);
lean_inc(v_a_72_);
lean_dec(v_t_68_);
v___x_73_ = lean_apply_3(v_k_69_, v_vs_70_, v_i_71_, v_a_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorElim(lean_object* v_00_u03b1_74_, lean_object* v_motive_75_, lean_object* v_ctorIdx_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_k_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_PersistentArray_RevZipper_ctorElim___redArg(v_t_77_, v_k_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_ctorElim___boxed(lean_object* v_00_u03b1_81_, lean_object* v_motive_82_, lean_object* v_ctorIdx_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_k_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_PersistentArray_RevZipper_ctorElim(v_00_u03b1_81_, v_motive_82_, v_ctorIdx_83_, v_t_84_, v_h_85_, v_k_86_);
lean_dec(v_ctorIdx_83_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_done_elim___redArg(lean_object* v_t_88_, lean_object* v_done_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_PersistentArray_RevZipper_ctorElim___redArg(v_t_88_, v_done_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_done_elim(lean_object* v_00_u03b1_91_, lean_object* v_motive_92_, lean_object* v_t_93_, lean_object* v_h_94_, lean_object* v_done_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_PersistentArray_RevZipper_ctorElim___redArg(v_t_93_, v_done_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_consLeaf_elim___redArg(lean_object* v_t_97_, lean_object* v_consLeaf_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_PersistentArray_RevZipper_ctorElim___redArg(v_t_97_, v_consLeaf_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_consLeaf_elim(lean_object* v_00_u03b1_100_, lean_object* v_motive_101_, lean_object* v_t_102_, lean_object* v_h_103_, lean_object* v_consLeaf_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_PersistentArray_RevZipper_ctorElim___redArg(v_t_102_, v_consLeaf_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_consNodes_elim___redArg(lean_object* v_t_106_, lean_object* v_consNodes_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_PersistentArray_RevZipper_ctorElim___redArg(v_t_106_, v_consNodes_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_consNodes_elim(lean_object* v_00_u03b1_109_, lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_consNodes_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_PersistentArray_RevZipper_ctorElim___redArg(v_t_111_, v_consNodes_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNode___redArg(lean_object* v_node_115_, lean_object* v_z_116_){
_start:
{
if (lean_obj_tag(v_node_115_) == 0)
{
lean_object* v_cs_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_cs_117_ = lean_ctor_get(v_node_115_, 0);
v___x_118_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_cs_117_);
v___x_119_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_119_, 0, v_cs_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
lean_ctor_set(v___x_119_, 2, v_z_116_);
return v___x_119_;
}
else
{
lean_object* v_vs_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_vs_120_ = lean_ctor_get(v_node_115_, 0);
v___x_121_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_vs_120_);
v___x_122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_122_, 0, v_vs_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
lean_ctor_set(v___x_122_, 2, v_z_116_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNode___redArg___boxed(lean_object* v_node_123_, lean_object* v_z_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_PersistentArray_Zipper_prependNode___redArg(v_node_123_, v_z_124_);
lean_dec_ref(v_node_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNode(lean_object* v_00_u03b1_126_, lean_object* v_node_127_, lean_object* v_z_128_){
_start:
{
if (lean_obj_tag(v_node_127_) == 0)
{
lean_object* v_cs_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_cs_129_ = lean_ctor_get(v_node_127_, 0);
v___x_130_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_cs_129_);
v___x_131_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_131_, 0, v_cs_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
lean_ctor_set(v___x_131_, 2, v_z_128_);
return v___x_131_;
}
else
{
lean_object* v_vs_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_vs_132_ = lean_ctor_get(v_node_127_, 0);
v___x_133_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_vs_132_);
v___x_134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_134_, 0, v_vs_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
lean_ctor_set(v___x_134_, 2, v_z_128_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNode___boxed(lean_object* v_00_u03b1_135_, lean_object* v_node_136_, lean_object* v_z_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_PersistentArray_Zipper_prependNode(v_00_u03b1_135_, v_node_136_, v_z_137_);
lean_dec_ref(v_node_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_prependNode___redArg(lean_object* v_node_139_, lean_object* v_z_140_){
_start:
{
if (lean_obj_tag(v_node_139_) == 0)
{
lean_object* v_cs_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_cs_141_ = lean_ctor_get(v_node_139_, 0);
v___x_142_ = lean_array_get_size(v_cs_141_);
lean_inc_ref(v_cs_141_);
v___x_143_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_143_, 0, v_cs_141_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
lean_ctor_set(v___x_143_, 2, v_z_140_);
return v___x_143_;
}
else
{
lean_object* v_vs_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_vs_144_ = lean_ctor_get(v_node_139_, 0);
v___x_145_ = lean_array_get_size(v_vs_144_);
lean_inc_ref(v_vs_144_);
v___x_146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_146_, 0, v_vs_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
lean_ctor_set(v___x_146_, 2, v_z_140_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_prependNode___redArg___boxed(lean_object* v_node_147_, lean_object* v_z_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_PersistentArray_RevZipper_prependNode___redArg(v_node_147_, v_z_148_);
lean_dec_ref(v_node_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_prependNode(lean_object* v_00_u03b1_150_, lean_object* v_node_151_, lean_object* v_z_152_){
_start:
{
if (lean_obj_tag(v_node_151_) == 0)
{
lean_object* v_cs_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_cs_153_ = lean_ctor_get(v_node_151_, 0);
v___x_154_ = lean_array_get_size(v_cs_153_);
lean_inc_ref(v_cs_153_);
v___x_155_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_155_, 0, v_cs_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
lean_ctor_set(v___x_155_, 2, v_z_152_);
return v___x_155_;
}
else
{
lean_object* v_vs_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_vs_156_ = lean_ctor_get(v_node_151_, 0);
v___x_157_ = lean_array_get_size(v_vs_156_);
lean_inc_ref(v_vs_156_);
v___x_158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_158_, 0, v_vs_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
lean_ctor_set(v___x_158_, 2, v_z_152_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_prependNode___boxed(lean_object* v_00_u03b1_159_, lean_object* v_node_160_, lean_object* v_z_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_PersistentArray_RevZipper_prependNode(v_00_u03b1_159_, v_node_160_, v_z_161_);
lean_dec_ref(v_node_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNodeFrom___redArg(lean_object* v_node_163_, size_t v_i_164_, size_t v_shift_165_, lean_object* v_z_166_){
_start:
{
if (lean_obj_tag(v_node_163_) == 0)
{
lean_object* v_cs_167_; size_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_cs_167_ = lean_ctor_get(v_node_163_, 0);
v___x_168_ = lean_usize_shift_right(v_i_164_, v_shift_165_);
v___x_169_ = lean_usize_to_nat(v___x_168_);
v___x_170_ = lean_array_get_size(v_cs_167_);
v___x_171_ = lean_nat_dec_lt(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
lean_dec(v___x_169_);
return v_z_166_;
}
else
{
lean_object* v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_172_ = lean_array_fget_borrowed(v_cs_167_, v___x_169_);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_shift_left(v___x_173_, v_shift_165_);
v___x_175_ = lean_usize_sub(v___x_174_, v___x_173_);
v___x_176_ = lean_usize_land(v_i_164_, v___x_175_);
v___x_177_ = ((size_t)5ULL);
v___x_178_ = lean_usize_sub(v_shift_165_, v___x_177_);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v___x_169_, v___x_179_);
lean_dec(v___x_169_);
lean_inc_ref(v_cs_167_);
v___x_181_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_181_, 0, v_cs_167_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
lean_ctor_set(v___x_181_, 2, v_z_166_);
v_node_163_ = v___x_172_;
v_i_164_ = v___x_176_;
v_shift_165_ = v___x_178_;
v_z_166_ = v___x_181_;
goto _start;
}
}
else
{
lean_object* v_vs_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_vs_183_ = lean_ctor_get(v_node_163_, 0);
v___x_184_ = lean_usize_to_nat(v_i_164_);
lean_inc_ref(v_vs_183_);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v_vs_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
lean_ctor_set(v___x_185_, 2, v_z_166_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNodeFrom___redArg___boxed(lean_object* v_node_186_, lean_object* v_i_187_, lean_object* v_shift_188_, lean_object* v_z_189_){
_start:
{
size_t v_i_boxed_190_; size_t v_shift_boxed_191_; lean_object* v_res_192_; 
v_i_boxed_190_ = lean_unbox_usize(v_i_187_);
lean_dec(v_i_187_);
v_shift_boxed_191_ = lean_unbox_usize(v_shift_188_);
lean_dec(v_shift_188_);
v_res_192_ = l_Lean_PersistentArray_Zipper_prependNodeFrom___redArg(v_node_186_, v_i_boxed_190_, v_shift_boxed_191_, v_z_189_);
lean_dec_ref(v_node_186_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNodeFrom(lean_object* v_00_u03b1_193_, lean_object* v_node_194_, size_t v_i_195_, size_t v_shift_196_, lean_object* v_z_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_PersistentArray_Zipper_prependNodeFrom___redArg(v_node_194_, v_i_195_, v_shift_196_, v_z_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_prependNodeFrom___boxed(lean_object* v_00_u03b1_199_, lean_object* v_node_200_, lean_object* v_i_201_, lean_object* v_shift_202_, lean_object* v_z_203_){
_start:
{
size_t v_i_boxed_204_; size_t v_shift_boxed_205_; lean_object* v_res_206_; 
v_i_boxed_204_ = lean_unbox_usize(v_i_201_);
lean_dec(v_i_201_);
v_shift_boxed_205_ = lean_unbox_usize(v_shift_202_);
lean_dec(v_shift_202_);
v_res_206_ = l_Lean_PersistentArray_Zipper_prependNodeFrom(v_00_u03b1_199_, v_node_200_, v_i_boxed_204_, v_shift_boxed_205_, v_z_203_);
lean_dec_ref(v_node_200_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_prependNode_match__1_splitter___redArg(lean_object* v_node_207_, lean_object* v_h__1_208_, lean_object* v_h__2_209_){
_start:
{
if (lean_obj_tag(v_node_207_) == 0)
{
lean_object* v_cs_210_; lean_object* v___x_211_; 
lean_dec(v_h__1_208_);
v_cs_210_ = lean_ctor_get(v_node_207_, 0);
lean_inc_ref(v_cs_210_);
lean_dec_ref_known(v_node_207_, 1);
v___x_211_ = lean_apply_1(v_h__2_209_, v_cs_210_);
return v___x_211_;
}
else
{
lean_object* v_vs_212_; lean_object* v___x_213_; 
lean_dec(v_h__2_209_);
v_vs_212_ = lean_ctor_get(v_node_207_, 0);
lean_inc_ref(v_vs_212_);
lean_dec_ref_known(v_node_207_, 1);
v___x_213_ = lean_apply_1(v_h__1_208_, v_vs_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_prependNode_match__1_splitter(lean_object* v_00_u03b1_214_, lean_object* v_motive_215_, lean_object* v_node_216_, lean_object* v_h__1_217_, lean_object* v_h__2_218_){
_start:
{
if (lean_obj_tag(v_node_216_) == 0)
{
lean_object* v_cs_219_; lean_object* v___x_220_; 
lean_dec(v_h__1_217_);
v_cs_219_ = lean_ctor_get(v_node_216_, 0);
lean_inc_ref(v_cs_219_);
lean_dec_ref_known(v_node_216_, 1);
v___x_220_ = lean_apply_1(v_h__2_218_, v_cs_219_);
return v___x_220_;
}
else
{
lean_object* v_vs_221_; lean_object* v___x_222_; 
lean_dec(v_h__2_218_);
v_vs_221_ = lean_ctor_get(v_node_216_, 0);
lean_inc_ref(v_vs_221_);
lean_dec_ref_known(v_node_216_, 1);
v___x_222_ = lean_apply_1(v_h__1_217_, v_vs_221_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_step___redArg(lean_object* v_it_223_){
_start:
{
switch(lean_obj_tag(v_it_223_))
{
case 0:
{
lean_object* v___x_224_; 
v___x_224_ = lean_box(2);
return v___x_224_;
}
case 1:
{
lean_object* v_vs_225_; lean_object* v_i_226_; lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_241_; 
v_vs_225_ = lean_ctor_get(v_it_223_, 0);
v_i_226_ = lean_ctor_get(v_it_223_, 1);
v_a_227_ = lean_ctor_get(v_it_223_, 2);
v_isSharedCheck_241_ = !lean_is_exclusive(v_it_223_);
if (v_isSharedCheck_241_ == 0)
{
v___x_229_ = v_it_223_;
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_inc(v_i_226_);
lean_inc(v_vs_225_);
lean_dec(v_it_223_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_array_get_size(v_vs_225_);
v___x_232_ = lean_nat_dec_lt(v_i_226_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
lean_del_object(v___x_229_);
lean_dec(v_i_226_);
lean_dec_ref(v_vs_225_);
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v_a_227_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_nat_add(v_i_226_, v___x_234_);
lean_inc_ref(v_vs_225_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_235_);
v___x_237_ = v___x_229_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_vs_225_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_a_227_);
v___x_237_ = v_reuseFailAlloc_240_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_array_fget(v_vs_225_, v_i_226_);
lean_dec(v_i_226_);
lean_dec_ref(v_vs_225_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
return v___x_239_;
}
}
}
}
default: 
{
lean_object* v_cs_242_; lean_object* v_i_243_; lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_277_; 
v_cs_242_ = lean_ctor_get(v_it_223_, 0);
v_i_243_ = lean_ctor_get(v_it_223_, 1);
v_a_244_ = lean_ctor_get(v_it_223_, 2);
v_isSharedCheck_277_ = !lean_is_exclusive(v_it_223_);
if (v_isSharedCheck_277_ == 0)
{
v___x_246_ = v_it_223_;
v_isShared_247_ = v_isSharedCheck_277_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_inc(v_i_243_);
lean_inc(v_cs_242_);
lean_dec(v_it_223_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_277_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_array_get_size(v_cs_242_);
v___x_249_ = lean_nat_dec_lt(v_i_243_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_del_object(v___x_246_);
lean_dec(v_i_243_);
lean_dec_ref(v_cs_242_);
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v_a_244_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_251_ = lean_array_fget(v_cs_242_, v_i_243_);
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_nat_add(v_i_243_, v___x_252_);
lean_dec(v_i_243_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v___x_253_);
v___x_255_ = v___x_246_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_cs_242_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v_a_244_);
v___x_255_ = v_reuseFailAlloc_276_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_cs_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_265_; 
v_cs_256_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_265_ == 0)
{
v___x_258_ = v___x_251_;
v_isShared_259_ = v_isSharedCheck_265_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_cs_256_);
lean_dec(v___x_251_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_265_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_261_, 0, v_cs_256_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
lean_ctor_set(v___x_261_, 2, v___x_255_);
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 1);
lean_ctor_set(v___x_258_, 0, v___x_261_);
v___x_263_ = v___x_258_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_vs_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_275_; 
v_vs_266_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_275_ == 0)
{
v___x_268_ = v___x_251_;
v_isShared_269_ = v_isSharedCheck_275_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_vs_266_);
lean_dec(v___x_251_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_275_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_271_, 0, v_vs_266_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
lean_ctor_set(v___x_271_, 2, v___x_255_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_271_);
v___x_273_ = v___x_268_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_step(lean_object* v_00_u03b1_278_, lean_object* v_it_279_){
_start:
{
switch(lean_obj_tag(v_it_279_))
{
case 0:
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(2);
return v___x_280_;
}
case 1:
{
lean_object* v_vs_281_; lean_object* v_i_282_; lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_297_; 
v_vs_281_ = lean_ctor_get(v_it_279_, 0);
v_i_282_ = lean_ctor_get(v_it_279_, 1);
v_a_283_ = lean_ctor_get(v_it_279_, 2);
v_isSharedCheck_297_ = !lean_is_exclusive(v_it_279_);
if (v_isSharedCheck_297_ == 0)
{
v___x_285_ = v_it_279_;
v_isShared_286_ = v_isSharedCheck_297_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_inc(v_i_282_);
lean_inc(v_vs_281_);
lean_dec(v_it_279_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_297_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_array_get_size(v_vs_281_);
v___x_288_ = lean_nat_dec_lt(v_i_282_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
lean_del_object(v___x_285_);
lean_dec(v_i_282_);
lean_dec_ref(v_vs_281_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_a_283_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_add(v_i_282_, v___x_290_);
lean_inc_ref(v_vs_281_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_291_);
v___x_293_ = v___x_285_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_vs_281_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_a_283_);
v___x_293_ = v_reuseFailAlloc_296_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_array_fget(v_vs_281_, v_i_282_);
lean_dec(v_i_282_);
lean_dec_ref(v_vs_281_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
}
}
}
default: 
{
lean_object* v_cs_298_; lean_object* v_i_299_; lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_333_; 
v_cs_298_ = lean_ctor_get(v_it_279_, 0);
v_i_299_ = lean_ctor_get(v_it_279_, 1);
v_a_300_ = lean_ctor_get(v_it_279_, 2);
v_isSharedCheck_333_ = !lean_is_exclusive(v_it_279_);
if (v_isSharedCheck_333_ == 0)
{
v___x_302_ = v_it_279_;
v_isShared_303_ = v_isSharedCheck_333_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_inc(v_i_299_);
lean_inc(v_cs_298_);
lean_dec(v_it_279_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_333_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = lean_array_get_size(v_cs_298_);
v___x_305_ = lean_nat_dec_lt(v_i_299_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_del_object(v___x_302_);
lean_dec(v_i_299_);
lean_dec_ref(v_cs_298_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v_a_300_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_307_ = lean_array_fget(v_cs_298_, v_i_299_);
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_i_299_, v___x_308_);
lean_dec(v_i_299_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_309_);
v___x_311_ = v___x_302_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_cs_298_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_a_300_);
v___x_311_ = v_reuseFailAlloc_332_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_cs_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_321_; 
v_cs_312_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_321_ == 0)
{
v___x_314_ = v___x_307_;
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_cs_312_);
lean_dec(v___x_307_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_317_, 0, v_cs_312_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
lean_ctor_set(v___x_317_, 2, v___x_311_);
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 1);
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_vs_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_331_; 
v_vs_322_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_331_ == 0)
{
v___x_324_ = v___x_307_;
v_isShared_325_ = v_isSharedCheck_331_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_vs_322_);
lean_dec(v___x_307_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_331_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_327_, 0, v_vs_322_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
lean_ctor_set(v___x_327_, 2, v___x_311_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_327_);
v___x_329_ = v___x_324_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_step___redArg(lean_object* v_it_334_){
_start:
{
switch(lean_obj_tag(v_it_334_))
{
case 0:
{
lean_object* v___x_335_; 
v___x_335_ = lean_box(2);
return v___x_335_;
}
case 1:
{
lean_object* v_vs_336_; lean_object* v_i_337_; lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_355_; 
v_vs_336_ = lean_ctor_get(v_it_334_, 0);
v_i_337_ = lean_ctor_get(v_it_334_, 1);
v_a_338_ = lean_ctor_get(v_it_334_, 2);
v_isSharedCheck_355_ = !lean_is_exclusive(v_it_334_);
if (v_isSharedCheck_355_ == 0)
{
v___x_340_ = v_it_334_;
v_isShared_341_ = v_isSharedCheck_355_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_inc(v_i_337_);
lean_inc(v_vs_336_);
lean_dec(v_it_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_355_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_zero_342_; uint8_t v_isZero_343_; 
v_zero_342_ = lean_unsigned_to_nat(0u);
v_isZero_343_ = lean_nat_dec_eq(v_i_337_, v_zero_342_);
if (v_isZero_343_ == 1)
{
lean_object* v___x_344_; 
lean_del_object(v___x_340_);
lean_dec(v_i_337_);
lean_dec_ref(v_vs_336_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v_a_338_);
return v___x_344_;
}
else
{
lean_object* v_one_345_; lean_object* v_n_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_one_345_ = lean_unsigned_to_nat(1u);
v_n_346_ = lean_nat_sub(v_i_337_, v_one_345_);
lean_dec(v_i_337_);
v___x_347_ = lean_array_get_size(v_vs_336_);
v___x_348_ = lean_nat_dec_lt(v_n_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec(v_n_346_);
lean_del_object(v___x_340_);
lean_dec_ref(v_vs_336_);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v_a_338_);
return v___x_349_;
}
else
{
lean_object* v___x_351_; 
lean_inc(v_n_346_);
lean_inc_ref(v_vs_336_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v_n_346_);
v___x_351_ = v___x_340_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_vs_336_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_n_346_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_a_338_);
v___x_351_ = v_reuseFailAlloc_354_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_array_fget(v_vs_336_, v_n_346_);
lean_dec(v_n_346_);
lean_dec_ref(v_vs_336_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
return v___x_353_;
}
}
}
}
}
default: 
{
lean_object* v_cs_356_; lean_object* v_i_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_394_; 
v_cs_356_ = lean_ctor_get(v_it_334_, 0);
v_i_357_ = lean_ctor_get(v_it_334_, 1);
v_a_358_ = lean_ctor_get(v_it_334_, 2);
v_isSharedCheck_394_ = !lean_is_exclusive(v_it_334_);
if (v_isSharedCheck_394_ == 0)
{
v___x_360_ = v_it_334_;
v_isShared_361_ = v_isSharedCheck_394_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_inc(v_i_357_);
lean_inc(v_cs_356_);
lean_dec(v_it_334_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_394_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_zero_362_; uint8_t v_isZero_363_; 
v_zero_362_ = lean_unsigned_to_nat(0u);
v_isZero_363_ = lean_nat_dec_eq(v_i_357_, v_zero_362_);
if (v_isZero_363_ == 1)
{
lean_object* v___x_364_; 
lean_del_object(v___x_360_);
lean_dec(v_i_357_);
lean_dec_ref(v_cs_356_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_a_358_);
return v___x_364_;
}
else
{
lean_object* v_one_365_; lean_object* v_n_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_one_365_ = lean_unsigned_to_nat(1u);
v_n_366_ = lean_nat_sub(v_i_357_, v_one_365_);
lean_dec(v_i_357_);
v___x_367_ = lean_array_get_size(v_cs_356_);
v___x_368_ = lean_nat_dec_lt(v_n_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_dec(v_n_366_);
lean_del_object(v___x_360_);
lean_dec_ref(v_cs_356_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v_a_358_);
return v___x_369_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_array_fget(v_cs_356_, v_n_366_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v_n_366_);
v___x_372_ = v___x_360_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_cs_356_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_n_366_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_a_358_);
v___x_372_ = v_reuseFailAlloc_393_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_cs_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_382_; 
v_cs_373_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_382_ == 0)
{
v___x_375_ = v___x_370_;
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_cs_373_);
lean_dec(v___x_370_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_377_ = lean_array_get_size(v_cs_373_);
v___x_378_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_378_, 0, v_cs_373_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
lean_ctor_set(v___x_378_, 2, v___x_372_);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 1);
lean_ctor_set(v___x_375_, 0, v___x_378_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
lean_object* v_vs_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_392_; 
v_vs_383_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_392_ == 0)
{
v___x_385_ = v___x_370_;
v_isShared_386_ = v_isSharedCheck_392_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_vs_383_);
lean_dec(v___x_370_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_392_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = lean_array_get_size(v_vs_383_);
v___x_388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_388_, 0, v_vs_383_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
lean_ctor_set(v___x_388_, 2, v___x_372_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_388_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_step(lean_object* v_00_u03b1_395_, lean_object* v_it_396_){
_start:
{
switch(lean_obj_tag(v_it_396_))
{
case 0:
{
lean_object* v___x_397_; 
v___x_397_ = lean_box(2);
return v___x_397_;
}
case 1:
{
lean_object* v_vs_398_; lean_object* v_i_399_; lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_417_; 
v_vs_398_ = lean_ctor_get(v_it_396_, 0);
v_i_399_ = lean_ctor_get(v_it_396_, 1);
v_a_400_ = lean_ctor_get(v_it_396_, 2);
v_isSharedCheck_417_ = !lean_is_exclusive(v_it_396_);
if (v_isSharedCheck_417_ == 0)
{
v___x_402_ = v_it_396_;
v_isShared_403_ = v_isSharedCheck_417_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_inc(v_i_399_);
lean_inc(v_vs_398_);
lean_dec(v_it_396_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_417_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_zero_404_; uint8_t v_isZero_405_; 
v_zero_404_ = lean_unsigned_to_nat(0u);
v_isZero_405_ = lean_nat_dec_eq(v_i_399_, v_zero_404_);
if (v_isZero_405_ == 1)
{
lean_object* v___x_406_; 
lean_del_object(v___x_402_);
lean_dec(v_i_399_);
lean_dec_ref(v_vs_398_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v_a_400_);
return v___x_406_;
}
else
{
lean_object* v_one_407_; lean_object* v_n_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_one_407_ = lean_unsigned_to_nat(1u);
v_n_408_ = lean_nat_sub(v_i_399_, v_one_407_);
lean_dec(v_i_399_);
v___x_409_ = lean_array_get_size(v_vs_398_);
v___x_410_ = lean_nat_dec_lt(v_n_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v_n_408_);
lean_del_object(v___x_402_);
lean_dec_ref(v_vs_398_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v_a_400_);
return v___x_411_;
}
else
{
lean_object* v___x_413_; 
lean_inc(v_n_408_);
lean_inc_ref(v_vs_398_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v_n_408_);
v___x_413_ = v___x_402_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_vs_398_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_n_408_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v_a_400_);
v___x_413_ = v_reuseFailAlloc_416_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_array_fget(v_vs_398_, v_n_408_);
lean_dec(v_n_408_);
lean_dec_ref(v_vs_398_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
return v___x_415_;
}
}
}
}
}
default: 
{
lean_object* v_cs_418_; lean_object* v_i_419_; lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_456_; 
v_cs_418_ = lean_ctor_get(v_it_396_, 0);
v_i_419_ = lean_ctor_get(v_it_396_, 1);
v_a_420_ = lean_ctor_get(v_it_396_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_it_396_);
if (v_isSharedCheck_456_ == 0)
{
v___x_422_ = v_it_396_;
v_isShared_423_ = v_isSharedCheck_456_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_inc(v_i_419_);
lean_inc(v_cs_418_);
lean_dec(v_it_396_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_456_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_zero_424_; uint8_t v_isZero_425_; 
v_zero_424_ = lean_unsigned_to_nat(0u);
v_isZero_425_ = lean_nat_dec_eq(v_i_419_, v_zero_424_);
if (v_isZero_425_ == 1)
{
lean_object* v___x_426_; 
lean_del_object(v___x_422_);
lean_dec(v_i_419_);
lean_dec_ref(v_cs_418_);
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v_a_420_);
return v___x_426_;
}
else
{
lean_object* v_one_427_; lean_object* v_n_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_one_427_ = lean_unsigned_to_nat(1u);
v_n_428_ = lean_nat_sub(v_i_419_, v_one_427_);
lean_dec(v_i_419_);
v___x_429_ = lean_array_get_size(v_cs_418_);
v___x_430_ = lean_nat_dec_lt(v_n_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_dec(v_n_428_);
lean_del_object(v___x_422_);
lean_dec_ref(v_cs_418_);
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_a_420_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_array_fget(v_cs_418_, v_n_428_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v_n_428_);
v___x_434_ = v___x_422_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_cs_418_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_n_428_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_a_420_);
v___x_434_ = v_reuseFailAlloc_455_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_cs_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_444_; 
v_cs_435_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_444_ == 0)
{
v___x_437_ = v___x_432_;
v_isShared_438_ = v_isSharedCheck_444_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_cs_435_);
lean_dec(v___x_432_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_444_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_439_ = lean_array_get_size(v_cs_435_);
v___x_440_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_440_, 0, v_cs_435_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
lean_ctor_set(v___x_440_, 2, v___x_434_);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 1);
lean_ctor_set(v___x_437_, 0, v___x_440_);
v___x_442_ = v___x_437_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_object* v_vs_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_454_; 
v_vs_445_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_454_ == 0)
{
v___x_447_ = v___x_432_;
v_isShared_448_ = v_isSharedCheck_454_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_vs_445_);
lean_dec(v___x_432_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_454_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_449_ = lean_array_get_size(v_vs_445_);
v___x_450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_450_, 0, v_vs_445_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
lean_ctor_set(v___x_450_, 2, v___x_434_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_450_);
v___x_452_ = v___x_447_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIterator___redArg___lam__0(lean_object* v_it_457_){
_start:
{
switch(lean_obj_tag(v_it_457_))
{
case 0:
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(2);
return v___x_458_;
}
case 1:
{
lean_object* v_vs_459_; lean_object* v_i_460_; lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_475_; 
v_vs_459_ = lean_ctor_get(v_it_457_, 0);
v_i_460_ = lean_ctor_get(v_it_457_, 1);
v_a_461_ = lean_ctor_get(v_it_457_, 2);
v_isSharedCheck_475_ = !lean_is_exclusive(v_it_457_);
if (v_isSharedCheck_475_ == 0)
{
v___x_463_ = v_it_457_;
v_isShared_464_ = v_isSharedCheck_475_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_inc(v_i_460_);
lean_inc(v_vs_459_);
lean_dec(v_it_457_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_475_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_array_get_size(v_vs_459_);
v___x_466_ = lean_nat_dec_lt(v_i_460_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_del_object(v___x_463_);
lean_dec(v_i_460_);
lean_dec_ref(v_vs_459_);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v_a_461_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_i_460_, v___x_468_);
lean_inc_ref(v_vs_459_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_469_);
v___x_471_ = v___x_463_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_vs_459_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_a_461_);
v___x_471_ = v_reuseFailAlloc_474_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_array_fget(v_vs_459_, v_i_460_);
lean_dec(v_i_460_);
lean_dec_ref(v_vs_459_);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
return v___x_473_;
}
}
}
}
default: 
{
lean_object* v_cs_476_; lean_object* v_i_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_511_; 
v_cs_476_ = lean_ctor_get(v_it_457_, 0);
v_i_477_ = lean_ctor_get(v_it_457_, 1);
v_a_478_ = lean_ctor_get(v_it_457_, 2);
v_isSharedCheck_511_ = !lean_is_exclusive(v_it_457_);
if (v_isSharedCheck_511_ == 0)
{
v___x_480_ = v_it_457_;
v_isShared_481_ = v_isSharedCheck_511_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_inc(v_i_477_);
lean_inc(v_cs_476_);
lean_dec(v_it_457_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_511_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_array_get_size(v_cs_476_);
v___x_483_ = lean_nat_dec_lt(v_i_477_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_del_object(v___x_480_);
lean_dec(v_i_477_);
lean_dec_ref(v_cs_476_);
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v_a_478_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_485_ = lean_array_fget(v_cs_476_, v_i_477_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_i_477_, v___x_486_);
lean_dec(v_i_477_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_487_);
v___x_489_ = v___x_480_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_cs_476_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_a_478_);
v___x_489_ = v_reuseFailAlloc_510_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_cs_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_499_; 
v_cs_490_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_499_ == 0)
{
v___x_492_ = v___x_485_;
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_cs_490_);
lean_dec(v___x_485_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_495_, 0, v_cs_490_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
lean_ctor_set(v___x_495_, 2, v___x_489_);
if (v_isShared_493_ == 0)
{
lean_ctor_set_tag(v___x_492_, 1);
lean_ctor_set(v___x_492_, 0, v___x_495_);
v___x_497_ = v___x_492_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v_vs_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_509_; 
v_vs_500_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_509_ == 0)
{
v___x_502_ = v___x_485_;
v_isShared_503_ = v_isSharedCheck_509_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_vs_500_);
lean_dec(v___x_485_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_509_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_505_, 0, v_vs_500_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
lean_ctor_set(v___x_505_, 2, v___x_489_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIterator___redArg(){
_start:
{
lean_object* v___f_514_; 
v___f_514_ = ((lean_object*)(l_Lean_PersistentArray_Zipper_instIterator___redArg___closed__0));
return v___f_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIterator___redArg___boxed(lean_object* v___dummy_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_PersistentArray_Zipper_instIterator___redArg();
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIterator(lean_object* v_00_u03b1_517_){
_start:
{
lean_object* v___f_518_; 
v___f_518_ = ((lean_object*)(l_Lean_PersistentArray_Zipper_instIterator___redArg___closed__0));
return v___f_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIterator___redArg___lam__0(lean_object* v_it_519_){
_start:
{
switch(lean_obj_tag(v_it_519_))
{
case 0:
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(2);
return v___x_520_;
}
case 1:
{
lean_object* v_vs_521_; lean_object* v_i_522_; lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_540_; 
v_vs_521_ = lean_ctor_get(v_it_519_, 0);
v_i_522_ = lean_ctor_get(v_it_519_, 1);
v_a_523_ = lean_ctor_get(v_it_519_, 2);
v_isSharedCheck_540_ = !lean_is_exclusive(v_it_519_);
if (v_isSharedCheck_540_ == 0)
{
v___x_525_ = v_it_519_;
v_isShared_526_ = v_isSharedCheck_540_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_inc(v_i_522_);
lean_inc(v_vs_521_);
lean_dec(v_it_519_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_540_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v_zero_527_; uint8_t v_isZero_528_; 
v_zero_527_ = lean_unsigned_to_nat(0u);
v_isZero_528_ = lean_nat_dec_eq(v_i_522_, v_zero_527_);
if (v_isZero_528_ == 1)
{
lean_object* v___x_529_; 
lean_del_object(v___x_525_);
lean_dec(v_i_522_);
lean_dec_ref(v_vs_521_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_a_523_);
return v___x_529_;
}
else
{
lean_object* v_one_530_; lean_object* v_n_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_one_530_ = lean_unsigned_to_nat(1u);
v_n_531_ = lean_nat_sub(v_i_522_, v_one_530_);
lean_dec(v_i_522_);
v___x_532_ = lean_array_get_size(v_vs_521_);
v___x_533_ = lean_nat_dec_lt(v_n_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_dec(v_n_531_);
lean_del_object(v___x_525_);
lean_dec_ref(v_vs_521_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_a_523_);
return v___x_534_;
}
else
{
lean_object* v___x_536_; 
lean_inc(v_n_531_);
lean_inc_ref(v_vs_521_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_n_531_);
v___x_536_ = v___x_525_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_vs_521_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_n_531_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_a_523_);
v___x_536_ = v_reuseFailAlloc_539_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_array_fget(v_vs_521_, v_n_531_);
lean_dec(v_n_531_);
lean_dec_ref(v_vs_521_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
return v___x_538_;
}
}
}
}
}
default: 
{
lean_object* v_cs_541_; lean_object* v_i_542_; lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_579_; 
v_cs_541_ = lean_ctor_get(v_it_519_, 0);
v_i_542_ = lean_ctor_get(v_it_519_, 1);
v_a_543_ = lean_ctor_get(v_it_519_, 2);
v_isSharedCheck_579_ = !lean_is_exclusive(v_it_519_);
if (v_isSharedCheck_579_ == 0)
{
v___x_545_ = v_it_519_;
v_isShared_546_ = v_isSharedCheck_579_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_inc(v_i_542_);
lean_inc(v_cs_541_);
lean_dec(v_it_519_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_579_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_zero_547_; uint8_t v_isZero_548_; 
v_zero_547_ = lean_unsigned_to_nat(0u);
v_isZero_548_ = lean_nat_dec_eq(v_i_542_, v_zero_547_);
if (v_isZero_548_ == 1)
{
lean_object* v___x_549_; 
lean_del_object(v___x_545_);
lean_dec(v_i_542_);
lean_dec_ref(v_cs_541_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v_a_543_);
return v___x_549_;
}
else
{
lean_object* v_one_550_; lean_object* v_n_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v_one_550_ = lean_unsigned_to_nat(1u);
v_n_551_ = lean_nat_sub(v_i_542_, v_one_550_);
lean_dec(v_i_542_);
v___x_552_ = lean_array_get_size(v_cs_541_);
v___x_553_ = lean_nat_dec_lt(v_n_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_dec(v_n_551_);
lean_del_object(v___x_545_);
lean_dec_ref(v_cs_541_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v_a_543_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = lean_array_fget(v_cs_541_, v_n_551_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v_n_551_);
v___x_557_ = v___x_545_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_cs_541_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_n_551_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_a_543_);
v___x_557_ = v_reuseFailAlloc_578_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_cs_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_567_; 
v_cs_558_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_567_ == 0)
{
v___x_560_ = v___x_555_;
v_isShared_561_ = v_isSharedCheck_567_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_cs_558_);
lean_dec(v___x_555_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_567_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_562_ = lean_array_get_size(v_cs_558_);
v___x_563_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_563_, 0, v_cs_558_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
lean_ctor_set(v___x_563_, 2, v___x_557_);
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 1);
lean_ctor_set(v___x_560_, 0, v___x_563_);
v___x_565_ = v___x_560_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v_vs_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_577_; 
v_vs_568_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_577_ == 0)
{
v___x_570_ = v___x_555_;
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_vs_568_);
lean_dec(v___x_555_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_572_ = lean_array_get_size(v_vs_568_);
v___x_573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_573_, 0, v_vs_568_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
lean_ctor_set(v___x_573_, 2, v___x_557_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_573_);
v___x_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIterator___redArg(){
_start:
{
lean_object* v___f_582_; 
v___f_582_ = ((lean_object*)(l_Lean_PersistentArray_RevZipper_instIterator___redArg___closed__0));
return v___f_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIterator___redArg___boxed(lean_object* v___dummy_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_PersistentArray_RevZipper_instIterator___redArg();
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIterator(lean_object* v_00_u03b1_585_){
_start:
{
lean_object* v___f_586_; 
v___f_586_ = ((lean_object*)(l_Lean_PersistentArray_RevZipper_instIterator___redArg___closed__0));
return v___f_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_nodeMeasure___redArg(lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
lean_object* v_cs_588_; lean_object* v_toList_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_cs_588_ = lean_ctor_get(v_x_587_, 0);
lean_inc_ref(v_cs_588_);
lean_dec_ref_known(v_x_587_, 1);
v_toList_589_ = lean_array_to_list(v_cs_588_);
v___x_590_ = l_Lean_PersistentArray_nodesMeasure___redArg(v_toList_589_);
v___x_591_ = lean_unsigned_to_nat(2u);
v___x_592_ = lean_nat_add(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
return v___x_592_;
}
else
{
lean_object* v_vs_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_vs_593_ = lean_ctor_get(v_x_587_, 0);
lean_inc_ref(v_vs_593_);
lean_dec_ref_known(v_x_587_, 1);
v___x_594_ = lean_array_get_size(v_vs_593_);
lean_dec_ref(v_vs_593_);
v___x_595_ = lean_unsigned_to_nat(2u);
v___x_596_ = lean_nat_add(v___x_594_, v___x_595_);
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_nodesMeasure___redArg(lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v___x_598_; 
v___x_598_ = lean_unsigned_to_nat(0u);
return v___x_598_;
}
else
{
lean_object* v_head_599_; lean_object* v_tail_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_head_599_ = lean_ctor_get(v_x_597_, 0);
lean_inc(v_head_599_);
v_tail_600_ = lean_ctor_get(v_x_597_, 1);
lean_inc(v_tail_600_);
lean_dec_ref_known(v_x_597_, 2);
v___x_601_ = l_Lean_PersistentArray_nodeMeasure___redArg(v_head_599_);
v___x_602_ = l_Lean_PersistentArray_nodesMeasure___redArg(v_tail_600_);
v___x_603_ = lean_nat_add(v___x_601_, v___x_602_);
lean_dec(v___x_602_);
lean_dec(v___x_601_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_nodeMeasure(lean_object* v_00_u03b1_604_, lean_object* v_x_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_PersistentArray_nodeMeasure___redArg(v_x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_nodesMeasure(lean_object* v_00_u03b1_607_, lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_PersistentArray_nodesMeasure___redArg(v_x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_nodesMeasure_match__1_splitter___redArg(lean_object* v_x_610_, lean_object* v_h__1_611_, lean_object* v_h__2_612_){
_start:
{
if (lean_obj_tag(v_x_610_) == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_h__2_612_);
v___x_613_ = lean_box(0);
v___x_614_ = lean_apply_1(v_h__1_611_, v___x_613_);
return v___x_614_;
}
else
{
lean_object* v_head_615_; lean_object* v_tail_616_; lean_object* v___x_617_; 
lean_dec(v_h__1_611_);
v_head_615_ = lean_ctor_get(v_x_610_, 0);
lean_inc(v_head_615_);
v_tail_616_ = lean_ctor_get(v_x_610_, 1);
lean_inc(v_tail_616_);
lean_dec_ref_known(v_x_610_, 2);
v___x_617_ = lean_apply_2(v_h__2_612_, v_head_615_, v_tail_616_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_nodesMeasure_match__1_splitter(lean_object* v_00_u03b1_618_, lean_object* v_motive_619_, lean_object* v_x_620_, lean_object* v_h__1_621_, lean_object* v_h__2_622_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
lean_dec(v_h__2_622_);
v___x_623_ = lean_box(0);
v___x_624_ = lean_apply_1(v_h__1_621_, v___x_623_);
return v___x_624_;
}
else
{
lean_object* v_head_625_; lean_object* v_tail_626_; lean_object* v___x_627_; 
lean_dec(v_h__1_621_);
v_head_625_ = lean_ctor_get(v_x_620_, 0);
lean_inc(v_head_625_);
v_tail_626_ = lean_ctor_get(v_x_620_, 1);
lean_inc(v_tail_626_);
lean_dec_ref_known(v_x_620_, 2);
v___x_627_ = lean_apply_2(v_h__2_622_, v_head_625_, v_tail_626_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_measure___redArg(lean_object* v_x_628_){
_start:
{
switch(lean_obj_tag(v_x_628_))
{
case 0:
{
lean_object* v___x_629_; 
v___x_629_ = lean_unsigned_to_nat(0u);
return v___x_629_;
}
case 1:
{
lean_object* v_vs_630_; lean_object* v_i_631_; lean_object* v_a_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_vs_630_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_vs_630_);
v_i_631_ = lean_ctor_get(v_x_628_, 1);
lean_inc(v_i_631_);
v_a_632_ = lean_ctor_get(v_x_628_, 2);
lean_inc(v_a_632_);
lean_dec_ref_known(v_x_628_, 3);
v___x_633_ = lean_array_get_size(v_vs_630_);
lean_dec_ref(v_vs_630_);
v___x_634_ = lean_nat_sub(v___x_633_, v_i_631_);
lean_dec(v_i_631_);
v___x_635_ = l_Lean_PersistentArray_Zipper_measure___redArg(v_a_632_);
v___x_636_ = lean_nat_add(v___x_634_, v___x_635_);
lean_dec(v___x_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_nat_add(v___x_636_, v___x_637_);
lean_dec(v___x_636_);
return v___x_638_;
}
default: 
{
lean_object* v_cs_639_; lean_object* v_i_640_; lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_cs_639_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_cs_639_);
v_i_640_ = lean_ctor_get(v_x_628_, 1);
lean_inc(v_i_640_);
v_a_641_ = lean_ctor_get(v_x_628_, 2);
lean_inc(v_a_641_);
lean_dec_ref_known(v_x_628_, 3);
v___x_642_ = lean_array_to_list(v_cs_639_);
v___x_643_ = l_List_drop___redArg(v_i_640_, v___x_642_);
lean_dec(v___x_642_);
v___x_644_ = l_Lean_PersistentArray_nodesMeasure___redArg(v___x_643_);
v___x_645_ = l_Lean_PersistentArray_Zipper_measure___redArg(v_a_641_);
v___x_646_ = lean_nat_add(v___x_644_, v___x_645_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_add(v___x_646_, v___x_647_);
lean_dec(v___x_646_);
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_measure(lean_object* v_00_u03b1_649_, lean_object* v_x_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_PersistentArray_Zipper_measure___redArg(v_x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_step_match__1_splitter___redArg(lean_object* v_x_652_, lean_object* v_h__1_653_, lean_object* v_h__2_654_, lean_object* v_h__3_655_){
_start:
{
switch(lean_obj_tag(v_x_652_))
{
case 0:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_h__3_655_);
lean_dec(v_h__2_654_);
v___x_656_ = lean_box(0);
v___x_657_ = lean_apply_1(v_h__1_653_, v___x_656_);
return v___x_657_;
}
case 1:
{
lean_object* v_vs_658_; lean_object* v_i_659_; lean_object* v_a_660_; lean_object* v___x_661_; 
lean_dec(v_h__3_655_);
lean_dec(v_h__1_653_);
v_vs_658_ = lean_ctor_get(v_x_652_, 0);
lean_inc_ref(v_vs_658_);
v_i_659_ = lean_ctor_get(v_x_652_, 1);
lean_inc(v_i_659_);
v_a_660_ = lean_ctor_get(v_x_652_, 2);
lean_inc(v_a_660_);
lean_dec_ref_known(v_x_652_, 3);
v___x_661_ = lean_apply_3(v_h__2_654_, v_vs_658_, v_i_659_, v_a_660_);
return v___x_661_;
}
default: 
{
lean_object* v_cs_662_; lean_object* v_i_663_; lean_object* v_a_664_; lean_object* v___x_665_; 
lean_dec(v_h__2_654_);
lean_dec(v_h__1_653_);
v_cs_662_ = lean_ctor_get(v_x_652_, 0);
lean_inc_ref(v_cs_662_);
v_i_663_ = lean_ctor_get(v_x_652_, 1);
lean_inc(v_i_663_);
v_a_664_ = lean_ctor_get(v_x_652_, 2);
lean_inc(v_a_664_);
lean_dec_ref_known(v_x_652_, 3);
v___x_665_ = lean_apply_3(v_h__3_655_, v_cs_662_, v_i_663_, v_a_664_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_step_match__1_splitter(lean_object* v_00_u03b1_666_, lean_object* v_motive_667_, lean_object* v_x_668_, lean_object* v_h__1_669_, lean_object* v_h__2_670_, lean_object* v_h__3_671_){
_start:
{
switch(lean_obj_tag(v_x_668_))
{
case 0:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec(v_h__3_671_);
lean_dec(v_h__2_670_);
v___x_672_ = lean_box(0);
v___x_673_ = lean_apply_1(v_h__1_669_, v___x_672_);
return v___x_673_;
}
case 1:
{
lean_object* v_vs_674_; lean_object* v_i_675_; lean_object* v_a_676_; lean_object* v___x_677_; 
lean_dec(v_h__3_671_);
lean_dec(v_h__1_669_);
v_vs_674_ = lean_ctor_get(v_x_668_, 0);
lean_inc_ref(v_vs_674_);
v_i_675_ = lean_ctor_get(v_x_668_, 1);
lean_inc(v_i_675_);
v_a_676_ = lean_ctor_get(v_x_668_, 2);
lean_inc(v_a_676_);
lean_dec_ref_known(v_x_668_, 3);
v___x_677_ = lean_apply_3(v_h__2_670_, v_vs_674_, v_i_675_, v_a_676_);
return v___x_677_;
}
default: 
{
lean_object* v_cs_678_; lean_object* v_i_679_; lean_object* v_a_680_; lean_object* v___x_681_; 
lean_dec(v_h__2_670_);
lean_dec(v_h__1_669_);
v_cs_678_ = lean_ctor_get(v_x_668_, 0);
lean_inc_ref(v_cs_678_);
v_i_679_ = lean_ctor_get(v_x_668_, 1);
lean_inc(v_i_679_);
v_a_680_ = lean_ctor_get(v_x_668_, 2);
lean_inc(v_a_680_);
lean_dec_ref_known(v_x_668_, 3);
v___x_681_ = lean_apply_3(v_h__3_671_, v_cs_678_, v_i_679_, v_a_680_);
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_nodeMeasure_match__1_splitter___redArg(lean_object* v_x_682_, lean_object* v_h__1_683_, lean_object* v_h__2_684_){
_start:
{
if (lean_obj_tag(v_x_682_) == 0)
{
lean_object* v_cs_685_; lean_object* v_toList_686_; lean_object* v___x_687_; 
lean_dec(v_h__1_683_);
v_cs_685_ = lean_ctor_get(v_x_682_, 0);
lean_inc_ref(v_cs_685_);
lean_dec_ref_known(v_x_682_, 1);
v_toList_686_ = lean_array_to_list(v_cs_685_);
v___x_687_ = lean_apply_1(v_h__2_684_, v_toList_686_);
return v___x_687_;
}
else
{
lean_object* v_vs_688_; lean_object* v___x_689_; 
lean_dec(v_h__2_684_);
v_vs_688_ = lean_ctor_get(v_x_682_, 0);
lean_inc_ref(v_vs_688_);
lean_dec_ref_known(v_x_682_, 1);
v___x_689_ = lean_apply_1(v_h__1_683_, v_vs_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_nodeMeasure_match__1_splitter(lean_object* v_00_u03b1_690_, lean_object* v_motive_691_, lean_object* v_x_692_, lean_object* v_h__1_693_, lean_object* v_h__2_694_){
_start:
{
if (lean_obj_tag(v_x_692_) == 0)
{
lean_object* v_cs_695_; lean_object* v_toList_696_; lean_object* v___x_697_; 
lean_dec(v_h__1_693_);
v_cs_695_ = lean_ctor_get(v_x_692_, 0);
lean_inc_ref(v_cs_695_);
lean_dec_ref_known(v_x_692_, 1);
v_toList_696_ = lean_array_to_list(v_cs_695_);
v___x_697_ = lean_apply_1(v_h__2_694_, v_toList_696_);
return v___x_697_;
}
else
{
lean_object* v_vs_698_; lean_object* v___x_699_; 
lean_dec(v_h__2_694_);
v_vs_698_ = lean_ctor_get(v_x_692_, 0);
lean_inc_ref(v_vs_698_);
lean_dec_ref_known(v_x_692_, 1);
v___x_699_ = lean_apply_1(v_h__1_693_, v_vs_698_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_measure_match__1_splitter___redArg(lean_object* v_x_700_, lean_object* v_h__1_701_, lean_object* v_h__2_702_, lean_object* v_h__3_703_){
_start:
{
switch(lean_obj_tag(v_x_700_))
{
case 0:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_h__3_703_);
lean_dec(v_h__2_702_);
v___x_704_ = lean_box(0);
v___x_705_ = lean_apply_1(v_h__1_701_, v___x_704_);
return v___x_705_;
}
case 1:
{
lean_object* v_vs_706_; lean_object* v_i_707_; lean_object* v_a_708_; lean_object* v___x_709_; 
lean_dec(v_h__3_703_);
lean_dec(v_h__1_701_);
v_vs_706_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref(v_vs_706_);
v_i_707_ = lean_ctor_get(v_x_700_, 1);
lean_inc(v_i_707_);
v_a_708_ = lean_ctor_get(v_x_700_, 2);
lean_inc(v_a_708_);
lean_dec_ref_known(v_x_700_, 3);
v___x_709_ = lean_apply_3(v_h__2_702_, v_vs_706_, v_i_707_, v_a_708_);
return v___x_709_;
}
default: 
{
lean_object* v_cs_710_; lean_object* v_i_711_; lean_object* v_a_712_; lean_object* v___x_713_; 
lean_dec(v_h__2_702_);
lean_dec(v_h__1_701_);
v_cs_710_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref(v_cs_710_);
v_i_711_ = lean_ctor_get(v_x_700_, 1);
lean_inc(v_i_711_);
v_a_712_ = lean_ctor_get(v_x_700_, 2);
lean_inc(v_a_712_);
lean_dec_ref_known(v_x_700_, 3);
v___x_713_ = lean_apply_3(v_h__3_703_, v_cs_710_, v_i_711_, v_a_712_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_measure_match__1_splitter(lean_object* v_00_u03b1_714_, lean_object* v_motive_715_, lean_object* v_x_716_, lean_object* v_h__1_717_, lean_object* v_h__2_718_, lean_object* v_h__3_719_){
_start:
{
switch(lean_obj_tag(v_x_716_))
{
case 0:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
v___x_720_ = lean_box(0);
v___x_721_ = lean_apply_1(v_h__1_717_, v___x_720_);
return v___x_721_;
}
case 1:
{
lean_object* v_vs_722_; lean_object* v_i_723_; lean_object* v_a_724_; lean_object* v___x_725_; 
lean_dec(v_h__3_719_);
lean_dec(v_h__1_717_);
v_vs_722_ = lean_ctor_get(v_x_716_, 0);
lean_inc_ref(v_vs_722_);
v_i_723_ = lean_ctor_get(v_x_716_, 1);
lean_inc(v_i_723_);
v_a_724_ = lean_ctor_get(v_x_716_, 2);
lean_inc(v_a_724_);
lean_dec_ref_known(v_x_716_, 3);
v___x_725_ = lean_apply_3(v_h__2_718_, v_vs_722_, v_i_723_, v_a_724_);
return v___x_725_;
}
default: 
{
lean_object* v_cs_726_; lean_object* v_i_727_; lean_object* v_a_728_; lean_object* v___x_729_; 
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_cs_726_ = lean_ctor_get(v_x_716_, 0);
lean_inc_ref(v_cs_726_);
v_i_727_ = lean_ctor_get(v_x_716_, 1);
lean_inc(v_i_727_);
v_a_728_ = lean_ctor_get(v_x_716_, 2);
lean_inc(v_a_728_);
lean_dec_ref_known(v_x_716_, 3);
v___x_729_ = lean_apply_3(v_h__3_719_, v_cs_726_, v_i_727_, v_a_728_);
return v___x_729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(0);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_instFinitenessRelation___redArg();
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_Zipper_instFinitenessRelation(lean_object* v_00_u03b1_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_box(0);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_step_match__1_splitter___redArg(lean_object* v_x_736_, lean_object* v_h__1_737_, lean_object* v_h__2_738_, lean_object* v_h__3_739_, lean_object* v_h__4_740_, lean_object* v_h__5_741_){
_start:
{
switch(lean_obj_tag(v_x_736_))
{
case 0:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec(v_h__5_741_);
lean_dec(v_h__4_740_);
lean_dec(v_h__3_739_);
lean_dec(v_h__2_738_);
v___x_742_ = lean_box(0);
v___x_743_ = lean_apply_1(v_h__1_737_, v___x_742_);
return v___x_743_;
}
case 1:
{
lean_object* v_vs_744_; lean_object* v_i_745_; lean_object* v_a_746_; lean_object* v_zero_747_; uint8_t v_isZero_748_; 
lean_dec(v_h__5_741_);
lean_dec(v_h__4_740_);
lean_dec(v_h__1_737_);
v_vs_744_ = lean_ctor_get(v_x_736_, 0);
lean_inc_ref(v_vs_744_);
v_i_745_ = lean_ctor_get(v_x_736_, 1);
lean_inc(v_i_745_);
v_a_746_ = lean_ctor_get(v_x_736_, 2);
lean_inc(v_a_746_);
lean_dec_ref_known(v_x_736_, 3);
v_zero_747_ = lean_unsigned_to_nat(0u);
v_isZero_748_ = lean_nat_dec_eq(v_i_745_, v_zero_747_);
if (v_isZero_748_ == 1)
{
lean_object* v___x_749_; 
lean_dec(v_i_745_);
lean_dec(v_h__3_739_);
v___x_749_ = lean_apply_2(v_h__2_738_, v_vs_744_, v_a_746_);
return v___x_749_;
}
else
{
lean_object* v_one_750_; lean_object* v_n_751_; lean_object* v___x_752_; 
lean_dec(v_h__2_738_);
v_one_750_ = lean_unsigned_to_nat(1u);
v_n_751_ = lean_nat_sub(v_i_745_, v_one_750_);
lean_dec(v_i_745_);
v___x_752_ = lean_apply_3(v_h__3_739_, v_vs_744_, v_n_751_, v_a_746_);
return v___x_752_;
}
}
default: 
{
lean_object* v_cs_753_; lean_object* v_i_754_; lean_object* v_a_755_; lean_object* v_zero_756_; uint8_t v_isZero_757_; 
lean_dec(v_h__3_739_);
lean_dec(v_h__2_738_);
lean_dec(v_h__1_737_);
v_cs_753_ = lean_ctor_get(v_x_736_, 0);
lean_inc_ref(v_cs_753_);
v_i_754_ = lean_ctor_get(v_x_736_, 1);
lean_inc(v_i_754_);
v_a_755_ = lean_ctor_get(v_x_736_, 2);
lean_inc(v_a_755_);
lean_dec_ref_known(v_x_736_, 3);
v_zero_756_ = lean_unsigned_to_nat(0u);
v_isZero_757_ = lean_nat_dec_eq(v_i_754_, v_zero_756_);
if (v_isZero_757_ == 1)
{
lean_object* v___x_758_; 
lean_dec(v_i_754_);
lean_dec(v_h__5_741_);
v___x_758_ = lean_apply_2(v_h__4_740_, v_cs_753_, v_a_755_);
return v___x_758_;
}
else
{
lean_object* v_one_759_; lean_object* v_n_760_; lean_object* v___x_761_; 
lean_dec(v_h__4_740_);
v_one_759_ = lean_unsigned_to_nat(1u);
v_n_760_ = lean_nat_sub(v_i_754_, v_one_759_);
lean_dec(v_i_754_);
v___x_761_ = lean_apply_3(v_h__5_741_, v_cs_753_, v_n_760_, v_a_755_);
return v___x_761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_step_match__1_splitter(lean_object* v_00_u03b1_762_, lean_object* v_motive_763_, lean_object* v_x_764_, lean_object* v_h__1_765_, lean_object* v_h__2_766_, lean_object* v_h__3_767_, lean_object* v_h__4_768_, lean_object* v_h__5_769_){
_start:
{
switch(lean_obj_tag(v_x_764_))
{
case 0:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v_h__5_769_);
lean_dec(v_h__4_768_);
lean_dec(v_h__3_767_);
lean_dec(v_h__2_766_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_apply_1(v_h__1_765_, v___x_770_);
return v___x_771_;
}
case 1:
{
lean_object* v_vs_772_; lean_object* v_i_773_; lean_object* v_a_774_; lean_object* v_zero_775_; uint8_t v_isZero_776_; 
lean_dec(v_h__5_769_);
lean_dec(v_h__4_768_);
lean_dec(v_h__1_765_);
v_vs_772_ = lean_ctor_get(v_x_764_, 0);
lean_inc_ref(v_vs_772_);
v_i_773_ = lean_ctor_get(v_x_764_, 1);
lean_inc(v_i_773_);
v_a_774_ = lean_ctor_get(v_x_764_, 2);
lean_inc(v_a_774_);
lean_dec_ref_known(v_x_764_, 3);
v_zero_775_ = lean_unsigned_to_nat(0u);
v_isZero_776_ = lean_nat_dec_eq(v_i_773_, v_zero_775_);
if (v_isZero_776_ == 1)
{
lean_object* v___x_777_; 
lean_dec(v_i_773_);
lean_dec(v_h__3_767_);
v___x_777_ = lean_apply_2(v_h__2_766_, v_vs_772_, v_a_774_);
return v___x_777_;
}
else
{
lean_object* v_one_778_; lean_object* v_n_779_; lean_object* v___x_780_; 
lean_dec(v_h__2_766_);
v_one_778_ = lean_unsigned_to_nat(1u);
v_n_779_ = lean_nat_sub(v_i_773_, v_one_778_);
lean_dec(v_i_773_);
v___x_780_ = lean_apply_3(v_h__3_767_, v_vs_772_, v_n_779_, v_a_774_);
return v___x_780_;
}
}
default: 
{
lean_object* v_cs_781_; lean_object* v_i_782_; lean_object* v_a_783_; lean_object* v_zero_784_; uint8_t v_isZero_785_; 
lean_dec(v_h__3_767_);
lean_dec(v_h__2_766_);
lean_dec(v_h__1_765_);
v_cs_781_ = lean_ctor_get(v_x_764_, 0);
lean_inc_ref(v_cs_781_);
v_i_782_ = lean_ctor_get(v_x_764_, 1);
lean_inc(v_i_782_);
v_a_783_ = lean_ctor_get(v_x_764_, 2);
lean_inc(v_a_783_);
lean_dec_ref_known(v_x_764_, 3);
v_zero_784_ = lean_unsigned_to_nat(0u);
v_isZero_785_ = lean_nat_dec_eq(v_i_782_, v_zero_784_);
if (v_isZero_785_ == 1)
{
lean_object* v___x_786_; 
lean_dec(v_i_782_);
lean_dec(v_h__5_769_);
v___x_786_ = lean_apply_2(v_h__4_768_, v_cs_781_, v_a_783_);
return v___x_786_;
}
else
{
lean_object* v_one_787_; lean_object* v_n_788_; lean_object* v___x_789_; 
lean_dec(v_h__4_768_);
v_one_787_ = lean_unsigned_to_nat(1u);
v_n_788_ = lean_nat_sub(v_i_782_, v_one_787_);
lean_dec(v_i_782_);
v___x_789_ = lean_apply_3(v_h__5_769_, v_cs_781_, v_n_788_, v_a_783_);
return v___x_789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = lean_box(0);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_instFinitenessRelation___redArg();
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Iterators_Producers_PersistentArray_0__Lean_PersistentArray_RevZipper_instFinitenessRelation(lean_object* v_00_u03b1_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = lean_box(0);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_796_, lean_object* v_recur_797_, lean_object* v_it_798_, lean_object* v_____do__lift_799_){
_start:
{
if (lean_obj_tag(v_____do__lift_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; 
lean_dec(v_it_798_);
lean_dec(v_recur_797_);
v_a_800_ = lean_ctor_get(v_____do__lift_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v_____do__lift_799_, 1);
v___x_801_ = lean_apply_2(v_toPure_796_, lean_box(0), v_a_800_);
return v___x_801_;
}
else
{
lean_object* v_a_802_; lean_object* v___x_803_; 
lean_dec(v_toPure_796_);
v_a_802_ = lean_ctor_get(v_____do__lift_799_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v_____do__lift_799_, 1);
v___x_803_ = lean_apply_4(v_recur_797_, v_it_798_, v_a_802_, lean_box(0), lean_box(0));
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_804_, lean_object* v_recur_805_, lean_object* v___y_806_, lean_object* v_acc_807_, lean_object* v_toBind_808_, lean_object* v_s_809_){
_start:
{
switch(lean_obj_tag(v_s_809_))
{
case 0:
{
lean_object* v_it_810_; lean_object* v_out_811_; lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_it_810_ = lean_ctor_get(v_s_809_, 0);
lean_inc(v_it_810_);
v_out_811_ = lean_ctor_get(v_s_809_, 1);
lean_inc(v_out_811_);
lean_dec_ref_known(v_s_809_, 2);
v___f_812_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_812_, 0, v_toPure_804_);
lean_closure_set(v___f_812_, 1, v_recur_805_);
lean_closure_set(v___f_812_, 2, v_it_810_);
v___x_813_ = lean_apply_3(v___y_806_, v_out_811_, lean_box(0), v_acc_807_);
v___x_814_ = lean_apply_4(v_toBind_808_, lean_box(0), lean_box(0), v___x_813_, v___f_812_);
return v___x_814_;
}
case 1:
{
lean_object* v_it_815_; lean_object* v___x_816_; 
lean_dec(v_toBind_808_);
lean_dec(v___y_806_);
lean_dec(v_toPure_804_);
v_it_815_ = lean_ctor_get(v_s_809_, 0);
lean_inc(v_it_815_);
lean_dec_ref_known(v_s_809_, 1);
v___x_816_ = lean_apply_4(v_recur_805_, v_it_815_, v_acc_807_, lean_box(0), lean_box(0));
return v___x_816_;
}
default: 
{
lean_object* v___x_817_; 
lean_dec(v_toBind_808_);
lean_dec(v___y_806_);
lean_dec(v_recur_805_);
v___x_817_ = lean_apply_2(v_toPure_804_, lean_box(0), v_acc_807_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_818_, lean_object* v___y_819_, lean_object* v_toBind_820_, lean_object* v_lift_821_, lean_object* v_it_822_, lean_object* v_acc_823_, lean_object* v_hP_824_, lean_object* v_recur_825_){
_start:
{
lean_object* v___f_826_; lean_object* v___y_828_; 
v___f_826_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_826_, 0, v_toPure_818_);
lean_closure_set(v___f_826_, 1, v_recur_825_);
lean_closure_set(v___f_826_, 2, v___y_819_);
lean_closure_set(v___f_826_, 3, v_acc_823_);
lean_closure_set(v___f_826_, 4, v_toBind_820_);
switch(lean_obj_tag(v_it_822_))
{
case 0:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_box(2);
v___x_832_ = lean_apply_4(v_lift_821_, lean_box(0), lean_box(0), v___f_826_, v___x_831_);
return v___x_832_;
}
case 1:
{
lean_object* v_vs_833_; lean_object* v_i_834_; lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_851_; 
v_vs_833_ = lean_ctor_get(v_it_822_, 0);
v_i_834_ = lean_ctor_get(v_it_822_, 1);
v_a_835_ = lean_ctor_get(v_it_822_, 2);
v_isSharedCheck_851_ = !lean_is_exclusive(v_it_822_);
if (v_isSharedCheck_851_ == 0)
{
v___x_837_ = v_it_822_;
v_isShared_838_ = v_isSharedCheck_851_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_inc(v_i_834_);
lean_inc(v_vs_833_);
lean_dec(v_it_822_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_851_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = lean_array_get_size(v_vs_833_);
v___x_840_ = lean_nat_dec_lt(v_i_834_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_del_object(v___x_837_);
lean_dec(v_i_834_);
lean_dec_ref(v_vs_833_);
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v_a_835_);
v___x_842_ = lean_apply_4(v_lift_821_, lean_box(0), lean_box(0), v___f_826_, v___x_841_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_add(v_i_834_, v___x_843_);
lean_inc_ref(v_vs_833_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_844_);
v___x_846_ = v___x_837_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_vs_833_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_a_835_);
v___x_846_ = v_reuseFailAlloc_850_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = lean_array_fget(v_vs_833_, v_i_834_);
lean_dec(v_i_834_);
lean_dec_ref(v_vs_833_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = lean_apply_4(v_lift_821_, lean_box(0), lean_box(0), v___f_826_, v___x_848_);
return v___x_849_;
}
}
}
}
default: 
{
lean_object* v_cs_852_; lean_object* v_i_853_; lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_874_; 
v_cs_852_ = lean_ctor_get(v_it_822_, 0);
v_i_853_ = lean_ctor_get(v_it_822_, 1);
v_a_854_ = lean_ctor_get(v_it_822_, 2);
v_isSharedCheck_874_ = !lean_is_exclusive(v_it_822_);
if (v_isSharedCheck_874_ == 0)
{
v___x_856_ = v_it_822_;
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_inc(v_i_853_);
lean_inc(v_cs_852_);
lean_dec(v_it_822_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = lean_array_get_size(v_cs_852_);
v___x_859_ = lean_nat_dec_lt(v_i_853_, v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_del_object(v___x_856_);
lean_dec(v_i_853_);
lean_dec_ref(v_cs_852_);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_a_854_);
v___x_861_ = lean_apply_4(v_lift_821_, lean_box(0), lean_box(0), v___f_826_, v___x_860_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_862_ = lean_array_fget(v_cs_852_, v_i_853_);
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_nat_add(v_i_853_, v___x_863_);
lean_dec(v_i_853_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v___x_864_);
v___x_866_ = v___x_856_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_cs_852_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_a_854_);
v___x_866_ = v_reuseFailAlloc_873_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_cs_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_cs_867_ = lean_ctor_get(v___x_862_, 0);
lean_inc_ref(v_cs_867_);
lean_dec_ref_known(v___x_862_, 1);
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_869_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_869_, 0, v_cs_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
lean_ctor_set(v___x_869_, 2, v___x_866_);
v___y_828_ = v___x_869_;
goto v___jp_827_;
}
else
{
lean_object* v_vs_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_vs_870_ = lean_ctor_get(v___x_862_, 0);
lean_inc_ref(v_vs_870_);
lean_dec_ref_known(v___x_862_, 1);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_872_, 0, v_vs_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
lean_ctor_set(v___x_872_, 2, v___x_866_);
v___y_828_ = v___x_872_;
goto v___jp_827_;
}
}
}
}
}
}
v___jp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___y_828_);
v___x_830_ = lean_apply_4(v_lift_821_, lean_box(0), lean_box(0), v___f_826_, v___x_829_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__3(lean_object* v_inst_875_, lean_object* v_lift_876_, lean_object* v_00_u03b3_877_, lean_object* v_Pl_878_, lean_object* v_it_879_, lean_object* v_init_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_toApplicative_882_; lean_object* v_toBind_883_; lean_object* v_toPure_884_; lean_object* v___f_885_; lean_object* v___x_886_; 
v_toApplicative_882_ = lean_ctor_get(v_inst_875_, 0);
lean_inc_ref(v_toApplicative_882_);
v_toBind_883_ = lean_ctor_get(v_inst_875_, 1);
lean_inc(v_toBind_883_);
lean_dec_ref(v_inst_875_);
v_toPure_884_ = lean_ctor_get(v_toApplicative_882_, 1);
lean_inc(v_toPure_884_);
lean_dec_ref(v_toApplicative_882_);
v___f_885_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_885_, 0, v_toPure_884_);
lean_closure_set(v___f_885_, 1, v___y_881_);
lean_closure_set(v___f_885_, 2, v_toBind_883_);
lean_closure_set(v___f_885_, 3, v_lift_876_);
v___x_886_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_885_, v_it_879_, v_init_880_, lean_box(0));
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg(lean_object* v_inst_887_){
_start:
{
lean_object* v___f_888_; 
v___f_888_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_888_, 0, v_inst_887_);
return v___f_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Zipper_instIteratorLoop(lean_object* v_00_u03b1_889_, lean_object* v_n_890_, lean_object* v_inst_891_){
_start:
{
lean_object* v___f_892_; 
v___f_892_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_892_, 0, v_inst_891_);
return v___f_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_893_, lean_object* v_recur_894_, lean_object* v_it_895_, lean_object* v_____do__lift_896_){
_start:
{
if (lean_obj_tag(v_____do__lift_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; 
lean_dec(v_it_895_);
lean_dec(v_recur_894_);
v_a_897_ = lean_ctor_get(v_____do__lift_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v_____do__lift_896_, 1);
v___x_898_ = lean_apply_2(v_toPure_893_, lean_box(0), v_a_897_);
return v___x_898_;
}
else
{
lean_object* v_a_899_; lean_object* v___x_900_; 
lean_dec(v_toPure_893_);
v_a_899_ = lean_ctor_get(v_____do__lift_896_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v_____do__lift_896_, 1);
v___x_900_ = lean_apply_4(v_recur_894_, v_it_895_, v_a_899_, lean_box(0), lean_box(0));
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_901_, lean_object* v_recur_902_, lean_object* v___y_903_, lean_object* v_acc_904_, lean_object* v_toBind_905_, lean_object* v_s_906_){
_start:
{
switch(lean_obj_tag(v_s_906_))
{
case 0:
{
lean_object* v_it_907_; lean_object* v_out_908_; lean_object* v___f_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_it_907_ = lean_ctor_get(v_s_906_, 0);
lean_inc(v_it_907_);
v_out_908_ = lean_ctor_get(v_s_906_, 1);
lean_inc(v_out_908_);
lean_dec_ref_known(v_s_906_, 2);
v___f_909_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_909_, 0, v_toPure_901_);
lean_closure_set(v___f_909_, 1, v_recur_902_);
lean_closure_set(v___f_909_, 2, v_it_907_);
v___x_910_ = lean_apply_3(v___y_903_, v_out_908_, lean_box(0), v_acc_904_);
v___x_911_ = lean_apply_4(v_toBind_905_, lean_box(0), lean_box(0), v___x_910_, v___f_909_);
return v___x_911_;
}
case 1:
{
lean_object* v_it_912_; lean_object* v___x_913_; 
lean_dec(v_toBind_905_);
lean_dec(v___y_903_);
lean_dec(v_toPure_901_);
v_it_912_ = lean_ctor_get(v_s_906_, 0);
lean_inc(v_it_912_);
lean_dec_ref_known(v_s_906_, 1);
v___x_913_ = lean_apply_4(v_recur_902_, v_it_912_, v_acc_904_, lean_box(0), lean_box(0));
return v___x_913_;
}
default: 
{
lean_object* v___x_914_; 
lean_dec(v_toBind_905_);
lean_dec(v___y_903_);
lean_dec(v_recur_902_);
v___x_914_ = lean_apply_2(v_toPure_901_, lean_box(0), v_acc_904_);
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_915_, lean_object* v___y_916_, lean_object* v_toBind_917_, lean_object* v_lift_918_, lean_object* v_it_919_, lean_object* v_acc_920_, lean_object* v_hP_921_, lean_object* v_recur_922_){
_start:
{
lean_object* v___f_923_; lean_object* v___y_925_; 
v___f_923_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_923_, 0, v_toPure_915_);
lean_closure_set(v___f_923_, 1, v_recur_922_);
lean_closure_set(v___f_923_, 2, v___y_916_);
lean_closure_set(v___f_923_, 3, v_acc_920_);
lean_closure_set(v___f_923_, 4, v_toBind_917_);
switch(lean_obj_tag(v_it_919_))
{
case 0:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_box(2);
v___x_929_ = lean_apply_4(v_lift_918_, lean_box(0), lean_box(0), v___f_923_, v___x_928_);
return v___x_929_;
}
case 1:
{
lean_object* v_vs_930_; lean_object* v_i_931_; lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_952_; 
v_vs_930_ = lean_ctor_get(v_it_919_, 0);
v_i_931_ = lean_ctor_get(v_it_919_, 1);
v_a_932_ = lean_ctor_get(v_it_919_, 2);
v_isSharedCheck_952_ = !lean_is_exclusive(v_it_919_);
if (v_isSharedCheck_952_ == 0)
{
v___x_934_ = v_it_919_;
v_isShared_935_ = v_isSharedCheck_952_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_inc(v_i_931_);
lean_inc(v_vs_930_);
lean_dec(v_it_919_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_952_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_zero_936_; uint8_t v_isZero_937_; 
v_zero_936_ = lean_unsigned_to_nat(0u);
v_isZero_937_ = lean_nat_dec_eq(v_i_931_, v_zero_936_);
if (v_isZero_937_ == 1)
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_del_object(v___x_934_);
lean_dec(v_i_931_);
lean_dec_ref(v_vs_930_);
v___x_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_938_, 0, v_a_932_);
v___x_939_ = lean_apply_4(v_lift_918_, lean_box(0), lean_box(0), v___f_923_, v___x_938_);
return v___x_939_;
}
else
{
lean_object* v_one_940_; lean_object* v_n_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v_one_940_ = lean_unsigned_to_nat(1u);
v_n_941_ = lean_nat_sub(v_i_931_, v_one_940_);
lean_dec(v_i_931_);
v___x_942_ = lean_array_get_size(v_vs_930_);
v___x_943_ = lean_nat_dec_lt(v_n_941_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_n_941_);
lean_del_object(v___x_934_);
lean_dec_ref(v_vs_930_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_a_932_);
v___x_945_ = lean_apply_4(v_lift_918_, lean_box(0), lean_box(0), v___f_923_, v___x_944_);
return v___x_945_;
}
else
{
lean_object* v___x_947_; 
lean_inc(v_n_941_);
lean_inc_ref(v_vs_930_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 1, v_n_941_);
v___x_947_ = v___x_934_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_vs_930_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_n_941_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_a_932_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_array_fget(v_vs_930_, v_n_941_);
lean_dec(v_n_941_);
lean_dec_ref(v_vs_930_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_apply_4(v_lift_918_, lean_box(0), lean_box(0), v___f_923_, v___x_949_);
return v___x_950_;
}
}
}
}
}
default: 
{
lean_object* v_cs_953_; lean_object* v_i_954_; lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_979_; 
v_cs_953_ = lean_ctor_get(v_it_919_, 0);
v_i_954_ = lean_ctor_get(v_it_919_, 1);
v_a_955_ = lean_ctor_get(v_it_919_, 2);
v_isSharedCheck_979_ = !lean_is_exclusive(v_it_919_);
if (v_isSharedCheck_979_ == 0)
{
v___x_957_ = v_it_919_;
v_isShared_958_ = v_isSharedCheck_979_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_inc(v_i_954_);
lean_inc(v_cs_953_);
lean_dec(v_it_919_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_979_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_zero_959_; uint8_t v_isZero_960_; 
v_zero_959_ = lean_unsigned_to_nat(0u);
v_isZero_960_ = lean_nat_dec_eq(v_i_954_, v_zero_959_);
if (v_isZero_960_ == 1)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_del_object(v___x_957_);
lean_dec(v_i_954_);
lean_dec_ref(v_cs_953_);
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v_a_955_);
v___x_962_ = lean_apply_4(v_lift_918_, lean_box(0), lean_box(0), v___f_923_, v___x_961_);
return v___x_962_;
}
else
{
lean_object* v_one_963_; lean_object* v_n_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_one_963_ = lean_unsigned_to_nat(1u);
v_n_964_ = lean_nat_sub(v_i_954_, v_one_963_);
lean_dec(v_i_954_);
v___x_965_ = lean_array_get_size(v_cs_953_);
v___x_966_ = lean_nat_dec_lt(v_n_964_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_n_964_);
lean_del_object(v___x_957_);
lean_dec_ref(v_cs_953_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v_a_955_);
v___x_968_ = lean_apply_4(v_lift_918_, lean_box(0), lean_box(0), v___f_923_, v___x_967_);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = lean_array_fget(v_cs_953_, v_n_964_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_n_964_);
v___x_971_ = v___x_957_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_cs_953_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_n_964_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_a_955_);
v___x_971_ = v_reuseFailAlloc_978_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_cs_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_cs_972_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_cs_972_);
lean_dec_ref_known(v___x_969_, 1);
v___x_973_ = lean_array_get_size(v_cs_972_);
v___x_974_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_974_, 0, v_cs_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
lean_ctor_set(v___x_974_, 2, v___x_971_);
v___y_925_ = v___x_974_;
goto v___jp_924_;
}
else
{
lean_object* v_vs_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_vs_975_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_vs_975_);
lean_dec_ref_known(v___x_969_, 1);
v___x_976_ = lean_array_get_size(v_vs_975_);
v___x_977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_977_, 0, v_vs_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
lean_ctor_set(v___x_977_, 2, v___x_971_);
v___y_925_ = v___x_977_;
goto v___jp_924_;
}
}
}
}
}
}
}
v___jp_924_:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_926_, 0, v___y_925_);
v___x_927_ = lean_apply_4(v_lift_918_, lean_box(0), lean_box(0), v___f_923_, v___x_926_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__3(lean_object* v_inst_980_, lean_object* v_lift_981_, lean_object* v_00_u03b3_982_, lean_object* v_Pl_983_, lean_object* v_it_984_, lean_object* v_init_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_toApplicative_987_; lean_object* v_toBind_988_; lean_object* v_toPure_989_; lean_object* v___f_990_; lean_object* v___x_991_; 
v_toApplicative_987_ = lean_ctor_get(v_inst_980_, 0);
lean_inc_ref(v_toApplicative_987_);
v_toBind_988_ = lean_ctor_get(v_inst_980_, 1);
lean_inc(v_toBind_988_);
lean_dec_ref(v_inst_980_);
v_toPure_989_ = lean_ctor_get(v_toApplicative_987_, 1);
lean_inc(v_toPure_989_);
lean_dec_ref(v_toApplicative_987_);
v___f_990_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_990_, 0, v_toPure_989_);
lean_closure_set(v___f_990_, 1, v___y_986_);
lean_closure_set(v___f_990_, 2, v_toBind_988_);
lean_closure_set(v___f_990_, 3, v_lift_981_);
v___x_991_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_990_, v_it_984_, v_init_985_, lean_box(0));
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg(lean_object* v_inst_992_){
_start:
{
lean_object* v___f_993_; 
v___f_993_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_993_, 0, v_inst_992_);
return v___f_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_RevZipper_instIteratorLoop(lean_object* v_00_u03b1_994_, lean_object* v_n_995_, lean_object* v_inst_996_){
_start:
{
lean_object* v___f_997_; 
v___f_997_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_RevZipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_997_, 0, v_inst_996_);
return v___f_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iter___redArg(lean_object* v_t_998_){
_start:
{
lean_object* v_root_999_; lean_object* v_tail_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_root_999_ = lean_ctor_get(v_t_998_, 0);
v_tail_1000_ = lean_ctor_get(v_t_998_, 1);
v___x_1001_ = lean_unsigned_to_nat(0u);
v___x_1002_ = lean_box(0);
lean_inc_ref(v_tail_1000_);
v___x_1003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1003_, 0, v_tail_1000_);
lean_ctor_set(v___x_1003_, 1, v___x_1001_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
if (lean_obj_tag(v_root_999_) == 0)
{
lean_object* v_cs_1004_; lean_object* v___x_1005_; 
v_cs_1004_ = lean_ctor_get(v_root_999_, 0);
lean_inc_ref(v_cs_1004_);
v___x_1005_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1005_, 0, v_cs_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_1001_);
lean_ctor_set(v___x_1005_, 2, v___x_1003_);
return v___x_1005_;
}
else
{
lean_object* v_vs_1006_; lean_object* v___x_1007_; 
v_vs_1006_ = lean_ctor_get(v_root_999_, 0);
lean_inc_ref(v_vs_1006_);
v___x_1007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1007_, 0, v_vs_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1001_);
lean_ctor_set(v___x_1007_, 2, v___x_1003_);
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iter___redArg___boxed(lean_object* v_t_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_PersistentArray_iter___redArg(v_t_1008_);
lean_dec_ref(v_t_1008_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iter(lean_object* v_00_u03b1_1010_, lean_object* v_t_1011_){
_start:
{
lean_object* v_root_1012_; lean_object* v_tail_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_root_1012_ = lean_ctor_get(v_t_1011_, 0);
v_tail_1013_ = lean_ctor_get(v_t_1011_, 1);
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = lean_box(0);
lean_inc_ref(v_tail_1013_);
v___x_1016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1016_, 0, v_tail_1013_);
lean_ctor_set(v___x_1016_, 1, v___x_1014_);
lean_ctor_set(v___x_1016_, 2, v___x_1015_);
if (lean_obj_tag(v_root_1012_) == 0)
{
lean_object* v_cs_1017_; lean_object* v___x_1018_; 
v_cs_1017_ = lean_ctor_get(v_root_1012_, 0);
lean_inc_ref(v_cs_1017_);
v___x_1018_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1018_, 0, v_cs_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_1014_);
lean_ctor_set(v___x_1018_, 2, v___x_1016_);
return v___x_1018_;
}
else
{
lean_object* v_vs_1019_; lean_object* v___x_1020_; 
v_vs_1019_ = lean_ctor_get(v_root_1012_, 0);
lean_inc_ref(v_vs_1019_);
v___x_1020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1020_, 0, v_vs_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_1014_);
lean_ctor_set(v___x_1020_, 2, v___x_1016_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iter___boxed(lean_object* v_00_u03b1_1021_, lean_object* v_t_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_PersistentArray_iter(v_00_u03b1_1021_, v_t_1022_);
lean_dec_ref(v_t_1022_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iterFromIdx___redArg(lean_object* v_t_1024_, lean_object* v_start_1025_){
_start:
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = lean_nat_dec_eq(v_start_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v_root_1028_; lean_object* v_tail_1029_; size_t v_shift_1030_; lean_object* v_tailOff_1031_; uint8_t v___x_1032_; 
v_root_1028_ = lean_ctor_get(v_t_1024_, 0);
v_tail_1029_ = lean_ctor_get(v_t_1024_, 1);
v_shift_1030_ = lean_ctor_get_usize(v_t_1024_, 4);
v_tailOff_1031_ = lean_ctor_get(v_t_1024_, 3);
v___x_1032_ = lean_nat_dec_le(v_tailOff_1031_, v_start_1025_);
if (v___x_1032_ == 0)
{
size_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1033_ = lean_usize_of_nat(v_start_1025_);
v___x_1034_ = lean_box(0);
lean_inc_ref(v_tail_1029_);
v___x_1035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1035_, 0, v_tail_1029_);
lean_ctor_set(v___x_1035_, 1, v___x_1026_);
lean_ctor_set(v___x_1035_, 2, v___x_1034_);
v___x_1036_ = l_Lean_PersistentArray_Zipper_prependNodeFrom___redArg(v_root_1028_, v___x_1033_, v_shift_1030_, v___x_1035_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = lean_nat_sub(v_start_1025_, v_tailOff_1031_);
v___x_1038_ = lean_box(0);
lean_inc_ref(v_tail_1029_);
v___x_1039_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1039_, 0, v_tail_1029_);
lean_ctor_set(v___x_1039_, 1, v___x_1037_);
lean_ctor_set(v___x_1039_, 2, v___x_1038_);
return v___x_1039_;
}
}
else
{
lean_object* v_root_1040_; lean_object* v_tail_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_root_1040_ = lean_ctor_get(v_t_1024_, 0);
v_tail_1041_ = lean_ctor_get(v_t_1024_, 1);
v___x_1042_ = lean_box(0);
lean_inc_ref(v_tail_1041_);
v___x_1043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1043_, 0, v_tail_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1026_);
lean_ctor_set(v___x_1043_, 2, v___x_1042_);
if (lean_obj_tag(v_root_1040_) == 0)
{
lean_object* v_cs_1044_; lean_object* v___x_1045_; 
v_cs_1044_ = lean_ctor_get(v_root_1040_, 0);
lean_inc_ref(v_cs_1044_);
v___x_1045_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1045_, 0, v_cs_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1026_);
lean_ctor_set(v___x_1045_, 2, v___x_1043_);
return v___x_1045_;
}
else
{
lean_object* v_vs_1046_; lean_object* v___x_1047_; 
v_vs_1046_ = lean_ctor_get(v_root_1040_, 0);
lean_inc_ref(v_vs_1046_);
v___x_1047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1047_, 0, v_vs_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1026_);
lean_ctor_set(v___x_1047_, 2, v___x_1043_);
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iterFromIdx___redArg___boxed(lean_object* v_t_1048_, lean_object* v_start_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_PersistentArray_iterFromIdx___redArg(v_t_1048_, v_start_1049_);
lean_dec(v_start_1049_);
lean_dec_ref(v_t_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iterFromIdx(lean_object* v_00_u03b1_1051_, lean_object* v_t_1052_, lean_object* v_start_1053_){
_start:
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = lean_nat_dec_eq(v_start_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v_root_1056_; lean_object* v_tail_1057_; size_t v_shift_1058_; lean_object* v_tailOff_1059_; uint8_t v___x_1060_; 
v_root_1056_ = lean_ctor_get(v_t_1052_, 0);
v_tail_1057_ = lean_ctor_get(v_t_1052_, 1);
v_shift_1058_ = lean_ctor_get_usize(v_t_1052_, 4);
v_tailOff_1059_ = lean_ctor_get(v_t_1052_, 3);
v___x_1060_ = lean_nat_dec_le(v_tailOff_1059_, v_start_1053_);
if (v___x_1060_ == 0)
{
size_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = lean_usize_of_nat(v_start_1053_);
v___x_1062_ = lean_box(0);
lean_inc_ref(v_tail_1057_);
v___x_1063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1063_, 0, v_tail_1057_);
lean_ctor_set(v___x_1063_, 1, v___x_1054_);
lean_ctor_set(v___x_1063_, 2, v___x_1062_);
v___x_1064_ = l_Lean_PersistentArray_Zipper_prependNodeFrom___redArg(v_root_1056_, v___x_1061_, v_shift_1058_, v___x_1063_);
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = lean_nat_sub(v_start_1053_, v_tailOff_1059_);
v___x_1066_ = lean_box(0);
lean_inc_ref(v_tail_1057_);
v___x_1067_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1067_, 0, v_tail_1057_);
lean_ctor_set(v___x_1067_, 1, v___x_1065_);
lean_ctor_set(v___x_1067_, 2, v___x_1066_);
return v___x_1067_;
}
}
else
{
lean_object* v_root_1068_; lean_object* v_tail_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_root_1068_ = lean_ctor_get(v_t_1052_, 0);
v_tail_1069_ = lean_ctor_get(v_t_1052_, 1);
v___x_1070_ = lean_box(0);
lean_inc_ref(v_tail_1069_);
v___x_1071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1071_, 0, v_tail_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1054_);
lean_ctor_set(v___x_1071_, 2, v___x_1070_);
if (lean_obj_tag(v_root_1068_) == 0)
{
lean_object* v_cs_1072_; lean_object* v___x_1073_; 
v_cs_1072_ = lean_ctor_get(v_root_1068_, 0);
lean_inc_ref(v_cs_1072_);
v___x_1073_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1073_, 0, v_cs_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1054_);
lean_ctor_set(v___x_1073_, 2, v___x_1071_);
return v___x_1073_;
}
else
{
lean_object* v_vs_1074_; lean_object* v___x_1075_; 
v_vs_1074_ = lean_ctor_get(v_root_1068_, 0);
lean_inc_ref(v_vs_1074_);
v___x_1075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1075_, 0, v_vs_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1054_);
lean_ctor_set(v___x_1075_, 2, v___x_1071_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_iterFromIdx___boxed(lean_object* v_00_u03b1_1076_, lean_object* v_t_1077_, lean_object* v_start_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_PersistentArray_iterFromIdx(v_00_u03b1_1076_, v_t_1077_, v_start_1078_);
lean_dec(v_start_1078_);
lean_dec_ref(v_t_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_revIter___redArg(lean_object* v_t_1080_){
_start:
{
lean_object* v_root_1081_; lean_object* v_tail_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_root_1081_ = lean_ctor_get(v_t_1080_, 0);
v_tail_1082_ = lean_ctor_get(v_t_1080_, 1);
v___x_1083_ = lean_array_get_size(v_tail_1082_);
v___x_1084_ = lean_box(0);
if (lean_obj_tag(v_root_1081_) == 0)
{
lean_object* v_cs_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_cs_1085_ = lean_ctor_get(v_root_1081_, 0);
v___x_1086_ = lean_array_get_size(v_cs_1085_);
lean_inc_ref(v_cs_1085_);
v___x_1087_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1087_, 0, v_cs_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
lean_ctor_set(v___x_1087_, 2, v___x_1084_);
lean_inc_ref(v_tail_1082_);
v___x_1088_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1088_, 0, v_tail_1082_);
lean_ctor_set(v___x_1088_, 1, v___x_1083_);
lean_ctor_set(v___x_1088_, 2, v___x_1087_);
return v___x_1088_;
}
else
{
lean_object* v_vs_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_vs_1089_ = lean_ctor_get(v_root_1081_, 0);
v___x_1090_ = lean_array_get_size(v_vs_1089_);
lean_inc_ref(v_vs_1089_);
v___x_1091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1091_, 0, v_vs_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
lean_ctor_set(v___x_1091_, 2, v___x_1084_);
lean_inc_ref(v_tail_1082_);
v___x_1092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1092_, 0, v_tail_1082_);
lean_ctor_set(v___x_1092_, 1, v___x_1083_);
lean_ctor_set(v___x_1092_, 2, v___x_1091_);
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_revIter___redArg___boxed(lean_object* v_t_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_PersistentArray_revIter___redArg(v_t_1093_);
lean_dec_ref(v_t_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_revIter(lean_object* v_00_u03b1_1095_, lean_object* v_t_1096_){
_start:
{
lean_object* v_root_1097_; lean_object* v_tail_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_root_1097_ = lean_ctor_get(v_t_1096_, 0);
v_tail_1098_ = lean_ctor_get(v_t_1096_, 1);
v___x_1099_ = lean_array_get_size(v_tail_1098_);
v___x_1100_ = lean_box(0);
if (lean_obj_tag(v_root_1097_) == 0)
{
lean_object* v_cs_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_cs_1101_ = lean_ctor_get(v_root_1097_, 0);
v___x_1102_ = lean_array_get_size(v_cs_1101_);
lean_inc_ref(v_cs_1101_);
v___x_1103_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1103_, 0, v_cs_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
lean_ctor_set(v___x_1103_, 2, v___x_1100_);
lean_inc_ref(v_tail_1098_);
v___x_1104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1104_, 0, v_tail_1098_);
lean_ctor_set(v___x_1104_, 1, v___x_1099_);
lean_ctor_set(v___x_1104_, 2, v___x_1103_);
return v___x_1104_;
}
else
{
lean_object* v_vs_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_vs_1105_ = lean_ctor_get(v_root_1097_, 0);
v___x_1106_ = lean_array_get_size(v_vs_1105_);
lean_inc_ref(v_vs_1105_);
v___x_1107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1107_, 0, v_vs_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
lean_ctor_set(v___x_1107_, 2, v___x_1100_);
lean_inc_ref(v_tail_1098_);
v___x_1108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1108_, 0, v_tail_1098_);
lean_ctor_set(v___x_1108_, 1, v___x_1099_);
lean_ctor_set(v___x_1108_, 2, v___x_1107_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_revIter___boxed(lean_object* v_00_u03b1_1109_, lean_object* v_t_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_PersistentArray_revIter(v_00_u03b1_1109_, v_t_1110_);
lean_dec_ref(v_t_1110_);
return v_res_1111_;
}
}
lean_object* runtime_initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Iterators_Producers_PersistentArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Iterators_Producers_PersistentArray(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Iterators_Producers_PersistentArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Iterators_Producers_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Iterators_Producers_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Iterators_Producers_PersistentArray(builtin);
}
#ifdef __cplusplus
}
#endif
