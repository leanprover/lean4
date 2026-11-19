// Lean compiler output
// Module: Init.Data.String.Pattern.Basic
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Loop public import Init.Data.String.Defs public import Init.Data.String.Basic public import Init.Data.String.FindPos import Init.Data.String.Lemmas.FindPos import Init.Data.Iterators.Consumers.Loop import Init.Omega import Init.Data.String.Lemmas.IsEmpty import Init.Data.String.Termination import Init.Data.String.OrderInstances import Init.Data.String.Lemmas.Order
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_rejected_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_rejected_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_rejected_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_matched_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_matched_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_matched_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg___closed__0 = (const lean_object*)&l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep_beq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_instBEqSearchStep_beq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_String_Slice_Pattern_SearchStep_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___impl(lean_object* v_s_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___impl___boxed(lean_object* v_s_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_String_Slice_Pattern_SearchStep_ctorIdx___impl(v_s_8_, v_x_9_);
lean_dec_ref(v_x_9_);
lean_dec_ref(v_s_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
lean_object* v_startPos_13_; lean_object* v_endPos_14_; lean_object* v___x_15_; 
v_startPos_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_startPos_13_);
v_endPos_14_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_endPos_14_);
lean_dec_ref(v_t_11_);
v___x_15_ = lean_apply_2(v_k_12_, v_startPos_13_, v_endPos_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorElim(lean_object* v_s_16_, lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_19_, v_k_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorElim___boxed(lean_object* v_s_23_, lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_String_Slice_Pattern_SearchStep_ctorElim(v_s_23_, v_motive_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_ctorIdx_25_);
lean_dec_ref(v_s_23_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_rejected_elim___redArg(lean_object* v_t_30_, lean_object* v_rejected_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_30_, v_rejected_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_rejected_elim(lean_object* v_s_33_, lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_rejected_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_35_, v_rejected_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_rejected_elim___boxed(lean_object* v_s_39_, lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_rejected_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_String_Slice_Pattern_SearchStep_rejected_elim(v_s_39_, v_motive_40_, v_t_41_, v_h_42_, v_rejected_43_);
lean_dec_ref(v_s_39_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_matched_elim___redArg(lean_object* v_t_45_, lean_object* v_matched_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_45_, v_matched_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_matched_elim(lean_object* v_s_48_, lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_matched_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_50_, v_matched_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_matched_elim___boxed(lean_object* v_s_54_, lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_matched_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_String_Slice_Pattern_SearchStep_matched_elim(v_s_54_, v_motive_55_, v_t_56_, v_h_57_, v_matched_58_);
lean_dec_ref(v_s_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg(){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = ((lean_object*)(l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg___closed__0));
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg___boxed(lean_object* v___dummy_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg();
return v_res_65_;
}
}
static lean_object* _init_l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg();
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default(lean_object* v_s_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_obj_once(&l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0, &l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_once, _init_l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___boxed(lean_object* v_s_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_String_Slice_Pattern_instInhabitedSearchStep_default(v_s_69_);
lean_dec_ref(v_s_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___redArg(){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0, &l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_once, _init_l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___redArg___boxed(lean_object* v___dummy_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_String_Slice_Pattern_instInhabitedSearchStep___redArg();
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep(lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0, &l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_once, _init_l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_String_Slice_Pattern_instInhabitedSearchStep(v_a_77_);
lean_dec_ref(v_a_77_);
return v_res_78_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_a_82_; lean_object* v_a_83_; lean_object* v_b_84_; lean_object* v_b_85_; 
if (lean_obj_tag(v_x_79_) == 0)
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v_startPos_88_; lean_object* v_endPos_89_; lean_object* v_startPos_90_; lean_object* v_endPos_91_; 
v_startPos_88_ = lean_ctor_get(v_x_79_, 0);
v_endPos_89_ = lean_ctor_get(v_x_79_, 1);
v_startPos_90_ = lean_ctor_get(v_x_80_, 0);
v_endPos_91_ = lean_ctor_get(v_x_80_, 1);
v_a_82_ = v_startPos_88_;
v_a_83_ = v_endPos_89_;
v_b_84_ = v_startPos_90_;
v_b_85_ = v_endPos_91_;
goto v___jp_81_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
else
{
if (lean_obj_tag(v_x_80_) == 1)
{
lean_object* v_startPos_93_; lean_object* v_endPos_94_; lean_object* v_startPos_95_; lean_object* v_endPos_96_; 
v_startPos_93_ = lean_ctor_get(v_x_79_, 0);
v_endPos_94_ = lean_ctor_get(v_x_79_, 1);
v_startPos_95_ = lean_ctor_get(v_x_80_, 0);
v_endPos_96_ = lean_ctor_get(v_x_80_, 1);
v_a_82_ = v_startPos_93_;
v_a_83_ = v_endPos_94_;
v_b_84_ = v_startPos_95_;
v_b_85_ = v_endPos_96_;
goto v___jp_81_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
v___jp_81_:
{
uint8_t v_decide_86_; 
v_decide_86_ = lean_nat_dec_eq(v_a_82_, v_b_84_);
if (v_decide_86_ == 0)
{
return v_decide_86_;
}
else
{
uint8_t v_decide_87_; 
v_decide_87_ = lean_nat_dec_eq(v_a_83_, v_b_85_);
return v_decide_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep_beq___redArg___boxed(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_98_, v_x_99_);
lean_dec_ref(v_x_99_);
lean_dec_ref(v_x_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_instBEqSearchStep_beq(lean_object* v_s_102_, lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
uint8_t v___x_105_; 
v___x_105_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_103_, v_x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep_beq___boxed(lean_object* v_s_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_String_Slice_Pattern_instBEqSearchStep_beq(v_s_106_, v_x_107_, v_x_108_);
lean_dec_ref(v_x_108_);
lean_dec_ref(v_x_107_);
lean_dec_ref(v_s_106_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep(lean_object* v_s_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_instBEqSearchStep_beq___boxed), 3, 1);
lean_closure_set(v___x_112_, 0, v_s_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___redArg(lean_object* v_st_113_){
_start:
{
lean_object* v_startPos_114_; 
v_startPos_114_ = lean_ctor_get(v_st_113_, 0);
lean_inc(v_startPos_114_);
return v_startPos_114_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___redArg___boxed(lean_object* v_st_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_String_Slice_Pattern_SearchStep_startPos___redArg(v_st_115_);
lean_dec_ref(v_st_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos(lean_object* v_s_117_, lean_object* v_st_118_){
_start:
{
lean_object* v_startPos_119_; 
v_startPos_119_ = lean_ctor_get(v_st_118_, 0);
lean_inc(v_startPos_119_);
return v_startPos_119_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___boxed(lean_object* v_s_120_, lean_object* v_st_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_String_Slice_Pattern_SearchStep_startPos(v_s_120_, v_st_121_);
lean_dec_ref(v_st_121_);
lean_dec_ref(v_s_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___redArg(lean_object* v_st_123_){
_start:
{
lean_object* v_endPos_124_; 
v_endPos_124_ = lean_ctor_get(v_st_123_, 1);
lean_inc(v_endPos_124_);
return v_endPos_124_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___redArg___boxed(lean_object* v_st_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_String_Slice_Pattern_SearchStep_endPos___redArg(v_st_125_);
lean_dec_ref(v_st_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos(lean_object* v_s_127_, lean_object* v_st_128_){
_start:
{
lean_object* v_endPos_129_; 
v_endPos_129_ = lean_ctor_get(v_st_128_, 1);
lean_inc(v_endPos_129_);
return v_endPos_129_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___boxed(lean_object* v_s_130_, lean_object* v_st_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_String_Slice_Pattern_SearchStep_endPos(v_s_130_, v_st_131_);
lean_dec_ref(v_st_131_);
lean_dec_ref(v_s_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(lean_object* v_p_133_, lean_object* v_st_134_){
_start:
{
if (lean_obj_tag(v_st_134_) == 0)
{
lean_object* v_startPos_135_; lean_object* v_endPos_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_145_; 
v_startPos_135_ = lean_ctor_get(v_st_134_, 0);
v_endPos_136_ = lean_ctor_get(v_st_134_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_st_134_);
if (v_isSharedCheck_145_ == 0)
{
v___x_138_ = v_st_134_;
v_isShared_139_ = v_isSharedCheck_145_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_endPos_136_);
lean_inc(v_startPos_135_);
lean_dec(v_st_134_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_145_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_nat_add(v_p_133_, v_startPos_135_);
lean_dec(v_startPos_135_);
v___x_141_ = lean_nat_add(v_p_133_, v_endPos_136_);
lean_dec(v_endPos_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v___x_141_);
lean_ctor_set(v___x_138_, 0, v___x_140_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
lean_object* v_startPos_146_; lean_object* v_endPos_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_156_; 
v_startPos_146_ = lean_ctor_get(v_st_134_, 0);
v_endPos_147_ = lean_ctor_get(v_st_134_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_st_134_);
if (v_isSharedCheck_156_ == 0)
{
v___x_149_ = v_st_134_;
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_endPos_147_);
lean_inc(v_startPos_146_);
lean_dec(v_st_134_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_151_ = lean_nat_add(v_p_133_, v_startPos_146_);
lean_dec(v_startPos_146_);
v___x_152_ = lean_nat_add(v_p_133_, v_endPos_147_);
lean_dec(v_endPos_147_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v___x_152_);
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_154_ = v___x_149_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg___boxed(lean_object* v_p_157_, lean_object* v_st_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_157_, v_st_158_);
lean_dec(v_p_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom(lean_object* v_s_160_, lean_object* v_p_161_, lean_object* v_st_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_161_, v_st_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___boxed(lean_object* v_s_164_, lean_object* v_p_165_, lean_object* v_st_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom(v_s_164_, v_p_165_, v_st_166_);
lean_dec(v_p_165_);
lean_dec_ref(v_s_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___redArg(lean_object* v_st_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
if (lean_obj_tag(v_st_168_) == 0)
{
lean_object* v_startPos_171_; lean_object* v_endPos_172_; lean_object* v___x_173_; 
lean_dec(v_h__2_170_);
v_startPos_171_ = lean_ctor_get(v_st_168_, 0);
lean_inc(v_startPos_171_);
v_endPos_172_ = lean_ctor_get(v_st_168_, 1);
lean_inc(v_endPos_172_);
lean_dec_ref_known(v_st_168_, 2);
v___x_173_ = lean_apply_2(v_h__1_169_, v_startPos_171_, v_endPos_172_);
return v___x_173_;
}
else
{
lean_object* v_startPos_174_; lean_object* v_endPos_175_; lean_object* v___x_176_; 
lean_dec(v_h__1_169_);
v_startPos_174_ = lean_ctor_get(v_st_168_, 0);
lean_inc(v_startPos_174_);
v_endPos_175_ = lean_ctor_get(v_st_168_, 1);
lean_inc(v_endPos_175_);
lean_dec_ref_known(v_st_168_, 2);
v___x_176_ = lean_apply_2(v_h__2_170_, v_startPos_174_, v_endPos_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(lean_object* v_s_177_, lean_object* v_p_178_, lean_object* v_motive_179_, lean_object* v_st_180_, lean_object* v_h__1_181_, lean_object* v_h__2_182_){
_start:
{
if (lean_obj_tag(v_st_180_) == 0)
{
lean_object* v_startPos_183_; lean_object* v_endPos_184_; lean_object* v___x_185_; 
lean_dec(v_h__2_182_);
v_startPos_183_ = lean_ctor_get(v_st_180_, 0);
lean_inc(v_startPos_183_);
v_endPos_184_ = lean_ctor_get(v_st_180_, 1);
lean_inc(v_endPos_184_);
lean_dec_ref_known(v_st_180_, 2);
v___x_185_ = lean_apply_2(v_h__1_181_, v_startPos_183_, v_endPos_184_);
return v___x_185_;
}
else
{
lean_object* v_startPos_186_; lean_object* v_endPos_187_; lean_object* v___x_188_; 
lean_dec(v_h__1_181_);
v_startPos_186_ = lean_ctor_get(v_st_180_, 0);
lean_inc(v_startPos_186_);
v_endPos_187_ = lean_ctor_get(v_st_180_, 1);
lean_inc(v_endPos_187_);
lean_dec_ref_known(v_st_180_, 2);
v___x_188_ = lean_apply_2(v_h__2_182_, v_startPos_186_, v_endPos_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___boxed(lean_object* v_s_189_, lean_object* v_p_190_, lean_object* v_motive_191_, lean_object* v_st_192_, lean_object* v_h__1_193_, lean_object* v_h__2_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(v_s_189_, v_p_190_, v_motive_191_, v_st_192_, v_h__1_193_, v_h__2_194_);
lean_dec(v_p_190_);
lean_dec_ref(v_s_189_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___redArg(lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v_startPos_197_; lean_object* v_endPos_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_startPos_197_ = lean_ctor_get(v_x_196_, 0);
v_endPos_198_ = lean_ctor_get(v_x_196_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_196_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v_x_196_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_endPos_198_);
lean_inc(v_startPos_197_);
lean_dec(v_x_196_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_startPos_197_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_endPos_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_object* v_startPos_206_; lean_object* v_endPos_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_startPos_206_ = lean_ctor_get(v_x_196_, 0);
v_endPos_207_ = lean_ctor_get(v_x_196_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v_x_196_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v_x_196_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_endPos_207_);
lean_inc(v_startPos_206_);
lean_dec(v_x_196_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_startPos_206_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_endPos_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast(lean_object* v_s_215_, lean_object* v_t_216_, lean_object* v_hst_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v_startPos_219_; lean_object* v_endPos_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
v_startPos_219_ = lean_ctor_get(v_x_218_, 0);
v_endPos_220_ = lean_ctor_get(v_x_218_, 1);
v_isSharedCheck_227_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v_x_218_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_endPos_220_);
lean_inc(v_startPos_219_);
lean_dec(v_x_218_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_startPos_219_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_endPos_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
else
{
lean_object* v_startPos_228_; lean_object* v_endPos_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
v_startPos_228_ = lean_ctor_get(v_x_218_, 0);
v_endPos_229_ = lean_ctor_get(v_x_218_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v_x_218_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_endPos_229_);
lean_inc(v_startPos_228_);
lean_dec(v_x_218_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_startPos_228_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_endPos_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___boxed(lean_object* v_s_237_, lean_object* v_t_238_, lean_object* v_hst_239_, lean_object* v_x_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_String_Slice_Pattern_SearchStep_cast(v_s_237_, v_t_238_, v_hst_239_, v_x_240_);
lean_dec_ref(v_t_238_);
lean_dec_ref(v_s_237_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(lean_object* v_inst_242_, lean_object* v_s_243_){
_start:
{
lean_object* v_skipPrefix_x3f_244_; lean_object* v___x_245_; 
v_skipPrefix_x3f_244_ = lean_ctor_get(v_inst_242_, 0);
lean_inc_ref(v_skipPrefix_x3f_244_);
lean_dec_ref(v_inst_242_);
v___x_245_ = lean_apply_1(v_skipPrefix_x3f_244_, v_s_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(lean_object* v_00_u03c1_246_, lean_object* v_pat_247_, lean_object* v_inst_248_, lean_object* v_s_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(v_inst_248_, v_s_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_251_, lean_object* v_pat_252_, lean_object* v_inst_253_, lean_object* v_s_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(v_00_u03c1_251_, v_pat_252_, v_inst_253_, v_s_254_);
lean_dec(v_pat_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg(){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_unsigned_to_nat(0u);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg___boxed(lean_object* v___dummy_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg();
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(lean_object* v_00_u03c1_260_, lean_object* v_pat_261_, lean_object* v_s_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_unsigned_to_nat(0u);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(lean_object* v_00_u03c1_264_, lean_object* v_pat_265_, lean_object* v_s_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(v_00_u03c1_264_, v_pat_265_, v_s_266_);
lean_dec_ref(v_s_266_);
lean_dec(v_pat_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg(){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_unsigned_to_nat(0u);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg___boxed(lean_object* v___dummy_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg();
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_unsigned_to_nat(0u);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(v_a_276_, v_a_277_, v_a_278_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg(){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_unsigned_to_nat(0u);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg___boxed(lean_object* v___dummy_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg();
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(lean_object* v_00_u03c1_284_, lean_object* v_pat_285_, lean_object* v_s_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_unsigned_to_nat(0u);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object* v_00_u03c1_288_, lean_object* v_pat_289_, lean_object* v_s_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(v_00_u03c1_288_, v_pat_289_, v_s_290_);
lean_dec_ref(v_s_290_);
lean_dec(v_pat_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(lean_object* v_s_292_, lean_object* v_inst_293_, lean_object* v_it_294_){
_start:
{
lean_object* v_str_295_; lean_object* v_startInclusive_296_; lean_object* v_endExclusive_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_318_; 
v_str_295_ = lean_ctor_get(v_s_292_, 0);
v_startInclusive_296_ = lean_ctor_get(v_s_292_, 1);
v_endExclusive_297_ = lean_ctor_get(v_s_292_, 2);
v_isSharedCheck_318_ = !lean_is_exclusive(v_s_292_);
if (v_isSharedCheck_318_ == 0)
{
v___x_299_ = v_s_292_;
v_isShared_300_ = v_isSharedCheck_318_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_endExclusive_297_);
lean_inc(v_startInclusive_296_);
lean_inc(v_str_295_);
lean_dec(v_s_292_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_318_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; uint8_t v_decide_302_; 
v___x_301_ = lean_nat_sub(v_endExclusive_297_, v_startInclusive_296_);
v_decide_302_ = lean_nat_dec_eq(v_it_294_, v___x_301_);
lean_dec(v___x_301_);
if (v_decide_302_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v_skipPrefixOfNonempty_x3f_303_ = lean_ctor_get(v_inst_293_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_303_);
lean_dec_ref(v_inst_293_);
v___x_304_ = lean_nat_add(v_startInclusive_296_, v_it_294_);
lean_inc(v___x_304_);
lean_inc_ref(v_str_295_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_304_);
v___x_306_ = v___x_299_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_str_295_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_endExclusive_297_);
v___x_306_ = v_reuseFailAlloc_316_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; 
v___x_307_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_303_, v___x_306_, lean_box(0));
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = lean_string_utf8_next_fast(v_str_295_, v___x_304_);
lean_dec(v___x_304_);
lean_dec_ref(v_str_295_);
v___x_309_ = lean_nat_sub(v___x_308_, v_startInclusive_296_);
lean_dec(v_startInclusive_296_);
lean_inc(v___x_309_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_it_294_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
return v___x_311_;
}
else
{
lean_object* v_val_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v___x_304_);
lean_dec(v_startInclusive_296_);
lean_dec_ref(v_str_295_);
v_val_312_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_val_312_);
lean_dec_ref_known(v___x_307_, 1);
v___x_313_ = lean_nat_add(v_it_294_, v_val_312_);
lean_dec(v_val_312_);
lean_inc(v___x_313_);
v___x_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_314_, 0, v_it_294_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
return v___x_315_;
}
}
}
else
{
lean_object* v___x_317_; 
lean_del_object(v___x_299_);
lean_dec(v_endExclusive_297_);
lean_dec(v_startInclusive_296_);
lean_dec_ref(v_str_295_);
lean_dec(v_it_294_);
lean_dec_ref(v_inst_293_);
v___x_317_ = lean_box(2);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(lean_object* v_s_319_, lean_object* v_inst_320_){
_start:
{
lean_object* v___f_321_; 
v___f_321_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_321_, 0, v_s_319_);
lean_closure_set(v___f_321_, 1, v_inst_320_);
return v___f_321_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(lean_object* v_00_u03c1_322_, lean_object* v_pat_323_, lean_object* v_s_324_, lean_object* v_inst_325_){
_start:
{
lean_object* v___f_326_; 
v___f_326_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_326_, 0, v_s_324_);
lean_closure_set(v___f_326_, 1, v_inst_325_);
return v___f_326_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(lean_object* v_00_u03c1_327_, lean_object* v_pat_328_, lean_object* v_s_329_, lean_object* v_inst_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(v_00_u03c1_327_, v_pat_328_, v_s_329_, v_inst_330_);
lean_dec(v_pat_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_box(0);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg();
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(lean_object* v_00_u03c1_336_, lean_object* v_pat_337_, lean_object* v_s_338_, lean_object* v_inst_339_, lean_object* v_inst_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_box(0);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_342_, lean_object* v_pat_343_, lean_object* v_s_344_, lean_object* v_inst_345_, lean_object* v_inst_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(v_00_u03c1_342_, v_pat_343_, v_s_344_, v_inst_345_, v_inst_346_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_s_344_);
lean_dec(v_pat_343_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v___y_348_, lean_object* v_acc_349_, lean_object* v_recur_350_, lean_object* v_s_351_){
_start:
{
switch(lean_obj_tag(v_s_351_))
{
case 0:
{
lean_object* v_it_352_; lean_object* v_out_353_; lean_object* v_val_354_; 
v_it_352_ = lean_ctor_get(v_s_351_, 0);
lean_inc(v_it_352_);
v_out_353_ = lean_ctor_get(v_s_351_, 1);
lean_inc(v_out_353_);
lean_dec_ref_known(v_s_351_, 2);
v_val_354_ = lean_apply_3(v___y_348_, v_out_353_, lean_box(0), v_acc_349_);
if (lean_obj_tag(v_val_354_) == 0)
{
lean_object* v_a_355_; 
lean_dec(v_it_352_);
lean_dec(v_recur_350_);
v_a_355_ = lean_ctor_get(v_val_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v_val_354_, 1);
return v_a_355_;
}
else
{
lean_object* v_a_356_; lean_object* v___x_357_; 
v_a_356_ = lean_ctor_get(v_val_354_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v_val_354_, 1);
v___x_357_ = lean_apply_4(v_recur_350_, v_it_352_, v_a_356_, lean_box(0), lean_box(0));
return v___x_357_;
}
}
case 1:
{
lean_object* v_it_358_; lean_object* v___x_359_; 
lean_dec_ref(v___y_348_);
v_it_358_ = lean_ctor_get(v_s_351_, 0);
lean_inc(v_it_358_);
lean_dec_ref_known(v_s_351_, 1);
v___x_359_ = lean_apply_4(v_recur_350_, v_it_358_, v_acc_349_, lean_box(0), lean_box(0));
return v___x_359_;
}
default: 
{
lean_dec(v_recur_350_);
lean_dec_ref(v___y_348_);
return v_acc_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v_s_360_, lean_object* v___y_361_, lean_object* v_inst_362_, lean_object* v_lift_363_, lean_object* v_it_364_, lean_object* v_acc_365_, lean_object* v_hP_366_, lean_object* v_recur_367_){
_start:
{
lean_object* v_str_368_; lean_object* v_startInclusive_369_; lean_object* v_endExclusive_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_395_; 
v_str_368_ = lean_ctor_get(v_s_360_, 0);
v_startInclusive_369_ = lean_ctor_get(v_s_360_, 1);
v_endExclusive_370_ = lean_ctor_get(v_s_360_, 2);
v_isSharedCheck_395_ = !lean_is_exclusive(v_s_360_);
if (v_isSharedCheck_395_ == 0)
{
v___x_372_ = v_s_360_;
v_isShared_373_ = v_isSharedCheck_395_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_endExclusive_370_);
lean_inc(v_startInclusive_369_);
lean_inc(v_str_368_);
lean_dec(v_s_360_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_395_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___f_374_; lean_object* v___x_375_; uint8_t v_decide_376_; 
v___f_374_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_374_, 0, v___y_361_);
lean_closure_set(v___f_374_, 1, v_acc_365_);
lean_closure_set(v___f_374_, 2, v_recur_367_);
v___x_375_ = lean_nat_sub(v_endExclusive_370_, v_startInclusive_369_);
v_decide_376_ = lean_nat_dec_eq(v_it_364_, v___x_375_);
lean_dec(v___x_375_);
if (v_decide_376_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v_skipPrefixOfNonempty_x3f_377_ = lean_ctor_get(v_inst_362_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_377_);
lean_dec_ref(v_inst_362_);
v___x_378_ = lean_nat_add(v_startInclusive_369_, v_it_364_);
lean_inc(v___x_378_);
lean_inc_ref(v_str_368_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v___x_378_);
v___x_380_ = v___x_372_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_str_368_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_endExclusive_370_);
v___x_380_ = v_reuseFailAlloc_392_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; 
v___x_381_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_377_, v___x_380_, lean_box(0));
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_382_ = lean_string_utf8_next_fast(v_str_368_, v___x_378_);
lean_dec(v___x_378_);
lean_dec_ref(v_str_368_);
v___x_383_ = lean_nat_sub(v___x_382_, v_startInclusive_369_);
lean_dec(v_startInclusive_369_);
lean_inc(v___x_383_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_it_364_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_apply_4(v_lift_363_, lean_box(0), lean_box(0), v___f_374_, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v_val_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v___x_378_);
lean_dec(v_startInclusive_369_);
lean_dec_ref(v_str_368_);
v_val_387_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v___x_381_, 1);
v___x_388_ = lean_nat_add(v_it_364_, v_val_387_);
lean_dec(v_val_387_);
lean_inc(v___x_388_);
v___x_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_389_, 0, v_it_364_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_apply_4(v_lift_363_, lean_box(0), lean_box(0), v___f_374_, v___x_390_);
return v___x_391_;
}
}
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_del_object(v___x_372_);
lean_dec(v_endExclusive_370_);
lean_dec(v_startInclusive_369_);
lean_dec_ref(v_str_368_);
lean_dec(v_it_364_);
lean_dec_ref(v_inst_362_);
v___x_393_ = lean_box(2);
v___x_394_ = lean_apply_4(v_lift_363_, lean_box(0), lean_box(0), v___f_374_, v___x_393_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object* v_s_396_, lean_object* v_inst_397_, lean_object* v_lift_398_, lean_object* v_00_u03b3_399_, lean_object* v_Pl_400_, lean_object* v_it_401_, lean_object* v_init_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___f_404_; lean_object* v___x_405_; 
v___f_404_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1), 8, 4);
lean_closure_set(v___f_404_, 0, v_s_396_);
lean_closure_set(v___f_404_, 1, v___y_403_);
lean_closure_set(v___f_404_, 2, v_inst_397_);
lean_closure_set(v___f_404_, 3, v_lift_398_);
v___x_405_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_404_, v_it_401_, v_init_402_, lean_box(0));
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_406_, lean_object* v_inst_407_){
_start:
{
lean_object* v___f_408_; 
v___f_408_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_408_, 0, v_s_406_);
lean_closure_set(v___f_408_, 1, v_inst_407_);
return v___f_408_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_409_, lean_object* v_pat_410_, lean_object* v_s_411_, lean_object* v_inst_412_){
_start:
{
lean_object* v___f_413_; 
v___f_413_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_413_, 0, v_s_411_);
lean_closure_set(v___f_413_, 1, v_inst_412_);
return v___f_413_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_414_, lean_object* v_pat_415_, lean_object* v_s_416_, lean_object* v_inst_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_414_, v_pat_415_, v_s_416_, v_inst_417_);
lean_dec(v_pat_415_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(lean_object* v_pat_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_420_, 0, lean_box(0));
lean_closure_set(v___x_420_, 1, v_pat_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(lean_object* v_00_u03c1_421_, lean_object* v_pat_422_, lean_object* v_inst_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_424_, 0, lean_box(0));
lean_closure_set(v___x_424_, 1, v_pat_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_425_, lean_object* v_pat_426_, lean_object* v_inst_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(v_00_u03c1_425_, v_pat_426_, v_inst_427_);
lean_dec_ref(v_inst_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg(){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_unsigned_to_nat(0u);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg___boxed(lean_object* v___dummy_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg();
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object* v_00_u03c1_433_, lean_object* v_pat_434_, lean_object* v_s_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_unsigned_to_nat(0u);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object* v_00_u03c1_437_, lean_object* v_pat_438_, lean_object* v_s_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(v_00_u03c1_437_, v_pat_438_, v_s_439_);
lean_dec_ref(v_s_439_);
lean_dec(v_pat_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg(){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = lean_unsigned_to_nat(0u);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg___boxed(lean_object* v___dummy_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg();
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_unsigned_to_nat(0u);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(v_a_449_, v_a_450_, v_a_451_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(lean_object* v_s_453_){
_start:
{
lean_object* v_startInclusive_454_; lean_object* v_endExclusive_455_; lean_object* v___x_456_; 
v_startInclusive_454_ = lean_ctor_get(v_s_453_, 1);
v_endExclusive_455_ = lean_ctor_get(v_s_453_, 2);
v___x_456_ = lean_nat_sub(v_endExclusive_455_, v_startInclusive_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(lean_object* v_s_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_457_);
lean_dec_ref(v_s_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(lean_object* v_00_u03c1_459_, lean_object* v_pat_460_, lean_object* v_s_461_){
_start:
{
lean_object* v_startInclusive_462_; lean_object* v_endExclusive_463_; lean_object* v___x_464_; 
v_startInclusive_462_ = lean_ctor_get(v_s_461_, 1);
v_endExclusive_463_ = lean_ctor_get(v_s_461_, 2);
v___x_464_ = lean_nat_sub(v_endExclusive_463_, v_startInclusive_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object* v_00_u03c1_465_, lean_object* v_pat_466_, lean_object* v_s_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(v_00_u03c1_465_, v_pat_466_, v_s_467_);
lean_dec_ref(v_s_467_);
lean_dec(v_pat_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(lean_object* v_inst_469_, lean_object* v_s_470_, lean_object* v_it_471_){
_start:
{
lean_object* v___x_472_; uint8_t v_decide_473_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v_decide_473_ = lean_nat_dec_eq(v_it_471_, v___x_472_);
if (v_decide_473_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_493_; 
v_skipSuffixOfNonempty_x3f_474_ = lean_ctor_get(v_inst_469_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_inst_469_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_494_ = lean_ctor_get(v_inst_469_, 2);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_inst_469_, 0);
lean_dec(v_unused_495_);
v___x_476_ = v_inst_469_;
v_isShared_477_ = v_isSharedCheck_493_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_474_);
lean_dec(v_inst_469_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_493_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_str_478_; lean_object* v_startInclusive_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v_str_478_ = lean_ctor_get(v_s_470_, 0);
v_startInclusive_479_ = lean_ctor_get(v_s_470_, 1);
v___x_480_ = lean_nat_add(v_startInclusive_479_, v_it_471_);
lean_inc(v_startInclusive_479_);
lean_inc_ref(v_str_478_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 2, v___x_480_);
lean_ctor_set(v___x_476_, 1, v_startInclusive_479_);
lean_ctor_set(v___x_476_, 0, v_str_478_);
v___x_482_ = v___x_476_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_str_478_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_startInclusive_479_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v___x_480_);
v___x_482_ = v_reuseFailAlloc_492_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; 
v___x_483_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_474_, v___x_482_, lean_box(0));
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_sub(v_it_471_, v___x_484_);
v___x_486_ = l_String_Slice_posLE(v_s_470_, v___x_485_);
lean_inc(v___x_486_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v_it_471_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
return v___x_488_;
}
else
{
lean_object* v_val_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_val_489_ = lean_ctor_get(v___x_483_, 0);
lean_inc_n(v_val_489_, 2);
lean_dec_ref_known(v___x_483_, 1);
v___x_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_490_, 0, v_val_489_);
lean_ctor_set(v___x_490_, 1, v_it_471_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v_val_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
return v___x_491_;
}
}
}
}
else
{
lean_object* v___x_496_; 
lean_dec(v_it_471_);
lean_dec_ref(v_inst_469_);
v___x_496_ = lean_box(2);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(lean_object* v_inst_497_, lean_object* v_s_498_, lean_object* v_it_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_497_, v_s_498_, v_it_499_);
lean_dec_ref(v_s_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(lean_object* v_s_501_, lean_object* v_inst_502_){
_start:
{
lean_object* v___f_503_; 
v___f_503_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_503_, 0, v_inst_502_);
lean_closure_set(v___f_503_, 1, v_s_501_);
return v___f_503_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(lean_object* v_00_u03c1_504_, lean_object* v_pat_505_, lean_object* v_s_506_, lean_object* v_inst_507_){
_start:
{
lean_object* v___f_508_; 
v___f_508_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_508_, 0, v_inst_507_);
lean_closure_set(v___f_508_, 1, v_s_506_);
return v___f_508_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(lean_object* v_00_u03c1_509_, lean_object* v_pat_510_, lean_object* v_s_511_, lean_object* v_inst_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_509_, v_pat_510_, v_s_511_, v_inst_512_);
lean_dec(v_pat_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_box(0);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg();
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(lean_object* v_00_u03c1_518_, lean_object* v_pat_519_, lean_object* v_s_520_, lean_object* v_inst_521_, lean_object* v_inst_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lean_box(0);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_524_, lean_object* v_pat_525_, lean_object* v_s_526_, lean_object* v_inst_527_, lean_object* v_inst_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(v_00_u03c1_524_, v_pat_525_, v_s_526_, v_inst_527_, v_inst_528_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_s_526_);
lean_dec(v_pat_525_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v___y_530_, lean_object* v_inst_531_, lean_object* v_s_532_, lean_object* v_lift_533_, lean_object* v_it_534_, lean_object* v_acc_535_, lean_object* v_hP_536_, lean_object* v_recur_537_){
_start:
{
lean_object* v___f_538_; lean_object* v___x_539_; uint8_t v_decide_540_; 
v___f_538_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_538_, 0, v___y_530_);
lean_closure_set(v___f_538_, 1, v_acc_535_);
lean_closure_set(v___f_538_, 2, v_recur_537_);
v___x_539_ = lean_unsigned_to_nat(0u);
v_decide_540_ = lean_nat_dec_eq(v_it_534_, v___x_539_);
if (v_decide_540_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_562_; 
v_skipSuffixOfNonempty_x3f_541_ = lean_ctor_get(v_inst_531_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_inst_531_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; lean_object* v_unused_564_; 
v_unused_563_ = lean_ctor_get(v_inst_531_, 2);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_inst_531_, 0);
lean_dec(v_unused_564_);
v___x_543_ = v_inst_531_;
v_isShared_544_ = v_isSharedCheck_562_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_541_);
lean_dec(v_inst_531_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_562_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_str_545_; lean_object* v_startInclusive_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v_str_545_ = lean_ctor_get(v_s_532_, 0);
v_startInclusive_546_ = lean_ctor_get(v_s_532_, 1);
v___x_547_ = lean_nat_add(v_startInclusive_546_, v_it_534_);
lean_inc(v_startInclusive_546_);
lean_inc_ref(v_str_545_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 2, v___x_547_);
lean_ctor_set(v___x_543_, 1, v_startInclusive_546_);
lean_ctor_set(v___x_543_, 0, v_str_545_);
v___x_549_ = v___x_543_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_str_545_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_startInclusive_546_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v___x_547_);
v___x_549_ = v_reuseFailAlloc_561_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_541_, v___x_549_, lean_box(0));
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = lean_nat_sub(v_it_534_, v___x_551_);
v___x_553_ = l_String_Slice_posLE(v_s_532_, v___x_552_);
lean_inc(v___x_553_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_it_534_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_apply_4(v_lift_533_, lean_box(0), lean_box(0), v___f_538_, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v_val_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_val_557_ = lean_ctor_get(v___x_550_, 0);
lean_inc_n(v_val_557_, 2);
lean_dec_ref_known(v___x_550_, 1);
v___x_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_558_, 0, v_val_557_);
lean_ctor_set(v___x_558_, 1, v_it_534_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v_val_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_apply_4(v_lift_533_, lean_box(0), lean_box(0), v___f_538_, v___x_559_);
return v___x_560_;
}
}
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v_it_534_);
lean_dec_ref(v_inst_531_);
v___x_565_ = lean_box(2);
v___x_566_ = lean_apply_4(v_lift_533_, lean_box(0), lean_box(0), v___f_538_, v___x_565_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed(lean_object* v___y_567_, lean_object* v_inst_568_, lean_object* v_s_569_, lean_object* v_lift_570_, lean_object* v_it_571_, lean_object* v_acc_572_, lean_object* v_hP_573_, lean_object* v_recur_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(v___y_567_, v_inst_568_, v_s_569_, v_lift_570_, v_it_571_, v_acc_572_, v_hP_573_, v_recur_574_);
lean_dec_ref(v_s_569_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v_inst_576_, lean_object* v_s_577_, lean_object* v_lift_578_, lean_object* v_00_u03b3_579_, lean_object* v_Pl_580_, lean_object* v_it_581_, lean_object* v_init_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___f_584_; lean_object* v___x_585_; 
v___f_584_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_584_, 0, v___y_583_);
lean_closure_set(v___f_584_, 1, v_inst_576_);
lean_closure_set(v___f_584_, 2, v_s_577_);
lean_closure_set(v___f_584_, 3, v_lift_578_);
v___x_585_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_584_, v_it_581_, v_init_582_, lean_box(0));
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_586_, lean_object* v_inst_587_){
_start:
{
lean_object* v___f_588_; 
v___f_588_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_588_, 0, v_inst_587_);
lean_closure_set(v___f_588_, 1, v_s_586_);
return v___f_588_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_589_, lean_object* v_pat_590_, lean_object* v_s_591_, lean_object* v_inst_592_){
_start:
{
lean_object* v___f_593_; 
v___f_593_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_593_, 0, v_inst_592_);
lean_closure_set(v___f_593_, 1, v_s_591_);
return v___f_593_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_594_, lean_object* v_pat_595_, lean_object* v_s_596_, lean_object* v_inst_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_594_, v_pat_595_, v_s_596_, v_inst_597_);
lean_dec(v_pat_595_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(lean_object* v_pat_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_600_, 0, lean_box(0));
lean_closure_set(v___x_600_, 1, v_pat_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(lean_object* v_00_u03c1_601_, lean_object* v_pat_602_, lean_object* v_inst_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_604_, 0, lean_box(0));
lean_closure_set(v___x_604_, 1, v_pat_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_605_, lean_object* v_pat_606_, lean_object* v_inst_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(v_00_u03c1_605_, v_pat_606_, v_inst_607_);
lean_dec_ref(v_inst_607_);
return v_res_608_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Pattern_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Pattern_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Pattern_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Pattern_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
