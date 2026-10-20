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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___redArg(lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v_startPos_169_; lean_object* v_endPos_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_startPos_169_ = lean_ctor_get(v_x_168_, 0);
v_endPos_170_ = lean_ctor_get(v_x_168_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v_x_168_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_endPos_170_);
lean_inc(v_startPos_169_);
lean_dec(v_x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_startPos_169_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_endPos_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
else
{
lean_object* v_startPos_178_; lean_object* v_endPos_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_startPos_178_ = lean_ctor_get(v_x_168_, 0);
v_endPos_179_ = lean_ctor_get(v_x_168_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v_x_168_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_endPos_179_);
lean_inc(v_startPos_178_);
lean_dec(v_x_168_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_startPos_178_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_endPos_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast(lean_object* v_s_187_, lean_object* v_t_188_, lean_object* v_hst_189_, lean_object* v_x_190_){
_start:
{
if (lean_obj_tag(v_x_190_) == 0)
{
lean_object* v_startPos_191_; lean_object* v_endPos_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_startPos_191_ = lean_ctor_get(v_x_190_, 0);
v_endPos_192_ = lean_ctor_get(v_x_190_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v_x_190_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_endPos_192_);
lean_inc(v_startPos_191_);
lean_dec(v_x_190_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_startPos_191_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_endPos_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
else
{
lean_object* v_startPos_200_; lean_object* v_endPos_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_startPos_200_ = lean_ctor_get(v_x_190_, 0);
v_endPos_201_ = lean_ctor_get(v_x_190_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v_x_190_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_endPos_201_);
lean_inc(v_startPos_200_);
lean_dec(v_x_190_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_startPos_200_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_endPos_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___boxed(lean_object* v_s_209_, lean_object* v_t_210_, lean_object* v_hst_211_, lean_object* v_x_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_String_Slice_Pattern_SearchStep_cast(v_s_209_, v_t_210_, v_hst_211_, v_x_212_);
lean_dec_ref(v_t_210_);
lean_dec_ref(v_s_209_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(lean_object* v_inst_214_, lean_object* v_s_215_){
_start:
{
lean_object* v_skipPrefix_x3f_216_; lean_object* v___x_217_; 
v_skipPrefix_x3f_216_ = lean_ctor_get(v_inst_214_, 0);
lean_inc_ref(v_skipPrefix_x3f_216_);
lean_dec_ref(v_inst_214_);
v___x_217_ = lean_apply_1(v_skipPrefix_x3f_216_, v_s_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(lean_object* v_00_u03c1_218_, lean_object* v_pat_219_, lean_object* v_inst_220_, lean_object* v_s_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(v_inst_220_, v_s_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_223_, lean_object* v_pat_224_, lean_object* v_inst_225_, lean_object* v_s_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(v_00_u03c1_223_, v_pat_224_, v_inst_225_, v_s_226_);
lean_dec(v_pat_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg(){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_unsigned_to_nat(0u);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg___boxed(lean_object* v___dummy_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg();
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(lean_object* v_00_u03c1_232_, lean_object* v_pat_233_, lean_object* v_s_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(0u);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(lean_object* v_00_u03c1_236_, lean_object* v_pat_237_, lean_object* v_s_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(v_00_u03c1_236_, v_pat_237_, v_s_238_);
lean_dec_ref(v_s_238_);
lean_dec(v_pat_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg(){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(0u);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg___boxed(lean_object* v___dummy_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg();
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_unsigned_to_nat(0u);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(v_a_248_, v_a_249_, v_a_250_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg(){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_unsigned_to_nat(0u);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg___boxed(lean_object* v___dummy_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg();
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(lean_object* v_00_u03c1_256_, lean_object* v_pat_257_, lean_object* v_s_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_unsigned_to_nat(0u);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object* v_00_u03c1_260_, lean_object* v_pat_261_, lean_object* v_s_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(v_00_u03c1_260_, v_pat_261_, v_s_262_);
lean_dec_ref(v_s_262_);
lean_dec(v_pat_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(lean_object* v_s_264_, lean_object* v_inst_265_, lean_object* v_it_266_){
_start:
{
lean_object* v_str_267_; lean_object* v_startInclusive_268_; lean_object* v_endExclusive_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_290_; 
v_str_267_ = lean_ctor_get(v_s_264_, 0);
v_startInclusive_268_ = lean_ctor_get(v_s_264_, 1);
v_endExclusive_269_ = lean_ctor_get(v_s_264_, 2);
v_isSharedCheck_290_ = !lean_is_exclusive(v_s_264_);
if (v_isSharedCheck_290_ == 0)
{
v___x_271_ = v_s_264_;
v_isShared_272_ = v_isSharedCheck_290_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_endExclusive_269_);
lean_inc(v_startInclusive_268_);
lean_inc(v_str_267_);
lean_dec(v_s_264_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_290_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; uint8_t v_decide_274_; 
v___x_273_ = lean_nat_sub(v_endExclusive_269_, v_startInclusive_268_);
v_decide_274_ = lean_nat_dec_eq(v_it_266_, v___x_273_);
lean_dec(v___x_273_);
if (v_decide_274_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v_skipPrefixOfNonempty_x3f_275_ = lean_ctor_get(v_inst_265_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_275_);
lean_dec_ref(v_inst_265_);
v___x_276_ = lean_nat_add(v_startInclusive_268_, v_it_266_);
lean_inc(v___x_276_);
lean_inc_ref(v_str_267_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_276_);
v___x_278_ = v___x_271_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_str_267_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_endExclusive_269_);
v___x_278_ = v_reuseFailAlloc_288_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; 
v___x_279_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_275_, v___x_278_, lean_box(0));
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_280_ = lean_string_utf8_next_fast(v_str_267_, v___x_276_);
lean_dec(v___x_276_);
lean_dec_ref(v_str_267_);
v___x_281_ = lean_nat_sub(v___x_280_, v_startInclusive_268_);
lean_dec(v_startInclusive_268_);
lean_inc(v___x_281_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_it_266_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
return v___x_283_;
}
else
{
lean_object* v_val_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v___x_276_);
lean_dec(v_startInclusive_268_);
lean_dec_ref(v_str_267_);
v_val_284_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_val_284_);
lean_dec_ref_known(v___x_279_, 1);
v___x_285_ = lean_nat_add(v_it_266_, v_val_284_);
lean_dec(v_val_284_);
lean_inc(v___x_285_);
v___x_286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_286_, 0, v_it_266_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
return v___x_287_;
}
}
}
else
{
lean_object* v___x_289_; 
lean_del_object(v___x_271_);
lean_dec(v_endExclusive_269_);
lean_dec(v_startInclusive_268_);
lean_dec_ref(v_str_267_);
lean_dec(v_it_266_);
lean_dec_ref(v_inst_265_);
v___x_289_ = lean_box(2);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(lean_object* v_s_291_, lean_object* v_inst_292_){
_start:
{
lean_object* v___f_293_; 
v___f_293_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_293_, 0, v_s_291_);
lean_closure_set(v___f_293_, 1, v_inst_292_);
return v___f_293_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(lean_object* v_00_u03c1_294_, lean_object* v_pat_295_, lean_object* v_s_296_, lean_object* v_inst_297_){
_start:
{
lean_object* v___f_298_; 
v___f_298_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_298_, 0, v_s_296_);
lean_closure_set(v___f_298_, 1, v_inst_297_);
return v___f_298_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(lean_object* v_00_u03c1_299_, lean_object* v_pat_300_, lean_object* v_s_301_, lean_object* v_inst_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(v_00_u03c1_299_, v_pat_300_, v_s_301_, v_inst_302_);
lean_dec(v_pat_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_box(0);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg();
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(lean_object* v_00_u03c1_308_, lean_object* v_pat_309_, lean_object* v_s_310_, lean_object* v_inst_311_, lean_object* v_inst_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_box(0);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_314_, lean_object* v_pat_315_, lean_object* v_s_316_, lean_object* v_inst_317_, lean_object* v_inst_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(v_00_u03c1_314_, v_pat_315_, v_s_316_, v_inst_317_, v_inst_318_);
lean_dec_ref(v_inst_317_);
lean_dec_ref(v_s_316_);
lean_dec(v_pat_315_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v___y_320_, lean_object* v_acc_321_, lean_object* v_recur_322_, lean_object* v_s_323_){
_start:
{
switch(lean_obj_tag(v_s_323_))
{
case 0:
{
lean_object* v_it_324_; lean_object* v_out_325_; lean_object* v_val_326_; 
v_it_324_ = lean_ctor_get(v_s_323_, 0);
lean_inc(v_it_324_);
v_out_325_ = lean_ctor_get(v_s_323_, 1);
lean_inc(v_out_325_);
lean_dec_ref_known(v_s_323_, 2);
v_val_326_ = lean_apply_3(v___y_320_, v_out_325_, lean_box(0), v_acc_321_);
if (lean_obj_tag(v_val_326_) == 0)
{
lean_object* v_a_327_; 
lean_dec(v_it_324_);
lean_dec(v_recur_322_);
v_a_327_ = lean_ctor_get(v_val_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v_val_326_, 1);
return v_a_327_;
}
else
{
lean_object* v_a_328_; lean_object* v___x_329_; 
v_a_328_ = lean_ctor_get(v_val_326_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v_val_326_, 1);
v___x_329_ = lean_apply_4(v_recur_322_, v_it_324_, v_a_328_, lean_box(0), lean_box(0));
return v___x_329_;
}
}
case 1:
{
lean_object* v_it_330_; lean_object* v___x_331_; 
lean_dec_ref(v___y_320_);
v_it_330_ = lean_ctor_get(v_s_323_, 0);
lean_inc(v_it_330_);
lean_dec_ref_known(v_s_323_, 1);
v___x_331_ = lean_apply_4(v_recur_322_, v_it_330_, v_acc_321_, lean_box(0), lean_box(0));
return v___x_331_;
}
default: 
{
lean_dec(v_recur_322_);
lean_dec_ref(v___y_320_);
return v_acc_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v_s_332_, lean_object* v___y_333_, lean_object* v_inst_334_, lean_object* v_lift_335_, lean_object* v_it_336_, lean_object* v_acc_337_, lean_object* v_hP_338_, lean_object* v_recur_339_){
_start:
{
lean_object* v_str_340_; lean_object* v_startInclusive_341_; lean_object* v_endExclusive_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_367_; 
v_str_340_ = lean_ctor_get(v_s_332_, 0);
v_startInclusive_341_ = lean_ctor_get(v_s_332_, 1);
v_endExclusive_342_ = lean_ctor_get(v_s_332_, 2);
v_isSharedCheck_367_ = !lean_is_exclusive(v_s_332_);
if (v_isSharedCheck_367_ == 0)
{
v___x_344_ = v_s_332_;
v_isShared_345_ = v_isSharedCheck_367_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_endExclusive_342_);
lean_inc(v_startInclusive_341_);
lean_inc(v_str_340_);
lean_dec(v_s_332_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_367_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___f_346_; lean_object* v___x_347_; uint8_t v_decide_348_; 
v___f_346_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_346_, 0, v___y_333_);
lean_closure_set(v___f_346_, 1, v_acc_337_);
lean_closure_set(v___f_346_, 2, v_recur_339_);
v___x_347_ = lean_nat_sub(v_endExclusive_342_, v_startInclusive_341_);
v_decide_348_ = lean_nat_dec_eq(v_it_336_, v___x_347_);
lean_dec(v___x_347_);
if (v_decide_348_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v_skipPrefixOfNonempty_x3f_349_ = lean_ctor_get(v_inst_334_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_349_);
lean_dec_ref(v_inst_334_);
v___x_350_ = lean_nat_add(v_startInclusive_341_, v_it_336_);
lean_inc(v___x_350_);
lean_inc_ref(v_str_340_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v___x_350_);
v___x_352_ = v___x_344_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_str_340_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_endExclusive_342_);
v___x_352_ = v_reuseFailAlloc_364_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; 
v___x_353_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_349_, v___x_352_, lean_box(0));
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_354_ = lean_string_utf8_next_fast(v_str_340_, v___x_350_);
lean_dec(v___x_350_);
lean_dec_ref(v_str_340_);
v___x_355_ = lean_nat_sub(v___x_354_, v_startInclusive_341_);
lean_dec(v_startInclusive_341_);
lean_inc(v___x_355_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v_it_336_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = lean_apply_4(v_lift_335_, lean_box(0), lean_box(0), v___f_346_, v___x_357_);
return v___x_358_;
}
else
{
lean_object* v_val_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v___x_350_);
lean_dec(v_startInclusive_341_);
lean_dec_ref(v_str_340_);
v_val_359_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_val_359_);
lean_dec_ref_known(v___x_353_, 1);
v___x_360_ = lean_nat_add(v_it_336_, v_val_359_);
lean_dec(v_val_359_);
lean_inc(v___x_360_);
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v_it_336_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_apply_4(v_lift_335_, lean_box(0), lean_box(0), v___f_346_, v___x_362_);
return v___x_363_;
}
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_del_object(v___x_344_);
lean_dec(v_endExclusive_342_);
lean_dec(v_startInclusive_341_);
lean_dec_ref(v_str_340_);
lean_dec(v_it_336_);
lean_dec_ref(v_inst_334_);
v___x_365_ = lean_box(2);
v___x_366_ = lean_apply_4(v_lift_335_, lean_box(0), lean_box(0), v___f_346_, v___x_365_);
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object* v_s_368_, lean_object* v_inst_369_, lean_object* v_lift_370_, lean_object* v_00_u03b3_371_, lean_object* v_Pl_372_, lean_object* v_it_373_, lean_object* v_init_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___f_376_; lean_object* v___x_377_; 
v___f_376_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1), 8, 4);
lean_closure_set(v___f_376_, 0, v_s_368_);
lean_closure_set(v___f_376_, 1, v___y_375_);
lean_closure_set(v___f_376_, 2, v_inst_369_);
lean_closure_set(v___f_376_, 3, v_lift_370_);
v___x_377_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_376_, v_it_373_, v_init_374_, lean_box(0));
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_378_, lean_object* v_inst_379_){
_start:
{
lean_object* v___f_380_; 
v___f_380_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_380_, 0, v_s_378_);
lean_closure_set(v___f_380_, 1, v_inst_379_);
return v___f_380_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_381_, lean_object* v_pat_382_, lean_object* v_s_383_, lean_object* v_inst_384_){
_start:
{
lean_object* v___f_385_; 
v___f_385_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_385_, 0, v_s_383_);
lean_closure_set(v___f_385_, 1, v_inst_384_);
return v___f_385_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_386_, lean_object* v_pat_387_, lean_object* v_s_388_, lean_object* v_inst_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_386_, v_pat_387_, v_s_388_, v_inst_389_);
lean_dec(v_pat_387_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(lean_object* v_pat_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_392_, 0, lean_box(0));
lean_closure_set(v___x_392_, 1, v_pat_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(lean_object* v_00_u03c1_393_, lean_object* v_pat_394_, lean_object* v_inst_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_396_, 0, lean_box(0));
lean_closure_set(v___x_396_, 1, v_pat_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_397_, lean_object* v_pat_398_, lean_object* v_inst_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(v_00_u03c1_397_, v_pat_398_, v_inst_399_);
lean_dec_ref(v_inst_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg(){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_unsigned_to_nat(0u);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg___boxed(lean_object* v___dummy_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg();
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object* v_00_u03c1_405_, lean_object* v_pat_406_, lean_object* v_s_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_unsigned_to_nat(0u);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object* v_00_u03c1_409_, lean_object* v_pat_410_, lean_object* v_s_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(v_00_u03c1_409_, v_pat_410_, v_s_411_);
lean_dec_ref(v_s_411_);
lean_dec(v_pat_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg(){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_unsigned_to_nat(0u);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg___boxed(lean_object* v___dummy_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg();
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_unsigned_to_nat(0u);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(v_a_421_, v_a_422_, v_a_423_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(lean_object* v_s_425_){
_start:
{
lean_object* v_startInclusive_426_; lean_object* v_endExclusive_427_; lean_object* v___x_428_; 
v_startInclusive_426_ = lean_ctor_get(v_s_425_, 1);
v_endExclusive_427_ = lean_ctor_get(v_s_425_, 2);
v___x_428_ = lean_nat_sub(v_endExclusive_427_, v_startInclusive_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(lean_object* v_s_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_429_);
lean_dec_ref(v_s_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(lean_object* v_00_u03c1_431_, lean_object* v_pat_432_, lean_object* v_s_433_){
_start:
{
lean_object* v_startInclusive_434_; lean_object* v_endExclusive_435_; lean_object* v___x_436_; 
v_startInclusive_434_ = lean_ctor_get(v_s_433_, 1);
v_endExclusive_435_ = lean_ctor_get(v_s_433_, 2);
v___x_436_ = lean_nat_sub(v_endExclusive_435_, v_startInclusive_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object* v_00_u03c1_437_, lean_object* v_pat_438_, lean_object* v_s_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(v_00_u03c1_437_, v_pat_438_, v_s_439_);
lean_dec_ref(v_s_439_);
lean_dec(v_pat_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(lean_object* v_inst_441_, lean_object* v_s_442_, lean_object* v_it_443_){
_start:
{
lean_object* v___x_444_; uint8_t v_decide_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v_decide_445_ = lean_nat_dec_eq(v_it_443_, v___x_444_);
if (v_decide_445_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_465_; 
v_skipSuffixOfNonempty_x3f_446_ = lean_ctor_get(v_inst_441_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_inst_441_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_466_ = lean_ctor_get(v_inst_441_, 2);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_inst_441_, 0);
lean_dec(v_unused_467_);
v___x_448_ = v_inst_441_;
v_isShared_449_ = v_isSharedCheck_465_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_446_);
lean_dec(v_inst_441_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_465_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v_str_450_; lean_object* v_startInclusive_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v_str_450_ = lean_ctor_get(v_s_442_, 0);
v_startInclusive_451_ = lean_ctor_get(v_s_442_, 1);
v___x_452_ = lean_nat_add(v_startInclusive_451_, v_it_443_);
lean_inc(v_startInclusive_451_);
lean_inc_ref(v_str_450_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 2, v___x_452_);
lean_ctor_set(v___x_448_, 1, v_startInclusive_451_);
lean_ctor_set(v___x_448_, 0, v_str_450_);
v___x_454_ = v___x_448_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_str_450_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_startInclusive_451_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v___x_452_);
v___x_454_ = v_reuseFailAlloc_464_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; 
v___x_455_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_446_, v___x_454_, lean_box(0));
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_sub(v_it_443_, v___x_456_);
v___x_458_ = l_String_Slice_posLE(v_s_442_, v___x_457_);
lean_inc(v___x_458_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_it_443_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
return v___x_460_;
}
else
{
lean_object* v_val_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_val_461_ = lean_ctor_get(v___x_455_, 0);
lean_inc_n(v_val_461_, 2);
lean_dec_ref_known(v___x_455_, 1);
v___x_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_462_, 0, v_val_461_);
lean_ctor_set(v___x_462_, 1, v_it_443_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_val_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
return v___x_463_;
}
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec(v_it_443_);
lean_dec_ref(v_inst_441_);
v___x_468_ = lean_box(2);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(lean_object* v_inst_469_, lean_object* v_s_470_, lean_object* v_it_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_469_, v_s_470_, v_it_471_);
lean_dec_ref(v_s_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(lean_object* v_s_473_, lean_object* v_inst_474_){
_start:
{
lean_object* v___f_475_; 
v___f_475_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_475_, 0, v_inst_474_);
lean_closure_set(v___f_475_, 1, v_s_473_);
return v___f_475_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(lean_object* v_00_u03c1_476_, lean_object* v_pat_477_, lean_object* v_s_478_, lean_object* v_inst_479_){
_start:
{
lean_object* v___f_480_; 
v___f_480_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_480_, 0, v_inst_479_);
lean_closure_set(v___f_480_, 1, v_s_478_);
return v___f_480_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(lean_object* v_00_u03c1_481_, lean_object* v_pat_482_, lean_object* v_s_483_, lean_object* v_inst_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_481_, v_pat_482_, v_s_483_, v_inst_484_);
lean_dec(v_pat_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = lean_box(0);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg();
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(lean_object* v_00_u03c1_490_, lean_object* v_pat_491_, lean_object* v_s_492_, lean_object* v_inst_493_, lean_object* v_inst_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_box(0);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_496_, lean_object* v_pat_497_, lean_object* v_s_498_, lean_object* v_inst_499_, lean_object* v_inst_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(v_00_u03c1_496_, v_pat_497_, v_s_498_, v_inst_499_, v_inst_500_);
lean_dec_ref(v_inst_499_);
lean_dec_ref(v_s_498_);
lean_dec(v_pat_497_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v___y_502_, lean_object* v_inst_503_, lean_object* v_s_504_, lean_object* v_lift_505_, lean_object* v_it_506_, lean_object* v_acc_507_, lean_object* v_hP_508_, lean_object* v_recur_509_){
_start:
{
lean_object* v___f_510_; lean_object* v___x_511_; uint8_t v_decide_512_; 
v___f_510_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_510_, 0, v___y_502_);
lean_closure_set(v___f_510_, 1, v_acc_507_);
lean_closure_set(v___f_510_, 2, v_recur_509_);
v___x_511_ = lean_unsigned_to_nat(0u);
v_decide_512_ = lean_nat_dec_eq(v_it_506_, v___x_511_);
if (v_decide_512_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_534_; 
v_skipSuffixOfNonempty_x3f_513_ = lean_ctor_get(v_inst_503_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_inst_503_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; lean_object* v_unused_536_; 
v_unused_535_ = lean_ctor_get(v_inst_503_, 2);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_inst_503_, 0);
lean_dec(v_unused_536_);
v___x_515_ = v_inst_503_;
v_isShared_516_ = v_isSharedCheck_534_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_513_);
lean_dec(v_inst_503_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_534_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_str_517_; lean_object* v_startInclusive_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v_str_517_ = lean_ctor_get(v_s_504_, 0);
v_startInclusive_518_ = lean_ctor_get(v_s_504_, 1);
v___x_519_ = lean_nat_add(v_startInclusive_518_, v_it_506_);
lean_inc(v_startInclusive_518_);
lean_inc_ref(v_str_517_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 2, v___x_519_);
lean_ctor_set(v___x_515_, 1, v_startInclusive_518_);
lean_ctor_set(v___x_515_, 0, v_str_517_);
v___x_521_ = v___x_515_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_str_517_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_startInclusive_518_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v___x_519_);
v___x_521_ = v_reuseFailAlloc_533_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_513_, v___x_521_, lean_box(0));
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_sub(v_it_506_, v___x_523_);
v___x_525_ = l_String_Slice_posLE(v_s_504_, v___x_524_);
lean_inc(v___x_525_);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v_it_506_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_apply_4(v_lift_505_, lean_box(0), lean_box(0), v___f_510_, v___x_527_);
return v___x_528_;
}
else
{
lean_object* v_val_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_val_529_ = lean_ctor_get(v___x_522_, 0);
lean_inc_n(v_val_529_, 2);
lean_dec_ref_known(v___x_522_, 1);
v___x_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_530_, 0, v_val_529_);
lean_ctor_set(v___x_530_, 1, v_it_506_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_val_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_apply_4(v_lift_505_, lean_box(0), lean_box(0), v___f_510_, v___x_531_);
return v___x_532_;
}
}
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_it_506_);
lean_dec_ref(v_inst_503_);
v___x_537_ = lean_box(2);
v___x_538_ = lean_apply_4(v_lift_505_, lean_box(0), lean_box(0), v___f_510_, v___x_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed(lean_object* v___y_539_, lean_object* v_inst_540_, lean_object* v_s_541_, lean_object* v_lift_542_, lean_object* v_it_543_, lean_object* v_acc_544_, lean_object* v_hP_545_, lean_object* v_recur_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(v___y_539_, v_inst_540_, v_s_541_, v_lift_542_, v_it_543_, v_acc_544_, v_hP_545_, v_recur_546_);
lean_dec_ref(v_s_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v_inst_548_, lean_object* v_s_549_, lean_object* v_lift_550_, lean_object* v_00_u03b3_551_, lean_object* v_Pl_552_, lean_object* v_it_553_, lean_object* v_init_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___f_556_; lean_object* v___x_557_; 
v___f_556_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_556_, 0, v___y_555_);
lean_closure_set(v___f_556_, 1, v_inst_548_);
lean_closure_set(v___f_556_, 2, v_s_549_);
lean_closure_set(v___f_556_, 3, v_lift_550_);
v___x_557_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_556_, v_it_553_, v_init_554_, lean_box(0));
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_558_, lean_object* v_inst_559_){
_start:
{
lean_object* v___f_560_; 
v___f_560_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_560_, 0, v_inst_559_);
lean_closure_set(v___f_560_, 1, v_s_558_);
return v___f_560_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_561_, lean_object* v_pat_562_, lean_object* v_s_563_, lean_object* v_inst_564_){
_start:
{
lean_object* v___f_565_; 
v___f_565_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_565_, 0, v_inst_564_);
lean_closure_set(v___f_565_, 1, v_s_563_);
return v___f_565_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_566_, lean_object* v_pat_567_, lean_object* v_s_568_, lean_object* v_inst_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_566_, v_pat_567_, v_s_568_, v_inst_569_);
lean_dec(v_pat_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(lean_object* v_pat_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_572_, 0, lean_box(0));
lean_closure_set(v___x_572_, 1, v_pat_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(lean_object* v_00_u03c1_573_, lean_object* v_pat_574_, lean_object* v_inst_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_576_, 0, lean_box(0));
lean_closure_set(v___x_576_, 1, v_pat_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_577_, lean_object* v_pat_578_, lean_object* v_inst_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(v_00_u03c1_577_, v_pat_578_, v_inst_579_);
lean_dec_ref(v_inst_579_);
return v_res_580_;
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
