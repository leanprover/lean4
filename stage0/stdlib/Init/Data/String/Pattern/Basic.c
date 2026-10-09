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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg(){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = ((lean_object*)(l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg___closed__0));
return v___x_63_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_64_;
v_res_64_ = l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg();
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg___boxed(lean_object* v___dummy_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg();
return v_res_66_;
}
}
static lean_object* _init_l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg();
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default(lean_object* v_s_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_obj_once(&l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0, &l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_once, _init_l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___boxed(lean_object* v_s_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_String_Slice_Pattern_instInhabitedSearchStep_default(v_s_70_);
lean_dec_ref(v_s_70_);
return v_res_71_;
}
}
lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___redArg(){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0, &l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_once, _init_l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0);
return v___x_73_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_instInhabitedSearchStep___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_74_;
v_res_74_ = l_String_Slice_Pattern_instInhabitedSearchStep___redArg();
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_String_Slice_Pattern_instInhabitedSearchStep___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep(lean_object* v_a_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0, &l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_once, _init_l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___boxed(lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_String_Slice_Pattern_instInhabitedSearchStep(v_a_79_);
lean_dec_ref(v_a_79_);
return v_res_80_;
}
}
uint8_t l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
lean_object* v_a_84_; lean_object* v_a_85_; lean_object* v_b_86_; lean_object* v_b_87_; 
if (lean_obj_tag(v_x_81_) == 0)
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v_startPos_90_; lean_object* v_endPos_91_; lean_object* v_startPos_92_; lean_object* v_endPos_93_; 
v_startPos_90_ = lean_ctor_get(v_x_81_, 0);
v_endPos_91_ = lean_ctor_get(v_x_81_, 1);
v_startPos_92_ = lean_ctor_get(v_x_82_, 0);
v_endPos_93_ = lean_ctor_get(v_x_82_, 1);
v_a_84_ = v_startPos_90_;
v_a_85_ = v_endPos_91_;
v_b_86_ = v_startPos_92_;
v_b_87_ = v_endPos_93_;
goto v___jp_83_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
else
{
if (lean_obj_tag(v_x_82_) == 1)
{
lean_object* v_startPos_95_; lean_object* v_endPos_96_; lean_object* v_startPos_97_; lean_object* v_endPos_98_; 
v_startPos_95_ = lean_ctor_get(v_x_81_, 0);
v_endPos_96_ = lean_ctor_get(v_x_81_, 1);
v_startPos_97_ = lean_ctor_get(v_x_82_, 0);
v_endPos_98_ = lean_ctor_get(v_x_82_, 1);
v_a_84_ = v_startPos_95_;
v_a_85_ = v_endPos_96_;
v_b_86_ = v_startPos_97_;
v_b_87_ = v_endPos_98_;
goto v___jp_83_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = 0;
return v___x_99_;
}
}
v___jp_83_:
{
uint8_t v_decide_88_; 
v_decide_88_ = lean_nat_dec_eq(v_a_84_, v_b_86_);
if (v_decide_88_ == 0)
{
return v_decide_88_;
}
else
{
uint8_t v_decide_89_; 
v_decide_89_ = lean_nat_dec_eq(v_a_85_, v_b_87_);
return v_decide_89_;
}
}
}
}
LEAN_EXPORT void l_String_Slice_Pattern_instBEqSearchStep_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_81_ = stack[0].m_obj;
lean_object* v_x_82_ = stack[1].m_obj;
uint8_t v_res_100_;
v_res_100_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_81_, v_x_82_);
stack->m_num = v_res_100_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep_beq___redArg___boxed(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_101_, v_x_102_);
lean_dec_ref(v_x_102_);
lean_dec_ref(v_x_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
uint8_t l_String_Slice_Pattern_instBEqSearchStep_beq(lean_object* v_s_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_106_, v_x_107_);
return v___x_108_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_instBEqSearchStep_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_105_ = stack[0].m_obj;
lean_object* v_x_106_ = stack[1].m_obj;
lean_object* v_x_107_ = stack[2].m_obj;
uint8_t v_res_109_;
v_res_109_ = l_String_Slice_Pattern_instBEqSearchStep_beq(v_s_105_, v_x_106_, v_x_107_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep_beq___boxed(lean_object* v_s_110_, lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_String_Slice_Pattern_instBEqSearchStep_beq(v_s_110_, v_x_111_, v_x_112_);
lean_dec_ref(v_x_112_);
lean_dec_ref(v_x_111_);
lean_dec_ref(v_s_110_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep(lean_object* v_s_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_instBEqSearchStep_beq___boxed), 3, 1);
lean_closure_set(v___x_116_, 0, v_s_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___redArg(lean_object* v_st_117_){
_start:
{
lean_object* v_startPos_118_; 
v_startPos_118_ = lean_ctor_get(v_st_117_, 0);
lean_inc(v_startPos_118_);
return v_startPos_118_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___redArg___boxed(lean_object* v_st_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_String_Slice_Pattern_SearchStep_startPos___redArg(v_st_119_);
lean_dec_ref(v_st_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos(lean_object* v_s_121_, lean_object* v_st_122_){
_start:
{
lean_object* v_startPos_123_; 
v_startPos_123_ = lean_ctor_get(v_st_122_, 0);
lean_inc(v_startPos_123_);
return v_startPos_123_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___boxed(lean_object* v_s_124_, lean_object* v_st_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_String_Slice_Pattern_SearchStep_startPos(v_s_124_, v_st_125_);
lean_dec_ref(v_st_125_);
lean_dec_ref(v_s_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___redArg(lean_object* v_st_127_){
_start:
{
lean_object* v_endPos_128_; 
v_endPos_128_ = lean_ctor_get(v_st_127_, 1);
lean_inc(v_endPos_128_);
return v_endPos_128_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___redArg___boxed(lean_object* v_st_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_String_Slice_Pattern_SearchStep_endPos___redArg(v_st_129_);
lean_dec_ref(v_st_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos(lean_object* v_s_131_, lean_object* v_st_132_){
_start:
{
lean_object* v_endPos_133_; 
v_endPos_133_ = lean_ctor_get(v_st_132_, 1);
lean_inc(v_endPos_133_);
return v_endPos_133_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___boxed(lean_object* v_s_134_, lean_object* v_st_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_String_Slice_Pattern_SearchStep_endPos(v_s_134_, v_st_135_);
lean_dec_ref(v_st_135_);
lean_dec_ref(v_s_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(lean_object* v_p_137_, lean_object* v_st_138_){
_start:
{
if (lean_obj_tag(v_st_138_) == 0)
{
lean_object* v_startPos_139_; lean_object* v_endPos_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_149_; 
v_startPos_139_ = lean_ctor_get(v_st_138_, 0);
v_endPos_140_ = lean_ctor_get(v_st_138_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_st_138_);
if (v_isSharedCheck_149_ == 0)
{
v___x_142_ = v_st_138_;
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_endPos_140_);
lean_inc(v_startPos_139_);
lean_dec(v_st_138_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_144_ = lean_nat_add(v_p_137_, v_startPos_139_);
lean_dec(v_startPos_139_);
v___x_145_ = lean_nat_add(v_p_137_, v_endPos_140_);
lean_dec(v_endPos_140_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_145_);
lean_ctor_set(v___x_142_, 0, v___x_144_);
v___x_147_ = v___x_142_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v_startPos_150_; lean_object* v_endPos_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_160_; 
v_startPos_150_ = lean_ctor_get(v_st_138_, 0);
v_endPos_151_ = lean_ctor_get(v_st_138_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_st_138_);
if (v_isSharedCheck_160_ == 0)
{
v___x_153_ = v_st_138_;
v_isShared_154_ = v_isSharedCheck_160_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_endPos_151_);
lean_inc(v_startPos_150_);
lean_dec(v_st_138_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_160_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = lean_nat_add(v_p_137_, v_startPos_150_);
lean_dec(v_startPos_150_);
v___x_156_ = lean_nat_add(v_p_137_, v_endPos_151_);
lean_dec(v_endPos_151_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___x_156_);
lean_ctor_set(v___x_153_, 0, v___x_155_);
v___x_158_ = v___x_153_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg___boxed(lean_object* v_p_161_, lean_object* v_st_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_161_, v_st_162_);
lean_dec(v_p_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom(lean_object* v_s_164_, lean_object* v_p_165_, lean_object* v_st_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_165_, v_st_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___boxed(lean_object* v_s_168_, lean_object* v_p_169_, lean_object* v_st_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom(v_s_168_, v_p_169_, v_st_170_);
lean_dec(v_p_169_);
lean_dec_ref(v_s_168_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___redArg(lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
lean_object* v_startPos_173_; lean_object* v_endPos_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
v_startPos_173_ = lean_ctor_get(v_x_172_, 0);
v_endPos_174_ = lean_ctor_get(v_x_172_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_172_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v_x_172_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_endPos_174_);
lean_inc(v_startPos_173_);
lean_dec(v_x_172_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
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
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_startPos_173_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_endPos_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v_startPos_182_; lean_object* v_endPos_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_startPos_182_ = lean_ctor_get(v_x_172_, 0);
v_endPos_183_ = lean_ctor_get(v_x_172_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_x_172_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v_x_172_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_endPos_183_);
lean_inc(v_startPos_182_);
lean_dec(v_x_172_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_startPos_182_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_endPos_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast(lean_object* v_s_191_, lean_object* v_t_192_, lean_object* v_hst_193_, lean_object* v_x_194_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
lean_object* v_startPos_195_; lean_object* v_endPos_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_startPos_195_ = lean_ctor_get(v_x_194_, 0);
v_endPos_196_ = lean_ctor_get(v_x_194_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_194_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v_x_194_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_endPos_196_);
lean_inc(v_startPos_195_);
lean_dec(v_x_194_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_startPos_195_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_endPos_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_object* v_startPos_204_; lean_object* v_endPos_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_startPos_204_ = lean_ctor_get(v_x_194_, 0);
v_endPos_205_ = lean_ctor_get(v_x_194_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_x_194_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v_x_194_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_endPos_205_);
lean_inc(v_startPos_204_);
lean_dec(v_x_194_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_startPos_204_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_endPos_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___boxed(lean_object* v_s_213_, lean_object* v_t_214_, lean_object* v_hst_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_String_Slice_Pattern_SearchStep_cast(v_s_213_, v_t_214_, v_hst_215_, v_x_216_);
lean_dec_ref(v_t_214_);
lean_dec_ref(v_s_213_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(lean_object* v_inst_218_, lean_object* v_s_219_){
_start:
{
lean_object* v_skipPrefix_x3f_220_; lean_object* v___x_221_; 
v_skipPrefix_x3f_220_ = lean_ctor_get(v_inst_218_, 0);
lean_inc_ref(v_skipPrefix_x3f_220_);
lean_dec_ref(v_inst_218_);
v___x_221_ = lean_apply_1(v_skipPrefix_x3f_220_, v_s_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(lean_object* v_00_u03c1_222_, lean_object* v_pat_223_, lean_object* v_inst_224_, lean_object* v_s_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(v_inst_224_, v_s_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_227_, lean_object* v_pat_228_, lean_object* v_inst_229_, lean_object* v_s_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(v_00_u03c1_227_, v_pat_228_, v_inst_229_, v_s_230_);
lean_dec(v_pat_228_);
return v_res_231_;
}
}
lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg(){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(0u);
return v___x_233_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_234_;
v_res_234_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg();
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg___boxed(lean_object* v___dummy_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg();
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(lean_object* v_00_u03c1_237_, lean_object* v_pat_238_, lean_object* v_s_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_unsigned_to_nat(0u);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(lean_object* v_00_u03c1_241_, lean_object* v_pat_242_, lean_object* v_s_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(v_00_u03c1_241_, v_pat_242_, v_s_243_);
lean_dec_ref(v_s_243_);
lean_dec(v_pat_242_);
return v_res_244_;
}
}
lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg(){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_unsigned_to_nat(0u);
return v___x_246_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_247_;
v_res_247_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg();
stack->m_obj
 = v_res_247_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg___boxed(lean_object* v___dummy_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg();
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_unsigned_to_nat(0u);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(v_a_254_, v_a_255_, v_a_256_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
return v_res_257_;
}
}
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg(){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_unsigned_to_nat(0u);
return v___x_259_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_260_;
v_res_260_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg();
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg___boxed(lean_object* v___dummy_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg();
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(lean_object* v_00_u03c1_263_, lean_object* v_pat_264_, lean_object* v_s_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_unsigned_to_nat(0u);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object* v_00_u03c1_267_, lean_object* v_pat_268_, lean_object* v_s_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(v_00_u03c1_267_, v_pat_268_, v_s_269_);
lean_dec_ref(v_s_269_);
lean_dec(v_pat_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(lean_object* v_s_271_, lean_object* v_inst_272_, lean_object* v_it_273_){
_start:
{
lean_object* v_str_274_; lean_object* v_startInclusive_275_; lean_object* v_endExclusive_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_297_; 
v_str_274_ = lean_ctor_get(v_s_271_, 0);
v_startInclusive_275_ = lean_ctor_get(v_s_271_, 1);
v_endExclusive_276_ = lean_ctor_get(v_s_271_, 2);
v_isSharedCheck_297_ = !lean_is_exclusive(v_s_271_);
if (v_isSharedCheck_297_ == 0)
{
v___x_278_ = v_s_271_;
v_isShared_279_ = v_isSharedCheck_297_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_endExclusive_276_);
lean_inc(v_startInclusive_275_);
lean_inc(v_str_274_);
lean_dec(v_s_271_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_297_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; uint8_t v_decide_281_; 
v___x_280_ = lean_nat_sub(v_endExclusive_276_, v_startInclusive_275_);
v_decide_281_ = lean_nat_dec_eq(v_it_273_, v___x_280_);
lean_dec(v___x_280_);
if (v_decide_281_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v_skipPrefixOfNonempty_x3f_282_ = lean_ctor_get(v_inst_272_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_282_);
lean_dec_ref(v_inst_272_);
v___x_283_ = lean_nat_add(v_startInclusive_275_, v_it_273_);
lean_inc(v___x_283_);
lean_inc_ref(v_str_274_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v___x_283_);
v___x_285_ = v___x_278_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_str_274_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_endExclusive_276_);
v___x_285_ = v_reuseFailAlloc_295_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; 
v___x_286_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_282_, v___x_285_, lean_box(0));
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_287_ = lean_string_utf8_next_fast(v_str_274_, v___x_283_);
lean_dec(v___x_283_);
lean_dec_ref(v_str_274_);
v___x_288_ = lean_nat_sub(v___x_287_, v_startInclusive_275_);
lean_dec(v_startInclusive_275_);
lean_inc(v___x_288_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_it_273_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec(v___x_283_);
lean_dec(v_startInclusive_275_);
lean_dec_ref(v_str_274_);
v_val_291_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v___x_286_, 1);
v___x_292_ = lean_nat_add(v_it_273_, v_val_291_);
lean_dec(v_val_291_);
lean_inc(v___x_292_);
v___x_293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_293_, 0, v_it_273_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
return v___x_294_;
}
}
}
else
{
lean_object* v___x_296_; 
lean_del_object(v___x_278_);
lean_dec(v_endExclusive_276_);
lean_dec(v_startInclusive_275_);
lean_dec_ref(v_str_274_);
lean_dec(v_it_273_);
lean_dec_ref(v_inst_272_);
v___x_296_ = lean_box(2);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(lean_object* v_s_298_, lean_object* v_inst_299_){
_start:
{
lean_object* v___f_300_; 
v___f_300_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_300_, 0, v_s_298_);
lean_closure_set(v___f_300_, 1, v_inst_299_);
return v___f_300_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(lean_object* v_00_u03c1_301_, lean_object* v_pat_302_, lean_object* v_s_303_, lean_object* v_inst_304_){
_start:
{
lean_object* v___f_305_; 
v___f_305_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_305_, 0, v_s_303_);
lean_closure_set(v___f_305_, 1, v_inst_304_);
return v___f_305_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(lean_object* v_00_u03c1_306_, lean_object* v_pat_307_, lean_object* v_s_308_, lean_object* v_inst_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(v_00_u03c1_306_, v_pat_307_, v_s_308_, v_inst_309_);
lean_dec(v_pat_307_);
return v_res_310_;
}
}
lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_box(0);
return v___x_312_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_313_;
v_res_313_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg();
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg();
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(lean_object* v_00_u03c1_316_, lean_object* v_pat_317_, lean_object* v_s_318_, lean_object* v_inst_319_, lean_object* v_inst_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_box(0);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_322_, lean_object* v_pat_323_, lean_object* v_s_324_, lean_object* v_inst_325_, lean_object* v_inst_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(v_00_u03c1_322_, v_pat_323_, v_s_324_, v_inst_325_, v_inst_326_);
lean_dec_ref(v_inst_325_);
lean_dec_ref(v_s_324_);
lean_dec(v_pat_323_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v___y_328_, lean_object* v_acc_329_, lean_object* v_recur_330_, lean_object* v_s_331_){
_start:
{
switch(lean_obj_tag(v_s_331_))
{
case 0:
{
lean_object* v_it_332_; lean_object* v_out_333_; lean_object* v_val_334_; 
v_it_332_ = lean_ctor_get(v_s_331_, 0);
lean_inc(v_it_332_);
v_out_333_ = lean_ctor_get(v_s_331_, 1);
lean_inc(v_out_333_);
lean_dec_ref_known(v_s_331_, 2);
v_val_334_ = lean_apply_3(v___y_328_, v_out_333_, lean_box(0), v_acc_329_);
if (lean_obj_tag(v_val_334_) == 0)
{
lean_object* v_a_335_; 
lean_dec(v_it_332_);
lean_dec(v_recur_330_);
v_a_335_ = lean_ctor_get(v_val_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v_val_334_, 1);
return v_a_335_;
}
else
{
lean_object* v_a_336_; lean_object* v___x_337_; 
v_a_336_ = lean_ctor_get(v_val_334_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v_val_334_, 1);
v___x_337_ = lean_apply_4(v_recur_330_, v_it_332_, v_a_336_, lean_box(0), lean_box(0));
return v___x_337_;
}
}
case 1:
{
lean_object* v_it_338_; lean_object* v___x_339_; 
lean_dec_ref(v___y_328_);
v_it_338_ = lean_ctor_get(v_s_331_, 0);
lean_inc(v_it_338_);
lean_dec_ref_known(v_s_331_, 1);
v___x_339_ = lean_apply_4(v_recur_330_, v_it_338_, v_acc_329_, lean_box(0), lean_box(0));
return v___x_339_;
}
default: 
{
lean_dec(v_recur_330_);
lean_dec_ref(v___y_328_);
return v_acc_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v_s_340_, lean_object* v___y_341_, lean_object* v_inst_342_, lean_object* v_lift_343_, lean_object* v_it_344_, lean_object* v_acc_345_, lean_object* v_hP_346_, lean_object* v_recur_347_){
_start:
{
lean_object* v_str_348_; lean_object* v_startInclusive_349_; lean_object* v_endExclusive_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_375_; 
v_str_348_ = lean_ctor_get(v_s_340_, 0);
v_startInclusive_349_ = lean_ctor_get(v_s_340_, 1);
v_endExclusive_350_ = lean_ctor_get(v_s_340_, 2);
v_isSharedCheck_375_ = !lean_is_exclusive(v_s_340_);
if (v_isSharedCheck_375_ == 0)
{
v___x_352_ = v_s_340_;
v_isShared_353_ = v_isSharedCheck_375_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_endExclusive_350_);
lean_inc(v_startInclusive_349_);
lean_inc(v_str_348_);
lean_dec(v_s_340_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_375_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___f_354_; lean_object* v___x_355_; uint8_t v_decide_356_; 
v___f_354_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_354_, 0, v___y_341_);
lean_closure_set(v___f_354_, 1, v_acc_345_);
lean_closure_set(v___f_354_, 2, v_recur_347_);
v___x_355_ = lean_nat_sub(v_endExclusive_350_, v_startInclusive_349_);
v_decide_356_ = lean_nat_dec_eq(v_it_344_, v___x_355_);
lean_dec(v___x_355_);
if (v_decide_356_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v_skipPrefixOfNonempty_x3f_357_ = lean_ctor_get(v_inst_342_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_357_);
lean_dec_ref(v_inst_342_);
v___x_358_ = lean_nat_add(v_startInclusive_349_, v_it_344_);
lean_inc(v___x_358_);
lean_inc_ref(v_str_348_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v___x_358_);
v___x_360_ = v___x_352_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_str_348_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_endExclusive_350_);
v___x_360_ = v_reuseFailAlloc_372_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; 
v___x_361_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_357_, v___x_360_, lean_box(0));
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_362_ = lean_string_utf8_next_fast(v_str_348_, v___x_358_);
lean_dec(v___x_358_);
lean_dec_ref(v_str_348_);
v___x_363_ = lean_nat_sub(v___x_362_, v_startInclusive_349_);
lean_dec(v_startInclusive_349_);
lean_inc(v___x_363_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_it_344_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = lean_apply_4(v_lift_343_, lean_box(0), lean_box(0), v___f_354_, v___x_365_);
return v___x_366_;
}
else
{
lean_object* v_val_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec(v___x_358_);
lean_dec(v_startInclusive_349_);
lean_dec_ref(v_str_348_);
v_val_367_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v___x_361_, 1);
v___x_368_ = lean_nat_add(v_it_344_, v_val_367_);
lean_dec(v_val_367_);
lean_inc(v___x_368_);
v___x_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_369_, 0, v_it_344_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_apply_4(v_lift_343_, lean_box(0), lean_box(0), v___f_354_, v___x_370_);
return v___x_371_;
}
}
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_del_object(v___x_352_);
lean_dec(v_endExclusive_350_);
lean_dec(v_startInclusive_349_);
lean_dec_ref(v_str_348_);
lean_dec(v_it_344_);
lean_dec_ref(v_inst_342_);
v___x_373_ = lean_box(2);
v___x_374_ = lean_apply_4(v_lift_343_, lean_box(0), lean_box(0), v___f_354_, v___x_373_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object* v_s_376_, lean_object* v_inst_377_, lean_object* v_lift_378_, lean_object* v_00_u03b3_379_, lean_object* v_Pl_380_, lean_object* v_it_381_, lean_object* v_init_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___f_384_; lean_object* v___x_385_; 
v___f_384_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1), 8, 4);
lean_closure_set(v___f_384_, 0, v_s_376_);
lean_closure_set(v___f_384_, 1, v___y_383_);
lean_closure_set(v___f_384_, 2, v_inst_377_);
lean_closure_set(v___f_384_, 3, v_lift_378_);
v___x_385_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_384_, v_it_381_, v_init_382_, lean_box(0));
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_386_, lean_object* v_inst_387_){
_start:
{
lean_object* v___f_388_; 
v___f_388_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_388_, 0, v_s_386_);
lean_closure_set(v___f_388_, 1, v_inst_387_);
return v___f_388_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_389_, lean_object* v_pat_390_, lean_object* v_s_391_, lean_object* v_inst_392_){
_start:
{
lean_object* v___f_393_; 
v___f_393_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_393_, 0, v_s_391_);
lean_closure_set(v___f_393_, 1, v_inst_392_);
return v___f_393_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_394_, lean_object* v_pat_395_, lean_object* v_s_396_, lean_object* v_inst_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_394_, v_pat_395_, v_s_396_, v_inst_397_);
lean_dec(v_pat_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(lean_object* v_pat_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_400_, 0, lean_box(0));
lean_closure_set(v___x_400_, 1, v_pat_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(lean_object* v_00_u03c1_401_, lean_object* v_pat_402_, lean_object* v_inst_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_404_, 0, lean_box(0));
lean_closure_set(v___x_404_, 1, v_pat_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_405_, lean_object* v_pat_406_, lean_object* v_inst_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(v_00_u03c1_405_, v_pat_406_, v_inst_407_);
lean_dec_ref(v_inst_407_);
return v_res_408_;
}
}
uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(lean_object* v_lhs_409_, lean_object* v_rhs_410_, lean_object* v_lstart_411_, lean_object* v_rstart_412_, lean_object* v_len_413_, lean_object* v_curr_414_){
_start:
{
uint8_t v___y_416_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_nat_add(v_curr_414_, v___x_420_);
v___x_422_ = lean_nat_dec_le(v___x_421_, v_len_413_);
lean_dec(v___x_421_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; 
lean_dec(v_curr_414_);
v___x_423_ = 1;
return v___x_423_;
}
else
{
if (v___x_422_ == 0)
{
v___y_416_ = v___x_422_;
goto v___jp_415_;
}
else
{
lean_object* v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; uint8_t v___x_428_; 
v___x_424_ = lean_nat_add(v_lstart_411_, v_curr_414_);
v___x_425_ = lean_string_get_byte_fast(v_lhs_409_, v___x_424_);
v___x_426_ = lean_nat_add(v_rstart_412_, v_curr_414_);
v___x_427_ = lean_string_get_byte_fast(v_rhs_410_, v___x_426_);
v___x_428_ = lean_uint8_dec_eq(v___x_425_, v___x_427_);
v___y_416_ = v___x_428_;
goto v___jp_415_;
}
}
v___jp_415_:
{
if (v___y_416_ == 0)
{
lean_dec(v_curr_414_);
return v___y_416_;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_add(v_curr_414_, v___x_417_);
lean_dec(v_curr_414_);
v_curr_414_ = v___x_418_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_409_ = stack[0].m_obj;
lean_object* v_rhs_410_ = stack[1].m_obj;
lean_object* v_lstart_411_ = stack[2].m_obj;
lean_object* v_rstart_412_ = stack[3].m_obj;
lean_object* v_len_413_ = stack[4].m_obj;
lean_object* v_curr_414_ = stack[5].m_obj;
uint8_t v_res_429_;
v_res_429_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_409_, v_rhs_410_, v_lstart_411_, v_rstart_412_, v_len_413_, v_curr_414_);
stack->m_num = v_res_429_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg___boxed(lean_object* v_lhs_430_, lean_object* v_rhs_431_, lean_object* v_lstart_432_, lean_object* v_rstart_433_, lean_object* v_len_434_, lean_object* v_curr_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_430_, v_rhs_431_, v_lstart_432_, v_rstart_433_, v_len_434_, v_curr_435_);
lean_dec(v_len_434_);
lean_dec(v_rstart_433_);
lean_dec(v_lstart_432_);
lean_dec_ref(v_rhs_431_);
lean_dec_ref(v_lhs_430_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object* v_lhs_438_, lean_object* v_rhs_439_, lean_object* v_lstart_440_, lean_object* v_rstart_441_, lean_object* v_len_442_, lean_object* v_h1_443_, lean_object* v_h2_444_, lean_object* v_curr_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_438_, v_rhs_439_, v_lstart_440_, v_rstart_441_, v_len_442_, v_curr_445_);
return v___x_446_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_438_ = stack[0].m_obj;
lean_object* v_rhs_439_ = stack[1].m_obj;
lean_object* v_lstart_440_ = stack[2].m_obj;
lean_object* v_rstart_441_ = stack[3].m_obj;
lean_object* v_len_442_ = stack[4].m_obj;
lean_object* v_curr_445_ = stack[7].m_obj;
uint8_t v_res_447_;
v_res_447_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(v_lhs_438_, v_rhs_439_, v_lstart_440_, v_rstart_441_, v_len_442_, lean_box(0), lean_box(0), v_curr_445_);
stack->m_num = v_res_447_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object* v_lhs_448_, lean_object* v_rhs_449_, lean_object* v_lstart_450_, lean_object* v_rstart_451_, lean_object* v_len_452_, lean_object* v_h1_453_, lean_object* v_h2_454_, lean_object* v_curr_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(v_lhs_448_, v_rhs_449_, v_lstart_450_, v_rstart_451_, v_len_452_, v_h1_453_, v_h2_454_, v_curr_455_);
lean_dec(v_len_452_);
lean_dec(v_rstart_451_);
lean_dec(v_lstart_450_);
lean_dec_ref(v_rhs_449_);
lean_dec_ref(v_lhs_448_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_Internal_memcmpStr_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_458_ = stack[0].m_obj;
lean_object* v_rhs_459_ = stack[1].m_obj;
lean_object* v_lstart_460_ = stack[2].m_obj;
lean_object* v_rstart_461_ = stack[3].m_obj;
lean_object* v_len_462_ = stack[4].m_obj;
uint8_t v_res_465_;
v_res_465_ = lean_string_memcmp(v_lhs_458_, v_rhs_459_, v_lstart_460_, v_rstart_461_, v_len_462_);
stack->m_num = v_res_465_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object* v_lhs_466_, lean_object* v_rhs_467_, lean_object* v_lstart_468_, lean_object* v_rstart_469_, lean_object* v_len_470_, lean_object* v_h1_471_, lean_object* v_h2_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = lean_string_memcmp(v_lhs_466_, v_rhs_467_, v_lstart_468_, v_rstart_469_, v_len_470_);
lean_dec(v_len_470_);
lean_dec(v_rstart_469_);
lean_dec(v_lstart_468_);
lean_dec_ref(v_rhs_467_);
lean_dec_ref(v_lhs_466_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object* v_lhs_475_, lean_object* v_rhs_476_, lean_object* v_lstart_477_, lean_object* v_rstart_478_, lean_object* v_len_479_){
_start:
{
lean_object* v_str_480_; lean_object* v_startInclusive_481_; lean_object* v_str_482_; lean_object* v_startInclusive_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_str_480_ = lean_ctor_get(v_lhs_475_, 0);
v_startInclusive_481_ = lean_ctor_get(v_lhs_475_, 1);
v_str_482_ = lean_ctor_get(v_rhs_476_, 0);
v_startInclusive_483_ = lean_ctor_get(v_rhs_476_, 1);
v___x_484_ = lean_nat_add(v_startInclusive_481_, v_lstart_477_);
v___x_485_ = lean_nat_add(v_startInclusive_483_, v_rstart_478_);
v___x_486_ = lean_string_memcmp(v_str_480_, v_str_482_, v___x_484_, v___x_485_, v_len_479_);
lean_dec(v___x_485_);
lean_dec(v___x_484_);
return v___x_486_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_Internal_memcmpSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_475_ = stack[0].m_obj;
lean_object* v_rhs_476_ = stack[1].m_obj;
lean_object* v_lstart_477_ = stack[2].m_obj;
lean_object* v_rstart_478_ = stack[3].m_obj;
lean_object* v_len_479_ = stack[4].m_obj;
uint8_t v_res_487_;
v_res_487_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(v_lhs_475_, v_rhs_476_, v_lstart_477_, v_rstart_478_, v_len_479_);
stack->m_num = v_res_487_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object* v_lhs_488_, lean_object* v_rhs_489_, lean_object* v_lstart_490_, lean_object* v_rstart_491_, lean_object* v_len_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(v_lhs_488_, v_rhs_489_, v_lstart_490_, v_rstart_491_, v_len_492_);
lean_dec(v_len_492_);
lean_dec(v_rstart_491_);
lean_dec(v_lstart_490_);
lean_dec_ref(v_rhs_489_);
lean_dec_ref(v_lhs_488_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object* v_lhs_495_, lean_object* v_rhs_496_, lean_object* v_lstart_497_, lean_object* v_rstart_498_, lean_object* v_len_499_, lean_object* v_h1_500_, lean_object* v_h2_501_){
_start:
{
lean_object* v_str_502_; lean_object* v_startInclusive_503_; lean_object* v_str_504_; lean_object* v_startInclusive_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_str_502_ = lean_ctor_get(v_lhs_495_, 0);
v_startInclusive_503_ = lean_ctor_get(v_lhs_495_, 1);
v_str_504_ = lean_ctor_get(v_rhs_496_, 0);
v_startInclusive_505_ = lean_ctor_get(v_rhs_496_, 1);
v___x_506_ = lean_nat_add(v_startInclusive_503_, v_lstart_497_);
v___x_507_ = lean_nat_add(v_startInclusive_505_, v_rstart_498_);
v___x_508_ = lean_string_memcmp(v_str_502_, v_str_504_, v___x_506_, v___x_507_, v_len_499_);
lean_dec(v___x_507_);
lean_dec(v___x_506_);
return v___x_508_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_Internal_memcmpSlice_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_495_ = stack[0].m_obj;
lean_object* v_rhs_496_ = stack[1].m_obj;
lean_object* v_lstart_497_ = stack[2].m_obj;
lean_object* v_rstart_498_ = stack[3].m_obj;
lean_object* v_len_499_ = stack[4].m_obj;
uint8_t v_res_509_;
v_res_509_ = l_String_Slice_Pattern_Internal_memcmpSlice(v_lhs_495_, v_rhs_496_, v_lstart_497_, v_rstart_498_, v_len_499_, lean_box(0), lean_box(0));
stack->m_num = v_res_509_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object* v_lhs_510_, lean_object* v_rhs_511_, lean_object* v_lstart_512_, lean_object* v_rstart_513_, lean_object* v_len_514_, lean_object* v_h1_515_, lean_object* v_h2_516_){
_start:
{
uint8_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = l_String_Slice_Pattern_Internal_memcmpSlice(v_lhs_510_, v_rhs_511_, v_lstart_512_, v_rstart_513_, v_len_514_, v_h1_515_, v_h2_516_);
lean_dec(v_len_514_);
lean_dec(v_rstart_513_);
lean_dec(v_lstart_512_);
lean_dec_ref(v_rhs_511_);
lean_dec_ref(v_lhs_510_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg(){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_unsigned_to_nat(0u);
return v___x_520_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_521_;
v_res_521_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg();
stack->m_obj
 = v_res_521_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg___boxed(lean_object* v___dummy_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg();
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object* v_00_u03c1_524_, lean_object* v_pat_525_, lean_object* v_s_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_unsigned_to_nat(0u);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object* v_00_u03c1_528_, lean_object* v_pat_529_, lean_object* v_s_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(v_00_u03c1_528_, v_pat_529_, v_s_530_);
lean_dec_ref(v_s_530_);
lean_dec(v_pat_529_);
return v_res_531_;
}
}
lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg(){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_unsigned_to_nat(0u);
return v___x_533_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_534_;
v_res_534_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg();
stack->m_obj
 = v_res_534_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg___boxed(lean_object* v___dummy_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg();
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_unsigned_to_nat(0u);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(v_a_541_, v_a_542_, v_a_543_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(lean_object* v_s_545_){
_start:
{
lean_object* v_startInclusive_546_; lean_object* v_endExclusive_547_; lean_object* v___x_548_; 
v_startInclusive_546_ = lean_ctor_get(v_s_545_, 1);
v_endExclusive_547_ = lean_ctor_get(v_s_545_, 2);
v___x_548_ = lean_nat_sub(v_endExclusive_547_, v_startInclusive_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(lean_object* v_s_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_549_);
lean_dec_ref(v_s_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(lean_object* v_00_u03c1_551_, lean_object* v_pat_552_, lean_object* v_s_553_){
_start:
{
lean_object* v_startInclusive_554_; lean_object* v_endExclusive_555_; lean_object* v___x_556_; 
v_startInclusive_554_ = lean_ctor_get(v_s_553_, 1);
v_endExclusive_555_ = lean_ctor_get(v_s_553_, 2);
v___x_556_ = lean_nat_sub(v_endExclusive_555_, v_startInclusive_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object* v_00_u03c1_557_, lean_object* v_pat_558_, lean_object* v_s_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(v_00_u03c1_557_, v_pat_558_, v_s_559_);
lean_dec_ref(v_s_559_);
lean_dec(v_pat_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(lean_object* v_inst_561_, lean_object* v_s_562_, lean_object* v_it_563_){
_start:
{
lean_object* v___x_564_; uint8_t v_decide_565_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v_decide_565_ = lean_nat_dec_eq(v_it_563_, v___x_564_);
if (v_decide_565_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_585_; 
v_skipSuffixOfNonempty_x3f_566_ = lean_ctor_get(v_inst_561_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_inst_561_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; lean_object* v_unused_587_; 
v_unused_586_ = lean_ctor_get(v_inst_561_, 2);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_inst_561_, 0);
lean_dec(v_unused_587_);
v___x_568_ = v_inst_561_;
v_isShared_569_ = v_isSharedCheck_585_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_566_);
lean_dec(v_inst_561_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_585_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_str_570_; lean_object* v_startInclusive_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v_str_570_ = lean_ctor_get(v_s_562_, 0);
v_startInclusive_571_ = lean_ctor_get(v_s_562_, 1);
v___x_572_ = lean_nat_add(v_startInclusive_571_, v_it_563_);
lean_inc(v_startInclusive_571_);
lean_inc_ref(v_str_570_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 2, v___x_572_);
lean_ctor_set(v___x_568_, 1, v_startInclusive_571_);
lean_ctor_set(v___x_568_, 0, v_str_570_);
v___x_574_ = v___x_568_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_str_570_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_startInclusive_571_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v___x_572_);
v___x_574_ = v_reuseFailAlloc_584_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; 
v___x_575_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_566_, v___x_574_, lean_box(0));
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_sub(v_it_563_, v___x_576_);
v___x_578_ = l_String_Slice_posLE(v_s_562_, v___x_577_);
lean_inc(v___x_578_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_it_563_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
else
{
lean_object* v_val_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_val_581_ = lean_ctor_get(v___x_575_, 0);
lean_inc_n(v_val_581_, 2);
lean_dec_ref_known(v___x_575_, 1);
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v_val_581_);
lean_ctor_set(v___x_582_, 1, v_it_563_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v_val_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
return v___x_583_;
}
}
}
}
else
{
lean_object* v___x_588_; 
lean_dec(v_it_563_);
lean_dec_ref(v_inst_561_);
v___x_588_ = lean_box(2);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(lean_object* v_inst_589_, lean_object* v_s_590_, lean_object* v_it_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_589_, v_s_590_, v_it_591_);
lean_dec_ref(v_s_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(lean_object* v_s_593_, lean_object* v_inst_594_){
_start:
{
lean_object* v___f_595_; 
v___f_595_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_595_, 0, v_inst_594_);
lean_closure_set(v___f_595_, 1, v_s_593_);
return v___f_595_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(lean_object* v_00_u03c1_596_, lean_object* v_pat_597_, lean_object* v_s_598_, lean_object* v_inst_599_){
_start:
{
lean_object* v___f_600_; 
v___f_600_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_600_, 0, v_inst_599_);
lean_closure_set(v___f_600_, 1, v_s_598_);
return v___f_600_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(lean_object* v_00_u03c1_601_, lean_object* v_pat_602_, lean_object* v_s_603_, lean_object* v_inst_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_601_, v_pat_602_, v_s_603_, v_inst_604_);
lean_dec(v_pat_602_);
return v_res_605_;
}
}
lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = lean_box(0);
return v___x_607_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_608_;
v_res_608_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg();
stack->m_obj
 = v_res_608_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg();
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(lean_object* v_00_u03c1_611_, lean_object* v_pat_612_, lean_object* v_s_613_, lean_object* v_inst_614_, lean_object* v_inst_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_box(0);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_617_, lean_object* v_pat_618_, lean_object* v_s_619_, lean_object* v_inst_620_, lean_object* v_inst_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(v_00_u03c1_617_, v_pat_618_, v_s_619_, v_inst_620_, v_inst_621_);
lean_dec_ref(v_inst_620_);
lean_dec_ref(v_s_619_);
lean_dec(v_pat_618_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v___y_623_, lean_object* v_inst_624_, lean_object* v_s_625_, lean_object* v_lift_626_, lean_object* v_it_627_, lean_object* v_acc_628_, lean_object* v_hP_629_, lean_object* v_recur_630_){
_start:
{
lean_object* v___f_631_; lean_object* v___x_632_; uint8_t v_decide_633_; 
v___f_631_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_631_, 0, v___y_623_);
lean_closure_set(v___f_631_, 1, v_acc_628_);
lean_closure_set(v___f_631_, 2, v_recur_630_);
v___x_632_ = lean_unsigned_to_nat(0u);
v_decide_633_ = lean_nat_dec_eq(v_it_627_, v___x_632_);
if (v_decide_633_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_655_; 
v_skipSuffixOfNonempty_x3f_634_ = lean_ctor_get(v_inst_624_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_inst_624_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; lean_object* v_unused_657_; 
v_unused_656_ = lean_ctor_get(v_inst_624_, 2);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v_inst_624_, 0);
lean_dec(v_unused_657_);
v___x_636_ = v_inst_624_;
v_isShared_637_ = v_isSharedCheck_655_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_634_);
lean_dec(v_inst_624_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_655_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_str_638_; lean_object* v_startInclusive_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v_str_638_ = lean_ctor_get(v_s_625_, 0);
v_startInclusive_639_ = lean_ctor_get(v_s_625_, 1);
v___x_640_ = lean_nat_add(v_startInclusive_639_, v_it_627_);
lean_inc(v_startInclusive_639_);
lean_inc_ref(v_str_638_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 2, v___x_640_);
lean_ctor_set(v___x_636_, 1, v_startInclusive_639_);
lean_ctor_set(v___x_636_, 0, v_str_638_);
v___x_642_ = v___x_636_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_str_638_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_startInclusive_639_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v___x_640_);
v___x_642_ = v_reuseFailAlloc_654_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; 
v___x_643_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_634_, v___x_642_, lean_box(0));
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_sub(v_it_627_, v___x_644_);
v___x_646_ = l_String_Slice_posLE(v_s_625_, v___x_645_);
lean_inc(v___x_646_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v_it_627_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_apply_4(v_lift_626_, lean_box(0), lean_box(0), v___f_631_, v___x_648_);
return v___x_649_;
}
else
{
lean_object* v_val_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_val_650_ = lean_ctor_get(v___x_643_, 0);
lean_inc_n(v_val_650_, 2);
lean_dec_ref_known(v___x_643_, 1);
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v_val_650_);
lean_ctor_set(v___x_651_, 1, v_it_627_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v_val_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_apply_4(v_lift_626_, lean_box(0), lean_box(0), v___f_631_, v___x_652_);
return v___x_653_;
}
}
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v_it_627_);
lean_dec_ref(v_inst_624_);
v___x_658_ = lean_box(2);
v___x_659_ = lean_apply_4(v_lift_626_, lean_box(0), lean_box(0), v___f_631_, v___x_658_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed(lean_object* v___y_660_, lean_object* v_inst_661_, lean_object* v_s_662_, lean_object* v_lift_663_, lean_object* v_it_664_, lean_object* v_acc_665_, lean_object* v_hP_666_, lean_object* v_recur_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(v___y_660_, v_inst_661_, v_s_662_, v_lift_663_, v_it_664_, v_acc_665_, v_hP_666_, v_recur_667_);
lean_dec_ref(v_s_662_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v_inst_669_, lean_object* v_s_670_, lean_object* v_lift_671_, lean_object* v_00_u03b3_672_, lean_object* v_Pl_673_, lean_object* v_it_674_, lean_object* v_init_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___f_677_; lean_object* v___x_678_; 
v___f_677_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_677_, 0, v___y_676_);
lean_closure_set(v___f_677_, 1, v_inst_669_);
lean_closure_set(v___f_677_, 2, v_s_670_);
lean_closure_set(v___f_677_, 3, v_lift_671_);
v___x_678_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_677_, v_it_674_, v_init_675_, lean_box(0));
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_679_, lean_object* v_inst_680_){
_start:
{
lean_object* v___f_681_; 
v___f_681_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_681_, 0, v_inst_680_);
lean_closure_set(v___f_681_, 1, v_s_679_);
return v___f_681_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_682_, lean_object* v_pat_683_, lean_object* v_s_684_, lean_object* v_inst_685_){
_start:
{
lean_object* v___f_686_; 
v___f_686_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_686_, 0, v_inst_685_);
lean_closure_set(v___f_686_, 1, v_s_684_);
return v___f_686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_687_, lean_object* v_pat_688_, lean_object* v_s_689_, lean_object* v_inst_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_687_, v_pat_688_, v_s_689_, v_inst_690_);
lean_dec(v_pat_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(lean_object* v_pat_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_693_, 0, lean_box(0));
lean_closure_set(v___x_693_, 1, v_pat_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(lean_object* v_00_u03c1_694_, lean_object* v_pat_695_, lean_object* v_inst_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_697_, 0, lean_box(0));
lean_closure_set(v___x_697_, 1, v_pat_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_698_, lean_object* v_pat_699_, lean_object* v_inst_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(v_00_u03c1_698_, v_pat_699_, v_inst_700_);
lean_dec_ref(v_inst_700_);
return v_res_701_;
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
