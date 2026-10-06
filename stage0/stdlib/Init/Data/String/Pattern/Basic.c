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
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(lean_object* v_lhs_429_, lean_object* v_rhs_430_, lean_object* v_lstart_431_, lean_object* v_rstart_432_, lean_object* v_len_433_, lean_object* v_curr_434_){
_start:
{
uint8_t v___y_436_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_curr_434_, v___x_440_);
v___x_442_ = lean_nat_dec_le(v___x_441_, v_len_433_);
lean_dec(v___x_441_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; 
lean_dec(v_curr_434_);
v___x_443_ = 1;
return v___x_443_;
}
else
{
if (v___x_442_ == 0)
{
v___y_436_ = v___x_442_;
goto v___jp_435_;
}
else
{
lean_object* v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_444_ = lean_nat_add(v_lstart_431_, v_curr_434_);
v___x_445_ = lean_string_get_byte_fast(v_lhs_429_, v___x_444_);
v___x_446_ = lean_nat_add(v_rstart_432_, v_curr_434_);
v___x_447_ = lean_string_get_byte_fast(v_rhs_430_, v___x_446_);
v___x_448_ = lean_uint8_dec_eq(v___x_445_, v___x_447_);
v___y_436_ = v___x_448_;
goto v___jp_435_;
}
}
v___jp_435_:
{
if (v___y_436_ == 0)
{
lean_dec(v_curr_434_);
return v___y_436_;
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_add(v_curr_434_, v___x_437_);
lean_dec(v_curr_434_);
v_curr_434_ = v___x_438_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg___boxed(lean_object* v_lhs_449_, lean_object* v_rhs_450_, lean_object* v_lstart_451_, lean_object* v_rstart_452_, lean_object* v_len_453_, lean_object* v_curr_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_449_, v_rhs_450_, v_lstart_451_, v_rstart_452_, v_len_453_, v_curr_454_);
lean_dec(v_len_453_);
lean_dec(v_rstart_452_);
lean_dec(v_lstart_451_);
lean_dec_ref(v_rhs_450_);
lean_dec_ref(v_lhs_449_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object* v_lhs_457_, lean_object* v_rhs_458_, lean_object* v_lstart_459_, lean_object* v_rstart_460_, lean_object* v_len_461_, lean_object* v_h1_462_, lean_object* v_h2_463_, lean_object* v_curr_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_457_, v_rhs_458_, v_lstart_459_, v_rstart_460_, v_len_461_, v_curr_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object* v_lhs_466_, lean_object* v_rhs_467_, lean_object* v_lstart_468_, lean_object* v_rstart_469_, lean_object* v_len_470_, lean_object* v_h1_471_, lean_object* v_h2_472_, lean_object* v_curr_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(v_lhs_466_, v_rhs_467_, v_lstart_468_, v_rstart_469_, v_len_470_, v_h1_471_, v_h2_472_, v_curr_473_);
lean_dec(v_len_470_);
lean_dec(v_rstart_469_);
lean_dec(v_lstart_468_);
lean_dec_ref(v_rhs_467_);
lean_dec_ref(v_lhs_466_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object* v_lhs_483_, lean_object* v_rhs_484_, lean_object* v_lstart_485_, lean_object* v_rstart_486_, lean_object* v_len_487_, lean_object* v_h1_488_, lean_object* v_h2_489_){
_start:
{
uint8_t v_res_490_; lean_object* v_r_491_; 
v_res_490_ = lean_string_memcmp(v_lhs_483_, v_rhs_484_, v_lstart_485_, v_rstart_486_, v_len_487_);
lean_dec(v_len_487_);
lean_dec(v_rstart_486_);
lean_dec(v_lstart_485_);
lean_dec_ref(v_rhs_484_);
lean_dec_ref(v_lhs_483_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object* v_lhs_492_, lean_object* v_rhs_493_, lean_object* v_lstart_494_, lean_object* v_rstart_495_, lean_object* v_len_496_){
_start:
{
lean_object* v_str_497_; lean_object* v_startInclusive_498_; lean_object* v_str_499_; lean_object* v_startInclusive_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_str_497_ = lean_ctor_get(v_lhs_492_, 0);
v_startInclusive_498_ = lean_ctor_get(v_lhs_492_, 1);
v_str_499_ = lean_ctor_get(v_rhs_493_, 0);
v_startInclusive_500_ = lean_ctor_get(v_rhs_493_, 1);
v___x_501_ = lean_nat_add(v_startInclusive_498_, v_lstart_494_);
v___x_502_ = lean_nat_add(v_startInclusive_500_, v_rstart_495_);
v___x_503_ = lean_string_memcmp(v_str_497_, v_str_499_, v___x_501_, v___x_502_, v_len_496_);
lean_dec(v___x_502_);
lean_dec(v___x_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object* v_lhs_504_, lean_object* v_rhs_505_, lean_object* v_lstart_506_, lean_object* v_rstart_507_, lean_object* v_len_508_){
_start:
{
uint8_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(v_lhs_504_, v_rhs_505_, v_lstart_506_, v_rstart_507_, v_len_508_);
lean_dec(v_len_508_);
lean_dec(v_rstart_507_);
lean_dec(v_lstart_506_);
lean_dec_ref(v_rhs_505_);
lean_dec_ref(v_lhs_504_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object* v_lhs_511_, lean_object* v_rhs_512_, lean_object* v_lstart_513_, lean_object* v_rstart_514_, lean_object* v_len_515_, lean_object* v_h1_516_, lean_object* v_h2_517_){
_start:
{
lean_object* v_str_518_; lean_object* v_startInclusive_519_; lean_object* v_str_520_; lean_object* v_startInclusive_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_str_518_ = lean_ctor_get(v_lhs_511_, 0);
v_startInclusive_519_ = lean_ctor_get(v_lhs_511_, 1);
v_str_520_ = lean_ctor_get(v_rhs_512_, 0);
v_startInclusive_521_ = lean_ctor_get(v_rhs_512_, 1);
v___x_522_ = lean_nat_add(v_startInclusive_519_, v_lstart_513_);
v___x_523_ = lean_nat_add(v_startInclusive_521_, v_rstart_514_);
v___x_524_ = lean_string_memcmp(v_str_518_, v_str_520_, v___x_522_, v___x_523_, v_len_515_);
lean_dec(v___x_523_);
lean_dec(v___x_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object* v_lhs_525_, lean_object* v_rhs_526_, lean_object* v_lstart_527_, lean_object* v_rstart_528_, lean_object* v_len_529_, lean_object* v_h1_530_, lean_object* v_h2_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_String_Slice_Pattern_Internal_memcmpSlice(v_lhs_525_, v_rhs_526_, v_lstart_527_, v_rstart_528_, v_len_529_, v_h1_530_, v_h2_531_);
lean_dec(v_len_529_);
lean_dec(v_rstart_528_);
lean_dec(v_lstart_527_);
lean_dec_ref(v_rhs_526_);
lean_dec_ref(v_lhs_525_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg(){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_unsigned_to_nat(0u);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg___boxed(lean_object* v___dummy_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg();
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object* v_00_u03c1_538_, lean_object* v_pat_539_, lean_object* v_s_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_unsigned_to_nat(0u);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object* v_00_u03c1_542_, lean_object* v_pat_543_, lean_object* v_s_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(v_00_u03c1_542_, v_pat_543_, v_s_544_);
lean_dec_ref(v_s_544_);
lean_dec(v_pat_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg(){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lean_unsigned_to_nat(0u);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg___boxed(lean_object* v___dummy_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg();
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lean_unsigned_to_nat(0u);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(v_a_554_, v_a_555_, v_a_556_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(lean_object* v_s_558_){
_start:
{
lean_object* v_startInclusive_559_; lean_object* v_endExclusive_560_; lean_object* v___x_561_; 
v_startInclusive_559_ = lean_ctor_get(v_s_558_, 1);
v_endExclusive_560_ = lean_ctor_get(v_s_558_, 2);
v___x_561_ = lean_nat_sub(v_endExclusive_560_, v_startInclusive_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(lean_object* v_s_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_562_);
lean_dec_ref(v_s_562_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(lean_object* v_00_u03c1_564_, lean_object* v_pat_565_, lean_object* v_s_566_){
_start:
{
lean_object* v_startInclusive_567_; lean_object* v_endExclusive_568_; lean_object* v___x_569_; 
v_startInclusive_567_ = lean_ctor_get(v_s_566_, 1);
v_endExclusive_568_ = lean_ctor_get(v_s_566_, 2);
v___x_569_ = lean_nat_sub(v_endExclusive_568_, v_startInclusive_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object* v_00_u03c1_570_, lean_object* v_pat_571_, lean_object* v_s_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(v_00_u03c1_570_, v_pat_571_, v_s_572_);
lean_dec_ref(v_s_572_);
lean_dec(v_pat_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(lean_object* v_inst_574_, lean_object* v_s_575_, lean_object* v_it_576_){
_start:
{
lean_object* v___x_577_; uint8_t v_decide_578_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v_decide_578_ = lean_nat_dec_eq(v_it_576_, v___x_577_);
if (v_decide_578_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_598_; 
v_skipSuffixOfNonempty_x3f_579_ = lean_ctor_get(v_inst_574_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_inst_574_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; lean_object* v_unused_600_; 
v_unused_599_ = lean_ctor_get(v_inst_574_, 2);
lean_dec(v_unused_599_);
v_unused_600_ = lean_ctor_get(v_inst_574_, 0);
lean_dec(v_unused_600_);
v___x_581_ = v_inst_574_;
v_isShared_582_ = v_isSharedCheck_598_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_579_);
lean_dec(v_inst_574_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_598_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_str_583_; lean_object* v_startInclusive_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v_str_583_ = lean_ctor_get(v_s_575_, 0);
v_startInclusive_584_ = lean_ctor_get(v_s_575_, 1);
v___x_585_ = lean_nat_add(v_startInclusive_584_, v_it_576_);
lean_inc(v_startInclusive_584_);
lean_inc_ref(v_str_583_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 2, v___x_585_);
lean_ctor_set(v___x_581_, 1, v_startInclusive_584_);
lean_ctor_set(v___x_581_, 0, v_str_583_);
v___x_587_ = v___x_581_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_str_583_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_startInclusive_584_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v___x_585_);
v___x_587_ = v_reuseFailAlloc_597_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; 
v___x_588_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_579_, v___x_587_, lean_box(0));
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_sub(v_it_576_, v___x_589_);
v___x_591_ = l_String_Slice_posLE(v_s_575_, v___x_590_);
lean_inc(v___x_591_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v_it_576_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
return v___x_593_;
}
else
{
lean_object* v_val_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_val_594_ = lean_ctor_get(v___x_588_, 0);
lean_inc_n(v_val_594_, 2);
lean_dec_ref_known(v___x_588_, 1);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v_val_594_);
lean_ctor_set(v___x_595_, 1, v_it_576_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_val_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
return v___x_596_;
}
}
}
}
else
{
lean_object* v___x_601_; 
lean_dec(v_it_576_);
lean_dec_ref(v_inst_574_);
v___x_601_ = lean_box(2);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(lean_object* v_inst_602_, lean_object* v_s_603_, lean_object* v_it_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_602_, v_s_603_, v_it_604_);
lean_dec_ref(v_s_603_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(lean_object* v_s_606_, lean_object* v_inst_607_){
_start:
{
lean_object* v___f_608_; 
v___f_608_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_608_, 0, v_inst_607_);
lean_closure_set(v___f_608_, 1, v_s_606_);
return v___f_608_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(lean_object* v_00_u03c1_609_, lean_object* v_pat_610_, lean_object* v_s_611_, lean_object* v_inst_612_){
_start:
{
lean_object* v___f_613_; 
v___f_613_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_613_, 0, v_inst_612_);
lean_closure_set(v___f_613_, 1, v_s_611_);
return v___f_613_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(lean_object* v_00_u03c1_614_, lean_object* v_pat_615_, lean_object* v_s_616_, lean_object* v_inst_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_614_, v_pat_615_, v_s_616_, v_inst_617_);
lean_dec(v_pat_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_box(0);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg();
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(lean_object* v_00_u03c1_623_, lean_object* v_pat_624_, lean_object* v_s_625_, lean_object* v_inst_626_, lean_object* v_inst_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_box(0);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_629_, lean_object* v_pat_630_, lean_object* v_s_631_, lean_object* v_inst_632_, lean_object* v_inst_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(v_00_u03c1_629_, v_pat_630_, v_s_631_, v_inst_632_, v_inst_633_);
lean_dec_ref(v_inst_632_);
lean_dec_ref(v_s_631_);
lean_dec(v_pat_630_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v___y_635_, lean_object* v_inst_636_, lean_object* v_s_637_, lean_object* v_lift_638_, lean_object* v_it_639_, lean_object* v_acc_640_, lean_object* v_hP_641_, lean_object* v_recur_642_){
_start:
{
lean_object* v___f_643_; lean_object* v___x_644_; uint8_t v_decide_645_; 
v___f_643_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_643_, 0, v___y_635_);
lean_closure_set(v___f_643_, 1, v_acc_640_);
lean_closure_set(v___f_643_, 2, v_recur_642_);
v___x_644_ = lean_unsigned_to_nat(0u);
v_decide_645_ = lean_nat_dec_eq(v_it_639_, v___x_644_);
if (v_decide_645_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_667_; 
v_skipSuffixOfNonempty_x3f_646_ = lean_ctor_get(v_inst_636_, 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v_inst_636_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; lean_object* v_unused_669_; 
v_unused_668_ = lean_ctor_get(v_inst_636_, 2);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_inst_636_, 0);
lean_dec(v_unused_669_);
v___x_648_ = v_inst_636_;
v_isShared_649_ = v_isSharedCheck_667_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_646_);
lean_dec(v_inst_636_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_667_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_str_650_; lean_object* v_startInclusive_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v_str_650_ = lean_ctor_get(v_s_637_, 0);
v_startInclusive_651_ = lean_ctor_get(v_s_637_, 1);
v___x_652_ = lean_nat_add(v_startInclusive_651_, v_it_639_);
lean_inc(v_startInclusive_651_);
lean_inc_ref(v_str_650_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 2, v___x_652_);
lean_ctor_set(v___x_648_, 1, v_startInclusive_651_);
lean_ctor_set(v___x_648_, 0, v_str_650_);
v___x_654_ = v___x_648_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_str_650_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_startInclusive_651_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v___x_652_);
v___x_654_ = v_reuseFailAlloc_666_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; 
v___x_655_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_646_, v___x_654_, lean_box(0));
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_sub(v_it_639_, v___x_656_);
v___x_658_ = l_String_Slice_posLE(v_s_637_, v___x_657_);
lean_inc(v___x_658_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_it_639_);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_apply_4(v_lift_638_, lean_box(0), lean_box(0), v___f_643_, v___x_660_);
return v___x_661_;
}
else
{
lean_object* v_val_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_val_662_ = lean_ctor_get(v___x_655_, 0);
lean_inc_n(v_val_662_, 2);
lean_dec_ref_known(v___x_655_, 1);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v_val_662_);
lean_ctor_set(v___x_663_, 1, v_it_639_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_val_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_apply_4(v_lift_638_, lean_box(0), lean_box(0), v___f_643_, v___x_664_);
return v___x_665_;
}
}
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec(v_it_639_);
lean_dec_ref(v_inst_636_);
v___x_670_ = lean_box(2);
v___x_671_ = lean_apply_4(v_lift_638_, lean_box(0), lean_box(0), v___f_643_, v___x_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed(lean_object* v___y_672_, lean_object* v_inst_673_, lean_object* v_s_674_, lean_object* v_lift_675_, lean_object* v_it_676_, lean_object* v_acc_677_, lean_object* v_hP_678_, lean_object* v_recur_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(v___y_672_, v_inst_673_, v_s_674_, v_lift_675_, v_it_676_, v_acc_677_, v_hP_678_, v_recur_679_);
lean_dec_ref(v_s_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v_inst_681_, lean_object* v_s_682_, lean_object* v_lift_683_, lean_object* v_00_u03b3_684_, lean_object* v_Pl_685_, lean_object* v_it_686_, lean_object* v_init_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___f_689_; lean_object* v___x_690_; 
v___f_689_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_689_, 0, v___y_688_);
lean_closure_set(v___f_689_, 1, v_inst_681_);
lean_closure_set(v___f_689_, 2, v_s_682_);
lean_closure_set(v___f_689_, 3, v_lift_683_);
v___x_690_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_689_, v_it_686_, v_init_687_, lean_box(0));
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_691_, lean_object* v_inst_692_){
_start:
{
lean_object* v___f_693_; 
v___f_693_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_693_, 0, v_inst_692_);
lean_closure_set(v___f_693_, 1, v_s_691_);
return v___f_693_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_694_, lean_object* v_pat_695_, lean_object* v_s_696_, lean_object* v_inst_697_){
_start:
{
lean_object* v___f_698_; 
v___f_698_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_698_, 0, v_inst_697_);
lean_closure_set(v___f_698_, 1, v_s_696_);
return v___f_698_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_699_, lean_object* v_pat_700_, lean_object* v_s_701_, lean_object* v_inst_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_699_, v_pat_700_, v_s_701_, v_inst_702_);
lean_dec(v_pat_700_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(lean_object* v_pat_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_705_, 0, lean_box(0));
lean_closure_set(v___x_705_, 1, v_pat_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(lean_object* v_00_u03c1_706_, lean_object* v_pat_707_, lean_object* v_inst_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_709_, 0, lean_box(0));
lean_closure_set(v___x_709_, 1, v_pat_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_710_, lean_object* v_pat_711_, lean_object* v_inst_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(v_00_u03c1_710_, v_pat_711_, v_inst_712_);
lean_dec_ref(v_inst_712_);
return v_res_713_;
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
