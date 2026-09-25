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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_String_Slice_Pattern_SearchStep_ctorIdx___redArg(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx(lean_object* v_s_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_String_Slice_Pattern_SearchStep_ctorIdx___redArg(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorIdx___boxed(lean_object* v_s_9_, lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_String_Slice_Pattern_SearchStep_ctorIdx(v_s_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_s_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_startPos_14_; lean_object* v_endPos_15_; lean_object* v___x_16_; 
v_startPos_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_startPos_14_);
v_endPos_15_ = lean_ctor_get(v_t_12_, 1);
lean_inc(v_endPos_15_);
lean_dec_ref(v_t_12_);
v___x_16_ = lean_apply_2(v_k_13_, v_startPos_14_, v_endPos_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorElim(lean_object* v_s_17_, lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ctorElim___boxed(lean_object* v_s_24_, lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_String_Slice_Pattern_SearchStep_ctorElim(v_s_24_, v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
lean_dec_ref(v_s_24_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_rejected_elim___redArg(lean_object* v_t_31_, lean_object* v_rejected_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_31_, v_rejected_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_rejected_elim(lean_object* v_s_34_, lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_rejected_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_36_, v_rejected_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_rejected_elim___boxed(lean_object* v_s_40_, lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_rejected_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_String_Slice_Pattern_SearchStep_rejected_elim(v_s_40_, v_motive_41_, v_t_42_, v_h_43_, v_rejected_44_);
lean_dec_ref(v_s_40_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_matched_elim___redArg(lean_object* v_t_46_, lean_object* v_matched_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_46_, v_matched_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_matched_elim(lean_object* v_s_49_, lean_object* v_motive_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_matched_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_51_, v_matched_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_matched_elim___boxed(lean_object* v_s_55_, lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_matched_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_String_Slice_Pattern_SearchStep_matched_elim(v_s_55_, v_motive_56_, v_t_57_, v_h_58_, v_matched_59_);
lean_dec_ref(v_s_55_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg(){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = ((lean_object*)(l_String_Slice_Pattern_instInhabitedSearchStep_default___redArg___closed__0));
return v___x_64_;
}
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___redArg(){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0, &l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_once, _init_l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___redArg___boxed(lean_object* v___dummy_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_String_Slice_Pattern_instInhabitedSearchStep___redArg();
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep(lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0, &l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_once, _init_l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___boxed(lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_String_Slice_Pattern_instInhabitedSearchStep(v_a_78_);
lean_dec_ref(v_a_78_);
return v_res_79_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
lean_object* v_a_83_; lean_object* v_a_84_; lean_object* v_b_85_; lean_object* v_b_86_; 
if (lean_obj_tag(v_x_80_) == 0)
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v_startPos_89_; lean_object* v_endPos_90_; lean_object* v_startPos_91_; lean_object* v_endPos_92_; 
v_startPos_89_ = lean_ctor_get(v_x_80_, 0);
v_endPos_90_ = lean_ctor_get(v_x_80_, 1);
v_startPos_91_ = lean_ctor_get(v_x_81_, 0);
v_endPos_92_ = lean_ctor_get(v_x_81_, 1);
v_a_83_ = v_startPos_89_;
v_a_84_ = v_endPos_90_;
v_b_85_ = v_startPos_91_;
v_b_86_ = v_endPos_92_;
goto v___jp_82_;
}
else
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
else
{
if (lean_obj_tag(v_x_81_) == 1)
{
lean_object* v_startPos_94_; lean_object* v_endPos_95_; lean_object* v_startPos_96_; lean_object* v_endPos_97_; 
v_startPos_94_ = lean_ctor_get(v_x_80_, 0);
v_endPos_95_ = lean_ctor_get(v_x_80_, 1);
v_startPos_96_ = lean_ctor_get(v_x_81_, 0);
v_endPos_97_ = lean_ctor_get(v_x_81_, 1);
v_a_83_ = v_startPos_94_;
v_a_84_ = v_endPos_95_;
v_b_85_ = v_startPos_96_;
v_b_86_ = v_endPos_97_;
goto v___jp_82_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
v___jp_82_:
{
uint8_t v_decide_87_; 
v_decide_87_ = lean_nat_dec_eq(v_a_83_, v_b_85_);
if (v_decide_87_ == 0)
{
return v_decide_87_;
}
else
{
uint8_t v_decide_88_; 
v_decide_88_ = lean_nat_dec_eq(v_a_84_, v_b_86_);
return v_decide_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep_beq___redArg___boxed(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_99_, v_x_100_);
lean_dec_ref(v_x_100_);
lean_dec_ref(v_x_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_instBEqSearchStep_beq(lean_object* v_s_103_, lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_104_, v_x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep_beq___boxed(lean_object* v_s_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_String_Slice_Pattern_instBEqSearchStep_beq(v_s_107_, v_x_108_, v_x_109_);
lean_dec_ref(v_x_109_);
lean_dec_ref(v_x_108_);
lean_dec_ref(v_s_107_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep(lean_object* v_s_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_instBEqSearchStep_beq___boxed), 3, 1);
lean_closure_set(v___x_113_, 0, v_s_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___redArg(lean_object* v_st_114_){
_start:
{
lean_object* v_startPos_115_; 
v_startPos_115_ = lean_ctor_get(v_st_114_, 0);
lean_inc(v_startPos_115_);
return v_startPos_115_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___redArg___boxed(lean_object* v_st_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_String_Slice_Pattern_SearchStep_startPos___redArg(v_st_116_);
lean_dec_ref(v_st_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos(lean_object* v_s_118_, lean_object* v_st_119_){
_start:
{
lean_object* v_startPos_120_; 
v_startPos_120_ = lean_ctor_get(v_st_119_, 0);
lean_inc(v_startPos_120_);
return v_startPos_120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___boxed(lean_object* v_s_121_, lean_object* v_st_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_String_Slice_Pattern_SearchStep_startPos(v_s_121_, v_st_122_);
lean_dec_ref(v_st_122_);
lean_dec_ref(v_s_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___redArg(lean_object* v_st_124_){
_start:
{
lean_object* v_endPos_125_; 
v_endPos_125_ = lean_ctor_get(v_st_124_, 1);
lean_inc(v_endPos_125_);
return v_endPos_125_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___redArg___boxed(lean_object* v_st_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_String_Slice_Pattern_SearchStep_endPos___redArg(v_st_126_);
lean_dec_ref(v_st_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos(lean_object* v_s_128_, lean_object* v_st_129_){
_start:
{
lean_object* v_endPos_130_; 
v_endPos_130_ = lean_ctor_get(v_st_129_, 1);
lean_inc(v_endPos_130_);
return v_endPos_130_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___boxed(lean_object* v_s_131_, lean_object* v_st_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_String_Slice_Pattern_SearchStep_endPos(v_s_131_, v_st_132_);
lean_dec_ref(v_st_132_);
lean_dec_ref(v_s_131_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(lean_object* v_p_134_, lean_object* v_st_135_){
_start:
{
if (lean_obj_tag(v_st_135_) == 0)
{
lean_object* v_startPos_136_; lean_object* v_endPos_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_146_; 
v_startPos_136_ = lean_ctor_get(v_st_135_, 0);
v_endPos_137_ = lean_ctor_get(v_st_135_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_st_135_);
if (v_isSharedCheck_146_ == 0)
{
v___x_139_ = v_st_135_;
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_endPos_137_);
lean_inc(v_startPos_136_);
lean_dec(v_st_135_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_141_ = lean_nat_add(v_p_134_, v_startPos_136_);
lean_dec(v_startPos_136_);
v___x_142_ = lean_nat_add(v_p_134_, v_endPos_137_);
lean_dec(v_endPos_137_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_142_);
lean_ctor_set(v___x_139_, 0, v___x_141_);
v___x_144_ = v___x_139_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v_startPos_147_; lean_object* v_endPos_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_157_; 
v_startPos_147_ = lean_ctor_get(v_st_135_, 0);
v_endPos_148_ = lean_ctor_get(v_st_135_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_st_135_);
if (v_isSharedCheck_157_ == 0)
{
v___x_150_ = v_st_135_;
v_isShared_151_ = v_isSharedCheck_157_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_endPos_148_);
lean_inc(v_startPos_147_);
lean_dec(v_st_135_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_157_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_152_ = lean_nat_add(v_p_134_, v_startPos_147_);
lean_dec(v_startPos_147_);
v___x_153_ = lean_nat_add(v_p_134_, v_endPos_148_);
lean_dec(v_endPos_148_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_153_);
lean_ctor_set(v___x_150_, 0, v___x_152_);
v___x_155_ = v___x_150_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg___boxed(lean_object* v_p_158_, lean_object* v_st_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_158_, v_st_159_);
lean_dec(v_p_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom(lean_object* v_s_161_, lean_object* v_p_162_, lean_object* v_st_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_162_, v_st_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___boxed(lean_object* v_s_165_, lean_object* v_p_166_, lean_object* v_st_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom(v_s_165_, v_p_166_, v_st_167_);
lean_dec(v_p_166_);
lean_dec_ref(v_s_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___redArg(lean_object* v_st_169_, lean_object* v_h__1_170_, lean_object* v_h__2_171_){
_start:
{
if (lean_obj_tag(v_st_169_) == 0)
{
lean_object* v_startPos_172_; lean_object* v_endPos_173_; lean_object* v___x_174_; 
lean_dec(v_h__2_171_);
v_startPos_172_ = lean_ctor_get(v_st_169_, 0);
lean_inc(v_startPos_172_);
v_endPos_173_ = lean_ctor_get(v_st_169_, 1);
lean_inc(v_endPos_173_);
lean_dec_ref_known(v_st_169_, 2);
v___x_174_ = lean_apply_2(v_h__1_170_, v_startPos_172_, v_endPos_173_);
return v___x_174_;
}
else
{
lean_object* v_startPos_175_; lean_object* v_endPos_176_; lean_object* v___x_177_; 
lean_dec(v_h__1_170_);
v_startPos_175_ = lean_ctor_get(v_st_169_, 0);
lean_inc(v_startPos_175_);
v_endPos_176_ = lean_ctor_get(v_st_169_, 1);
lean_inc(v_endPos_176_);
lean_dec_ref_known(v_st_169_, 2);
v___x_177_ = lean_apply_2(v_h__2_171_, v_startPos_175_, v_endPos_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(lean_object* v_s_178_, lean_object* v_p_179_, lean_object* v_motive_180_, lean_object* v_st_181_, lean_object* v_h__1_182_, lean_object* v_h__2_183_){
_start:
{
if (lean_obj_tag(v_st_181_) == 0)
{
lean_object* v_startPos_184_; lean_object* v_endPos_185_; lean_object* v___x_186_; 
lean_dec(v_h__2_183_);
v_startPos_184_ = lean_ctor_get(v_st_181_, 0);
lean_inc(v_startPos_184_);
v_endPos_185_ = lean_ctor_get(v_st_181_, 1);
lean_inc(v_endPos_185_);
lean_dec_ref_known(v_st_181_, 2);
v___x_186_ = lean_apply_2(v_h__1_182_, v_startPos_184_, v_endPos_185_);
return v___x_186_;
}
else
{
lean_object* v_startPos_187_; lean_object* v_endPos_188_; lean_object* v___x_189_; 
lean_dec(v_h__1_182_);
v_startPos_187_ = lean_ctor_get(v_st_181_, 0);
lean_inc(v_startPos_187_);
v_endPos_188_ = lean_ctor_get(v_st_181_, 1);
lean_inc(v_endPos_188_);
lean_dec_ref_known(v_st_181_, 2);
v___x_189_ = lean_apply_2(v_h__2_183_, v_startPos_187_, v_endPos_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___boxed(lean_object* v_s_190_, lean_object* v_p_191_, lean_object* v_motive_192_, lean_object* v_st_193_, lean_object* v_h__1_194_, lean_object* v_h__2_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(v_s_190_, v_p_191_, v_motive_192_, v_st_193_, v_h__1_194_, v_h__2_195_);
lean_dec(v_p_191_);
lean_dec_ref(v_s_190_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___redArg(lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v_startPos_198_; lean_object* v_endPos_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_startPos_198_ = lean_ctor_get(v_x_197_, 0);
v_endPos_199_ = lean_ctor_get(v_x_197_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_x_197_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v_x_197_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_endPos_199_);
lean_inc(v_startPos_198_);
lean_dec(v_x_197_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_startPos_198_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_endPos_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
else
{
lean_object* v_startPos_207_; lean_object* v_endPos_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_startPos_207_ = lean_ctor_get(v_x_197_, 0);
v_endPos_208_ = lean_ctor_get(v_x_197_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_197_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v_x_197_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_endPos_208_);
lean_inc(v_startPos_207_);
lean_dec(v_x_197_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_startPos_207_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_endPos_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast(lean_object* v_s_216_, lean_object* v_t_217_, lean_object* v_hst_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v_startPos_220_; lean_object* v_endPos_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_startPos_220_ = lean_ctor_get(v_x_219_, 0);
v_endPos_221_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v_x_219_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_endPos_221_);
lean_inc(v_startPos_220_);
lean_dec(v_x_219_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_startPos_220_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_endPos_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
else
{
lean_object* v_startPos_229_; lean_object* v_endPos_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
v_startPos_229_ = lean_ctor_get(v_x_219_, 0);
v_endPos_230_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v_x_219_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_endPos_230_);
lean_inc(v_startPos_229_);
lean_dec(v_x_219_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_startPos_229_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_endPos_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___boxed(lean_object* v_s_238_, lean_object* v_t_239_, lean_object* v_hst_240_, lean_object* v_x_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_String_Slice_Pattern_SearchStep_cast(v_s_238_, v_t_239_, v_hst_240_, v_x_241_);
lean_dec_ref(v_t_239_);
lean_dec_ref(v_s_238_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(lean_object* v_inst_243_, lean_object* v_s_244_){
_start:
{
lean_object* v_skipPrefix_x3f_245_; lean_object* v___x_246_; 
v_skipPrefix_x3f_245_ = lean_ctor_get(v_inst_243_, 0);
lean_inc_ref(v_skipPrefix_x3f_245_);
lean_dec_ref(v_inst_243_);
v___x_246_ = lean_apply_1(v_skipPrefix_x3f_245_, v_s_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(lean_object* v_00_u03c1_247_, lean_object* v_pat_248_, lean_object* v_inst_249_, lean_object* v_s_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(v_inst_249_, v_s_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_252_, lean_object* v_pat_253_, lean_object* v_inst_254_, lean_object* v_s_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(v_00_u03c1_252_, v_pat_253_, v_inst_254_, v_s_255_);
lean_dec(v_pat_253_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg(){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_unsigned_to_nat(0u);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg___boxed(lean_object* v___dummy_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___redArg();
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(lean_object* v_00_u03c1_261_, lean_object* v_pat_262_, lean_object* v_s_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_unsigned_to_nat(0u);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(lean_object* v_00_u03c1_265_, lean_object* v_pat_266_, lean_object* v_s_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(v_00_u03c1_265_, v_pat_266_, v_s_267_);
lean_dec_ref(v_s_267_);
lean_dec(v_pat_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg(){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_unsigned_to_nat(0u);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg___boxed(lean_object* v___dummy_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___redArg();
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_unsigned_to_nat(0u);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(v_a_277_, v_a_278_, v_a_279_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg(){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_unsigned_to_nat(0u);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg___boxed(lean_object* v___dummy_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___redArg();
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(lean_object* v_00_u03c1_285_, lean_object* v_pat_286_, lean_object* v_s_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_unsigned_to_nat(0u);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object* v_00_u03c1_289_, lean_object* v_pat_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(v_00_u03c1_289_, v_pat_290_, v_s_291_);
lean_dec_ref(v_s_291_);
lean_dec(v_pat_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(lean_object* v_s_293_, lean_object* v_inst_294_, lean_object* v_it_295_){
_start:
{
lean_object* v_str_296_; lean_object* v_startInclusive_297_; lean_object* v_endExclusive_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_319_; 
v_str_296_ = lean_ctor_get(v_s_293_, 0);
v_startInclusive_297_ = lean_ctor_get(v_s_293_, 1);
v_endExclusive_298_ = lean_ctor_get(v_s_293_, 2);
v_isSharedCheck_319_ = !lean_is_exclusive(v_s_293_);
if (v_isSharedCheck_319_ == 0)
{
v___x_300_ = v_s_293_;
v_isShared_301_ = v_isSharedCheck_319_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_endExclusive_298_);
lean_inc(v_startInclusive_297_);
lean_inc(v_str_296_);
lean_dec(v_s_293_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_319_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; uint8_t v_decide_303_; 
v___x_302_ = lean_nat_sub(v_endExclusive_298_, v_startInclusive_297_);
v_decide_303_ = lean_nat_dec_eq(v_it_295_, v___x_302_);
lean_dec(v___x_302_);
if (v_decide_303_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v_skipPrefixOfNonempty_x3f_304_ = lean_ctor_get(v_inst_294_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_304_);
lean_dec_ref(v_inst_294_);
v___x_305_ = lean_nat_add(v_startInclusive_297_, v_it_295_);
lean_inc(v___x_305_);
lean_inc_ref(v_str_296_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v___x_305_);
v___x_307_ = v___x_300_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_str_296_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_endExclusive_298_);
v___x_307_ = v_reuseFailAlloc_317_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; 
v___x_308_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_304_, v___x_307_, lean_box(0));
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_string_utf8_next_fast(v_str_296_, v___x_305_);
lean_dec(v___x_305_);
lean_dec_ref(v_str_296_);
v___x_310_ = lean_nat_sub(v___x_309_, v_startInclusive_297_);
lean_dec(v_startInclusive_297_);
lean_inc(v___x_310_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v_it_295_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
return v___x_312_;
}
else
{
lean_object* v_val_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v___x_305_);
lean_dec(v_startInclusive_297_);
lean_dec_ref(v_str_296_);
v_val_313_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_val_313_);
lean_dec_ref_known(v___x_308_, 1);
v___x_314_ = lean_nat_add(v_it_295_, v_val_313_);
lean_dec(v_val_313_);
lean_inc(v___x_314_);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v_it_295_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
return v___x_316_;
}
}
}
else
{
lean_object* v___x_318_; 
lean_del_object(v___x_300_);
lean_dec(v_endExclusive_298_);
lean_dec(v_startInclusive_297_);
lean_dec_ref(v_str_296_);
lean_dec(v_it_295_);
lean_dec_ref(v_inst_294_);
v___x_318_ = lean_box(2);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(lean_object* v_s_320_, lean_object* v_inst_321_){
_start:
{
lean_object* v___f_322_; 
v___f_322_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_322_, 0, v_s_320_);
lean_closure_set(v___f_322_, 1, v_inst_321_);
return v___f_322_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(lean_object* v_00_u03c1_323_, lean_object* v_pat_324_, lean_object* v_s_325_, lean_object* v_inst_326_){
_start:
{
lean_object* v___f_327_; 
v___f_327_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_327_, 0, v_s_325_);
lean_closure_set(v___f_327_, 1, v_inst_326_);
return v___f_327_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(lean_object* v_00_u03c1_328_, lean_object* v_pat_329_, lean_object* v_s_330_, lean_object* v_inst_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(v_00_u03c1_328_, v_pat_329_, v_s_330_, v_inst_331_);
lean_dec(v_pat_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_box(0);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___redArg();
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(lean_object* v_00_u03c1_337_, lean_object* v_pat_338_, lean_object* v_s_339_, lean_object* v_inst_340_, lean_object* v_inst_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = lean_box(0);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_343_, lean_object* v_pat_344_, lean_object* v_s_345_, lean_object* v_inst_346_, lean_object* v_inst_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(v_00_u03c1_343_, v_pat_344_, v_s_345_, v_inst_346_, v_inst_347_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_s_345_);
lean_dec(v_pat_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v___y_349_, lean_object* v_acc_350_, lean_object* v_recur_351_, lean_object* v_s_352_){
_start:
{
switch(lean_obj_tag(v_s_352_))
{
case 0:
{
lean_object* v_it_353_; lean_object* v_out_354_; lean_object* v_val_355_; 
v_it_353_ = lean_ctor_get(v_s_352_, 0);
lean_inc(v_it_353_);
v_out_354_ = lean_ctor_get(v_s_352_, 1);
lean_inc(v_out_354_);
lean_dec_ref_known(v_s_352_, 2);
v_val_355_ = lean_apply_3(v___y_349_, v_out_354_, lean_box(0), v_acc_350_);
if (lean_obj_tag(v_val_355_) == 0)
{
lean_object* v_a_356_; 
lean_dec(v_it_353_);
lean_dec(v_recur_351_);
v_a_356_ = lean_ctor_get(v_val_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v_val_355_, 1);
return v_a_356_;
}
else
{
lean_object* v_a_357_; lean_object* v___x_358_; 
v_a_357_ = lean_ctor_get(v_val_355_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v_val_355_, 1);
v___x_358_ = lean_apply_4(v_recur_351_, v_it_353_, v_a_357_, lean_box(0), lean_box(0));
return v___x_358_;
}
}
case 1:
{
lean_object* v_it_359_; lean_object* v___x_360_; 
lean_dec_ref(v___y_349_);
v_it_359_ = lean_ctor_get(v_s_352_, 0);
lean_inc(v_it_359_);
lean_dec_ref_known(v_s_352_, 1);
v___x_360_ = lean_apply_4(v_recur_351_, v_it_359_, v_acc_350_, lean_box(0), lean_box(0));
return v___x_360_;
}
default: 
{
lean_dec(v_recur_351_);
lean_dec_ref(v___y_349_);
return v_acc_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v_s_361_, lean_object* v___y_362_, lean_object* v_inst_363_, lean_object* v_lift_364_, lean_object* v_it_365_, lean_object* v_acc_366_, lean_object* v_hP_367_, lean_object* v_recur_368_){
_start:
{
lean_object* v_str_369_; lean_object* v_startInclusive_370_; lean_object* v_endExclusive_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_396_; 
v_str_369_ = lean_ctor_get(v_s_361_, 0);
v_startInclusive_370_ = lean_ctor_get(v_s_361_, 1);
v_endExclusive_371_ = lean_ctor_get(v_s_361_, 2);
v_isSharedCheck_396_ = !lean_is_exclusive(v_s_361_);
if (v_isSharedCheck_396_ == 0)
{
v___x_373_ = v_s_361_;
v_isShared_374_ = v_isSharedCheck_396_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_endExclusive_371_);
lean_inc(v_startInclusive_370_);
lean_inc(v_str_369_);
lean_dec(v_s_361_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_396_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___f_375_; lean_object* v___x_376_; uint8_t v_decide_377_; 
v___f_375_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_375_, 0, v___y_362_);
lean_closure_set(v___f_375_, 1, v_acc_366_);
lean_closure_set(v___f_375_, 2, v_recur_368_);
v___x_376_ = lean_nat_sub(v_endExclusive_371_, v_startInclusive_370_);
v_decide_377_ = lean_nat_dec_eq(v_it_365_, v___x_376_);
lean_dec(v___x_376_);
if (v_decide_377_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v_skipPrefixOfNonempty_x3f_378_ = lean_ctor_get(v_inst_363_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_378_);
lean_dec_ref(v_inst_363_);
v___x_379_ = lean_nat_add(v_startInclusive_370_, v_it_365_);
lean_inc(v___x_379_);
lean_inc_ref(v_str_369_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 1, v___x_379_);
v___x_381_ = v___x_373_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_str_369_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_endExclusive_371_);
v___x_381_ = v_reuseFailAlloc_393_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; 
v___x_382_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_378_, v___x_381_, lean_box(0));
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_383_ = lean_string_utf8_next_fast(v_str_369_, v___x_379_);
lean_dec(v___x_379_);
lean_dec_ref(v_str_369_);
v___x_384_ = lean_nat_sub(v___x_383_, v_startInclusive_370_);
lean_dec(v_startInclusive_370_);
lean_inc(v___x_384_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_it_365_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_apply_4(v_lift_364_, lean_box(0), lean_box(0), v___f_375_, v___x_386_);
return v___x_387_;
}
else
{
lean_object* v_val_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v___x_379_);
lean_dec(v_startInclusive_370_);
lean_dec_ref(v_str_369_);
v_val_388_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v___x_382_, 1);
v___x_389_ = lean_nat_add(v_it_365_, v_val_388_);
lean_dec(v_val_388_);
lean_inc(v___x_389_);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v_it_365_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_apply_4(v_lift_364_, lean_box(0), lean_box(0), v___f_375_, v___x_391_);
return v___x_392_;
}
}
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_del_object(v___x_373_);
lean_dec(v_endExclusive_371_);
lean_dec(v_startInclusive_370_);
lean_dec_ref(v_str_369_);
lean_dec(v_it_365_);
lean_dec_ref(v_inst_363_);
v___x_394_ = lean_box(2);
v___x_395_ = lean_apply_4(v_lift_364_, lean_box(0), lean_box(0), v___f_375_, v___x_394_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object* v_s_397_, lean_object* v_inst_398_, lean_object* v_lift_399_, lean_object* v_00_u03b3_400_, lean_object* v_Pl_401_, lean_object* v_it_402_, lean_object* v_init_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___f_405_; lean_object* v___x_406_; 
v___f_405_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1), 8, 4);
lean_closure_set(v___f_405_, 0, v_s_397_);
lean_closure_set(v___f_405_, 1, v___y_404_);
lean_closure_set(v___f_405_, 2, v_inst_398_);
lean_closure_set(v___f_405_, 3, v_lift_399_);
v___x_406_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_405_, v_it_402_, v_init_403_, lean_box(0));
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_407_, lean_object* v_inst_408_){
_start:
{
lean_object* v___f_409_; 
v___f_409_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_409_, 0, v_s_407_);
lean_closure_set(v___f_409_, 1, v_inst_408_);
return v___f_409_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_410_, lean_object* v_pat_411_, lean_object* v_s_412_, lean_object* v_inst_413_){
_start:
{
lean_object* v___f_414_; 
v___f_414_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_414_, 0, v_s_412_);
lean_closure_set(v___f_414_, 1, v_inst_413_);
return v___f_414_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_415_, lean_object* v_pat_416_, lean_object* v_s_417_, lean_object* v_inst_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_415_, v_pat_416_, v_s_417_, v_inst_418_);
lean_dec(v_pat_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(lean_object* v_pat_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_421_, 0, lean_box(0));
lean_closure_set(v___x_421_, 1, v_pat_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(lean_object* v_00_u03c1_422_, lean_object* v_pat_423_, lean_object* v_inst_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_425_, 0, lean_box(0));
lean_closure_set(v___x_425_, 1, v_pat_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_426_, lean_object* v_pat_427_, lean_object* v_inst_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(v_00_u03c1_426_, v_pat_427_, v_inst_428_);
lean_dec_ref(v_inst_428_);
return v_res_429_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(lean_object* v_lhs_430_, lean_object* v_rhs_431_, lean_object* v_lstart_432_, lean_object* v_rstart_433_, lean_object* v_len_434_, lean_object* v_curr_435_){
_start:
{
uint8_t v___y_437_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_add(v_curr_435_, v___x_441_);
v___x_443_ = lean_nat_dec_le(v___x_442_, v_len_434_);
lean_dec(v___x_442_);
if (v___x_443_ == 0)
{
uint8_t v___x_444_; 
lean_dec(v_curr_435_);
v___x_444_ = 1;
return v___x_444_;
}
else
{
if (v___x_443_ == 0)
{
v___y_437_ = v___x_443_;
goto v___jp_436_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; uint8_t v___x_449_; 
v___x_445_ = lean_nat_add(v_lstart_432_, v_curr_435_);
v___x_446_ = lean_string_get_byte_fast(v_lhs_430_, v___x_445_);
v___x_447_ = lean_nat_add(v_rstart_433_, v_curr_435_);
v___x_448_ = lean_string_get_byte_fast(v_rhs_431_, v___x_447_);
v___x_449_ = lean_uint8_dec_eq(v___x_446_, v___x_448_);
v___y_437_ = v___x_449_;
goto v___jp_436_;
}
}
v___jp_436_:
{
if (v___y_437_ == 0)
{
lean_dec(v_curr_435_);
return v___y_437_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_curr_435_, v___x_438_);
lean_dec(v_curr_435_);
v_curr_435_ = v___x_439_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg___boxed(lean_object* v_lhs_450_, lean_object* v_rhs_451_, lean_object* v_lstart_452_, lean_object* v_rstart_453_, lean_object* v_len_454_, lean_object* v_curr_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_450_, v_rhs_451_, v_lstart_452_, v_rstart_453_, v_len_454_, v_curr_455_);
lean_dec(v_len_454_);
lean_dec(v_rstart_453_);
lean_dec(v_lstart_452_);
lean_dec_ref(v_rhs_451_);
lean_dec_ref(v_lhs_450_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object* v_lhs_458_, lean_object* v_rhs_459_, lean_object* v_lstart_460_, lean_object* v_rstart_461_, lean_object* v_len_462_, lean_object* v_h1_463_, lean_object* v_h2_464_, lean_object* v_curr_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_458_, v_rhs_459_, v_lstart_460_, v_rstart_461_, v_len_462_, v_curr_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object* v_lhs_467_, lean_object* v_rhs_468_, lean_object* v_lstart_469_, lean_object* v_rstart_470_, lean_object* v_len_471_, lean_object* v_h1_472_, lean_object* v_h2_473_, lean_object* v_curr_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(v_lhs_467_, v_rhs_468_, v_lstart_469_, v_rstart_470_, v_len_471_, v_h1_472_, v_h2_473_, v_curr_474_);
lean_dec(v_len_471_);
lean_dec(v_rstart_470_);
lean_dec(v_lstart_469_);
lean_dec_ref(v_rhs_468_);
lean_dec_ref(v_lhs_467_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object* v_lhs_484_, lean_object* v_rhs_485_, lean_object* v_lstart_486_, lean_object* v_rstart_487_, lean_object* v_len_488_, lean_object* v_h1_489_, lean_object* v_h2_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = lean_string_memcmp(v_lhs_484_, v_rhs_485_, v_lstart_486_, v_rstart_487_, v_len_488_);
lean_dec(v_len_488_);
lean_dec(v_rstart_487_);
lean_dec(v_lstart_486_);
lean_dec_ref(v_rhs_485_);
lean_dec_ref(v_lhs_484_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object* v_lhs_493_, lean_object* v_rhs_494_, lean_object* v_lstart_495_, lean_object* v_rstart_496_, lean_object* v_len_497_){
_start:
{
lean_object* v_str_498_; lean_object* v_startInclusive_499_; lean_object* v_str_500_; lean_object* v_startInclusive_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v_str_498_ = lean_ctor_get(v_lhs_493_, 0);
v_startInclusive_499_ = lean_ctor_get(v_lhs_493_, 1);
v_str_500_ = lean_ctor_get(v_rhs_494_, 0);
v_startInclusive_501_ = lean_ctor_get(v_rhs_494_, 1);
v___x_502_ = lean_nat_add(v_startInclusive_499_, v_lstart_495_);
v___x_503_ = lean_nat_add(v_startInclusive_501_, v_rstart_496_);
v___x_504_ = lean_string_memcmp(v_str_498_, v_str_500_, v___x_502_, v___x_503_, v_len_497_);
lean_dec(v___x_503_);
lean_dec(v___x_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object* v_lhs_505_, lean_object* v_rhs_506_, lean_object* v_lstart_507_, lean_object* v_rstart_508_, lean_object* v_len_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(v_lhs_505_, v_rhs_506_, v_lstart_507_, v_rstart_508_, v_len_509_);
lean_dec(v_len_509_);
lean_dec(v_rstart_508_);
lean_dec(v_lstart_507_);
lean_dec_ref(v_rhs_506_);
lean_dec_ref(v_lhs_505_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object* v_lhs_512_, lean_object* v_rhs_513_, lean_object* v_lstart_514_, lean_object* v_rstart_515_, lean_object* v_len_516_, lean_object* v_h1_517_, lean_object* v_h2_518_){
_start:
{
lean_object* v_str_519_; lean_object* v_startInclusive_520_; lean_object* v_str_521_; lean_object* v_startInclusive_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_str_519_ = lean_ctor_get(v_lhs_512_, 0);
v_startInclusive_520_ = lean_ctor_get(v_lhs_512_, 1);
v_str_521_ = lean_ctor_get(v_rhs_513_, 0);
v_startInclusive_522_ = lean_ctor_get(v_rhs_513_, 1);
v___x_523_ = lean_nat_add(v_startInclusive_520_, v_lstart_514_);
v___x_524_ = lean_nat_add(v_startInclusive_522_, v_rstart_515_);
v___x_525_ = lean_string_memcmp(v_str_519_, v_str_521_, v___x_523_, v___x_524_, v_len_516_);
lean_dec(v___x_524_);
lean_dec(v___x_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object* v_lhs_526_, lean_object* v_rhs_527_, lean_object* v_lstart_528_, lean_object* v_rstart_529_, lean_object* v_len_530_, lean_object* v_h1_531_, lean_object* v_h2_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_String_Slice_Pattern_Internal_memcmpSlice(v_lhs_526_, v_rhs_527_, v_lstart_528_, v_rstart_529_, v_len_530_, v_h1_531_, v_h2_532_);
lean_dec(v_len_530_);
lean_dec(v_rstart_529_);
lean_dec(v_lstart_528_);
lean_dec_ref(v_rhs_527_);
lean_dec_ref(v_lhs_526_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg(){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_unsigned_to_nat(0u);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg___boxed(lean_object* v___dummy_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___redArg();
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object* v_00_u03c1_539_, lean_object* v_pat_540_, lean_object* v_s_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_unsigned_to_nat(0u);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object* v_00_u03c1_543_, lean_object* v_pat_544_, lean_object* v_s_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(v_00_u03c1_543_, v_pat_544_, v_s_545_);
lean_dec_ref(v_s_545_);
lean_dec(v_pat_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg(){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_unsigned_to_nat(0u);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg___boxed(lean_object* v___dummy_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___redArg();
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = lean_unsigned_to_nat(0u);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(v_a_555_, v_a_556_, v_a_557_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(lean_object* v_s_559_){
_start:
{
lean_object* v_startInclusive_560_; lean_object* v_endExclusive_561_; lean_object* v___x_562_; 
v_startInclusive_560_ = lean_ctor_get(v_s_559_, 1);
v_endExclusive_561_ = lean_ctor_get(v_s_559_, 2);
v___x_562_ = lean_nat_sub(v_endExclusive_561_, v_startInclusive_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(lean_object* v_s_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_563_);
lean_dec_ref(v_s_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(lean_object* v_00_u03c1_565_, lean_object* v_pat_566_, lean_object* v_s_567_){
_start:
{
lean_object* v_startInclusive_568_; lean_object* v_endExclusive_569_; lean_object* v___x_570_; 
v_startInclusive_568_ = lean_ctor_get(v_s_567_, 1);
v_endExclusive_569_ = lean_ctor_get(v_s_567_, 2);
v___x_570_ = lean_nat_sub(v_endExclusive_569_, v_startInclusive_568_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object* v_00_u03c1_571_, lean_object* v_pat_572_, lean_object* v_s_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(v_00_u03c1_571_, v_pat_572_, v_s_573_);
lean_dec_ref(v_s_573_);
lean_dec(v_pat_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(lean_object* v_inst_575_, lean_object* v_s_576_, lean_object* v_it_577_){
_start:
{
lean_object* v___x_578_; uint8_t v_decide_579_; 
v___x_578_ = lean_unsigned_to_nat(0u);
v_decide_579_ = lean_nat_dec_eq(v_it_577_, v___x_578_);
if (v_decide_579_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_599_; 
v_skipSuffixOfNonempty_x3f_580_ = lean_ctor_get(v_inst_575_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_inst_575_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; lean_object* v_unused_601_; 
v_unused_600_ = lean_ctor_get(v_inst_575_, 2);
lean_dec(v_unused_600_);
v_unused_601_ = lean_ctor_get(v_inst_575_, 0);
lean_dec(v_unused_601_);
v___x_582_ = v_inst_575_;
v_isShared_583_ = v_isSharedCheck_599_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_580_);
lean_dec(v_inst_575_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_599_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_str_584_; lean_object* v_startInclusive_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v_str_584_ = lean_ctor_get(v_s_576_, 0);
v_startInclusive_585_ = lean_ctor_get(v_s_576_, 1);
v___x_586_ = lean_nat_add(v_startInclusive_585_, v_it_577_);
lean_inc(v_startInclusive_585_);
lean_inc_ref(v_str_584_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 2, v___x_586_);
lean_ctor_set(v___x_582_, 1, v_startInclusive_585_);
lean_ctor_set(v___x_582_, 0, v_str_584_);
v___x_588_ = v___x_582_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_str_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_startInclusive_585_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v___x_586_);
v___x_588_ = v_reuseFailAlloc_598_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_580_, v___x_588_, lean_box(0));
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_sub(v_it_577_, v___x_590_);
v___x_592_ = l_String_Slice_posLE(v_s_576_, v___x_591_);
lean_inc(v___x_592_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_it_577_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
return v___x_594_;
}
else
{
lean_object* v_val_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_val_595_ = lean_ctor_get(v___x_589_, 0);
lean_inc_n(v_val_595_, 2);
lean_dec_ref_known(v___x_589_, 1);
v___x_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_596_, 0, v_val_595_);
lean_ctor_set(v___x_596_, 1, v_it_577_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_val_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
return v___x_597_;
}
}
}
}
else
{
lean_object* v___x_602_; 
lean_dec(v_it_577_);
lean_dec_ref(v_inst_575_);
v___x_602_ = lean_box(2);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(lean_object* v_inst_603_, lean_object* v_s_604_, lean_object* v_it_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_603_, v_s_604_, v_it_605_);
lean_dec_ref(v_s_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(lean_object* v_s_607_, lean_object* v_inst_608_){
_start:
{
lean_object* v___f_609_; 
v___f_609_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_609_, 0, v_inst_608_);
lean_closure_set(v___f_609_, 1, v_s_607_);
return v___f_609_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(lean_object* v_00_u03c1_610_, lean_object* v_pat_611_, lean_object* v_s_612_, lean_object* v_inst_613_){
_start:
{
lean_object* v___f_614_; 
v___f_614_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_614_, 0, v_inst_613_);
lean_closure_set(v___f_614_, 1, v_s_612_);
return v___f_614_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(lean_object* v_00_u03c1_615_, lean_object* v_pat_616_, lean_object* v_s_617_, lean_object* v_inst_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_615_, v_pat_616_, v_s_617_, v_inst_618_);
lean_dec(v_pat_616_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_box(0);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___redArg();
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(lean_object* v_00_u03c1_624_, lean_object* v_pat_625_, lean_object* v_s_626_, lean_object* v_inst_627_, lean_object* v_inst_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_box(0);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_630_, lean_object* v_pat_631_, lean_object* v_s_632_, lean_object* v_inst_633_, lean_object* v_inst_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(v_00_u03c1_630_, v_pat_631_, v_s_632_, v_inst_633_, v_inst_634_);
lean_dec_ref(v_inst_633_);
lean_dec_ref(v_s_632_);
lean_dec(v_pat_631_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v___y_636_, lean_object* v_inst_637_, lean_object* v_s_638_, lean_object* v_lift_639_, lean_object* v_it_640_, lean_object* v_acc_641_, lean_object* v_hP_642_, lean_object* v_recur_643_){
_start:
{
lean_object* v___f_644_; lean_object* v___x_645_; uint8_t v_decide_646_; 
v___f_644_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_644_, 0, v___y_636_);
lean_closure_set(v___f_644_, 1, v_acc_641_);
lean_closure_set(v___f_644_, 2, v_recur_643_);
v___x_645_ = lean_unsigned_to_nat(0u);
v_decide_646_ = lean_nat_dec_eq(v_it_640_, v___x_645_);
if (v_decide_646_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_668_; 
v_skipSuffixOfNonempty_x3f_647_ = lean_ctor_get(v_inst_637_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_inst_637_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; lean_object* v_unused_670_; 
v_unused_669_ = lean_ctor_get(v_inst_637_, 2);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v_inst_637_, 0);
lean_dec(v_unused_670_);
v___x_649_ = v_inst_637_;
v_isShared_650_ = v_isSharedCheck_668_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_647_);
lean_dec(v_inst_637_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_668_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_str_651_; lean_object* v_startInclusive_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v_str_651_ = lean_ctor_get(v_s_638_, 0);
v_startInclusive_652_ = lean_ctor_get(v_s_638_, 1);
v___x_653_ = lean_nat_add(v_startInclusive_652_, v_it_640_);
lean_inc(v_startInclusive_652_);
lean_inc_ref(v_str_651_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 2, v___x_653_);
lean_ctor_set(v___x_649_, 1, v_startInclusive_652_);
lean_ctor_set(v___x_649_, 0, v_str_651_);
v___x_655_ = v___x_649_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_str_651_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_startInclusive_652_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v___x_653_);
v___x_655_ = v_reuseFailAlloc_667_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; 
v___x_656_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_647_, v___x_655_, lean_box(0));
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_sub(v_it_640_, v___x_657_);
v___x_659_ = l_String_Slice_posLE(v_s_638_, v___x_658_);
lean_inc(v___x_659_);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v_it_640_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = lean_apply_4(v_lift_639_, lean_box(0), lean_box(0), v___f_644_, v___x_661_);
return v___x_662_;
}
else
{
lean_object* v_val_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_val_663_ = lean_ctor_get(v___x_656_, 0);
lean_inc_n(v_val_663_, 2);
lean_dec_ref_known(v___x_656_, 1);
v___x_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_664_, 0, v_val_663_);
lean_ctor_set(v___x_664_, 1, v_it_640_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_val_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_apply_4(v_lift_639_, lean_box(0), lean_box(0), v___f_644_, v___x_665_);
return v___x_666_;
}
}
}
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_it_640_);
lean_dec_ref(v_inst_637_);
v___x_671_ = lean_box(2);
v___x_672_ = lean_apply_4(v_lift_639_, lean_box(0), lean_box(0), v___f_644_, v___x_671_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed(lean_object* v___y_673_, lean_object* v_inst_674_, lean_object* v_s_675_, lean_object* v_lift_676_, lean_object* v_it_677_, lean_object* v_acc_678_, lean_object* v_hP_679_, lean_object* v_recur_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(v___y_673_, v_inst_674_, v_s_675_, v_lift_676_, v_it_677_, v_acc_678_, v_hP_679_, v_recur_680_);
lean_dec_ref(v_s_675_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v_inst_682_, lean_object* v_s_683_, lean_object* v_lift_684_, lean_object* v_00_u03b3_685_, lean_object* v_Pl_686_, lean_object* v_it_687_, lean_object* v_init_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___f_690_; lean_object* v___x_691_; 
v___f_690_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_690_, 0, v___y_689_);
lean_closure_set(v___f_690_, 1, v_inst_682_);
lean_closure_set(v___f_690_, 2, v_s_683_);
lean_closure_set(v___f_690_, 3, v_lift_684_);
v___x_691_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_690_, v_it_687_, v_init_688_, lean_box(0));
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_692_, lean_object* v_inst_693_){
_start:
{
lean_object* v___f_694_; 
v___f_694_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_694_, 0, v_inst_693_);
lean_closure_set(v___f_694_, 1, v_s_692_);
return v___f_694_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_695_, lean_object* v_pat_696_, lean_object* v_s_697_, lean_object* v_inst_698_){
_start:
{
lean_object* v___f_699_; 
v___f_699_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_699_, 0, v_inst_698_);
lean_closure_set(v___f_699_, 1, v_s_697_);
return v___f_699_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_700_, lean_object* v_pat_701_, lean_object* v_s_702_, lean_object* v_inst_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_700_, v_pat_701_, v_s_702_, v_inst_703_);
lean_dec(v_pat_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(lean_object* v_pat_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_706_, 0, lean_box(0));
lean_closure_set(v___x_706_, 1, v_pat_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(lean_object* v_00_u03c1_707_, lean_object* v_pat_708_, lean_object* v_inst_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_710_, 0, lean_box(0));
lean_closure_set(v___x_710_, 1, v_pat_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_711_, lean_object* v_pat_712_, lean_object* v_inst_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(v_00_u03c1_711_, v_pat_712_, v_inst_713_);
lean_dec_ref(v_inst_713_);
return v_res_714_;
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
