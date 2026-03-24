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
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0 = (const lean_object*)&l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default(lean_object* v_a_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = ((lean_object*)(l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0));
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___boxed(lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_String_Slice_Pattern_instInhabitedSearchStep_default(v_a_65_);
lean_dec_ref(v_a_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep(lean_object* v_a_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_String_Slice_Pattern_instInhabitedSearchStep_default(v_a_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep___boxed(lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_String_Slice_Pattern_instInhabitedSearchStep(v_a_69_);
lean_dec_ref(v_a_69_);
return v_res_70_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
lean_object* v_a_74_; lean_object* v_a_75_; lean_object* v_b_76_; lean_object* v_b_77_; 
if (lean_obj_tag(v_x_71_) == 0)
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_object* v_startPos_80_; lean_object* v_endPos_81_; lean_object* v_startPos_82_; lean_object* v_endPos_83_; 
v_startPos_80_ = lean_ctor_get(v_x_71_, 0);
v_endPos_81_ = lean_ctor_get(v_x_71_, 1);
v_startPos_82_ = lean_ctor_get(v_x_72_, 0);
v_endPos_83_ = lean_ctor_get(v_x_72_, 1);
v_a_74_ = v_startPos_80_;
v_a_75_ = v_endPos_81_;
v_b_76_ = v_startPos_82_;
v_b_77_ = v_endPos_83_;
goto v___jp_73_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
else
{
if (lean_obj_tag(v_x_72_) == 1)
{
lean_object* v_startPos_85_; lean_object* v_endPos_86_; lean_object* v_startPos_87_; lean_object* v_endPos_88_; 
v_startPos_85_ = lean_ctor_get(v_x_71_, 0);
v_endPos_86_ = lean_ctor_get(v_x_71_, 1);
v_startPos_87_ = lean_ctor_get(v_x_72_, 0);
v_endPos_88_ = lean_ctor_get(v_x_72_, 1);
v_a_74_ = v_startPos_85_;
v_a_75_ = v_endPos_86_;
v_b_76_ = v_startPos_87_;
v_b_77_ = v_endPos_88_;
goto v___jp_73_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
v___jp_73_:
{
uint8_t v___x_78_; 
v___x_78_ = lean_nat_dec_eq(v_a_74_, v_b_76_);
if (v___x_78_ == 0)
{
return v___x_78_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = lean_nat_dec_eq(v_a_75_, v_b_77_);
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep_beq___redArg___boxed(lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_90_, v_x_91_);
lean_dec_ref(v_x_91_);
lean_dec_ref(v_x_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_instBEqSearchStep_beq(lean_object* v_s_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_95_, v_x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep_beq___boxed(lean_object* v_s_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_String_Slice_Pattern_instBEqSearchStep_beq(v_s_98_, v_x_99_, v_x_100_);
lean_dec_ref(v_x_100_);
lean_dec_ref(v_x_99_);
lean_dec_ref(v_s_98_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instBEqSearchStep(lean_object* v_s_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_instBEqSearchStep_beq___boxed), 3, 1);
lean_closure_set(v___x_104_, 0, v_s_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___redArg(lean_object* v_st_105_){
_start:
{
lean_object* v_startPos_106_; 
v_startPos_106_ = lean_ctor_get(v_st_105_, 0);
lean_inc(v_startPos_106_);
return v_startPos_106_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___redArg___boxed(lean_object* v_st_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_String_Slice_Pattern_SearchStep_startPos___redArg(v_st_107_);
lean_dec_ref(v_st_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos(lean_object* v_s_109_, lean_object* v_st_110_){
_start:
{
lean_object* v_startPos_111_; 
v_startPos_111_ = lean_ctor_get(v_st_110_, 0);
lean_inc(v_startPos_111_);
return v_startPos_111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_startPos___boxed(lean_object* v_s_112_, lean_object* v_st_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_String_Slice_Pattern_SearchStep_startPos(v_s_112_, v_st_113_);
lean_dec_ref(v_st_113_);
lean_dec_ref(v_s_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___redArg(lean_object* v_st_115_){
_start:
{
lean_object* v_endPos_116_; 
v_endPos_116_ = lean_ctor_get(v_st_115_, 1);
lean_inc(v_endPos_116_);
return v_endPos_116_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___redArg___boxed(lean_object* v_st_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_String_Slice_Pattern_SearchStep_endPos___redArg(v_st_117_);
lean_dec_ref(v_st_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos(lean_object* v_s_119_, lean_object* v_st_120_){
_start:
{
lean_object* v_endPos_121_; 
v_endPos_121_ = lean_ctor_get(v_st_120_, 1);
lean_inc(v_endPos_121_);
return v_endPos_121_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_endPos___boxed(lean_object* v_s_122_, lean_object* v_st_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_String_Slice_Pattern_SearchStep_endPos(v_s_122_, v_st_123_);
lean_dec_ref(v_st_123_);
lean_dec_ref(v_s_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(lean_object* v_p_125_, lean_object* v_st_126_){
_start:
{
if (lean_obj_tag(v_st_126_) == 0)
{
lean_object* v_startPos_127_; lean_object* v_endPos_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_137_; 
v_startPos_127_ = lean_ctor_get(v_st_126_, 0);
v_endPos_128_ = lean_ctor_get(v_st_126_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_st_126_);
if (v_isSharedCheck_137_ == 0)
{
v___x_130_ = v_st_126_;
v_isShared_131_ = v_isSharedCheck_137_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_endPos_128_);
lean_inc(v_startPos_127_);
lean_dec(v_st_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_137_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_132_ = lean_nat_add(v_p_125_, v_startPos_127_);
lean_dec(v_startPos_127_);
v___x_133_ = lean_nat_add(v_p_125_, v_endPos_128_);
lean_dec(v_endPos_128_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_133_);
lean_ctor_set(v___x_130_, 0, v___x_132_);
v___x_135_ = v___x_130_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
else
{
lean_object* v_startPos_138_; lean_object* v_endPos_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_148_; 
v_startPos_138_ = lean_ctor_get(v_st_126_, 0);
v_endPos_139_ = lean_ctor_get(v_st_126_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_st_126_);
if (v_isSharedCheck_148_ == 0)
{
v___x_141_ = v_st_126_;
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_endPos_139_);
lean_inc(v_startPos_138_);
lean_dec(v_st_126_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_143_ = lean_nat_add(v_p_125_, v_startPos_138_);
lean_dec(v_startPos_138_);
v___x_144_ = lean_nat_add(v_p_125_, v_endPos_139_);
lean_dec(v_endPos_139_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v___x_144_);
lean_ctor_set(v___x_141_, 0, v___x_143_);
v___x_146_ = v___x_141_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg___boxed(lean_object* v_p_149_, lean_object* v_st_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_149_, v_st_150_);
lean_dec(v_p_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom(lean_object* v_s_152_, lean_object* v_p_153_, lean_object* v_st_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_153_, v_st_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_ofSliceFrom___boxed(lean_object* v_s_156_, lean_object* v_p_157_, lean_object* v_st_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom(v_s_156_, v_p_157_, v_st_158_);
lean_dec(v_p_157_);
lean_dec_ref(v_s_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___redArg(lean_object* v_st_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_){
_start:
{
if (lean_obj_tag(v_st_160_) == 0)
{
lean_object* v_startPos_163_; lean_object* v_endPos_164_; lean_object* v___x_165_; 
lean_dec(v_h__2_162_);
v_startPos_163_ = lean_ctor_get(v_st_160_, 0);
lean_inc(v_startPos_163_);
v_endPos_164_ = lean_ctor_get(v_st_160_, 1);
lean_inc(v_endPos_164_);
lean_dec_ref(v_st_160_);
v___x_165_ = lean_apply_2(v_h__1_161_, v_startPos_163_, v_endPos_164_);
return v___x_165_;
}
else
{
lean_object* v_startPos_166_; lean_object* v_endPos_167_; lean_object* v___x_168_; 
lean_dec(v_h__1_161_);
v_startPos_166_ = lean_ctor_get(v_st_160_, 0);
lean_inc(v_startPos_166_);
v_endPos_167_ = lean_ctor_get(v_st_160_, 1);
lean_inc(v_endPos_167_);
lean_dec_ref(v_st_160_);
v___x_168_ = lean_apply_2(v_h__2_162_, v_startPos_166_, v_endPos_167_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(lean_object* v_s_169_, lean_object* v_p_170_, lean_object* v_motive_171_, lean_object* v_st_172_, lean_object* v_h__1_173_, lean_object* v_h__2_174_){
_start:
{
if (lean_obj_tag(v_st_172_) == 0)
{
lean_object* v_startPos_175_; lean_object* v_endPos_176_; lean_object* v___x_177_; 
lean_dec(v_h__2_174_);
v_startPos_175_ = lean_ctor_get(v_st_172_, 0);
lean_inc(v_startPos_175_);
v_endPos_176_ = lean_ctor_get(v_st_172_, 1);
lean_inc(v_endPos_176_);
lean_dec_ref(v_st_172_);
v___x_177_ = lean_apply_2(v_h__1_173_, v_startPos_175_, v_endPos_176_);
return v___x_177_;
}
else
{
lean_object* v_startPos_178_; lean_object* v_endPos_179_; lean_object* v___x_180_; 
lean_dec(v_h__1_173_);
v_startPos_178_ = lean_ctor_get(v_st_172_, 0);
lean_inc(v_startPos_178_);
v_endPos_179_ = lean_ctor_get(v_st_172_, 1);
lean_inc(v_endPos_179_);
lean_dec_ref(v_st_172_);
v___x_180_ = lean_apply_2(v_h__2_174_, v_startPos_178_, v_endPos_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___boxed(lean_object* v_s_181_, lean_object* v_p_182_, lean_object* v_motive_183_, lean_object* v_st_184_, lean_object* v_h__1_185_, lean_object* v_h__2_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(v_s_181_, v_p_182_, v_motive_183_, v_st_184_, v_h__1_185_, v_h__2_186_);
lean_dec(v_p_182_);
lean_dec_ref(v_s_181_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(lean_object* v_inst_188_, lean_object* v_s_189_){
_start:
{
lean_object* v_skipPrefix_x3f_190_; lean_object* v___x_191_; 
v_skipPrefix_x3f_190_ = lean_ctor_get(v_inst_188_, 0);
lean_inc_ref(v_skipPrefix_x3f_190_);
lean_dec_ref(v_inst_188_);
v___x_191_ = lean_apply_1(v_skipPrefix_x3f_190_, v_s_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(lean_object* v_00_u03c1_192_, lean_object* v_pat_193_, lean_object* v_inst_194_, lean_object* v_s_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(v_inst_194_, v_s_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_197_, lean_object* v_pat_198_, lean_object* v_inst_199_, lean_object* v_s_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(v_00_u03c1_197_, v_pat_198_, v_inst_199_, v_s_200_);
lean_dec(v_pat_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_unsigned_to_nat(0u);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(v_a_206_, v_a_207_, v_a_208_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_unsigned_to_nat(0u);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(v_a_214_, v_a_215_, v_a_216_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(lean_object* v_00_u03c1_218_, lean_object* v_pat_219_, lean_object* v_s_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_unsigned_to_nat(0u);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object* v_00_u03c1_222_, lean_object* v_pat_223_, lean_object* v_s_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(v_00_u03c1_222_, v_pat_223_, v_s_224_);
lean_dec_ref(v_s_224_);
lean_dec(v_pat_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(lean_object* v_s_226_, lean_object* v_inst_227_, lean_object* v_it_228_){
_start:
{
lean_object* v_str_229_; lean_object* v_startInclusive_230_; lean_object* v_endExclusive_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_252_; 
v_str_229_ = lean_ctor_get(v_s_226_, 0);
v_startInclusive_230_ = lean_ctor_get(v_s_226_, 1);
v_endExclusive_231_ = lean_ctor_get(v_s_226_, 2);
v_isSharedCheck_252_ = !lean_is_exclusive(v_s_226_);
if (v_isSharedCheck_252_ == 0)
{
v___x_233_ = v_s_226_;
v_isShared_234_ = v_isSharedCheck_252_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_endExclusive_231_);
lean_inc(v_startInclusive_230_);
lean_inc(v_str_229_);
lean_dec(v_s_226_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_252_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_nat_sub(v_endExclusive_231_, v_startInclusive_230_);
v___x_236_ = lean_nat_dec_eq(v_it_228_, v___x_235_);
lean_dec(v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v_skipPrefixOfNonempty_x3f_237_ = lean_ctor_get(v_inst_227_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_237_);
lean_dec_ref(v_inst_227_);
v___x_238_ = lean_nat_add(v_startInclusive_230_, v_it_228_);
lean_inc(v___x_238_);
lean_inc_ref(v_str_229_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_238_);
v___x_240_ = v___x_233_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_str_229_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_endExclusive_231_);
v___x_240_ = v_reuseFailAlloc_250_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; 
v___x_241_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_237_, v___x_240_, lean_box(0));
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = lean_string_utf8_next_fast(v_str_229_, v___x_238_);
lean_dec(v___x_238_);
lean_dec_ref(v_str_229_);
v___x_243_ = lean_nat_sub(v___x_242_, v_startInclusive_230_);
lean_dec(v_startInclusive_230_);
lean_inc(v___x_243_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v_it_228_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
return v___x_245_;
}
else
{
lean_object* v_val_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v___x_238_);
lean_dec(v_startInclusive_230_);
lean_dec_ref(v_str_229_);
v_val_246_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_val_246_);
lean_dec_ref(v___x_241_);
v___x_247_ = lean_nat_add(v_it_228_, v_val_246_);
lean_dec(v_val_246_);
lean_inc(v___x_247_);
v___x_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_248_, 0, v_it_228_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
return v___x_249_;
}
}
}
else
{
lean_object* v___x_251_; 
lean_del_object(v___x_233_);
lean_dec(v_endExclusive_231_);
lean_dec(v_startInclusive_230_);
lean_dec_ref(v_str_229_);
lean_dec(v_it_228_);
lean_dec_ref(v_inst_227_);
v___x_251_ = lean_box(2);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(lean_object* v_s_253_, lean_object* v_inst_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_255_, 0, v_s_253_);
lean_closure_set(v___f_255_, 1, v_inst_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(lean_object* v_00_u03c1_256_, lean_object* v_pat_257_, lean_object* v_s_258_, lean_object* v_inst_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_260_, 0, v_s_258_);
lean_closure_set(v___f_260_, 1, v_inst_259_);
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(lean_object* v_00_u03c1_261_, lean_object* v_pat_262_, lean_object* v_s_263_, lean_object* v_inst_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(v_00_u03c1_261_, v_pat_262_, v_s_263_, v_inst_264_);
lean_dec(v_pat_262_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(lean_object* v_00_u03c1_266_, lean_object* v_pat_267_, lean_object* v_s_268_, lean_object* v_inst_269_, lean_object* v_inst_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_box(0);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_272_, lean_object* v_pat_273_, lean_object* v_s_274_, lean_object* v_inst_275_, lean_object* v_inst_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(v_00_u03c1_272_, v_pat_273_, v_s_274_, v_inst_275_, v_inst_276_);
lean_dec_ref(v_inst_275_);
lean_dec_ref(v_s_274_);
lean_dec(v_pat_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v___y_278_, lean_object* v_acc_279_, lean_object* v_recur_280_, lean_object* v_s_281_){
_start:
{
switch(lean_obj_tag(v_s_281_))
{
case 0:
{
lean_object* v_it_282_; lean_object* v_out_283_; lean_object* v_val_284_; 
v_it_282_ = lean_ctor_get(v_s_281_, 0);
lean_inc(v_it_282_);
v_out_283_ = lean_ctor_get(v_s_281_, 1);
lean_inc(v_out_283_);
lean_dec_ref(v_s_281_);
v_val_284_ = lean_apply_3(v___y_278_, v_out_283_, lean_box(0), v_acc_279_);
if (lean_obj_tag(v_val_284_) == 0)
{
lean_object* v_a_285_; 
lean_dec(v_it_282_);
lean_dec(v_recur_280_);
v_a_285_ = lean_ctor_get(v_val_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref(v_val_284_);
return v_a_285_;
}
else
{
lean_object* v_a_286_; lean_object* v___x_287_; 
v_a_286_ = lean_ctor_get(v_val_284_, 0);
lean_inc(v_a_286_);
lean_dec_ref(v_val_284_);
v___x_287_ = lean_apply_4(v_recur_280_, v_it_282_, v_a_286_, lean_box(0), lean_box(0));
return v___x_287_;
}
}
case 1:
{
lean_object* v_it_288_; lean_object* v___x_289_; 
lean_dec_ref(v___y_278_);
v_it_288_ = lean_ctor_get(v_s_281_, 0);
lean_inc(v_it_288_);
lean_dec_ref(v_s_281_);
v___x_289_ = lean_apply_4(v_recur_280_, v_it_288_, v_acc_279_, lean_box(0), lean_box(0));
return v___x_289_;
}
default: 
{
lean_dec(v_recur_280_);
lean_dec_ref(v___y_278_);
return v_acc_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v_s_290_, lean_object* v___y_291_, lean_object* v_inst_292_, lean_object* v_lift_293_, lean_object* v_it_294_, lean_object* v_acc_295_, lean_object* v_hP_296_, lean_object* v_recur_297_){
_start:
{
lean_object* v_str_298_; lean_object* v_startInclusive_299_; lean_object* v_endExclusive_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_325_; 
v_str_298_ = lean_ctor_get(v_s_290_, 0);
v_startInclusive_299_ = lean_ctor_get(v_s_290_, 1);
v_endExclusive_300_ = lean_ctor_get(v_s_290_, 2);
v_isSharedCheck_325_ = !lean_is_exclusive(v_s_290_);
if (v_isSharedCheck_325_ == 0)
{
v___x_302_ = v_s_290_;
v_isShared_303_ = v_isSharedCheck_325_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_endExclusive_300_);
lean_inc(v_startInclusive_299_);
lean_inc(v_str_298_);
lean_dec(v_s_290_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_325_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___f_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___f_304_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_304_, 0, v___y_291_);
lean_closure_set(v___f_304_, 1, v_acc_295_);
lean_closure_set(v___f_304_, 2, v_recur_297_);
v___x_305_ = lean_nat_sub(v_endExclusive_300_, v_startInclusive_299_);
v___x_306_ = lean_nat_dec_eq(v_it_294_, v___x_305_);
lean_dec(v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v_skipPrefixOfNonempty_x3f_307_ = lean_ctor_get(v_inst_292_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_307_);
lean_dec_ref(v_inst_292_);
v___x_308_ = lean_nat_add(v_startInclusive_299_, v_it_294_);
lean_inc(v___x_308_);
lean_inc_ref(v_str_298_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_308_);
v___x_310_ = v___x_302_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_str_298_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_endExclusive_300_);
v___x_310_ = v_reuseFailAlloc_322_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; 
v___x_311_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_307_, v___x_310_, lean_box(0));
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_312_ = lean_string_utf8_next_fast(v_str_298_, v___x_308_);
lean_dec(v___x_308_);
lean_dec_ref(v_str_298_);
v___x_313_ = lean_nat_sub(v___x_312_, v_startInclusive_299_);
lean_dec(v_startInclusive_299_);
lean_inc(v___x_313_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v_it_294_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_apply_4(v_lift_293_, lean_box(0), lean_box(0), v___f_304_, v___x_315_);
return v___x_316_;
}
else
{
lean_object* v_val_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec(v___x_308_);
lean_dec(v_startInclusive_299_);
lean_dec_ref(v_str_298_);
v_val_317_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v___x_311_);
v___x_318_ = lean_nat_add(v_it_294_, v_val_317_);
lean_dec(v_val_317_);
lean_inc(v___x_318_);
v___x_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_319_, 0, v_it_294_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_apply_4(v_lift_293_, lean_box(0), lean_box(0), v___f_304_, v___x_320_);
return v___x_321_;
}
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_del_object(v___x_302_);
lean_dec(v_endExclusive_300_);
lean_dec(v_startInclusive_299_);
lean_dec_ref(v_str_298_);
lean_dec(v_it_294_);
lean_dec_ref(v_inst_292_);
v___x_323_ = lean_box(2);
v___x_324_ = lean_apply_4(v_lift_293_, lean_box(0), lean_box(0), v___f_304_, v___x_323_);
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object* v_s_326_, lean_object* v_inst_327_, lean_object* v_lift_328_, lean_object* v_00_u03b3_329_, lean_object* v_Pl_330_, lean_object* v_it_331_, lean_object* v_init_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___f_334_; lean_object* v___x_335_; 
v___f_334_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1), 8, 4);
lean_closure_set(v___f_334_, 0, v_s_326_);
lean_closure_set(v___f_334_, 1, v___y_333_);
lean_closure_set(v___f_334_, 2, v_inst_327_);
lean_closure_set(v___f_334_, 3, v_lift_328_);
v___x_335_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_334_, v_it_331_, v_init_332_, lean_box(0));
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_336_, lean_object* v_inst_337_){
_start:
{
lean_object* v___f_338_; 
v___f_338_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_338_, 0, v_s_336_);
lean_closure_set(v___f_338_, 1, v_inst_337_);
return v___f_338_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_339_, lean_object* v_pat_340_, lean_object* v_s_341_, lean_object* v_inst_342_){
_start:
{
lean_object* v___f_343_; 
v___f_343_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_343_, 0, v_s_341_);
lean_closure_set(v___f_343_, 1, v_inst_342_);
return v___f_343_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_344_, lean_object* v_pat_345_, lean_object* v_s_346_, lean_object* v_inst_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_344_, v_pat_345_, v_s_346_, v_inst_347_);
lean_dec(v_pat_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(lean_object* v_pat_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_350_, 0, lean_box(0));
lean_closure_set(v___x_350_, 1, v_pat_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(lean_object* v_00_u03c1_351_, lean_object* v_pat_352_, lean_object* v_inst_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_354_, 0, lean_box(0));
lean_closure_set(v___x_354_, 1, v_pat_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_355_, lean_object* v_pat_356_, lean_object* v_inst_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(v_00_u03c1_355_, v_pat_356_, v_inst_357_);
lean_dec_ref(v_inst_357_);
return v_res_358_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(lean_object* v_lhs_359_, lean_object* v_rhs_360_, lean_object* v_lstart_361_, lean_object* v_rstart_362_, lean_object* v_len_363_, lean_object* v_curr_364_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = l_String_instDecidableLtRaw___aux__1(v_curr_364_, v_len_363_);
if (v___x_365_ == 0)
{
uint8_t v___x_366_; 
lean_dec(v_curr_364_);
v___x_366_ = 1;
return v___x_366_;
}
else
{
lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; uint8_t v___x_371_; 
v___x_367_ = lean_nat_add(v_lstart_361_, v_curr_364_);
v___x_368_ = lean_string_get_byte_fast(v_lhs_359_, v___x_367_);
v___x_369_ = lean_nat_add(v_rstart_362_, v_curr_364_);
v___x_370_ = lean_string_get_byte_fast(v_rhs_360_, v___x_369_);
v___x_371_ = lean_uint8_dec_eq(v___x_368_, v___x_370_);
if (v___x_371_ == 0)
{
lean_dec(v_curr_364_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(1u);
v___x_373_ = lean_nat_add(v_curr_364_, v___x_372_);
lean_dec(v_curr_364_);
v_curr_364_ = v___x_373_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg___boxed(lean_object* v_lhs_375_, lean_object* v_rhs_376_, lean_object* v_lstart_377_, lean_object* v_rstart_378_, lean_object* v_len_379_, lean_object* v_curr_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_375_, v_rhs_376_, v_lstart_377_, v_rstart_378_, v_len_379_, v_curr_380_);
lean_dec(v_len_379_);
lean_dec(v_rstart_378_);
lean_dec(v_lstart_377_);
lean_dec_ref(v_rhs_376_);
lean_dec_ref(v_lhs_375_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object* v_lhs_383_, lean_object* v_rhs_384_, lean_object* v_lstart_385_, lean_object* v_rstart_386_, lean_object* v_len_387_, lean_object* v_h1_388_, lean_object* v_h2_389_, lean_object* v_curr_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_383_, v_rhs_384_, v_lstart_385_, v_rstart_386_, v_len_387_, v_curr_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object* v_lhs_392_, lean_object* v_rhs_393_, lean_object* v_lstart_394_, lean_object* v_rstart_395_, lean_object* v_len_396_, lean_object* v_h1_397_, lean_object* v_h2_398_, lean_object* v_curr_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(v_lhs_392_, v_rhs_393_, v_lstart_394_, v_rstart_395_, v_len_396_, v_h1_397_, v_h2_398_, v_curr_399_);
lean_dec(v_len_396_);
lean_dec(v_rstart_395_);
lean_dec(v_lstart_394_);
lean_dec_ref(v_rhs_393_);
lean_dec_ref(v_lhs_392_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object* v_lhs_409_, lean_object* v_rhs_410_, lean_object* v_lstart_411_, lean_object* v_rstart_412_, lean_object* v_len_413_, lean_object* v_h1_414_, lean_object* v_h2_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = lean_string_memcmp(v_lhs_409_, v_rhs_410_, v_lstart_411_, v_rstart_412_, v_len_413_);
lean_dec(v_len_413_);
lean_dec(v_rstart_412_);
lean_dec(v_lstart_411_);
lean_dec_ref(v_rhs_410_);
lean_dec_ref(v_lhs_409_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object* v_lhs_418_, lean_object* v_rhs_419_, lean_object* v_lstart_420_, lean_object* v_rstart_421_, lean_object* v_len_422_){
_start:
{
lean_object* v_str_423_; lean_object* v_startInclusive_424_; lean_object* v_str_425_; lean_object* v_startInclusive_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_str_423_ = lean_ctor_get(v_lhs_418_, 0);
v_startInclusive_424_ = lean_ctor_get(v_lhs_418_, 1);
v_str_425_ = lean_ctor_get(v_rhs_419_, 0);
v_startInclusive_426_ = lean_ctor_get(v_rhs_419_, 1);
v___x_427_ = lean_nat_add(v_startInclusive_424_, v_lstart_420_);
v___x_428_ = lean_nat_add(v_startInclusive_426_, v_rstart_421_);
v___x_429_ = lean_string_memcmp(v_str_423_, v_str_425_, v___x_427_, v___x_428_, v_len_422_);
lean_dec(v___x_428_);
lean_dec(v___x_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object* v_lhs_430_, lean_object* v_rhs_431_, lean_object* v_lstart_432_, lean_object* v_rstart_433_, lean_object* v_len_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(v_lhs_430_, v_rhs_431_, v_lstart_432_, v_rstart_433_, v_len_434_);
lean_dec(v_len_434_);
lean_dec(v_rstart_433_);
lean_dec(v_lstart_432_);
lean_dec_ref(v_rhs_431_);
lean_dec_ref(v_lhs_430_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object* v_lhs_437_, lean_object* v_rhs_438_, lean_object* v_lstart_439_, lean_object* v_rstart_440_, lean_object* v_len_441_, lean_object* v_h1_442_, lean_object* v_h2_443_){
_start:
{
lean_object* v_str_444_; lean_object* v_startInclusive_445_; lean_object* v_str_446_; lean_object* v_startInclusive_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_str_444_ = lean_ctor_get(v_lhs_437_, 0);
v_startInclusive_445_ = lean_ctor_get(v_lhs_437_, 1);
v_str_446_ = lean_ctor_get(v_rhs_438_, 0);
v_startInclusive_447_ = lean_ctor_get(v_rhs_438_, 1);
v___x_448_ = lean_nat_add(v_startInclusive_445_, v_lstart_439_);
v___x_449_ = lean_nat_add(v_startInclusive_447_, v_rstart_440_);
v___x_450_ = lean_string_memcmp(v_str_444_, v_str_446_, v___x_448_, v___x_449_, v_len_441_);
lean_dec(v___x_449_);
lean_dec(v___x_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object* v_lhs_451_, lean_object* v_rhs_452_, lean_object* v_lstart_453_, lean_object* v_rstart_454_, lean_object* v_len_455_, lean_object* v_h1_456_, lean_object* v_h2_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_String_Slice_Pattern_Internal_memcmpSlice(v_lhs_451_, v_rhs_452_, v_lstart_453_, v_rstart_454_, v_len_455_, v_h1_456_, v_h2_457_);
lean_dec(v_len_455_);
lean_dec(v_rstart_454_);
lean_dec(v_lstart_453_);
lean_dec_ref(v_rhs_452_);
lean_dec_ref(v_lhs_451_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_unsigned_to_nat(0u);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(v_a_464_, v_a_465_, v_a_466_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_unsigned_to_nat(0u);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(v_a_472_, v_a_473_, v_a_474_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(lean_object* v_s_476_){
_start:
{
lean_object* v_startInclusive_477_; lean_object* v_endExclusive_478_; lean_object* v___x_479_; 
v_startInclusive_477_ = lean_ctor_get(v_s_476_, 1);
v_endExclusive_478_ = lean_ctor_get(v_s_476_, 2);
v___x_479_ = lean_nat_sub(v_endExclusive_478_, v_startInclusive_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(lean_object* v_s_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_480_);
lean_dec_ref(v_s_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(lean_object* v_00_u03c1_482_, lean_object* v_pat_483_, lean_object* v_s_484_){
_start:
{
lean_object* v_startInclusive_485_; lean_object* v_endExclusive_486_; lean_object* v___x_487_; 
v_startInclusive_485_ = lean_ctor_get(v_s_484_, 1);
v_endExclusive_486_ = lean_ctor_get(v_s_484_, 2);
v___x_487_ = lean_nat_sub(v_endExclusive_486_, v_startInclusive_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object* v_00_u03c1_488_, lean_object* v_pat_489_, lean_object* v_s_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(v_00_u03c1_488_, v_pat_489_, v_s_490_);
lean_dec_ref(v_s_490_);
lean_dec(v_pat_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(lean_object* v_inst_492_, lean_object* v_s_493_, lean_object* v_it_494_){
_start:
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_nat_dec_eq(v_it_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_516_; 
v_skipSuffixOfNonempty_x3f_497_ = lean_ctor_get(v_inst_492_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_inst_492_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; lean_object* v_unused_518_; 
v_unused_517_ = lean_ctor_get(v_inst_492_, 2);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_inst_492_, 0);
lean_dec(v_unused_518_);
v___x_499_ = v_inst_492_;
v_isShared_500_ = v_isSharedCheck_516_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_497_);
lean_dec(v_inst_492_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_516_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_str_501_; lean_object* v_startInclusive_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v_str_501_ = lean_ctor_get(v_s_493_, 0);
v_startInclusive_502_ = lean_ctor_get(v_s_493_, 1);
v___x_503_ = lean_nat_add(v_startInclusive_502_, v_it_494_);
lean_inc(v_startInclusive_502_);
lean_inc_ref(v_str_501_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 2, v___x_503_);
lean_ctor_set(v___x_499_, 1, v_startInclusive_502_);
lean_ctor_set(v___x_499_, 0, v_str_501_);
v___x_505_ = v___x_499_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_str_501_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_startInclusive_502_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v___x_503_);
v___x_505_ = v_reuseFailAlloc_515_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; 
v___x_506_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_497_, v___x_505_, lean_box(0));
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_sub(v_it_494_, v___x_507_);
v___x_509_ = l_String_Slice_posLE(v_s_493_, v___x_508_);
lean_inc(v___x_509_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_it_494_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v_val_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_val_512_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_val_512_);
lean_dec_ref(v___x_506_);
lean_inc(v_val_512_);
v___x_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_513_, 0, v_val_512_);
lean_ctor_set(v___x_513_, 1, v_it_494_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v_val_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
return v___x_514_;
}
}
}
}
else
{
lean_object* v___x_519_; 
lean_dec(v_it_494_);
lean_dec_ref(v_inst_492_);
v___x_519_ = lean_box(2);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(lean_object* v_inst_520_, lean_object* v_s_521_, lean_object* v_it_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_520_, v_s_521_, v_it_522_);
lean_dec_ref(v_s_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(lean_object* v_s_524_, lean_object* v_inst_525_){
_start:
{
lean_object* v___f_526_; 
v___f_526_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_526_, 0, v_inst_525_);
lean_closure_set(v___f_526_, 1, v_s_524_);
return v___f_526_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(lean_object* v_00_u03c1_527_, lean_object* v_pat_528_, lean_object* v_s_529_, lean_object* v_inst_530_){
_start:
{
lean_object* v___f_531_; 
v___f_531_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_531_, 0, v_inst_530_);
lean_closure_set(v___f_531_, 1, v_s_529_);
return v___f_531_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(lean_object* v_00_u03c1_532_, lean_object* v_pat_533_, lean_object* v_s_534_, lean_object* v_inst_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_532_, v_pat_533_, v_s_534_, v_inst_535_);
lean_dec(v_pat_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(lean_object* v_00_u03c1_537_, lean_object* v_pat_538_, lean_object* v_s_539_, lean_object* v_inst_540_, lean_object* v_inst_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_box(0);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_543_, lean_object* v_pat_544_, lean_object* v_s_545_, lean_object* v_inst_546_, lean_object* v_inst_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(v_00_u03c1_543_, v_pat_544_, v_s_545_, v_inst_546_, v_inst_547_);
lean_dec_ref(v_inst_546_);
lean_dec_ref(v_s_545_);
lean_dec(v_pat_544_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v___y_549_, lean_object* v_inst_550_, lean_object* v_s_551_, lean_object* v_lift_552_, lean_object* v_it_553_, lean_object* v_acc_554_, lean_object* v_hP_555_, lean_object* v_recur_556_){
_start:
{
lean_object* v___f_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___f_557_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_557_, 0, v___y_549_);
lean_closure_set(v___f_557_, 1, v_acc_554_);
lean_closure_set(v___f_557_, 2, v_recur_556_);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_nat_dec_eq(v_it_553_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_581_; 
v_skipSuffixOfNonempty_x3f_560_ = lean_ctor_get(v_inst_550_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v_inst_550_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; lean_object* v_unused_583_; 
v_unused_582_ = lean_ctor_get(v_inst_550_, 2);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_inst_550_, 0);
lean_dec(v_unused_583_);
v___x_562_ = v_inst_550_;
v_isShared_563_ = v_isSharedCheck_581_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_560_);
lean_dec(v_inst_550_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_581_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_str_564_; lean_object* v_startInclusive_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v_str_564_ = lean_ctor_get(v_s_551_, 0);
v_startInclusive_565_ = lean_ctor_get(v_s_551_, 1);
v___x_566_ = lean_nat_add(v_startInclusive_565_, v_it_553_);
lean_inc(v_startInclusive_565_);
lean_inc_ref(v_str_564_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 2, v___x_566_);
lean_ctor_set(v___x_562_, 1, v_startInclusive_565_);
lean_ctor_set(v___x_562_, 0, v_str_564_);
v___x_568_ = v___x_562_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_str_564_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_startInclusive_565_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v___x_566_);
v___x_568_ = v_reuseFailAlloc_580_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; 
v___x_569_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_560_, v___x_568_, lean_box(0));
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_sub(v_it_553_, v___x_570_);
v___x_572_ = l_String_Slice_posLE(v_s_551_, v___x_571_);
lean_inc(v___x_572_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v_it_553_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_apply_4(v_lift_552_, lean_box(0), lean_box(0), v___f_557_, v___x_574_);
return v___x_575_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_val_576_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_val_576_);
lean_dec_ref(v___x_569_);
lean_inc(v_val_576_);
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v_val_576_);
lean_ctor_set(v___x_577_, 1, v_it_553_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_val_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_apply_4(v_lift_552_, lean_box(0), lean_box(0), v___f_557_, v___x_578_);
return v___x_579_;
}
}
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_it_553_);
lean_dec_ref(v_inst_550_);
v___x_584_ = lean_box(2);
v___x_585_ = lean_apply_4(v_lift_552_, lean_box(0), lean_box(0), v___f_557_, v___x_584_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed(lean_object* v___y_586_, lean_object* v_inst_587_, lean_object* v_s_588_, lean_object* v_lift_589_, lean_object* v_it_590_, lean_object* v_acc_591_, lean_object* v_hP_592_, lean_object* v_recur_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(v___y_586_, v_inst_587_, v_s_588_, v_lift_589_, v_it_590_, v_acc_591_, v_hP_592_, v_recur_593_);
lean_dec_ref(v_s_588_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v_inst_595_, lean_object* v_s_596_, lean_object* v_lift_597_, lean_object* v_00_u03b3_598_, lean_object* v_Pl_599_, lean_object* v_it_600_, lean_object* v_init_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___f_603_; lean_object* v___x_604_; 
v___f_603_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_603_, 0, v___y_602_);
lean_closure_set(v___f_603_, 1, v_inst_595_);
lean_closure_set(v___f_603_, 2, v_s_596_);
lean_closure_set(v___f_603_, 3, v_lift_597_);
v___x_604_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_603_, v_it_600_, v_init_601_, lean_box(0));
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_605_, lean_object* v_inst_606_){
_start:
{
lean_object* v___f_607_; 
v___f_607_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_607_, 0, v_inst_606_);
lean_closure_set(v___f_607_, 1, v_s_605_);
return v___f_607_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_608_, lean_object* v_pat_609_, lean_object* v_s_610_, lean_object* v_inst_611_){
_start:
{
lean_object* v___f_612_; 
v___f_612_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_612_, 0, v_inst_611_);
lean_closure_set(v___f_612_, 1, v_s_610_);
return v___f_612_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_613_, lean_object* v_pat_614_, lean_object* v_s_615_, lean_object* v_inst_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_613_, v_pat_614_, v_s_615_, v_inst_616_);
lean_dec(v_pat_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(lean_object* v_pat_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_619_, 0, lean_box(0));
lean_closure_set(v___x_619_, 1, v_pat_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(lean_object* v_00_u03c1_620_, lean_object* v_pat_621_, lean_object* v_inst_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_623_, 0, lean_box(0));
lean_closure_set(v___x_623_, 1, v_pat_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_624_, lean_object* v_pat_625_, lean_object* v_inst_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(v_00_u03c1_624_, v_pat_625_, v_inst_626_);
lean_dec_ref(v_inst_626_);
return v_res_627_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Pattern_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
