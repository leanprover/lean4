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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* v___x_175_; 
v___x_175_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___redArg(v_st_172_, v_h__1_173_, v_h__2_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___boxed(lean_object* v_s_176_, lean_object* v_p_177_, lean_object* v_motive_178_, lean_object* v_st_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(v_s_176_, v_p_177_, v_motive_178_, v_st_179_, v_h__1_180_, v_h__2_181_);
lean_dec(v_p_177_);
lean_dec_ref(v_s_176_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(lean_object* v_inst_183_, lean_object* v_s_184_){
_start:
{
lean_object* v_skipPrefix_x3f_185_; lean_object* v___x_186_; 
v_skipPrefix_x3f_185_ = lean_ctor_get(v_inst_183_, 0);
lean_inc_ref(v_skipPrefix_x3f_185_);
lean_dec_ref(v_inst_183_);
v___x_186_ = lean_apply_1(v_skipPrefix_x3f_185_, v_s_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(lean_object* v_00_u03c1_187_, lean_object* v_pat_188_, lean_object* v_inst_189_, lean_object* v_s_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(v_inst_189_, v_s_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_192_, lean_object* v_pat_193_, lean_object* v_inst_194_, lean_object* v_s_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(v_00_u03c1_192_, v_pat_193_, v_inst_194_, v_s_195_);
lean_dec(v_pat_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_unsigned_to_nat(0u);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(v_a_201_, v_a_202_, v_a_203_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(0u);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(v_a_209_, v_a_210_, v_a_211_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(lean_object* v_00_u03c1_213_, lean_object* v_pat_214_, lean_object* v_s_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_unsigned_to_nat(0u);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object* v_00_u03c1_217_, lean_object* v_pat_218_, lean_object* v_s_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(v_00_u03c1_217_, v_pat_218_, v_s_219_);
lean_dec_ref(v_s_219_);
lean_dec(v_pat_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(lean_object* v_s_221_, lean_object* v_inst_222_, lean_object* v_it_223_){
_start:
{
lean_object* v_str_224_; lean_object* v_startInclusive_225_; lean_object* v_endExclusive_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_247_; 
v_str_224_ = lean_ctor_get(v_s_221_, 0);
v_startInclusive_225_ = lean_ctor_get(v_s_221_, 1);
v_endExclusive_226_ = lean_ctor_get(v_s_221_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v_s_221_);
if (v_isSharedCheck_247_ == 0)
{
v___x_228_ = v_s_221_;
v_isShared_229_ = v_isSharedCheck_247_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_endExclusive_226_);
lean_inc(v_startInclusive_225_);
lean_inc(v_str_224_);
lean_dec(v_s_221_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_247_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_nat_sub(v_endExclusive_226_, v_startInclusive_225_);
v___x_231_ = lean_nat_dec_eq(v_it_223_, v___x_230_);
lean_dec(v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v_skipPrefixOfNonempty_x3f_232_ = lean_ctor_get(v_inst_222_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_232_);
lean_dec_ref(v_inst_222_);
v___x_233_ = lean_nat_add(v_startInclusive_225_, v_it_223_);
lean_inc(v___x_233_);
lean_inc_ref(v_str_224_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___x_233_);
v___x_235_ = v___x_228_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_str_224_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_endExclusive_226_);
v___x_235_ = v_reuseFailAlloc_245_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; 
v___x_236_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_232_, v___x_235_, lean_box(0));
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_237_ = lean_string_utf8_next_fast(v_str_224_, v___x_233_);
lean_dec(v___x_233_);
lean_dec_ref(v_str_224_);
v___x_238_ = lean_nat_sub(v___x_237_, v_startInclusive_225_);
lean_dec(v_startInclusive_225_);
lean_inc(v___x_238_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_it_223_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v_val_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v___x_233_);
lean_dec(v_startInclusive_225_);
lean_dec_ref(v_str_224_);
v_val_241_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_241_);
lean_dec_ref(v___x_236_);
v___x_242_ = lean_nat_add(v_it_223_, v_val_241_);
lean_dec(v_val_241_);
lean_inc(v___x_242_);
v___x_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_243_, 0, v_it_223_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
return v___x_244_;
}
}
}
else
{
lean_object* v___x_246_; 
lean_del_object(v___x_228_);
lean_dec(v_endExclusive_226_);
lean_dec(v_startInclusive_225_);
lean_dec_ref(v_str_224_);
lean_dec(v_it_223_);
lean_dec_ref(v_inst_222_);
v___x_246_ = lean_box(2);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(lean_object* v_s_248_, lean_object* v_inst_249_){
_start:
{
lean_object* v___f_250_; 
v___f_250_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_250_, 0, v_s_248_);
lean_closure_set(v___f_250_, 1, v_inst_249_);
return v___f_250_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(lean_object* v_00_u03c1_251_, lean_object* v_pat_252_, lean_object* v_s_253_, lean_object* v_inst_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_255_, 0, v_s_253_);
lean_closure_set(v___f_255_, 1, v_inst_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(lean_object* v_00_u03c1_256_, lean_object* v_pat_257_, lean_object* v_s_258_, lean_object* v_inst_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(v_00_u03c1_256_, v_pat_257_, v_s_258_, v_inst_259_);
lean_dec(v_pat_257_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(lean_object* v_00_u03c1_261_, lean_object* v_pat_262_, lean_object* v_s_263_, lean_object* v_inst_264_, lean_object* v_inst_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_267_, lean_object* v_pat_268_, lean_object* v_s_269_, lean_object* v_inst_270_, lean_object* v_inst_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(v_00_u03c1_267_, v_pat_268_, v_s_269_, v_inst_270_, v_inst_271_);
lean_dec_ref(v_inst_270_);
lean_dec_ref(v_s_269_);
lean_dec(v_pat_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v___y_273_, lean_object* v_acc_274_, lean_object* v_recur_275_, lean_object* v_s_276_){
_start:
{
switch(lean_obj_tag(v_s_276_))
{
case 0:
{
lean_object* v_it_277_; lean_object* v_out_278_; lean_object* v_val_279_; 
v_it_277_ = lean_ctor_get(v_s_276_, 0);
lean_inc(v_it_277_);
v_out_278_ = lean_ctor_get(v_s_276_, 1);
lean_inc(v_out_278_);
lean_dec_ref(v_s_276_);
v_val_279_ = lean_apply_3(v___y_273_, v_out_278_, lean_box(0), v_acc_274_);
if (lean_obj_tag(v_val_279_) == 0)
{
lean_object* v_a_280_; 
lean_dec(v_it_277_);
lean_dec(v_recur_275_);
v_a_280_ = lean_ctor_get(v_val_279_, 0);
lean_inc(v_a_280_);
lean_dec_ref(v_val_279_);
return v_a_280_;
}
else
{
lean_object* v_a_281_; lean_object* v___x_282_; 
v_a_281_ = lean_ctor_get(v_val_279_, 0);
lean_inc(v_a_281_);
lean_dec_ref(v_val_279_);
v___x_282_ = lean_apply_4(v_recur_275_, v_it_277_, v_a_281_, lean_box(0), lean_box(0));
return v___x_282_;
}
}
case 1:
{
lean_object* v_it_283_; lean_object* v___x_284_; 
lean_dec_ref(v___y_273_);
v_it_283_ = lean_ctor_get(v_s_276_, 0);
lean_inc(v_it_283_);
lean_dec_ref(v_s_276_);
v___x_284_ = lean_apply_4(v_recur_275_, v_it_283_, v_acc_274_, lean_box(0), lean_box(0));
return v___x_284_;
}
default: 
{
lean_dec(v_recur_275_);
lean_dec_ref(v___y_273_);
return v_acc_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v_s_285_, lean_object* v___y_286_, lean_object* v_inst_287_, lean_object* v_lift_288_, lean_object* v_it_289_, lean_object* v_acc_290_, lean_object* v_hP_291_, lean_object* v_recur_292_){
_start:
{
lean_object* v_str_293_; lean_object* v_startInclusive_294_; lean_object* v_endExclusive_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_320_; 
v_str_293_ = lean_ctor_get(v_s_285_, 0);
v_startInclusive_294_ = lean_ctor_get(v_s_285_, 1);
v_endExclusive_295_ = lean_ctor_get(v_s_285_, 2);
v_isSharedCheck_320_ = !lean_is_exclusive(v_s_285_);
if (v_isSharedCheck_320_ == 0)
{
v___x_297_ = v_s_285_;
v_isShared_298_ = v_isSharedCheck_320_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_endExclusive_295_);
lean_inc(v_startInclusive_294_);
lean_inc(v_str_293_);
lean_dec(v_s_285_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_320_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___f_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___f_299_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_299_, 0, v___y_286_);
lean_closure_set(v___f_299_, 1, v_acc_290_);
lean_closure_set(v___f_299_, 2, v_recur_292_);
v___x_300_ = lean_nat_sub(v_endExclusive_295_, v_startInclusive_294_);
v___x_301_ = lean_nat_dec_eq(v_it_289_, v___x_300_);
lean_dec(v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v_skipPrefixOfNonempty_x3f_302_ = lean_ctor_get(v_inst_287_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_302_);
lean_dec_ref(v_inst_287_);
v___x_303_ = lean_nat_add(v_startInclusive_294_, v_it_289_);
lean_inc(v___x_303_);
lean_inc_ref(v_str_293_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_303_);
v___x_305_ = v___x_297_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_str_293_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_endExclusive_295_);
v___x_305_ = v_reuseFailAlloc_317_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; 
v___x_306_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_302_, v___x_305_, lean_box(0));
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_307_ = lean_string_utf8_next_fast(v_str_293_, v___x_303_);
lean_dec(v___x_303_);
lean_dec_ref(v_str_293_);
v___x_308_ = lean_nat_sub(v___x_307_, v_startInclusive_294_);
lean_dec(v_startInclusive_294_);
lean_inc(v___x_308_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_it_289_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_apply_4(v_lift_288_, lean_box(0), lean_box(0), v___f_299_, v___x_310_);
return v___x_311_;
}
else
{
lean_object* v_val_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v___x_303_);
lean_dec(v_startInclusive_294_);
lean_dec_ref(v_str_293_);
v_val_312_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_312_);
lean_dec_ref(v___x_306_);
v___x_313_ = lean_nat_add(v_it_289_, v_val_312_);
lean_dec(v_val_312_);
lean_inc(v___x_313_);
v___x_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_314_, 0, v_it_289_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_apply_4(v_lift_288_, lean_box(0), lean_box(0), v___f_299_, v___x_315_);
return v___x_316_;
}
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_del_object(v___x_297_);
lean_dec(v_endExclusive_295_);
lean_dec(v_startInclusive_294_);
lean_dec_ref(v_str_293_);
lean_dec(v_it_289_);
lean_dec_ref(v_inst_287_);
v___x_318_ = lean_box(2);
v___x_319_ = lean_apply_4(v_lift_288_, lean_box(0), lean_box(0), v___f_299_, v___x_318_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object* v_s_321_, lean_object* v_inst_322_, lean_object* v_lift_323_, lean_object* v_00_u03b3_324_, lean_object* v_Pl_325_, lean_object* v_it_326_, lean_object* v_init_327_, lean_object* v___y_328_){
_start:
{
lean_object* v___f_329_; lean_object* v___x_330_; 
v___f_329_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1), 8, 4);
lean_closure_set(v___f_329_, 0, v_s_321_);
lean_closure_set(v___f_329_, 1, v___y_328_);
lean_closure_set(v___f_329_, 2, v_inst_322_);
lean_closure_set(v___f_329_, 3, v_lift_323_);
v___x_330_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_329_, v_it_326_, v_init_327_, lean_box(0));
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_331_, lean_object* v_inst_332_){
_start:
{
lean_object* v___f_333_; 
v___f_333_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_333_, 0, v_s_331_);
lean_closure_set(v___f_333_, 1, v_inst_332_);
return v___f_333_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_334_, lean_object* v_pat_335_, lean_object* v_s_336_, lean_object* v_inst_337_){
_start:
{
lean_object* v___f_338_; 
v___f_338_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_338_, 0, v_s_336_);
lean_closure_set(v___f_338_, 1, v_inst_337_);
return v___f_338_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_339_, lean_object* v_pat_340_, lean_object* v_s_341_, lean_object* v_inst_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_339_, v_pat_340_, v_s_341_, v_inst_342_);
lean_dec(v_pat_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(lean_object* v_pat_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_345_, 0, lean_box(0));
lean_closure_set(v___x_345_, 1, v_pat_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(lean_object* v_00_u03c1_346_, lean_object* v_pat_347_, lean_object* v_inst_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_349_, 0, lean_box(0));
lean_closure_set(v___x_349_, 1, v_pat_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_350_, lean_object* v_pat_351_, lean_object* v_inst_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(v_00_u03c1_350_, v_pat_351_, v_inst_352_);
lean_dec_ref(v_inst_352_);
return v_res_353_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(lean_object* v_lhs_354_, lean_object* v_rhs_355_, lean_object* v_lstart_356_, lean_object* v_rstart_357_, lean_object* v_len_358_, lean_object* v_curr_359_){
_start:
{
uint8_t v___x_360_; 
v___x_360_ = lean_nat_dec_lt(v_curr_359_, v_len_358_);
if (v___x_360_ == 0)
{
uint8_t v___x_361_; 
lean_dec(v_curr_359_);
v___x_361_ = 1;
return v___x_361_;
}
else
{
lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; uint8_t v___x_366_; 
v___x_362_ = lean_nat_add(v_lstart_356_, v_curr_359_);
v___x_363_ = lean_string_get_byte_fast(v_lhs_354_, v___x_362_);
v___x_364_ = lean_nat_add(v_rstart_357_, v_curr_359_);
v___x_365_ = lean_string_get_byte_fast(v_rhs_355_, v___x_364_);
v___x_366_ = lean_uint8_dec_eq(v___x_363_, v___x_365_);
if (v___x_366_ == 0)
{
lean_dec(v_curr_359_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_nat_add(v_curr_359_, v___x_367_);
lean_dec(v_curr_359_);
v_curr_359_ = v___x_368_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg___boxed(lean_object* v_lhs_370_, lean_object* v_rhs_371_, lean_object* v_lstart_372_, lean_object* v_rstart_373_, lean_object* v_len_374_, lean_object* v_curr_375_){
_start:
{
uint8_t v_res_376_; lean_object* v_r_377_; 
v_res_376_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_370_, v_rhs_371_, v_lstart_372_, v_rstart_373_, v_len_374_, v_curr_375_);
lean_dec(v_len_374_);
lean_dec(v_rstart_373_);
lean_dec(v_lstart_372_);
lean_dec_ref(v_rhs_371_);
lean_dec_ref(v_lhs_370_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object* v_lhs_378_, lean_object* v_rhs_379_, lean_object* v_lstart_380_, lean_object* v_rstart_381_, lean_object* v_len_382_, lean_object* v_h1_383_, lean_object* v_h2_384_, lean_object* v_curr_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_378_, v_rhs_379_, v_lstart_380_, v_rstart_381_, v_len_382_, v_curr_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object* v_lhs_387_, lean_object* v_rhs_388_, lean_object* v_lstart_389_, lean_object* v_rstart_390_, lean_object* v_len_391_, lean_object* v_h1_392_, lean_object* v_h2_393_, lean_object* v_curr_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(v_lhs_387_, v_rhs_388_, v_lstart_389_, v_rstart_390_, v_len_391_, v_h1_392_, v_h2_393_, v_curr_394_);
lean_dec(v_len_391_);
lean_dec(v_rstart_390_);
lean_dec(v_lstart_389_);
lean_dec_ref(v_rhs_388_);
lean_dec_ref(v_lhs_387_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object* v_lhs_404_, lean_object* v_rhs_405_, lean_object* v_lstart_406_, lean_object* v_rstart_407_, lean_object* v_len_408_, lean_object* v_h1_409_, lean_object* v_h2_410_){
_start:
{
uint8_t v_res_411_; lean_object* v_r_412_; 
v_res_411_ = lean_string_memcmp(v_lhs_404_, v_rhs_405_, v_lstart_406_, v_rstart_407_, v_len_408_);
lean_dec(v_len_408_);
lean_dec(v_rstart_407_);
lean_dec(v_lstart_406_);
lean_dec_ref(v_rhs_405_);
lean_dec_ref(v_lhs_404_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object* v_lhs_413_, lean_object* v_rhs_414_, lean_object* v_lstart_415_, lean_object* v_rstart_416_, lean_object* v_len_417_){
_start:
{
lean_object* v_str_418_; lean_object* v_startInclusive_419_; lean_object* v_str_420_; lean_object* v_startInclusive_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v_str_418_ = lean_ctor_get(v_lhs_413_, 0);
v_startInclusive_419_ = lean_ctor_get(v_lhs_413_, 1);
v_str_420_ = lean_ctor_get(v_rhs_414_, 0);
v_startInclusive_421_ = lean_ctor_get(v_rhs_414_, 1);
v___x_422_ = lean_nat_add(v_startInclusive_419_, v_lstart_415_);
v___x_423_ = lean_nat_add(v_startInclusive_421_, v_rstart_416_);
v___x_424_ = lean_string_memcmp(v_str_418_, v_str_420_, v___x_422_, v___x_423_, v_len_417_);
lean_dec(v___x_423_);
lean_dec(v___x_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object* v_lhs_425_, lean_object* v_rhs_426_, lean_object* v_lstart_427_, lean_object* v_rstart_428_, lean_object* v_len_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(v_lhs_425_, v_rhs_426_, v_lstart_427_, v_rstart_428_, v_len_429_);
lean_dec(v_len_429_);
lean_dec(v_rstart_428_);
lean_dec(v_lstart_427_);
lean_dec_ref(v_rhs_426_);
lean_dec_ref(v_lhs_425_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object* v_lhs_432_, lean_object* v_rhs_433_, lean_object* v_lstart_434_, lean_object* v_rstart_435_, lean_object* v_len_436_, lean_object* v_h1_437_, lean_object* v_h2_438_){
_start:
{
lean_object* v_str_439_; lean_object* v_startInclusive_440_; lean_object* v_str_441_; lean_object* v_startInclusive_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_str_439_ = lean_ctor_get(v_lhs_432_, 0);
v_startInclusive_440_ = lean_ctor_get(v_lhs_432_, 1);
v_str_441_ = lean_ctor_get(v_rhs_433_, 0);
v_startInclusive_442_ = lean_ctor_get(v_rhs_433_, 1);
v___x_443_ = lean_nat_add(v_startInclusive_440_, v_lstart_434_);
v___x_444_ = lean_nat_add(v_startInclusive_442_, v_rstart_435_);
v___x_445_ = lean_string_memcmp(v_str_439_, v_str_441_, v___x_443_, v___x_444_, v_len_436_);
lean_dec(v___x_444_);
lean_dec(v___x_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object* v_lhs_446_, lean_object* v_rhs_447_, lean_object* v_lstart_448_, lean_object* v_rstart_449_, lean_object* v_len_450_, lean_object* v_h1_451_, lean_object* v_h2_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_String_Slice_Pattern_Internal_memcmpSlice(v_lhs_446_, v_rhs_447_, v_lstart_448_, v_rstart_449_, v_len_450_, v_h1_451_, v_h2_452_);
lean_dec(v_len_450_);
lean_dec(v_rstart_449_);
lean_dec(v_lstart_448_);
lean_dec_ref(v_rhs_447_);
lean_dec_ref(v_lhs_446_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = lean_unsigned_to_nat(0u);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(v_a_459_, v_a_460_, v_a_461_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_unsigned_to_nat(0u);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(v_a_467_, v_a_468_, v_a_469_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(lean_object* v_s_471_){
_start:
{
lean_object* v_startInclusive_472_; lean_object* v_endExclusive_473_; lean_object* v___x_474_; 
v_startInclusive_472_ = lean_ctor_get(v_s_471_, 1);
v_endExclusive_473_ = lean_ctor_get(v_s_471_, 2);
v___x_474_ = lean_nat_sub(v_endExclusive_473_, v_startInclusive_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(lean_object* v_s_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_475_);
lean_dec_ref(v_s_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(lean_object* v_00_u03c1_477_, lean_object* v_pat_478_, lean_object* v_s_479_){
_start:
{
lean_object* v_startInclusive_480_; lean_object* v_endExclusive_481_; lean_object* v___x_482_; 
v_startInclusive_480_ = lean_ctor_get(v_s_479_, 1);
v_endExclusive_481_ = lean_ctor_get(v_s_479_, 2);
v___x_482_ = lean_nat_sub(v_endExclusive_481_, v_startInclusive_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object* v_00_u03c1_483_, lean_object* v_pat_484_, lean_object* v_s_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(v_00_u03c1_483_, v_pat_484_, v_s_485_);
lean_dec_ref(v_s_485_);
lean_dec(v_pat_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(lean_object* v_inst_487_, lean_object* v_s_488_, lean_object* v_it_489_){
_start:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = lean_nat_dec_eq(v_it_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_511_; 
v_skipSuffixOfNonempty_x3f_492_ = lean_ctor_get(v_inst_487_, 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_inst_487_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; lean_object* v_unused_513_; 
v_unused_512_ = lean_ctor_get(v_inst_487_, 2);
lean_dec(v_unused_512_);
v_unused_513_ = lean_ctor_get(v_inst_487_, 0);
lean_dec(v_unused_513_);
v___x_494_ = v_inst_487_;
v_isShared_495_ = v_isSharedCheck_511_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_492_);
lean_dec(v_inst_487_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_511_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v_str_496_; lean_object* v_startInclusive_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v_str_496_ = lean_ctor_get(v_s_488_, 0);
v_startInclusive_497_ = lean_ctor_get(v_s_488_, 1);
v___x_498_ = lean_nat_add(v_startInclusive_497_, v_it_489_);
lean_inc(v_startInclusive_497_);
lean_inc_ref(v_str_496_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 2, v___x_498_);
lean_ctor_set(v___x_494_, 1, v_startInclusive_497_);
lean_ctor_set(v___x_494_, 0, v_str_496_);
v___x_500_ = v___x_494_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_str_496_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_startInclusive_497_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v___x_498_);
v___x_500_ = v_reuseFailAlloc_510_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; 
v___x_501_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_492_, v___x_500_, lean_box(0));
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = lean_nat_sub(v_it_489_, v___x_502_);
v___x_504_ = l_String_Slice_posLE(v_s_488_, v___x_503_);
lean_inc(v___x_504_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_it_489_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
return v___x_506_;
}
else
{
lean_object* v_val_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_val_507_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_val_507_);
lean_dec_ref(v___x_501_);
lean_inc(v_val_507_);
v___x_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_508_, 0, v_val_507_);
lean_ctor_set(v___x_508_, 1, v_it_489_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_val_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
return v___x_509_;
}
}
}
}
else
{
lean_object* v___x_514_; 
lean_dec(v_it_489_);
lean_dec_ref(v_inst_487_);
v___x_514_ = lean_box(2);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(lean_object* v_inst_515_, lean_object* v_s_516_, lean_object* v_it_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_515_, v_s_516_, v_it_517_);
lean_dec_ref(v_s_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(lean_object* v_s_519_, lean_object* v_inst_520_){
_start:
{
lean_object* v___f_521_; 
v___f_521_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_521_, 0, v_inst_520_);
lean_closure_set(v___f_521_, 1, v_s_519_);
return v___f_521_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(lean_object* v_00_u03c1_522_, lean_object* v_pat_523_, lean_object* v_s_524_, lean_object* v_inst_525_){
_start:
{
lean_object* v___f_526_; 
v___f_526_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_526_, 0, v_inst_525_);
lean_closure_set(v___f_526_, 1, v_s_524_);
return v___f_526_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(lean_object* v_00_u03c1_527_, lean_object* v_pat_528_, lean_object* v_s_529_, lean_object* v_inst_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_527_, v_pat_528_, v_s_529_, v_inst_530_);
lean_dec(v_pat_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(lean_object* v_00_u03c1_532_, lean_object* v_pat_533_, lean_object* v_s_534_, lean_object* v_inst_535_, lean_object* v_inst_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_box(0);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_538_, lean_object* v_pat_539_, lean_object* v_s_540_, lean_object* v_inst_541_, lean_object* v_inst_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(v_00_u03c1_538_, v_pat_539_, v_s_540_, v_inst_541_, v_inst_542_);
lean_dec_ref(v_inst_541_);
lean_dec_ref(v_s_540_);
lean_dec(v_pat_539_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v___y_544_, lean_object* v_inst_545_, lean_object* v_s_546_, lean_object* v_lift_547_, lean_object* v_it_548_, lean_object* v_acc_549_, lean_object* v_hP_550_, lean_object* v_recur_551_){
_start:
{
lean_object* v___f_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___f_552_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_552_, 0, v___y_544_);
lean_closure_set(v___f_552_, 1, v_acc_549_);
lean_closure_set(v___f_552_, 2, v_recur_551_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_nat_dec_eq(v_it_548_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_576_; 
v_skipSuffixOfNonempty_x3f_555_ = lean_ctor_get(v_inst_545_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_inst_545_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; lean_object* v_unused_578_; 
v_unused_577_ = lean_ctor_get(v_inst_545_, 2);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_inst_545_, 0);
lean_dec(v_unused_578_);
v___x_557_ = v_inst_545_;
v_isShared_558_ = v_isSharedCheck_576_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_555_);
lean_dec(v_inst_545_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_576_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_str_559_; lean_object* v_startInclusive_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v_str_559_ = lean_ctor_get(v_s_546_, 0);
v_startInclusive_560_ = lean_ctor_get(v_s_546_, 1);
v___x_561_ = lean_nat_add(v_startInclusive_560_, v_it_548_);
lean_inc(v_startInclusive_560_);
lean_inc_ref(v_str_559_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 2, v___x_561_);
lean_ctor_set(v___x_557_, 1, v_startInclusive_560_);
lean_ctor_set(v___x_557_, 0, v_str_559_);
v___x_563_ = v___x_557_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_str_559_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_startInclusive_560_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v___x_561_);
v___x_563_ = v_reuseFailAlloc_575_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_555_, v___x_563_, lean_box(0));
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_sub(v_it_548_, v___x_565_);
v___x_567_ = l_String_Slice_posLE(v_s_546_, v___x_566_);
lean_inc(v___x_567_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v_it_548_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_apply_4(v_lift_547_, lean_box(0), lean_box(0), v___f_552_, v___x_569_);
return v___x_570_;
}
else
{
lean_object* v_val_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_val_571_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_571_);
lean_dec_ref(v___x_564_);
lean_inc(v_val_571_);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v_val_571_);
lean_ctor_set(v___x_572_, 1, v_it_548_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_val_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_apply_4(v_lift_547_, lean_box(0), lean_box(0), v___f_552_, v___x_573_);
return v___x_574_;
}
}
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_it_548_);
lean_dec_ref(v_inst_545_);
v___x_579_ = lean_box(2);
v___x_580_ = lean_apply_4(v_lift_547_, lean_box(0), lean_box(0), v___f_552_, v___x_579_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed(lean_object* v___y_581_, lean_object* v_inst_582_, lean_object* v_s_583_, lean_object* v_lift_584_, lean_object* v_it_585_, lean_object* v_acc_586_, lean_object* v_hP_587_, lean_object* v_recur_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(v___y_581_, v_inst_582_, v_s_583_, v_lift_584_, v_it_585_, v_acc_586_, v_hP_587_, v_recur_588_);
lean_dec_ref(v_s_583_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v_inst_590_, lean_object* v_s_591_, lean_object* v_lift_592_, lean_object* v_00_u03b3_593_, lean_object* v_Pl_594_, lean_object* v_it_595_, lean_object* v_init_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___f_598_; lean_object* v___x_599_; 
v___f_598_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_598_, 0, v___y_597_);
lean_closure_set(v___f_598_, 1, v_inst_590_);
lean_closure_set(v___f_598_, 2, v_s_591_);
lean_closure_set(v___f_598_, 3, v_lift_592_);
v___x_599_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_598_, v_it_595_, v_init_596_, lean_box(0));
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_600_, lean_object* v_inst_601_){
_start:
{
lean_object* v___f_602_; 
v___f_602_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_602_, 0, v_inst_601_);
lean_closure_set(v___f_602_, 1, v_s_600_);
return v___f_602_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_603_, lean_object* v_pat_604_, lean_object* v_s_605_, lean_object* v_inst_606_){
_start:
{
lean_object* v___f_607_; 
v___f_607_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_607_, 0, v_inst_606_);
lean_closure_set(v___f_607_, 1, v_s_605_);
return v___f_607_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_608_, lean_object* v_pat_609_, lean_object* v_s_610_, lean_object* v_inst_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_608_, v_pat_609_, v_s_610_, v_inst_611_);
lean_dec(v_pat_609_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(lean_object* v_pat_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_614_, 0, lean_box(0));
lean_closure_set(v___x_614_, 1, v_pat_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(lean_object* v_00_u03c1_615_, lean_object* v_pat_616_, lean_object* v_inst_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_618_, 0, lean_box(0));
lean_closure_set(v___x_618_, 1, v_pat_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_619_, lean_object* v_pat_620_, lean_object* v_inst_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(v_00_u03c1_619_, v_pat_620_, v_inst_621_);
lean_dec_ref(v_inst_621_);
return v_res_622_;
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
