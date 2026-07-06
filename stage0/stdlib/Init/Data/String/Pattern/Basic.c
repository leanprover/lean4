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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default(lean_object* v_s_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = ((lean_object*)(l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0));
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_instInhabitedSearchStep_default___boxed(lean_object* v_s_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_String_Slice_Pattern_instInhabitedSearchStep_default(v_s_65_);
lean_dec_ref(v_s_65_);
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
lean_dec_ref_known(v_st_160_, 2);
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
lean_dec_ref_known(v_st_160_, 2);
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
lean_dec_ref_known(v_st_172_, 2);
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
lean_dec_ref_known(v_st_172_, 2);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___redArg(lean_object* v_x_188_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v_startPos_189_; lean_object* v_endPos_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_startPos_189_ = lean_ctor_get(v_x_188_, 0);
v_endPos_190_ = lean_ctor_get(v_x_188_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v_x_188_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_endPos_190_);
lean_inc(v_startPos_189_);
lean_dec(v_x_188_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_startPos_189_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_endPos_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
else
{
lean_object* v_startPos_198_; lean_object* v_endPos_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_startPos_198_ = lean_ctor_get(v_x_188_, 0);
v_endPos_199_ = lean_ctor_get(v_x_188_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v_x_188_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_endPos_199_);
lean_inc(v_startPos_198_);
lean_dec(v_x_188_);
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
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 2, 0);
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
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast(lean_object* v_s_207_, lean_object* v_t_208_, lean_object* v_hst_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
lean_object* v_startPos_211_; lean_object* v_endPos_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
v_startPos_211_ = lean_ctor_get(v_x_210_, 0);
v_endPos_212_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v_x_210_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_endPos_212_);
lean_inc(v_startPos_211_);
lean_dec(v_x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_startPos_211_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_endPos_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v_startPos_220_; lean_object* v_endPos_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_startPos_220_ = lean_ctor_get(v_x_210_, 0);
v_endPos_221_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v_x_210_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_endPos_221_);
lean_inc(v_startPos_220_);
lean_dec(v_x_210_);
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
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 2, 0);
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
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_SearchStep_cast___boxed(lean_object* v_s_229_, lean_object* v_t_230_, lean_object* v_hst_231_, lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_String_Slice_Pattern_SearchStep_cast(v_s_229_, v_t_230_, v_hst_231_, v_x_232_);
lean_dec_ref(v_t_230_);
lean_dec_ref(v_s_229_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(lean_object* v_inst_234_, lean_object* v_s_235_){
_start:
{
lean_object* v_skipPrefix_x3f_236_; lean_object* v___x_237_; 
v_skipPrefix_x3f_236_ = lean_ctor_get(v_inst_234_, 0);
lean_inc_ref(v_skipPrefix_x3f_236_);
lean_dec_ref(v_inst_234_);
v___x_237_ = lean_apply_1(v_skipPrefix_x3f_236_, v_s_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(lean_object* v_00_u03c1_238_, lean_object* v_pat_239_, lean_object* v_inst_240_, lean_object* v_s_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(v_inst_240_, v_s_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_243_, lean_object* v_pat_244_, lean_object* v_inst_245_, lean_object* v_s_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(v_00_u03c1_243_, v_pat_244_, v_inst_245_, v_s_246_);
lean_dec(v_pat_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(lean_object* v_00_u03c1_248_, lean_object* v_pat_249_, lean_object* v_s_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_unsigned_to_nat(0u);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(lean_object* v_00_u03c1_252_, lean_object* v_pat_253_, lean_object* v_s_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(v_00_u03c1_252_, v_pat_253_, v_s_254_);
lean_dec_ref(v_s_254_);
lean_dec(v_pat_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_unsigned_to_nat(0u);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(v_a_260_, v_a_261_, v_a_262_);
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(lean_object* v_00_u03c1_264_, lean_object* v_pat_265_, lean_object* v_s_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_unsigned_to_nat(0u);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object* v_00_u03c1_268_, lean_object* v_pat_269_, lean_object* v_s_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(v_00_u03c1_268_, v_pat_269_, v_s_270_);
lean_dec_ref(v_s_270_);
lean_dec(v_pat_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(lean_object* v_s_272_, lean_object* v_inst_273_, lean_object* v_it_274_){
_start:
{
lean_object* v_str_275_; lean_object* v_startInclusive_276_; lean_object* v_endExclusive_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_298_; 
v_str_275_ = lean_ctor_get(v_s_272_, 0);
v_startInclusive_276_ = lean_ctor_get(v_s_272_, 1);
v_endExclusive_277_ = lean_ctor_get(v_s_272_, 2);
v_isSharedCheck_298_ = !lean_is_exclusive(v_s_272_);
if (v_isSharedCheck_298_ == 0)
{
v___x_279_ = v_s_272_;
v_isShared_280_ = v_isSharedCheck_298_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_endExclusive_277_);
lean_inc(v_startInclusive_276_);
lean_inc(v_str_275_);
lean_dec(v_s_272_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_298_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_nat_sub(v_endExclusive_277_, v_startInclusive_276_);
v___x_282_ = lean_nat_dec_eq(v_it_274_, v___x_281_);
lean_dec(v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v_skipPrefixOfNonempty_x3f_283_ = lean_ctor_get(v_inst_273_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_283_);
lean_dec_ref(v_inst_273_);
v___x_284_ = lean_nat_add(v_startInclusive_276_, v_it_274_);
lean_inc(v___x_284_);
lean_inc_ref(v_str_275_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v___x_284_);
v___x_286_ = v___x_279_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_str_275_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_endExclusive_277_);
v___x_286_ = v_reuseFailAlloc_296_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; 
v___x_287_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_283_, v___x_286_, lean_box(0));
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_288_ = lean_string_utf8_next_fast(v_str_275_, v___x_284_);
lean_dec(v___x_284_);
lean_dec_ref(v_str_275_);
v___x_289_ = lean_nat_sub(v___x_288_, v_startInclusive_276_);
lean_dec(v_startInclusive_276_);
lean_inc(v___x_289_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v_it_274_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
else
{
lean_object* v_val_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v___x_284_);
lean_dec(v_startInclusive_276_);
lean_dec_ref(v_str_275_);
v_val_292_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v___x_287_, 1);
v___x_293_ = lean_nat_add(v_it_274_, v_val_292_);
lean_dec(v_val_292_);
lean_inc(v___x_293_);
v___x_294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_294_, 0, v_it_274_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
}
}
else
{
lean_object* v___x_297_; 
lean_del_object(v___x_279_);
lean_dec(v_endExclusive_277_);
lean_dec(v_startInclusive_276_);
lean_dec_ref(v_str_275_);
lean_dec(v_it_274_);
lean_dec_ref(v_inst_273_);
v___x_297_ = lean_box(2);
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(lean_object* v_s_299_, lean_object* v_inst_300_){
_start:
{
lean_object* v___f_301_; 
v___f_301_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_301_, 0, v_s_299_);
lean_closure_set(v___f_301_, 1, v_inst_300_);
return v___f_301_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(lean_object* v_00_u03c1_302_, lean_object* v_pat_303_, lean_object* v_s_304_, lean_object* v_inst_305_){
_start:
{
lean_object* v___f_306_; 
v___f_306_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_306_, 0, v_s_304_);
lean_closure_set(v___f_306_, 1, v_inst_305_);
return v___f_306_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(lean_object* v_00_u03c1_307_, lean_object* v_pat_308_, lean_object* v_s_309_, lean_object* v_inst_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(v_00_u03c1_307_, v_pat_308_, v_s_309_, v_inst_310_);
lean_dec(v_pat_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(lean_object* v_00_u03c1_312_, lean_object* v_pat_313_, lean_object* v_s_314_, lean_object* v_inst_315_, lean_object* v_inst_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_box(0);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_318_, lean_object* v_pat_319_, lean_object* v_s_320_, lean_object* v_inst_321_, lean_object* v_inst_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(v_00_u03c1_318_, v_pat_319_, v_s_320_, v_inst_321_, v_inst_322_);
lean_dec_ref(v_inst_321_);
lean_dec_ref(v_s_320_);
lean_dec(v_pat_319_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v___y_324_, lean_object* v_acc_325_, lean_object* v_recur_326_, lean_object* v_s_327_){
_start:
{
switch(lean_obj_tag(v_s_327_))
{
case 0:
{
lean_object* v_it_328_; lean_object* v_out_329_; lean_object* v_val_330_; 
v_it_328_ = lean_ctor_get(v_s_327_, 0);
lean_inc(v_it_328_);
v_out_329_ = lean_ctor_get(v_s_327_, 1);
lean_inc(v_out_329_);
lean_dec_ref_known(v_s_327_, 2);
v_val_330_ = lean_apply_3(v___y_324_, v_out_329_, lean_box(0), v_acc_325_);
if (lean_obj_tag(v_val_330_) == 0)
{
lean_object* v_a_331_; 
lean_dec(v_it_328_);
lean_dec(v_recur_326_);
v_a_331_ = lean_ctor_get(v_val_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v_val_330_, 1);
return v_a_331_;
}
else
{
lean_object* v_a_332_; lean_object* v___x_333_; 
v_a_332_ = lean_ctor_get(v_val_330_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v_val_330_, 1);
v___x_333_ = lean_apply_4(v_recur_326_, v_it_328_, v_a_332_, lean_box(0), lean_box(0));
return v___x_333_;
}
}
case 1:
{
lean_object* v_it_334_; lean_object* v___x_335_; 
lean_dec_ref(v___y_324_);
v_it_334_ = lean_ctor_get(v_s_327_, 0);
lean_inc(v_it_334_);
lean_dec_ref_known(v_s_327_, 1);
v___x_335_ = lean_apply_4(v_recur_326_, v_it_334_, v_acc_325_, lean_box(0), lean_box(0));
return v___x_335_;
}
default: 
{
lean_dec(v_recur_326_);
lean_dec_ref(v___y_324_);
return v_acc_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v_s_336_, lean_object* v___y_337_, lean_object* v_inst_338_, lean_object* v_lift_339_, lean_object* v_it_340_, lean_object* v_acc_341_, lean_object* v_hP_342_, lean_object* v_recur_343_){
_start:
{
lean_object* v_str_344_; lean_object* v_startInclusive_345_; lean_object* v_endExclusive_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_371_; 
v_str_344_ = lean_ctor_get(v_s_336_, 0);
v_startInclusive_345_ = lean_ctor_get(v_s_336_, 1);
v_endExclusive_346_ = lean_ctor_get(v_s_336_, 2);
v_isSharedCheck_371_ = !lean_is_exclusive(v_s_336_);
if (v_isSharedCheck_371_ == 0)
{
v___x_348_ = v_s_336_;
v_isShared_349_ = v_isSharedCheck_371_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_endExclusive_346_);
lean_inc(v_startInclusive_345_);
lean_inc(v_str_344_);
lean_dec(v_s_336_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_371_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___f_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___f_350_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_350_, 0, v___y_337_);
lean_closure_set(v___f_350_, 1, v_acc_341_);
lean_closure_set(v___f_350_, 2, v_recur_343_);
v___x_351_ = lean_nat_sub(v_endExclusive_346_, v_startInclusive_345_);
v___x_352_ = lean_nat_dec_eq(v_it_340_, v___x_351_);
lean_dec(v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v_skipPrefixOfNonempty_x3f_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v_skipPrefixOfNonempty_x3f_353_ = lean_ctor_get(v_inst_338_, 1);
lean_inc_ref(v_skipPrefixOfNonempty_x3f_353_);
lean_dec_ref(v_inst_338_);
v___x_354_ = lean_nat_add(v_startInclusive_345_, v_it_340_);
lean_inc(v___x_354_);
lean_inc_ref(v_str_344_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v___x_354_);
v___x_356_ = v___x_348_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_str_344_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_endExclusive_346_);
v___x_356_ = v_reuseFailAlloc_368_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; 
v___x_357_ = lean_apply_2(v_skipPrefixOfNonempty_x3f_353_, v___x_356_, lean_box(0));
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_358_ = lean_string_utf8_next_fast(v_str_344_, v___x_354_);
lean_dec(v___x_354_);
lean_dec_ref(v_str_344_);
v___x_359_ = lean_nat_sub(v___x_358_, v_startInclusive_345_);
lean_dec(v_startInclusive_345_);
lean_inc(v___x_359_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_it_340_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_apply_4(v_lift_339_, lean_box(0), lean_box(0), v___f_350_, v___x_361_);
return v___x_362_;
}
else
{
lean_object* v_val_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v___x_354_);
lean_dec(v_startInclusive_345_);
lean_dec_ref(v_str_344_);
v_val_363_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v___x_357_, 1);
v___x_364_ = lean_nat_add(v_it_340_, v_val_363_);
lean_dec(v_val_363_);
lean_inc(v___x_364_);
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v_it_340_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_apply_4(v_lift_339_, lean_box(0), lean_box(0), v___f_350_, v___x_366_);
return v___x_367_;
}
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_del_object(v___x_348_);
lean_dec(v_endExclusive_346_);
lean_dec(v_startInclusive_345_);
lean_dec_ref(v_str_344_);
lean_dec(v_it_340_);
lean_dec_ref(v_inst_338_);
v___x_369_ = lean_box(2);
v___x_370_ = lean_apply_4(v_lift_339_, lean_box(0), lean_box(0), v___f_350_, v___x_369_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object* v_s_372_, lean_object* v_inst_373_, lean_object* v_lift_374_, lean_object* v_00_u03b3_375_, lean_object* v_Pl_376_, lean_object* v_it_377_, lean_object* v_init_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___f_380_; lean_object* v___x_381_; 
v___f_380_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1), 8, 4);
lean_closure_set(v___f_380_, 0, v_s_372_);
lean_closure_set(v___f_380_, 1, v___y_379_);
lean_closure_set(v___f_380_, 2, v_inst_373_);
lean_closure_set(v___f_380_, 3, v_lift_374_);
v___x_381_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_380_, v_it_377_, v_init_378_, lean_box(0));
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v___f_384_; 
v___f_384_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_384_, 0, v_s_382_);
lean_closure_set(v___f_384_, 1, v_inst_383_);
return v___f_384_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_385_, lean_object* v_pat_386_, lean_object* v_s_387_, lean_object* v_inst_388_){
_start:
{
lean_object* v___f_389_; 
v___f_389_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_389_, 0, v_s_387_);
lean_closure_set(v___f_389_, 1, v_inst_388_);
return v___f_389_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_390_, lean_object* v_pat_391_, lean_object* v_s_392_, lean_object* v_inst_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_390_, v_pat_391_, v_s_392_, v_inst_393_);
lean_dec(v_pat_391_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(lean_object* v_pat_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_396_, 0, lean_box(0));
lean_closure_set(v___x_396_, 1, v_pat_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(lean_object* v_00_u03c1_397_, lean_object* v_pat_398_, lean_object* v_inst_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_400_, 0, lean_box(0));
lean_closure_set(v___x_400_, 1, v_pat_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_401_, lean_object* v_pat_402_, lean_object* v_inst_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(v_00_u03c1_401_, v_pat_402_, v_inst_403_);
lean_dec_ref(v_inst_403_);
return v_res_404_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object* v_lhs_405_, lean_object* v_rhs_406_, lean_object* v_lstart_407_, lean_object* v_rstart_408_, lean_object* v_len_409_, lean_object* v_curr_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = lean_nat_dec_lt(v_curr_410_, v_len_409_);
if (v___x_411_ == 0)
{
uint8_t v___x_412_; 
lean_dec(v_curr_410_);
v___x_412_ = 1;
return v___x_412_;
}
else
{
lean_object* v___x_413_; uint8_t v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; uint8_t v___x_417_; 
v___x_413_ = lean_nat_add(v_lstart_407_, v_curr_410_);
v___x_414_ = lean_string_get_byte_fast(v_lhs_405_, v___x_413_);
v___x_415_ = lean_nat_add(v_rstart_408_, v_curr_410_);
v___x_416_ = lean_string_get_byte_fast(v_rhs_406_, v___x_415_);
v___x_417_ = lean_uint8_dec_eq(v___x_414_, v___x_416_);
if (v___x_417_ == 0)
{
lean_dec(v_curr_410_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_add(v_curr_410_, v___x_418_);
lean_dec(v_curr_410_);
v_curr_410_ = v___x_419_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object* v_lhs_421_, lean_object* v_rhs_422_, lean_object* v_lstart_423_, lean_object* v_rstart_424_, lean_object* v_len_425_, lean_object* v_curr_426_){
_start:
{
uint8_t v_res_427_; lean_object* v_r_428_; 
v_res_427_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(v_lhs_421_, v_rhs_422_, v_lstart_423_, v_rstart_424_, v_len_425_, v_curr_426_);
lean_dec(v_len_425_);
lean_dec(v_rstart_424_);
lean_dec(v_lstart_423_);
lean_dec_ref(v_rhs_422_);
lean_dec_ref(v_lhs_421_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object* v_lhs_436_, lean_object* v_rhs_437_, lean_object* v_lstart_438_, lean_object* v_rstart_439_, lean_object* v_len_440_, lean_object* v_h1_441_, lean_object* v_h2_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = lean_string_memcmp(v_lhs_436_, v_rhs_437_, v_lstart_438_, v_rstart_439_, v_len_440_);
lean_dec(v_len_440_);
lean_dec(v_rstart_439_);
lean_dec(v_lstart_438_);
lean_dec_ref(v_rhs_437_);
lean_dec_ref(v_lhs_436_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object* v_lhs_445_, lean_object* v_rhs_446_, lean_object* v_lstart_447_, lean_object* v_rstart_448_, lean_object* v_len_449_){
_start:
{
lean_object* v_str_450_; lean_object* v_startInclusive_451_; lean_object* v_str_452_; lean_object* v_startInclusive_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_str_450_ = lean_ctor_get(v_lhs_445_, 0);
v_startInclusive_451_ = lean_ctor_get(v_lhs_445_, 1);
v_str_452_ = lean_ctor_get(v_rhs_446_, 0);
v_startInclusive_453_ = lean_ctor_get(v_rhs_446_, 1);
v___x_454_ = lean_nat_add(v_startInclusive_451_, v_lstart_447_);
v___x_455_ = lean_nat_add(v_startInclusive_453_, v_rstart_448_);
v___x_456_ = lean_string_memcmp(v_str_450_, v_str_452_, v___x_454_, v___x_455_, v_len_449_);
lean_dec(v___x_455_);
lean_dec(v___x_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object* v_lhs_457_, lean_object* v_rhs_458_, lean_object* v_lstart_459_, lean_object* v_rstart_460_, lean_object* v_len_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(v_lhs_457_, v_rhs_458_, v_lstart_459_, v_rstart_460_, v_len_461_);
lean_dec(v_len_461_);
lean_dec(v_rstart_460_);
lean_dec(v_lstart_459_);
lean_dec_ref(v_rhs_458_);
lean_dec_ref(v_lhs_457_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object* v_lhs_464_, lean_object* v_rhs_465_, lean_object* v_lstart_466_, lean_object* v_rstart_467_, lean_object* v_len_468_, lean_object* v_h1_469_, lean_object* v_h2_470_){
_start:
{
lean_object* v_str_471_; lean_object* v_startInclusive_472_; lean_object* v_str_473_; lean_object* v_startInclusive_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_str_471_ = lean_ctor_get(v_lhs_464_, 0);
v_startInclusive_472_ = lean_ctor_get(v_lhs_464_, 1);
v_str_473_ = lean_ctor_get(v_rhs_465_, 0);
v_startInclusive_474_ = lean_ctor_get(v_rhs_465_, 1);
v___x_475_ = lean_nat_add(v_startInclusive_472_, v_lstart_466_);
v___x_476_ = lean_nat_add(v_startInclusive_474_, v_rstart_467_);
v___x_477_ = lean_string_memcmp(v_str_471_, v_str_473_, v___x_475_, v___x_476_, v_len_468_);
lean_dec(v___x_476_);
lean_dec(v___x_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object* v_lhs_478_, lean_object* v_rhs_479_, lean_object* v_lstart_480_, lean_object* v_rstart_481_, lean_object* v_len_482_, lean_object* v_h1_483_, lean_object* v_h2_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_String_Slice_Pattern_Internal_memcmpSlice(v_lhs_478_, v_rhs_479_, v_lstart_480_, v_rstart_481_, v_len_482_, v_h1_483_, v_h2_484_);
lean_dec(v_len_482_);
lean_dec(v_rstart_481_);
lean_dec(v_lstart_480_);
lean_dec_ref(v_rhs_479_);
lean_dec_ref(v_lhs_478_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object* v_00_u03c1_487_, lean_object* v_pat_488_, lean_object* v_s_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = lean_unsigned_to_nat(0u);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object* v_00_u03c1_491_, lean_object* v_pat_492_, lean_object* v_s_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(v_00_u03c1_491_, v_pat_492_, v_s_493_);
lean_dec_ref(v_s_493_);
lean_dec(v_pat_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_unsigned_to_nat(0u);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(v_a_499_, v_a_500_, v_a_501_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(lean_object* v_s_503_){
_start:
{
lean_object* v_startInclusive_504_; lean_object* v_endExclusive_505_; lean_object* v___x_506_; 
v_startInclusive_504_ = lean_ctor_get(v_s_503_, 1);
v_endExclusive_505_ = lean_ctor_get(v_s_503_, 2);
v___x_506_ = lean_nat_sub(v_endExclusive_505_, v_startInclusive_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(lean_object* v_s_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_507_);
lean_dec_ref(v_s_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(lean_object* v_00_u03c1_509_, lean_object* v_pat_510_, lean_object* v_s_511_){
_start:
{
lean_object* v_startInclusive_512_; lean_object* v_endExclusive_513_; lean_object* v___x_514_; 
v_startInclusive_512_ = lean_ctor_get(v_s_511_, 1);
v_endExclusive_513_ = lean_ctor_get(v_s_511_, 2);
v___x_514_ = lean_nat_sub(v_endExclusive_513_, v_startInclusive_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object* v_00_u03c1_515_, lean_object* v_pat_516_, lean_object* v_s_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(v_00_u03c1_515_, v_pat_516_, v_s_517_);
lean_dec_ref(v_s_517_);
lean_dec(v_pat_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(lean_object* v_inst_519_, lean_object* v_s_520_, lean_object* v_it_521_){
_start:
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_nat_dec_eq(v_it_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_543_; 
v_skipSuffixOfNonempty_x3f_524_ = lean_ctor_get(v_inst_519_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_inst_519_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; lean_object* v_unused_545_; 
v_unused_544_ = lean_ctor_get(v_inst_519_, 2);
lean_dec(v_unused_544_);
v_unused_545_ = lean_ctor_get(v_inst_519_, 0);
lean_dec(v_unused_545_);
v___x_526_ = v_inst_519_;
v_isShared_527_ = v_isSharedCheck_543_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_524_);
lean_dec(v_inst_519_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_543_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_str_528_; lean_object* v_startInclusive_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v_str_528_ = lean_ctor_get(v_s_520_, 0);
v_startInclusive_529_ = lean_ctor_get(v_s_520_, 1);
v___x_530_ = lean_nat_add(v_startInclusive_529_, v_it_521_);
lean_inc(v_startInclusive_529_);
lean_inc_ref(v_str_528_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 2, v___x_530_);
lean_ctor_set(v___x_526_, 1, v_startInclusive_529_);
lean_ctor_set(v___x_526_, 0, v_str_528_);
v___x_532_ = v___x_526_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_str_528_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_startInclusive_529_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v___x_530_);
v___x_532_ = v_reuseFailAlloc_542_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; 
v___x_533_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_524_, v___x_532_, lean_box(0));
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_sub(v_it_521_, v___x_534_);
v___x_536_ = l_String_Slice_posLE(v_s_520_, v___x_535_);
lean_inc(v___x_536_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v_it_521_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
return v___x_538_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_val_539_ = lean_ctor_get(v___x_533_, 0);
lean_inc_n(v_val_539_, 2);
lean_dec_ref_known(v___x_533_, 1);
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v_val_539_);
lean_ctor_set(v___x_540_, 1, v_it_521_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_val_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
return v___x_541_;
}
}
}
}
else
{
lean_object* v___x_546_; 
lean_dec(v_it_521_);
lean_dec_ref(v_inst_519_);
v___x_546_ = lean_box(2);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(lean_object* v_inst_547_, lean_object* v_s_548_, lean_object* v_it_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_547_, v_s_548_, v_it_549_);
lean_dec_ref(v_s_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(lean_object* v_s_551_, lean_object* v_inst_552_){
_start:
{
lean_object* v___f_553_; 
v___f_553_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_553_, 0, v_inst_552_);
lean_closure_set(v___f_553_, 1, v_s_551_);
return v___f_553_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(lean_object* v_00_u03c1_554_, lean_object* v_pat_555_, lean_object* v_s_556_, lean_object* v_inst_557_){
_start:
{
lean_object* v___f_558_; 
v___f_558_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_558_, 0, v_inst_557_);
lean_closure_set(v___f_558_, 1, v_s_556_);
return v___f_558_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(lean_object* v_00_u03c1_559_, lean_object* v_pat_560_, lean_object* v_s_561_, lean_object* v_inst_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_559_, v_pat_560_, v_s_561_, v_inst_562_);
lean_dec(v_pat_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(lean_object* v_00_u03c1_564_, lean_object* v_pat_565_, lean_object* v_s_566_, lean_object* v_inst_567_, lean_object* v_inst_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = lean_box(0);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_570_, lean_object* v_pat_571_, lean_object* v_s_572_, lean_object* v_inst_573_, lean_object* v_inst_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(v_00_u03c1_570_, v_pat_571_, v_s_572_, v_inst_573_, v_inst_574_);
lean_dec_ref(v_inst_573_);
lean_dec_ref(v_s_572_);
lean_dec(v_pat_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v___y_576_, lean_object* v_inst_577_, lean_object* v_s_578_, lean_object* v_lift_579_, lean_object* v_it_580_, lean_object* v_acc_581_, lean_object* v_hP_582_, lean_object* v_recur_583_){
_start:
{
lean_object* v___f_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___f_584_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_584_, 0, v___y_576_);
lean_closure_set(v___f_584_, 1, v_acc_581_);
lean_closure_set(v___f_584_, 2, v_recur_583_);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_nat_dec_eq(v_it_580_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v_skipSuffixOfNonempty_x3f_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_608_; 
v_skipSuffixOfNonempty_x3f_587_ = lean_ctor_get(v_inst_577_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_inst_577_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; lean_object* v_unused_610_; 
v_unused_609_ = lean_ctor_get(v_inst_577_, 2);
lean_dec(v_unused_609_);
v_unused_610_ = lean_ctor_get(v_inst_577_, 0);
lean_dec(v_unused_610_);
v___x_589_ = v_inst_577_;
v_isShared_590_ = v_isSharedCheck_608_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_skipSuffixOfNonempty_x3f_587_);
lean_dec(v_inst_577_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_608_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_str_591_; lean_object* v_startInclusive_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v_str_591_ = lean_ctor_get(v_s_578_, 0);
v_startInclusive_592_ = lean_ctor_get(v_s_578_, 1);
v___x_593_ = lean_nat_add(v_startInclusive_592_, v_it_580_);
lean_inc(v_startInclusive_592_);
lean_inc_ref(v_str_591_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 2, v___x_593_);
lean_ctor_set(v___x_589_, 1, v_startInclusive_592_);
lean_ctor_set(v___x_589_, 0, v_str_591_);
v___x_595_ = v___x_589_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_str_591_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_startInclusive_592_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v___x_593_);
v___x_595_ = v_reuseFailAlloc_607_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_apply_2(v_skipSuffixOfNonempty_x3f_587_, v___x_595_, lean_box(0));
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_sub(v_it_580_, v___x_597_);
v___x_599_ = l_String_Slice_posLE(v_s_578_, v___x_598_);
lean_inc(v___x_599_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v_it_580_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_apply_4(v_lift_579_, lean_box(0), lean_box(0), v___f_584_, v___x_601_);
return v___x_602_;
}
else
{
lean_object* v_val_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_val_603_ = lean_ctor_get(v___x_596_, 0);
lean_inc_n(v_val_603_, 2);
lean_dec_ref_known(v___x_596_, 1);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v_val_603_);
lean_ctor_set(v___x_604_, 1, v_it_580_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v_val_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_apply_4(v_lift_579_, lean_box(0), lean_box(0), v___f_584_, v___x_605_);
return v___x_606_;
}
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec(v_it_580_);
lean_dec_ref(v_inst_577_);
v___x_611_ = lean_box(2);
v___x_612_ = lean_apply_4(v_lift_579_, lean_box(0), lean_box(0), v___f_584_, v___x_611_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed(lean_object* v___y_613_, lean_object* v_inst_614_, lean_object* v_s_615_, lean_object* v_lift_616_, lean_object* v_it_617_, lean_object* v_acc_618_, lean_object* v_hP_619_, lean_object* v_recur_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(v___y_613_, v_inst_614_, v_s_615_, v_lift_616_, v_it_617_, v_acc_618_, v_hP_619_, v_recur_620_);
lean_dec_ref(v_s_615_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v_inst_622_, lean_object* v_s_623_, lean_object* v_lift_624_, lean_object* v_00_u03b3_625_, lean_object* v_Pl_626_, lean_object* v_it_627_, lean_object* v_init_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___f_630_; lean_object* v___x_631_; 
v___f_630_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed), 8, 4);
lean_closure_set(v___f_630_, 0, v___y_629_);
lean_closure_set(v___f_630_, 1, v_inst_622_);
lean_closure_set(v___f_630_, 2, v_s_623_);
lean_closure_set(v___f_630_, 3, v_lift_624_);
v___x_631_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_630_, v_it_627_, v_init_628_, lean_box(0));
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_632_, lean_object* v_inst_633_){
_start:
{
lean_object* v___f_634_; 
v___f_634_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_634_, 0, v_inst_633_);
lean_closure_set(v___f_634_, 1, v_s_632_);
return v___f_634_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_635_, lean_object* v_pat_636_, lean_object* v_s_637_, lean_object* v_inst_638_){
_start:
{
lean_object* v___f_639_; 
v___f_639_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 8, 2);
lean_closure_set(v___f_639_, 0, v_inst_638_);
lean_closure_set(v___f_639_, 1, v_s_637_);
return v___f_639_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_640_, lean_object* v_pat_641_, lean_object* v_s_642_, lean_object* v_inst_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_640_, v_pat_641_, v_s_642_, v_inst_643_);
lean_dec(v_pat_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(lean_object* v_pat_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_646_, 0, lean_box(0));
lean_closure_set(v___x_646_, 1, v_pat_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(lean_object* v_00_u03c1_647_, lean_object* v_pat_648_, lean_object* v_inst_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_650_, 0, lean_box(0));
lean_closure_set(v___x_650_, 1, v_pat_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_651_, lean_object* v_pat_652_, lean_object* v_inst_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(v_00_u03c1_651_, v_pat_652_, v_inst_653_);
lean_dec_ref(v_inst_653_);
return v_res_654_;
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
