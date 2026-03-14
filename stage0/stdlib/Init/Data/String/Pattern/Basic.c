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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_unsigned_to_nat(0u);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(v_a_187_, v_a_188_, v_a_189_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_unsigned_to_nat(0u);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(v_a_195_, v_a_196_, v_a_197_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(lean_object* v_00_u03c1_199_, lean_object* v_pat_200_, lean_object* v_s_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_unsigned_to_nat(0u);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object* v_00_u03c1_203_, lean_object* v_pat_204_, lean_object* v_s_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(v_00_u03c1_203_, v_pat_204_, v_s_205_);
lean_dec_ref(v_s_205_);
lean_dec(v_pat_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(lean_object* v_s_207_, lean_object* v_inst_208_, lean_object* v_it_209_){
_start:
{
lean_object* v_str_210_; lean_object* v_startInclusive_211_; lean_object* v_endExclusive_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_233_; 
v_str_210_ = lean_ctor_get(v_s_207_, 0);
v_startInclusive_211_ = lean_ctor_get(v_s_207_, 1);
v_endExclusive_212_ = lean_ctor_get(v_s_207_, 2);
v_isSharedCheck_233_ = !lean_is_exclusive(v_s_207_);
if (v_isSharedCheck_233_ == 0)
{
v___x_214_ = v_s_207_;
v_isShared_215_ = v_isSharedCheck_233_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_endExclusive_212_);
lean_inc(v_startInclusive_211_);
lean_inc(v_str_210_);
lean_dec(v_s_207_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_233_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_nat_sub(v_endExclusive_212_, v_startInclusive_211_);
v___x_217_ = lean_nat_dec_eq(v_it_209_, v___x_216_);
lean_dec(v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v_dropPrefixOfNonempty_x3f_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v_dropPrefixOfNonempty_x3f_218_ = lean_ctor_get(v_inst_208_, 1);
lean_inc_ref(v_dropPrefixOfNonempty_x3f_218_);
lean_dec_ref(v_inst_208_);
v___x_219_ = lean_nat_add(v_startInclusive_211_, v_it_209_);
lean_inc(v___x_219_);
lean_inc_ref(v_str_210_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_219_);
v___x_221_ = v___x_214_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_str_210_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_endExclusive_212_);
v___x_221_ = v_reuseFailAlloc_231_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_apply_2(v_dropPrefixOfNonempty_x3f_218_, v___x_221_, lean_box(0));
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = lean_string_utf8_next_fast(v_str_210_, v___x_219_);
lean_dec(v___x_219_);
lean_dec_ref(v_str_210_);
v___x_224_ = lean_nat_sub(v___x_223_, v_startInclusive_211_);
lean_dec(v_startInclusive_211_);
lean_inc(v___x_224_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v_it_209_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v_val_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v___x_219_);
lean_dec(v_startInclusive_211_);
lean_dec_ref(v_str_210_);
v_val_227_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_227_);
lean_dec_ref(v___x_222_);
v___x_228_ = lean_nat_add(v_it_209_, v_val_227_);
lean_dec(v_val_227_);
lean_inc(v___x_228_);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v_it_209_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
return v___x_230_;
}
}
}
else
{
lean_object* v___x_232_; 
lean_del_object(v___x_214_);
lean_dec(v_endExclusive_212_);
lean_dec(v_startInclusive_211_);
lean_dec_ref(v_str_210_);
lean_dec(v_it_209_);
lean_dec_ref(v_inst_208_);
v___x_232_ = lean_box(2);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(lean_object* v_s_234_, lean_object* v_inst_235_){
_start:
{
lean_object* v___f_236_; 
v___f_236_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_236_, 0, v_s_234_);
lean_closure_set(v___f_236_, 1, v_inst_235_);
return v___f_236_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(lean_object* v_00_u03c1_237_, lean_object* v_pat_238_, lean_object* v_s_239_, lean_object* v_inst_240_){
_start:
{
lean_object* v___f_241_; 
v___f_241_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0), 3, 2);
lean_closure_set(v___f_241_, 0, v_s_239_);
lean_closure_set(v___f_241_, 1, v_inst_240_);
return v___f_241_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(lean_object* v_00_u03c1_242_, lean_object* v_pat_243_, lean_object* v_s_244_, lean_object* v_inst_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(v_00_u03c1_242_, v_pat_243_, v_s_244_, v_inst_245_);
lean_dec(v_pat_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(lean_object* v_00_u03c1_247_, lean_object* v_pat_248_, lean_object* v_s_249_, lean_object* v_inst_250_, lean_object* v_inst_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_box(0);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(lean_object* v_00_u03c1_253_, lean_object* v_pat_254_, lean_object* v_s_255_, lean_object* v_inst_256_, lean_object* v_inst_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(v_00_u03c1_253_, v_pat_254_, v_s_255_, v_inst_256_, v_inst_257_);
lean_dec_ref(v_inst_256_);
lean_dec_ref(v_s_255_);
lean_dec(v_pat_254_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(lean_object* v___y_259_, lean_object* v_acc_260_, lean_object* v_recur_261_, lean_object* v_s_262_){
_start:
{
switch(lean_obj_tag(v_s_262_))
{
case 0:
{
lean_object* v_it_263_; lean_object* v_out_264_; lean_object* v_val_265_; 
v_it_263_ = lean_ctor_get(v_s_262_, 0);
lean_inc(v_it_263_);
v_out_264_ = lean_ctor_get(v_s_262_, 1);
lean_inc(v_out_264_);
lean_dec_ref(v_s_262_);
v_val_265_ = lean_apply_3(v___y_259_, v_out_264_, lean_box(0), v_acc_260_);
if (lean_obj_tag(v_val_265_) == 0)
{
lean_object* v_a_266_; 
lean_dec(v_it_263_);
lean_dec(v_recur_261_);
v_a_266_ = lean_ctor_get(v_val_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref(v_val_265_);
return v_a_266_;
}
else
{
lean_object* v_a_267_; lean_object* v___x_268_; 
v_a_267_ = lean_ctor_get(v_val_265_, 0);
lean_inc(v_a_267_);
lean_dec_ref(v_val_265_);
v___x_268_ = lean_apply_4(v_recur_261_, v_it_263_, v_a_267_, lean_box(0), lean_box(0));
return v___x_268_;
}
}
case 1:
{
lean_object* v_it_269_; lean_object* v___x_270_; 
lean_dec_ref(v___y_259_);
v_it_269_ = lean_ctor_get(v_s_262_, 0);
lean_inc(v_it_269_);
lean_dec_ref(v_s_262_);
v___x_270_ = lean_apply_4(v_recur_261_, v_it_269_, v_acc_260_, lean_box(0), lean_box(0));
return v___x_270_;
}
default: 
{
lean_dec(v_recur_261_);
lean_dec_ref(v___y_259_);
return v_acc_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(lean_object* v_s_271_, lean_object* v___y_272_, lean_object* v_inst_273_, lean_object* v_lift_274_, lean_object* v_it_275_, lean_object* v_acc_276_, lean_object* v_hP_277_, lean_object* v_recur_278_){
_start:
{
lean_object* v_str_279_; lean_object* v_startInclusive_280_; lean_object* v_endExclusive_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_306_; 
v_str_279_ = lean_ctor_get(v_s_271_, 0);
v_startInclusive_280_ = lean_ctor_get(v_s_271_, 1);
v_endExclusive_281_ = lean_ctor_get(v_s_271_, 2);
v_isSharedCheck_306_ = !lean_is_exclusive(v_s_271_);
if (v_isSharedCheck_306_ == 0)
{
v___x_283_ = v_s_271_;
v_isShared_284_ = v_isSharedCheck_306_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_endExclusive_281_);
lean_inc(v_startInclusive_280_);
lean_inc(v_str_279_);
lean_dec(v_s_271_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_306_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___f_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___f_285_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_285_, 0, v___y_272_);
lean_closure_set(v___f_285_, 1, v_acc_276_);
lean_closure_set(v___f_285_, 2, v_recur_278_);
v___x_286_ = lean_nat_sub(v_endExclusive_281_, v_startInclusive_280_);
v___x_287_ = lean_nat_dec_eq(v_it_275_, v___x_286_);
lean_dec(v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v_dropPrefixOfNonempty_x3f_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v_dropPrefixOfNonempty_x3f_288_ = lean_ctor_get(v_inst_273_, 1);
lean_inc_ref(v_dropPrefixOfNonempty_x3f_288_);
lean_dec_ref(v_inst_273_);
v___x_289_ = lean_nat_add(v_startInclusive_280_, v_it_275_);
lean_inc(v___x_289_);
lean_inc_ref(v_str_279_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_289_);
v___x_291_ = v___x_283_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_str_279_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_endExclusive_281_);
v___x_291_ = v_reuseFailAlloc_303_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; 
v___x_292_ = lean_apply_2(v_dropPrefixOfNonempty_x3f_288_, v___x_291_, lean_box(0));
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_293_ = lean_string_utf8_next_fast(v_str_279_, v___x_289_);
lean_dec(v___x_289_);
lean_dec_ref(v_str_279_);
v___x_294_ = lean_nat_sub(v___x_293_, v_startInclusive_280_);
lean_dec(v_startInclusive_280_);
lean_inc(v___x_294_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v_it_275_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_apply_4(v_lift_274_, lean_box(0), lean_box(0), v___f_285_, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v_val_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v___x_289_);
lean_dec(v_startInclusive_280_);
lean_dec_ref(v_str_279_);
v_val_298_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_val_298_);
lean_dec_ref(v___x_292_);
v___x_299_ = lean_nat_add(v_it_275_, v_val_298_);
lean_dec(v_val_298_);
lean_inc(v___x_299_);
v___x_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_300_, 0, v_it_275_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_apply_4(v_lift_274_, lean_box(0), lean_box(0), v___f_285_, v___x_301_);
return v___x_302_;
}
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_del_object(v___x_283_);
lean_dec(v_endExclusive_281_);
lean_dec(v_startInclusive_280_);
lean_dec_ref(v_str_279_);
lean_dec(v_it_275_);
lean_dec_ref(v_inst_273_);
v___x_304_ = lean_box(2);
v___x_305_ = lean_apply_4(v_lift_274_, lean_box(0), lean_box(0), v___f_285_, v___x_304_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object* v_s_307_, lean_object* v_inst_308_, lean_object* v_lift_309_, lean_object* v_00_u03b3_310_, lean_object* v_Pl_311_, lean_object* v_it_312_, lean_object* v_init_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___f_315_; lean_object* v___x_316_; 
v___f_315_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1), 8, 4);
lean_closure_set(v___f_315_, 0, v_s_307_);
lean_closure_set(v___f_315_, 1, v___y_314_);
lean_closure_set(v___f_315_, 2, v_inst_308_);
lean_closure_set(v___f_315_, 3, v_lift_309_);
v___x_316_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_315_, v_it_312_, v_init_313_, lean_box(0));
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(lean_object* v_s_317_, lean_object* v_inst_318_){
_start:
{
lean_object* v___f_319_; 
v___f_319_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_319_, 0, v_s_317_);
lean_closure_set(v___f_319_, 1, v_inst_318_);
return v___f_319_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(lean_object* v_00_u03c1_320_, lean_object* v_pat_321_, lean_object* v_s_322_, lean_object* v_inst_323_){
_start:
{
lean_object* v___f_324_; 
v___f_324_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2), 8, 2);
lean_closure_set(v___f_324_, 0, v_s_322_);
lean_closure_set(v___f_324_, 1, v_inst_323_);
return v___f_324_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(lean_object* v_00_u03c1_325_, lean_object* v_pat_326_, lean_object* v_s_327_, lean_object* v_inst_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_325_, v_pat_326_, v_s_327_, v_inst_328_);
lean_dec(v_pat_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(lean_object* v_pat_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_331_, 0, lean_box(0));
lean_closure_set(v___x_331_, 1, v_pat_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(lean_object* v_00_u03c1_332_, lean_object* v_pat_333_, lean_object* v_inst_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_335_, 0, lean_box(0));
lean_closure_set(v___x_335_, 1, v_pat_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(lean_object* v_00_u03c1_336_, lean_object* v_pat_337_, lean_object* v_inst_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(v_00_u03c1_336_, v_pat_337_, v_inst_338_);
lean_dec_ref(v_inst_338_);
return v_res_339_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(lean_object* v_lhs_340_, lean_object* v_rhs_341_, lean_object* v_lstart_342_, lean_object* v_rstart_343_, lean_object* v_len_344_, lean_object* v_curr_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_nat_dec_lt(v_curr_345_, v_len_344_);
if (v___x_346_ == 0)
{
uint8_t v___x_347_; 
lean_dec(v_curr_345_);
v___x_347_ = 1;
return v___x_347_;
}
else
{
lean_object* v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; uint8_t v___x_352_; 
v___x_348_ = lean_nat_add(v_lstart_342_, v_curr_345_);
v___x_349_ = lean_string_get_byte_fast(v_lhs_340_, v___x_348_);
v___x_350_ = lean_nat_add(v_rstart_343_, v_curr_345_);
v___x_351_ = lean_string_get_byte_fast(v_rhs_341_, v___x_350_);
v___x_352_ = lean_uint8_dec_eq(v___x_349_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v_curr_345_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_curr_345_, v___x_353_);
lean_dec(v_curr_345_);
v_curr_345_ = v___x_354_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg___boxed(lean_object* v_lhs_356_, lean_object* v_rhs_357_, lean_object* v_lstart_358_, lean_object* v_rstart_359_, lean_object* v_len_360_, lean_object* v_curr_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_356_, v_rhs_357_, v_lstart_358_, v_rstart_359_, v_len_360_, v_curr_361_);
lean_dec(v_len_360_);
lean_dec(v_rstart_359_);
lean_dec(v_lstart_358_);
lean_dec_ref(v_rhs_357_);
lean_dec_ref(v_lhs_356_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(lean_object* v_lhs_364_, lean_object* v_rhs_365_, lean_object* v_lstart_366_, lean_object* v_rstart_367_, lean_object* v_len_368_, lean_object* v_h1_369_, lean_object* v_h2_370_, lean_object* v_curr_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_364_, v_rhs_365_, v_lstart_366_, v_rstart_367_, v_len_368_, v_curr_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(lean_object* v_lhs_373_, lean_object* v_rhs_374_, lean_object* v_lstart_375_, lean_object* v_rstart_376_, lean_object* v_len_377_, lean_object* v_h1_378_, lean_object* v_h2_379_, lean_object* v_curr_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(v_lhs_373_, v_rhs_374_, v_lstart_375_, v_rstart_376_, v_len_377_, v_h1_378_, v_h2_379_, v_curr_380_);
lean_dec(v_len_377_);
lean_dec(v_rstart_376_);
lean_dec(v_lstart_375_);
lean_dec_ref(v_rhs_374_);
lean_dec_ref(v_lhs_373_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpStr___boxed(lean_object* v_lhs_390_, lean_object* v_rhs_391_, lean_object* v_lstart_392_, lean_object* v_rstart_393_, lean_object* v_len_394_, lean_object* v_h1_395_, lean_object* v_h2_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = lean_string_memcmp(v_lhs_390_, v_rhs_391_, v_lstart_392_, v_rstart_393_, v_len_394_);
lean_dec(v_len_394_);
lean_dec(v_rstart_393_);
lean_dec(v_lstart_392_);
lean_dec_ref(v_rhs_391_);
lean_dec_ref(v_lhs_390_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice___redArg(lean_object* v_lhs_399_, lean_object* v_rhs_400_, lean_object* v_lstart_401_, lean_object* v_rstart_402_, lean_object* v_len_403_){
_start:
{
lean_object* v_str_404_; lean_object* v_startInclusive_405_; lean_object* v_str_406_; lean_object* v_startInclusive_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_str_404_ = lean_ctor_get(v_lhs_399_, 0);
v_startInclusive_405_ = lean_ctor_get(v_lhs_399_, 1);
v_str_406_ = lean_ctor_get(v_rhs_400_, 0);
v_startInclusive_407_ = lean_ctor_get(v_rhs_400_, 1);
v___x_408_ = lean_nat_add(v_startInclusive_405_, v_lstart_401_);
v___x_409_ = lean_nat_add(v_startInclusive_407_, v_rstart_402_);
v___x_410_ = lean_string_memcmp(v_str_404_, v_str_406_, v___x_408_, v___x_409_, v_len_403_);
lean_dec(v___x_409_);
lean_dec(v___x_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(lean_object* v_lhs_411_, lean_object* v_rhs_412_, lean_object* v_lstart_413_, lean_object* v_rstart_414_, lean_object* v_len_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(v_lhs_411_, v_rhs_412_, v_lstart_413_, v_rstart_414_, v_len_415_);
lean_dec(v_len_415_);
lean_dec(v_rstart_414_);
lean_dec(v_lstart_413_);
lean_dec_ref(v_rhs_412_);
lean_dec_ref(v_lhs_411_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Internal_memcmpSlice(lean_object* v_lhs_418_, lean_object* v_rhs_419_, lean_object* v_lstart_420_, lean_object* v_rstart_421_, lean_object* v_len_422_, lean_object* v_h1_423_, lean_object* v_h2_424_){
_start:
{
lean_object* v_str_425_; lean_object* v_startInclusive_426_; lean_object* v_str_427_; lean_object* v_startInclusive_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_str_425_ = lean_ctor_get(v_lhs_418_, 0);
v_startInclusive_426_ = lean_ctor_get(v_lhs_418_, 1);
v_str_427_ = lean_ctor_get(v_rhs_419_, 0);
v_startInclusive_428_ = lean_ctor_get(v_rhs_419_, 1);
v___x_429_ = lean_nat_add(v_startInclusive_426_, v_lstart_420_);
v___x_430_ = lean_nat_add(v_startInclusive_428_, v_rstart_421_);
v___x_431_ = lean_string_memcmp(v_str_425_, v_str_427_, v___x_429_, v___x_430_, v_len_422_);
lean_dec(v___x_430_);
lean_dec(v___x_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Internal_memcmpSlice___boxed(lean_object* v_lhs_432_, lean_object* v_rhs_433_, lean_object* v_lstart_434_, lean_object* v_rstart_435_, lean_object* v_len_436_, lean_object* v_h1_437_, lean_object* v_h2_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_String_Slice_Pattern_Internal_memcmpSlice(v_lhs_432_, v_rhs_433_, v_lstart_434_, v_rstart_435_, v_len_436_, v_h1_437_, v_h2_438_);
lean_dec(v_len_436_);
lean_dec(v_rstart_435_);
lean_dec(v_lstart_434_);
lean_dec_ref(v_rhs_433_);
lean_dec_ref(v_lhs_432_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_unsigned_to_nat(0u);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(v_a_445_, v_a_446_, v_a_447_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = lean_unsigned_to_nat(0u);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(v_a_453_, v_a_454_, v_a_455_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(lean_object* v_s_457_){
_start:
{
lean_object* v_startInclusive_458_; lean_object* v_endExclusive_459_; lean_object* v___x_460_; 
v_startInclusive_458_ = lean_ctor_get(v_s_457_, 1);
v_endExclusive_459_ = lean_ctor_get(v_s_457_, 2);
v___x_460_ = lean_nat_sub(v_endExclusive_459_, v_startInclusive_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(lean_object* v_s_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_461_);
lean_dec_ref(v_s_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(lean_object* v_00_u03c1_463_, lean_object* v_pat_464_, lean_object* v_s_465_){
_start:
{
lean_object* v_startInclusive_466_; lean_object* v_endExclusive_467_; lean_object* v___x_468_; 
v_startInclusive_466_ = lean_ctor_get(v_s_465_, 1);
v_endExclusive_467_ = lean_ctor_get(v_s_465_, 2);
v___x_468_ = lean_nat_sub(v_endExclusive_467_, v_startInclusive_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object* v_00_u03c1_469_, lean_object* v_pat_470_, lean_object* v_s_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(v_00_u03c1_469_, v_pat_470_, v_s_471_);
lean_dec_ref(v_s_471_);
lean_dec(v_pat_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(lean_object* v_inst_473_, lean_object* v_s_474_, lean_object* v_it_475_){
_start:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_nat_dec_eq(v_it_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v_dropSuffixOfNonempty_x3f_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_497_; 
v_dropSuffixOfNonempty_x3f_478_ = lean_ctor_get(v_inst_473_, 1);
v_isSharedCheck_497_ = !lean_is_exclusive(v_inst_473_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_498_ = lean_ctor_get(v_inst_473_, 2);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_inst_473_, 0);
lean_dec(v_unused_499_);
v___x_480_ = v_inst_473_;
v_isShared_481_ = v_isSharedCheck_497_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_dropSuffixOfNonempty_x3f_478_);
lean_dec(v_inst_473_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_497_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v_str_482_; lean_object* v_startInclusive_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v_str_482_ = lean_ctor_get(v_s_474_, 0);
v_startInclusive_483_ = lean_ctor_get(v_s_474_, 1);
v___x_484_ = lean_nat_add(v_startInclusive_483_, v_it_475_);
lean_inc(v_startInclusive_483_);
lean_inc_ref(v_str_482_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 2, v___x_484_);
lean_ctor_set(v___x_480_, 1, v_startInclusive_483_);
lean_ctor_set(v___x_480_, 0, v_str_482_);
v___x_486_ = v___x_480_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_str_482_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_startInclusive_483_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v___x_484_);
v___x_486_ = v_reuseFailAlloc_496_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; 
v___x_487_ = lean_apply_2(v_dropSuffixOfNonempty_x3f_478_, v___x_486_, lean_box(0));
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_sub(v_it_475_, v___x_488_);
v___x_490_ = l_String_Slice_posLE(v_s_474_, v___x_489_);
lean_inc(v___x_490_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v_it_475_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
return v___x_492_;
}
else
{
lean_object* v_val_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_val_493_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_val_493_);
lean_dec_ref(v___x_487_);
lean_inc(v_val_493_);
v___x_494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_494_, 0, v_val_493_);
lean_ctor_set(v___x_494_, 1, v_it_475_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v_val_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
return v___x_495_;
}
}
}
}
else
{
lean_object* v___x_500_; 
lean_dec(v_it_475_);
lean_dec_ref(v_inst_473_);
v___x_500_ = lean_box(2);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(lean_object* v_inst_501_, lean_object* v_s_502_, lean_object* v_it_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_501_, v_s_502_, v_it_503_);
lean_dec_ref(v_s_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(lean_object* v_s_505_, lean_object* v_inst_506_){
_start:
{
lean_object* v___f_507_; 
v___f_507_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_507_, 0, v_inst_506_);
lean_closure_set(v___f_507_, 1, v_s_505_);
return v___f_507_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(lean_object* v_00_u03c1_508_, lean_object* v_pat_509_, lean_object* v_s_510_, lean_object* v_inst_511_){
_start:
{
lean_object* v___f_512_; 
v___f_512_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_512_, 0, v_inst_511_);
lean_closure_set(v___f_512_, 1, v_s_510_);
return v___f_512_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(lean_object* v_00_u03c1_513_, lean_object* v_pat_514_, lean_object* v_s_515_, lean_object* v_inst_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_513_, v_pat_514_, v_s_515_, v_inst_516_);
lean_dec(v_pat_514_);
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
lean_object* v___f_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___f_538_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0), 4, 3);
lean_closure_set(v___f_538_, 0, v___y_530_);
lean_closure_set(v___f_538_, 1, v_acc_535_);
lean_closure_set(v___f_538_, 2, v_recur_537_);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_nat_dec_eq(v_it_534_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v_dropSuffixOfNonempty_x3f_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_562_; 
v_dropSuffixOfNonempty_x3f_541_ = lean_ctor_get(v_inst_531_, 1);
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
lean_inc(v_dropSuffixOfNonempty_x3f_541_);
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
v___x_550_ = lean_apply_2(v_dropSuffixOfNonempty_x3f_541_, v___x_549_, lean_box(0));
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
lean_inc(v_val_557_);
lean_dec_ref(v___x_550_);
lean_inc(v_val_557_);
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
