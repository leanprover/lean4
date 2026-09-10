// Lean compiler output
// Module: Init.Data.String.Pattern.String
// Imports: public import Init.Data.String.Pattern.Basic public import Init.Data.Vector.Basic public import Init.Data.String.FindPos import Init.Data.String.Termination import Init.Data.String.Lemmas.FindPos import Init.ByCases import Init.Data.Array.Lemmas import Init.Data.Option.Lemmas import Init.Omega
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
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_remainingBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0 = (const lean_object*)&l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0 = (const lean_object*)&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(lean_object* v_pat_1_, uint8_t v_patByte_2_, lean_object* v_table_3_, lean_object* v_guess_4_){
_start:
{
lean_object* v_str_5_; lean_object* v_startInclusive_6_; lean_object* v___x_7_; uint8_t v___x_8_; uint8_t v___x_9_; 
v_str_5_ = lean_ctor_get(v_pat_1_, 0);
v_startInclusive_6_ = lean_ctor_get(v_pat_1_, 1);
v___x_7_ = lean_nat_add(v_startInclusive_6_, v_guess_4_);
v___x_8_ = lean_string_get_byte_fast(v_str_5_, v___x_7_);
v___x_9_ = lean_uint8_dec_eq(v___x_8_, v_patByte_2_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_nat_dec_eq(v_guess_4_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_sub(v_guess_4_, v___x_12_);
v___x_14_ = lean_array_fget_borrowed(v_table_3_, v___x_13_);
lean_dec(v___x_13_);
v_guess_4_ = v___x_14_;
goto _start;
}
else
{
return v___x_10_;
}
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_add(v_guess_4_, v___x_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg___boxed(lean_object* v_pat_18_, lean_object* v_patByte_19_, lean_object* v_table_20_, lean_object* v_guess_21_){
_start:
{
uint8_t v_patByte_boxed_22_; lean_object* v_res_23_; 
v_patByte_boxed_22_ = lean_unbox(v_patByte_19_);
v_res_23_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_18_, v_patByte_boxed_22_, v_table_20_, v_guess_21_);
lean_dec(v_guess_21_);
lean_dec_ref(v_table_20_);
lean_dec_ref(v_pat_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(lean_object* v_pat_24_, uint8_t v_patByte_25_, lean_object* v_table_26_, lean_object* v_ht_27_, lean_object* v_h_28_, lean_object* v_guess_29_, lean_object* v_hg_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_24_, v_patByte_25_, v_table_26_, v_guess_29_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___boxed(lean_object* v_pat_32_, lean_object* v_patByte_33_, lean_object* v_table_34_, lean_object* v_ht_35_, lean_object* v_h_36_, lean_object* v_guess_37_, lean_object* v_hg_38_){
_start:
{
uint8_t v_patByte_boxed_39_; lean_object* v_res_40_; 
v_patByte_boxed_39_ = lean_unbox(v_patByte_33_);
v_res_40_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(v_pat_32_, v_patByte_boxed_39_, v_table_34_, v_ht_35_, v_h_36_, v_guess_37_, v_hg_38_);
lean_dec(v_guess_37_);
lean_dec_ref(v_table_34_);
lean_dec_ref(v_pat_32_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(lean_object* v_pat_41_, lean_object* v_table_42_){
_start:
{
lean_object* v_str_43_; lean_object* v_startInclusive_44_; lean_object* v_endExclusive_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v_str_43_ = lean_ctor_get(v_pat_41_, 0);
v_startInclusive_44_ = lean_ctor_get(v_pat_41_, 1);
v_endExclusive_45_ = lean_ctor_get(v_pat_41_, 2);
v___x_46_ = lean_array_get_size(v_table_42_);
v___x_47_ = lean_nat_sub(v_endExclusive_45_, v_startInclusive_44_);
v___x_48_ = lean_nat_dec_lt(v___x_46_, v___x_47_);
lean_dec(v___x_47_);
if (v___x_48_ == 0)
{
return v_table_42_;
}
else
{
lean_object* v___x_49_; uint8_t v_patByte_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v_dist_54_; lean_object* v___x_55_; 
v___x_49_ = lean_nat_add(v_startInclusive_44_, v___x_46_);
v_patByte_50_ = lean_string_get_byte_fast(v_str_43_, v___x_49_);
v___x_51_ = lean_unsigned_to_nat(1u);
v___x_52_ = lean_nat_sub(v___x_46_, v___x_51_);
v___x_53_ = lean_array_fget_borrowed(v_table_42_, v___x_52_);
lean_dec(v___x_52_);
v_dist_54_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_41_, v_patByte_50_, v_table_42_, v___x_53_);
v___x_55_ = lean_array_push(v_table_42_, v_dist_54_);
v_table_42_ = v___x_55_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg___boxed(lean_object* v_pat_57_, lean_object* v_table_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_57_, v_table_58_);
lean_dec_ref(v_pat_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(lean_object* v_pat_60_, lean_object* v_table_61_, lean_object* v_ht_u2080_62_, lean_object* v_ht_63_, lean_object* v_h_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_60_, v_table_61_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___boxed(lean_object* v_pat_66_, lean_object* v_table_67_, lean_object* v_ht_u2080_68_, lean_object* v_ht_69_, lean_object* v_h_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(v_pat_66_, v_table_67_, v_ht_u2080_68_, v_ht_69_, v_h_70_);
lean_dec_ref(v_pat_66_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object* v_pat_74_){
_start:
{
lean_object* v_startInclusive_75_; lean_object* v_endExclusive_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_startInclusive_75_ = lean_ctor_get(v_pat_74_, 1);
v_endExclusive_76_ = lean_ctor_get(v_pat_74_, 2);
v___x_77_ = lean_nat_sub(v_endExclusive_76_, v_startInclusive_75_);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v_arr_80_; lean_object* v_arr_x27_81_; lean_object* v___x_82_; 
v_arr_80_ = lean_mk_empty_array_with_capacity(v___x_77_);
lean_dec(v___x_77_);
v_arr_x27_81_ = lean_array_push(v_arr_80_, v___x_78_);
v___x_82_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_74_, v_arr_x27_81_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; 
lean_dec(v___x_77_);
v___x_83_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0));
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___boxed(lean_object* v_pat_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_84_);
lean_dec_ref(v_pat_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(lean_object* v_x_86_){
_start:
{
switch(lean_obj_tag(v_x_86_))
{
case 0:
{
lean_object* v___x_87_; 
v___x_87_ = lean_unsigned_to_nat(0u);
return v___x_87_;
}
case 1:
{
lean_object* v___x_88_; 
v___x_88_ = lean_unsigned_to_nat(1u);
return v___x_88_;
}
case 2:
{
lean_object* v___x_89_; 
v___x_89_ = lean_unsigned_to_nat(2u);
return v___x_89_;
}
default: 
{
lean_object* v___x_90_; 
v___x_90_ = lean_unsigned_to_nat(3u);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg___boxed(lean_object* v_x_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(v_x_91_);
lean_dec(v_x_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx(lean_object* v_s_93_, lean_object* v_x_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(v_x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___boxed(lean_object* v_s_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx(v_s_96_, v_x_97_);
lean_dec(v_x_97_);
lean_dec_ref(v_s_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(lean_object* v_t_99_, lean_object* v_k_100_){
_start:
{
switch(lean_obj_tag(v_t_99_))
{
case 0:
{
lean_object* v_pos_101_; lean_object* v___x_102_; 
v_pos_101_ = lean_ctor_get(v_t_99_, 0);
lean_inc(v_pos_101_);
lean_dec_ref_known(v_t_99_, 1);
v___x_102_ = lean_apply_1(v_k_100_, v_pos_101_);
return v___x_102_;
}
case 1:
{
lean_object* v_pos_103_; lean_object* v___x_104_; 
v_pos_103_ = lean_ctor_get(v_t_99_, 0);
lean_inc(v_pos_103_);
lean_dec_ref_known(v_t_99_, 1);
v___x_104_ = lean_apply_2(v_k_100_, v_pos_103_, lean_box(0));
return v___x_104_;
}
case 2:
{
lean_object* v_needle_105_; lean_object* v_table_106_; lean_object* v_stackPos_107_; lean_object* v_needlePos_108_; lean_object* v___x_109_; 
v_needle_105_ = lean_ctor_get(v_t_99_, 0);
lean_inc_ref(v_needle_105_);
v_table_106_ = lean_ctor_get(v_t_99_, 1);
lean_inc_ref(v_table_106_);
v_stackPos_107_ = lean_ctor_get(v_t_99_, 2);
lean_inc(v_stackPos_107_);
v_needlePos_108_ = lean_ctor_get(v_t_99_, 3);
lean_inc(v_needlePos_108_);
lean_dec_ref_known(v_t_99_, 4);
v___x_109_ = lean_apply_6(v_k_100_, v_needle_105_, v_table_106_, lean_box(0), v_stackPos_107_, v_needlePos_108_, lean_box(0));
return v___x_109_;
}
default: 
{
return v_k_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(lean_object* v_s_110_, lean_object* v_motive_111_, lean_object* v_ctorIdx_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_k_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_113_, v_k_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___boxed(lean_object* v_s_117_, lean_object* v_motive_118_, lean_object* v_ctorIdx_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_k_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(v_s_117_, v_motive_118_, v_ctorIdx_119_, v_t_120_, v_h_121_, v_k_122_);
lean_dec(v_ctorIdx_119_);
lean_dec_ref(v_s_117_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___redArg(lean_object* v_t_124_, lean_object* v_emptyBefore_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_124_, v_emptyBefore_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(lean_object* v_s_127_, lean_object* v_motive_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_emptyBefore_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_129_, v_emptyBefore_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___boxed(lean_object* v_s_133_, lean_object* v_motive_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_emptyBefore_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(v_s_133_, v_motive_134_, v_t_135_, v_h_136_, v_emptyBefore_137_);
lean_dec_ref(v_s_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___redArg(lean_object* v_t_139_, lean_object* v_emptyAt_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_139_, v_emptyAt_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(lean_object* v_s_142_, lean_object* v_motive_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_emptyAt_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_144_, v_emptyAt_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___boxed(lean_object* v_s_148_, lean_object* v_motive_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_emptyAt_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(v_s_148_, v_motive_149_, v_t_150_, v_h_151_, v_emptyAt_152_);
lean_dec_ref(v_s_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___redArg(lean_object* v_t_154_, lean_object* v_proper_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_154_, v_proper_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(lean_object* v_s_157_, lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_proper_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_159_, v_proper_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___boxed(lean_object* v_s_163_, lean_object* v_motive_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_proper_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(v_s_163_, v_motive_164_, v_t_165_, v_h_166_, v_proper_167_);
lean_dec_ref(v_s_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___redArg(lean_object* v_t_169_, lean_object* v_atEnd_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_169_, v_atEnd_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(lean_object* v_s_172_, lean_object* v_motive_173_, lean_object* v_t_174_, lean_object* v_h_175_, lean_object* v_atEnd_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_174_, v_atEnd_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___boxed(lean_object* v_s_178_, lean_object* v_motive_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_atEnd_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(v_s_178_, v_motive_179_, v_t_180_, v_h_181_, v_atEnd_182_);
lean_dec_ref(v_s_178_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(lean_object* v_s_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0));
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___boxed(lean_object* v_s_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(v_s_188_);
lean_dec_ref(v_s_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(lean_object* v_a_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(v_a_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___boxed(lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(v_a_192_);
lean_dec_ref(v_a_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___redArg(lean_object* v_pat_194_){
_start:
{
lean_object* v_startInclusive_195_; lean_object* v_endExclusive_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_startInclusive_195_ = lean_ctor_get(v_pat_194_, 1);
v_endExclusive_196_ = lean_ctor_get(v_pat_194_, 2);
v___x_197_ = lean_nat_sub(v_endExclusive_196_, v_startInclusive_195_);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_nat_dec_eq(v___x_197_, v___x_198_);
lean_dec(v___x_197_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_194_);
v___x_201_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_201_, 0, v_pat_194_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
lean_ctor_set(v___x_201_, 2, v___x_198_);
lean_ctor_set(v___x_201_, 3, v___x_198_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; 
lean_dec_ref(v_pat_194_);
v___x_202_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0));
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter(lean_object* v_pat_203_, lean_object* v_s_204_){
_start:
{
lean_object* v_startInclusive_205_; lean_object* v_endExclusive_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_startInclusive_205_ = lean_ctor_get(v_pat_203_, 1);
v_endExclusive_206_ = lean_ctor_get(v_pat_203_, 2);
v___x_207_ = lean_nat_sub(v_endExclusive_206_, v_startInclusive_205_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_nat_dec_eq(v___x_207_, v___x_208_);
lean_dec(v___x_207_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_203_);
v___x_211_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_211_, 0, v_pat_203_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
lean_ctor_set(v___x_211_, 2, v___x_208_);
lean_ctor_set(v___x_211_, 3, v___x_208_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; 
lean_dec_ref(v_pat_203_);
v___x_212_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0));
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed(lean_object* v_pat_213_, lean_object* v_s_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_String_Slice_Pattern_ForwardSliceSearcher_iter(v_pat_213_, v_s_214_);
lean_dec_ref(v_s_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(lean_object* v_s_216_, lean_object* v_x_217_){
_start:
{
switch(lean_obj_tag(v_x_217_))
{
case 0:
{
lean_object* v_pos_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_233_; 
v_pos_218_ = lean_ctor_get(v_x_217_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_217_);
if (v_isSharedCheck_233_ == 0)
{
v___x_220_ = v_x_217_;
v_isShared_221_ = v_isSharedCheck_233_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_pos_218_);
lean_dec(v_x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_233_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_res_222_; lean_object* v_startInclusive_223_; lean_object* v_endExclusive_224_; lean_object* v___x_225_; uint8_t v_decide_226_; 
lean_inc_n(v_pos_218_, 2);
v_res_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_222_, 0, v_pos_218_);
lean_ctor_set(v_res_222_, 1, v_pos_218_);
v_startInclusive_223_ = lean_ctor_get(v_s_216_, 1);
v_endExclusive_224_ = lean_ctor_get(v_s_216_, 2);
v___x_225_ = lean_nat_sub(v_endExclusive_224_, v_startInclusive_223_);
v_decide_226_ = lean_nat_dec_eq(v_pos_218_, v___x_225_);
lean_dec(v___x_225_);
if (v_decide_226_ == 0)
{
lean_object* v___x_228_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 1);
v___x_228_ = v___x_220_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_pos_218_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_res_222_);
return v___x_229_;
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_del_object(v___x_220_);
lean_dec(v_pos_218_);
v___x_231_ = lean_box(3);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v_res_222_);
return v___x_232_;
}
}
}
case 1:
{
lean_object* v_pos_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_248_; 
v_pos_234_ = lean_ctor_get(v_x_217_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_217_);
if (v_isSharedCheck_248_ == 0)
{
v___x_236_ = v_x_217_;
v_isShared_237_ = v_isSharedCheck_248_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_pos_234_);
lean_dec(v_x_217_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_248_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_str_238_; lean_object* v_startInclusive_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v_res_243_; lean_object* v___x_245_; 
v_str_238_ = lean_ctor_get(v_s_216_, 0);
v_startInclusive_239_ = lean_ctor_get(v_s_216_, 1);
v___x_240_ = lean_nat_add(v_startInclusive_239_, v_pos_234_);
v___x_241_ = lean_string_utf8_next_fast(v_str_238_, v___x_240_);
lean_dec(v___x_240_);
v___x_242_ = lean_nat_sub(v___x_241_, v_startInclusive_239_);
lean_inc(v___x_242_);
v_res_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_243_, 0, v_pos_234_);
lean_ctor_set(v_res_243_, 1, v___x_242_);
if (v_isShared_237_ == 0)
{
lean_ctor_set_tag(v___x_236_, 0);
lean_ctor_set(v___x_236_, 0, v___x_242_);
v___x_245_ = v___x_236_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_242_);
v___x_245_ = v_reuseFailAlloc_247_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v_res_243_);
return v___x_246_;
}
}
}
case 2:
{
lean_object* v_needle_249_; lean_object* v_table_250_; lean_object* v_stackPos_251_; lean_object* v_needlePos_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_327_; 
v_needle_249_ = lean_ctor_get(v_x_217_, 0);
v_table_250_ = lean_ctor_get(v_x_217_, 1);
v_stackPos_251_ = lean_ctor_get(v_x_217_, 2);
v_needlePos_252_ = lean_ctor_get(v_x_217_, 3);
v_isSharedCheck_327_ = !lean_is_exclusive(v_x_217_);
if (v_isSharedCheck_327_ == 0)
{
v___x_254_ = v_x_217_;
v_isShared_255_ = v_isSharedCheck_327_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_needlePos_252_);
lean_inc(v_stackPos_251_);
lean_inc(v_table_250_);
lean_inc(v_needle_249_);
lean_dec(v_x_217_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_327_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_str_256_; lean_object* v_startInclusive_257_; lean_object* v_endExclusive_258_; lean_object* v_str_259_; lean_object* v_startInclusive_260_; lean_object* v_endExclusive_261_; lean_object* v_basePos_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_str_256_ = lean_ctor_get(v_needle_249_, 0);
v_startInclusive_257_ = lean_ctor_get(v_needle_249_, 1);
v_endExclusive_258_ = lean_ctor_get(v_needle_249_, 2);
v_str_259_ = lean_ctor_get(v_s_216_, 0);
v_startInclusive_260_ = lean_ctor_get(v_s_216_, 1);
v_endExclusive_261_ = lean_ctor_get(v_s_216_, 2);
v_basePos_262_ = lean_nat_sub(v_stackPos_251_, v_needlePos_252_);
v___x_263_ = lean_nat_sub(v_endExclusive_258_, v_startInclusive_257_);
v___x_264_ = lean_nat_add(v_basePos_262_, v___x_263_);
v___x_265_ = lean_nat_sub(v_endExclusive_261_, v_startInclusive_260_);
v___x_266_ = lean_nat_dec_le(v___x_264_, v___x_265_);
lean_dec(v___x_264_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
lean_dec(v___x_263_);
lean_del_object(v___x_254_);
lean_dec(v_needlePos_252_);
lean_dec(v_stackPos_251_);
lean_dec_ref(v_table_250_);
lean_dec_ref(v_needle_249_);
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_add(v_basePos_262_, v___x_267_);
v___x_269_ = lean_nat_dec_le(v___x_268_, v___x_265_);
lean_dec(v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
lean_dec(v___x_265_);
lean_dec(v_basePos_262_);
v___x_270_ = lean_box(2);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v_res_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = l_String_Slice_pos_x21(v_s_216_, v_basePos_262_);
lean_dec(v_basePos_262_);
v_res_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_272_, 0, v___x_271_);
lean_ctor_set(v_res_272_, 1, v___x_265_);
v___x_273_ = lean_box(3);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v_res_272_);
return v___x_274_;
}
}
else
{
lean_object* v___x_275_; uint8_t v_stackByte_276_; lean_object* v___x_277_; uint8_t v_patByte_278_; uint8_t v___x_279_; 
lean_dec(v___x_265_);
v___x_275_ = lean_nat_add(v_startInclusive_260_, v_stackPos_251_);
v_stackByte_276_ = lean_string_get_byte_fast(v_str_259_, v___x_275_);
v___x_277_ = lean_nat_add(v_startInclusive_257_, v_needlePos_252_);
v_patByte_278_ = lean_string_get_byte_fast(v_str_256_, v___x_277_);
v___x_279_ = lean_uint8_dec_eq(v_stackByte_276_, v_patByte_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; uint8_t v_decide_281_; 
lean_dec(v___x_263_);
v___x_280_ = lean_unsigned_to_nat(0u);
v_decide_281_ = lean_nat_dec_eq(v_needlePos_252_, v___x_280_);
if (v_decide_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_newNeedlePos_284_; uint8_t v___x_285_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_sub(v_needlePos_252_, v___x_282_);
lean_dec(v_needlePos_252_);
v_newNeedlePos_284_ = lean_array_fget_borrowed(v_table_250_, v___x_283_);
lean_dec(v___x_283_);
v___x_285_ = lean_nat_dec_eq(v_newNeedlePos_284_, v___x_280_);
if (v___x_285_ == 0)
{
lean_object* v_oldBasePos_286_; lean_object* v___x_287_; lean_object* v_newBasePos_288_; lean_object* v_res_289_; lean_object* v___x_291_; 
lean_inc(v_newNeedlePos_284_);
v_oldBasePos_286_ = l_String_Slice_pos_x21(v_s_216_, v_basePos_262_);
lean_dec(v_basePos_262_);
v___x_287_ = lean_nat_sub(v_stackPos_251_, v_newNeedlePos_284_);
v_newBasePos_288_ = l_String_Slice_pos_x21(v_s_216_, v___x_287_);
lean_dec(v___x_287_);
v_res_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_289_, 0, v_oldBasePos_286_);
lean_ctor_set(v_res_289_, 1, v_newBasePos_288_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v_newNeedlePos_284_);
v___x_291_ = v___x_254_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_needle_249_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_table_250_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_stackPos_251_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_newNeedlePos_284_);
v___x_291_ = v_reuseFailAlloc_293_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; 
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_res_289_);
return v___x_292_;
}
}
else
{
lean_object* v_basePos_294_; lean_object* v_nextStackPos_295_; lean_object* v_res_296_; lean_object* v___x_298_; 
v_basePos_294_ = l_String_Slice_pos_x21(v_s_216_, v_basePos_262_);
lean_dec(v_basePos_262_);
v_nextStackPos_295_ = l_String_Slice_posGE___redArg(v_s_216_, v_stackPos_251_);
lean_inc(v_nextStackPos_295_);
v_res_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_296_, 0, v_basePos_294_);
lean_ctor_set(v_res_296_, 1, v_nextStackPos_295_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v___x_280_);
lean_ctor_set(v___x_254_, 2, v_nextStackPos_295_);
v___x_298_ = v___x_254_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_needle_249_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_table_250_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v_nextStackPos_295_);
lean_ctor_set(v_reuseFailAlloc_300_, 3, v___x_280_);
v___x_298_ = v_reuseFailAlloc_300_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; 
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_res_296_);
return v___x_299_;
}
}
}
else
{
lean_object* v_basePos_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_nextStackPos_304_; lean_object* v_res_305_; lean_object* v___x_307_; 
lean_dec(v_basePos_262_);
lean_dec(v_needlePos_252_);
v_basePos_301_ = l_String_Slice_pos_x21(v_s_216_, v_stackPos_251_);
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_stackPos_251_, v___x_302_);
lean_dec(v_stackPos_251_);
v_nextStackPos_304_ = l_String_Slice_posGE___redArg(v_s_216_, v___x_303_);
lean_inc(v_nextStackPos_304_);
v_res_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_305_, 0, v_basePos_301_);
lean_ctor_set(v_res_305_, 1, v_nextStackPos_304_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v___x_280_);
lean_ctor_set(v___x_254_, 2, v_nextStackPos_304_);
v___x_307_ = v___x_254_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_needle_249_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_table_250_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_nextStackPos_304_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v___x_280_);
v___x_307_ = v_reuseFailAlloc_309_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; 
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_res_305_);
return v___x_308_;
}
}
}
else
{
lean_object* v___x_310_; lean_object* v_nextStackPos_311_; lean_object* v_nextNeedlePos_312_; uint8_t v_decide_313_; 
lean_dec(v_basePos_262_);
v___x_310_ = lean_unsigned_to_nat(1u);
v_nextStackPos_311_ = lean_nat_add(v_stackPos_251_, v___x_310_);
lean_dec(v_stackPos_251_);
v_nextNeedlePos_312_ = lean_nat_add(v_needlePos_252_, v___x_310_);
lean_dec(v_needlePos_252_);
v_decide_313_ = lean_nat_dec_eq(v_nextNeedlePos_312_, v___x_263_);
lean_dec(v___x_263_);
if (v_decide_313_ == 0)
{
lean_object* v___x_315_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v_nextNeedlePos_312_);
lean_ctor_set(v___x_254_, 2, v_nextStackPos_311_);
v___x_315_ = v___x_254_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_needle_249_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_table_250_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_nextStackPos_311_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_nextNeedlePos_312_);
v___x_315_ = v_reuseFailAlloc_317_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; 
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_res_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_318_ = lean_nat_sub(v_nextStackPos_311_, v_nextNeedlePos_312_);
lean_dec(v_nextNeedlePos_312_);
v___x_319_ = l_String_Slice_pos_x21(v_s_216_, v___x_318_);
lean_dec(v___x_318_);
v___x_320_ = l_String_Slice_pos_x21(v_s_216_, v_nextStackPos_311_);
v_res_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_321_, 0, v___x_319_);
lean_ctor_set(v_res_321_, 1, v___x_320_);
v___x_322_ = lean_unsigned_to_nat(0u);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v___x_322_);
lean_ctor_set(v___x_254_, 2, v_nextStackPos_311_);
v___x_324_ = v___x_254_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_needle_249_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_table_250_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_nextStackPos_311_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v___x_322_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v_res_321_);
return v___x_325_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_328_; 
v___x_328_ = lean_box(2);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed(lean_object* v_s_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(v_s_329_, v_x_330_);
lean_dec_ref(v_s_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep(lean_object* v_s_332_){
_start:
{
lean_object* v___f_333_; 
v___f_333_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed), 2, 1);
lean_closure_set(v___f_333_, 0, v_s_332_);
return v___f_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(lean_object* v_s_334_, lean_object* v_x_335_){
_start:
{
switch(lean_obj_tag(v_x_335_))
{
case 0:
{
lean_object* v_pos_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_346_; 
v_pos_336_ = lean_ctor_get(v_x_335_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_335_);
if (v_isSharedCheck_346_ == 0)
{
v___x_338_ = v_x_335_;
v_isShared_339_ = v_isSharedCheck_346_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_pos_336_);
lean_dec(v_x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_346_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_340_ = l_String_Slice_Pos_remainingBytes(v_s_334_, v_pos_336_);
lean_dec(v_pos_336_);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 1);
lean_ctor_set(v___x_338_, 0, v___x_342_);
v___x_344_ = v___x_338_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
case 1:
{
lean_object* v_pos_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_357_; 
v_pos_347_ = lean_ctor_get(v_x_335_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v_x_335_);
if (v_isSharedCheck_357_ == 0)
{
v___x_349_ = v_x_335_;
v_isShared_350_ = v_isSharedCheck_357_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_pos_347_);
lean_dec(v_x_335_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_357_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_351_ = l_String_Slice_Pos_remainingBytes(v_s_334_, v_pos_347_);
lean_dec(v_pos_347_);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_353_);
v___x_355_ = v___x_349_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
case 2:
{
lean_object* v_stackPos_358_; lean_object* v_needlePos_359_; lean_object* v_startInclusive_360_; lean_object* v_endExclusive_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_stackPos_358_ = lean_ctor_get(v_x_335_, 2);
lean_inc(v_stackPos_358_);
v_needlePos_359_ = lean_ctor_get(v_x_335_, 3);
lean_inc(v_needlePos_359_);
lean_dec_ref_known(v_x_335_, 4);
v_startInclusive_360_ = lean_ctor_get(v_s_334_, 1);
v_endExclusive_361_ = lean_ctor_get(v_s_334_, 2);
v___x_362_ = lean_nat_sub(v_endExclusive_361_, v_startInclusive_360_);
v___x_363_ = lean_nat_sub(v___x_362_, v_stackPos_358_);
lean_dec(v_stackPos_358_);
lean_dec(v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_needlePos_359_);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
default: 
{
lean_object* v___x_366_; 
v___x_366_ = lean_box(0);
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption___boxed(lean_object* v_s_367_, lean_object* v_x_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(v_s_367_, v_x_368_);
lean_dec_ref(v_s_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(lean_object* v_s_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(lean_object* v_s_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(v_s_372_);
lean_dec_ref(v_s_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(lean_object* v_x_374_, lean_object* v_h__1_375_, lean_object* v_h__2_376_, lean_object* v_h__3_377_, lean_object* v_h__4_378_){
_start:
{
switch(lean_obj_tag(v_x_374_))
{
case 0:
{
lean_object* v_pos_379_; lean_object* v___x_380_; 
lean_dec(v_h__4_378_);
lean_dec(v_h__3_377_);
lean_dec(v_h__2_376_);
v_pos_379_ = lean_ctor_get(v_x_374_, 0);
lean_inc(v_pos_379_);
lean_dec_ref_known(v_x_374_, 1);
v___x_380_ = lean_apply_1(v_h__1_375_, v_pos_379_);
return v___x_380_;
}
case 1:
{
lean_object* v_pos_381_; lean_object* v___x_382_; 
lean_dec(v_h__4_378_);
lean_dec(v_h__3_377_);
lean_dec(v_h__1_375_);
v_pos_381_ = lean_ctor_get(v_x_374_, 0);
lean_inc(v_pos_381_);
lean_dec_ref_known(v_x_374_, 1);
v___x_382_ = lean_apply_2(v_h__2_376_, v_pos_381_, lean_box(0));
return v___x_382_;
}
case 2:
{
lean_object* v_needle_383_; lean_object* v_table_384_; lean_object* v_stackPos_385_; lean_object* v_needlePos_386_; lean_object* v___x_387_; 
lean_dec(v_h__4_378_);
lean_dec(v_h__2_376_);
lean_dec(v_h__1_375_);
v_needle_383_ = lean_ctor_get(v_x_374_, 0);
lean_inc_ref(v_needle_383_);
v_table_384_ = lean_ctor_get(v_x_374_, 1);
lean_inc_ref(v_table_384_);
v_stackPos_385_ = lean_ctor_get(v_x_374_, 2);
lean_inc(v_stackPos_385_);
v_needlePos_386_ = lean_ctor_get(v_x_374_, 3);
lean_inc(v_needlePos_386_);
lean_dec_ref_known(v_x_374_, 4);
v___x_387_ = lean_apply_6(v_h__3_377_, v_needle_383_, v_table_384_, lean_box(0), v_stackPos_385_, v_needlePos_386_, lean_box(0));
return v___x_387_;
}
default: 
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v_h__3_377_);
lean_dec(v_h__2_376_);
lean_dec(v_h__1_375_);
v___x_388_ = lean_box(0);
v___x_389_ = lean_apply_1(v_h__4_378_, v___x_388_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(lean_object* v_s_390_, lean_object* v_motive_391_, lean_object* v_x_392_, lean_object* v_h__1_393_, lean_object* v_h__2_394_, lean_object* v_h__3_395_, lean_object* v_h__4_396_){
_start:
{
switch(lean_obj_tag(v_x_392_))
{
case 0:
{
lean_object* v_pos_397_; lean_object* v___x_398_; 
lean_dec(v_h__4_396_);
lean_dec(v_h__3_395_);
lean_dec(v_h__2_394_);
v_pos_397_ = lean_ctor_get(v_x_392_, 0);
lean_inc(v_pos_397_);
lean_dec_ref_known(v_x_392_, 1);
v___x_398_ = lean_apply_1(v_h__1_393_, v_pos_397_);
return v___x_398_;
}
case 1:
{
lean_object* v_pos_399_; lean_object* v___x_400_; 
lean_dec(v_h__4_396_);
lean_dec(v_h__3_395_);
lean_dec(v_h__1_393_);
v_pos_399_ = lean_ctor_get(v_x_392_, 0);
lean_inc(v_pos_399_);
lean_dec_ref_known(v_x_392_, 1);
v___x_400_ = lean_apply_2(v_h__2_394_, v_pos_399_, lean_box(0));
return v___x_400_;
}
case 2:
{
lean_object* v_needle_401_; lean_object* v_table_402_; lean_object* v_stackPos_403_; lean_object* v_needlePos_404_; lean_object* v___x_405_; 
lean_dec(v_h__4_396_);
lean_dec(v_h__2_394_);
lean_dec(v_h__1_393_);
v_needle_401_ = lean_ctor_get(v_x_392_, 0);
lean_inc_ref(v_needle_401_);
v_table_402_ = lean_ctor_get(v_x_392_, 1);
lean_inc_ref(v_table_402_);
v_stackPos_403_ = lean_ctor_get(v_x_392_, 2);
lean_inc(v_stackPos_403_);
v_needlePos_404_ = lean_ctor_get(v_x_392_, 3);
lean_inc(v_needlePos_404_);
lean_dec_ref_known(v_x_392_, 4);
v___x_405_ = lean_apply_6(v_h__3_395_, v_needle_401_, v_table_402_, lean_box(0), v_stackPos_403_, v_needlePos_404_, lean_box(0));
return v___x_405_;
}
default: 
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec(v_h__3_395_);
lean_dec(v_h__2_394_);
lean_dec(v_h__1_393_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_apply_1(v_h__4_396_, v___x_406_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(lean_object* v_s_408_, lean_object* v_motive_409_, lean_object* v_x_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_, lean_object* v_h__3_413_, lean_object* v_h__4_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(v_s_408_, v_motive_409_, v_x_410_, v_h__1_411_, v_h__2_412_, v_h__3_413_, v_h__4_414_);
lean_dec_ref(v_s_408_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___redArg(lean_object* v_x_416_, lean_object* v_h__1_417_, lean_object* v_h__2_418_, lean_object* v_h__3_419_){
_start:
{
switch(lean_obj_tag(v_x_416_))
{
case 0:
{
lean_object* v_it_420_; lean_object* v_out_421_; lean_object* v___x_422_; 
lean_dec(v_h__3_419_);
lean_dec(v_h__2_418_);
v_it_420_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_it_420_);
v_out_421_ = lean_ctor_get(v_x_416_, 1);
lean_inc(v_out_421_);
lean_dec_ref_known(v_x_416_, 2);
v___x_422_ = lean_apply_2(v_h__1_417_, v_it_420_, v_out_421_);
return v___x_422_;
}
case 1:
{
lean_object* v_it_423_; lean_object* v___x_424_; 
lean_dec(v_h__3_419_);
lean_dec(v_h__1_417_);
v_it_423_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_it_423_);
lean_dec_ref_known(v_x_416_, 1);
v___x_424_ = lean_apply_1(v_h__2_418_, v_it_423_);
return v___x_424_;
}
default: 
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v_h__2_418_);
lean_dec(v_h__1_417_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_apply_1(v_h__3_419_, v___x_425_);
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(lean_object* v_s_427_, lean_object* v_motive_428_, lean_object* v_x_429_, lean_object* v_h__1_430_, lean_object* v_h__2_431_, lean_object* v_h__3_432_){
_start:
{
switch(lean_obj_tag(v_x_429_))
{
case 0:
{
lean_object* v_it_433_; lean_object* v_out_434_; lean_object* v___x_435_; 
lean_dec(v_h__3_432_);
lean_dec(v_h__2_431_);
v_it_433_ = lean_ctor_get(v_x_429_, 0);
lean_inc(v_it_433_);
v_out_434_ = lean_ctor_get(v_x_429_, 1);
lean_inc(v_out_434_);
lean_dec_ref_known(v_x_429_, 2);
v___x_435_ = lean_apply_2(v_h__1_430_, v_it_433_, v_out_434_);
return v___x_435_;
}
case 1:
{
lean_object* v_it_436_; lean_object* v___x_437_; 
lean_dec(v_h__3_432_);
lean_dec(v_h__1_430_);
v_it_436_ = lean_ctor_get(v_x_429_, 0);
lean_inc(v_it_436_);
lean_dec_ref_known(v_x_429_, 1);
v___x_437_ = lean_apply_1(v_h__2_431_, v_it_436_);
return v___x_437_;
}
default: 
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v_h__2_431_);
lean_dec(v_h__1_430_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_apply_1(v_h__3_432_, v___x_438_);
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___boxed(lean_object* v_s_440_, lean_object* v_motive_441_, lean_object* v_x_442_, lean_object* v_h__1_443_, lean_object* v_h__2_444_, lean_object* v_h__3_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(v_s_440_, v_motive_441_, v_x_442_, v_h__1_443_, v_h__2_444_, v_h__3_445_);
lean_dec_ref(v_s_440_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(lean_object* v_s_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_box(0);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(lean_object* v_s_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(v_s_449_);
lean_dec_ref(v_s_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(lean_object* v___y_451_, lean_object* v_acc_452_, lean_object* v_recur_453_, lean_object* v_s_454_){
_start:
{
switch(lean_obj_tag(v_s_454_))
{
case 0:
{
lean_object* v_it_455_; lean_object* v_out_456_; lean_object* v_val_457_; 
v_it_455_ = lean_ctor_get(v_s_454_, 0);
lean_inc(v_it_455_);
v_out_456_ = lean_ctor_get(v_s_454_, 1);
lean_inc(v_out_456_);
lean_dec_ref_known(v_s_454_, 2);
v_val_457_ = lean_apply_3(v___y_451_, v_out_456_, lean_box(0), v_acc_452_);
if (lean_obj_tag(v_val_457_) == 0)
{
lean_object* v_a_458_; 
lean_dec(v_it_455_);
lean_dec(v_recur_453_);
v_a_458_ = lean_ctor_get(v_val_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v_val_457_, 1);
return v_a_458_;
}
else
{
lean_object* v_a_459_; lean_object* v___x_460_; 
v_a_459_ = lean_ctor_get(v_val_457_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v_val_457_, 1);
v___x_460_ = lean_apply_4(v_recur_453_, v_it_455_, v_a_459_, lean_box(0), lean_box(0));
return v___x_460_;
}
}
case 1:
{
lean_object* v_it_461_; lean_object* v___x_462_; 
lean_dec_ref(v___y_451_);
v_it_461_ = lean_ctor_get(v_s_454_, 0);
lean_inc(v_it_461_);
lean_dec_ref_known(v_s_454_, 1);
v___x_462_ = lean_apply_4(v_recur_453_, v_it_461_, v_acc_452_, lean_box(0), lean_box(0));
return v___x_462_;
}
default: 
{
lean_dec(v_recur_453_);
lean_dec_ref(v___y_451_);
return v_acc_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(lean_object* v___y_463_, lean_object* v_s_464_, lean_object* v_lift_465_, lean_object* v_it_466_, lean_object* v_acc_467_, lean_object* v_hP_468_, lean_object* v_recur_469_){
_start:
{
lean_object* v___f_470_; 
v___f_470_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0), 4, 3);
lean_closure_set(v___f_470_, 0, v___y_463_);
lean_closure_set(v___f_470_, 1, v_acc_467_);
lean_closure_set(v___f_470_, 2, v_recur_469_);
switch(lean_obj_tag(v_it_466_))
{
case 0:
{
lean_object* v_pos_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_488_; 
v_pos_471_ = lean_ctor_get(v_it_466_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_it_466_);
if (v_isSharedCheck_488_ == 0)
{
v___x_473_ = v_it_466_;
v_isShared_474_ = v_isSharedCheck_488_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_pos_471_);
lean_dec(v_it_466_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_488_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_res_475_; lean_object* v_startInclusive_476_; lean_object* v_endExclusive_477_; lean_object* v___x_478_; uint8_t v_decide_479_; 
lean_inc_n(v_pos_471_, 2);
v_res_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_475_, 0, v_pos_471_);
lean_ctor_set(v_res_475_, 1, v_pos_471_);
v_startInclusive_476_ = lean_ctor_get(v_s_464_, 1);
v_endExclusive_477_ = lean_ctor_get(v_s_464_, 2);
v___x_478_ = lean_nat_sub(v_endExclusive_477_, v_startInclusive_476_);
v_decide_479_ = lean_nat_dec_eq(v_pos_471_, v___x_478_);
lean_dec(v___x_478_);
if (v_decide_479_ == 0)
{
lean_object* v___x_481_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set_tag(v___x_473_, 1);
v___x_481_ = v___x_473_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_pos_471_);
v___x_481_ = v_reuseFailAlloc_484_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_res_475_);
v___x_483_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_482_);
return v___x_483_;
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_del_object(v___x_473_);
lean_dec(v_pos_471_);
v___x_485_ = lean_box(3);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_res_475_);
v___x_487_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_486_);
return v___x_487_;
}
}
}
case 1:
{
lean_object* v_pos_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_504_; 
v_pos_489_ = lean_ctor_get(v_it_466_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v_it_466_);
if (v_isSharedCheck_504_ == 0)
{
v___x_491_ = v_it_466_;
v_isShared_492_ = v_isSharedCheck_504_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_pos_489_);
lean_dec(v_it_466_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_504_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_str_493_; lean_object* v_startInclusive_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v_res_498_; lean_object* v___x_500_; 
v_str_493_ = lean_ctor_get(v_s_464_, 0);
v_startInclusive_494_ = lean_ctor_get(v_s_464_, 1);
v___x_495_ = lean_nat_add(v_startInclusive_494_, v_pos_489_);
v___x_496_ = lean_string_utf8_next_fast(v_str_493_, v___x_495_);
lean_dec(v___x_495_);
v___x_497_ = lean_nat_sub(v___x_496_, v_startInclusive_494_);
lean_inc(v___x_497_);
v_res_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_498_, 0, v_pos_489_);
lean_ctor_set(v_res_498_, 1, v___x_497_);
if (v_isShared_492_ == 0)
{
lean_ctor_set_tag(v___x_491_, 0);
lean_ctor_set(v___x_491_, 0, v___x_497_);
v___x_500_ = v___x_491_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_497_);
v___x_500_ = v_reuseFailAlloc_503_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v_res_498_);
v___x_502_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_501_);
return v___x_502_;
}
}
}
case 2:
{
lean_object* v_needle_505_; lean_object* v_table_506_; lean_object* v_stackPos_507_; lean_object* v_needlePos_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_590_; 
v_needle_505_ = lean_ctor_get(v_it_466_, 0);
v_table_506_ = lean_ctor_get(v_it_466_, 1);
v_stackPos_507_ = lean_ctor_get(v_it_466_, 2);
v_needlePos_508_ = lean_ctor_get(v_it_466_, 3);
v_isSharedCheck_590_ = !lean_is_exclusive(v_it_466_);
if (v_isSharedCheck_590_ == 0)
{
v___x_510_ = v_it_466_;
v_isShared_511_ = v_isSharedCheck_590_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_needlePos_508_);
lean_inc(v_stackPos_507_);
lean_inc(v_table_506_);
lean_inc(v_needle_505_);
lean_dec(v_it_466_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_590_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_str_512_; lean_object* v_startInclusive_513_; lean_object* v_endExclusive_514_; lean_object* v_str_515_; lean_object* v_startInclusive_516_; lean_object* v_endExclusive_517_; lean_object* v_basePos_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_str_512_ = lean_ctor_get(v_needle_505_, 0);
v_startInclusive_513_ = lean_ctor_get(v_needle_505_, 1);
v_endExclusive_514_ = lean_ctor_get(v_needle_505_, 2);
v_str_515_ = lean_ctor_get(v_s_464_, 0);
v_startInclusive_516_ = lean_ctor_get(v_s_464_, 1);
v_endExclusive_517_ = lean_ctor_get(v_s_464_, 2);
v_basePos_518_ = lean_nat_sub(v_stackPos_507_, v_needlePos_508_);
v___x_519_ = lean_nat_sub(v_endExclusive_514_, v_startInclusive_513_);
v___x_520_ = lean_nat_add(v_basePos_518_, v___x_519_);
v___x_521_ = lean_nat_sub(v_endExclusive_517_, v_startInclusive_516_);
v___x_522_ = lean_nat_dec_le(v___x_520_, v___x_521_);
lean_dec(v___x_520_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
lean_dec(v___x_519_);
lean_del_object(v___x_510_);
lean_dec(v_needlePos_508_);
lean_dec(v_stackPos_507_);
lean_dec_ref(v_table_506_);
lean_dec_ref(v_needle_505_);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_basePos_518_, v___x_523_);
v___x_525_ = lean_nat_dec_le(v___x_524_, v___x_521_);
lean_dec(v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v___x_521_);
lean_dec(v_basePos_518_);
v___x_526_ = lean_box(2);
v___x_527_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_526_);
return v___x_527_;
}
else
{
lean_object* v___x_528_; lean_object* v_res_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_528_ = l_String_Slice_pos_x21(v_s_464_, v_basePos_518_);
lean_dec(v_basePos_518_);
v_res_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_529_, 0, v___x_528_);
lean_ctor_set(v_res_529_, 1, v___x_521_);
v___x_530_ = lean_box(3);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v_res_529_);
v___x_532_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_531_);
return v___x_532_;
}
}
else
{
lean_object* v___x_533_; uint8_t v_stackByte_534_; lean_object* v___x_535_; uint8_t v_patByte_536_; uint8_t v___x_537_; 
lean_dec(v___x_521_);
v___x_533_ = lean_nat_add(v_startInclusive_516_, v_stackPos_507_);
v_stackByte_534_ = lean_string_get_byte_fast(v_str_515_, v___x_533_);
v___x_535_ = lean_nat_add(v_startInclusive_513_, v_needlePos_508_);
v_patByte_536_ = lean_string_get_byte_fast(v_str_512_, v___x_535_);
v___x_537_ = lean_uint8_dec_eq(v_stackByte_534_, v_patByte_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; uint8_t v_decide_539_; 
lean_dec(v___x_519_);
v___x_538_ = lean_unsigned_to_nat(0u);
v_decide_539_ = lean_nat_dec_eq(v_needlePos_508_, v___x_538_);
if (v_decide_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v_newNeedlePos_542_; uint8_t v___x_543_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_sub(v_needlePos_508_, v___x_540_);
lean_dec(v_needlePos_508_);
v_newNeedlePos_542_ = lean_array_fget_borrowed(v_table_506_, v___x_541_);
lean_dec(v___x_541_);
v___x_543_ = lean_nat_dec_eq(v_newNeedlePos_542_, v___x_538_);
if (v___x_543_ == 0)
{
lean_object* v_oldBasePos_544_; lean_object* v___x_545_; lean_object* v_newBasePos_546_; lean_object* v_res_547_; lean_object* v___x_549_; 
lean_inc(v_newNeedlePos_542_);
v_oldBasePos_544_ = l_String_Slice_pos_x21(v_s_464_, v_basePos_518_);
lean_dec(v_basePos_518_);
v___x_545_ = lean_nat_sub(v_stackPos_507_, v_newNeedlePos_542_);
v_newBasePos_546_ = l_String_Slice_pos_x21(v_s_464_, v___x_545_);
lean_dec(v___x_545_);
v_res_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_547_, 0, v_oldBasePos_544_);
lean_ctor_set(v_res_547_, 1, v_newBasePos_546_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 3, v_newNeedlePos_542_);
v___x_549_ = v___x_510_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_needle_505_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_table_506_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_stackPos_507_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_newNeedlePos_542_);
v___x_549_ = v_reuseFailAlloc_552_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v_res_547_);
v___x_551_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_550_);
return v___x_551_;
}
}
else
{
lean_object* v_basePos_553_; lean_object* v_nextStackPos_554_; lean_object* v_res_555_; lean_object* v___x_557_; 
v_basePos_553_ = l_String_Slice_pos_x21(v_s_464_, v_basePos_518_);
lean_dec(v_basePos_518_);
v_nextStackPos_554_ = l_String_Slice_posGE___redArg(v_s_464_, v_stackPos_507_);
lean_inc(v_nextStackPos_554_);
v_res_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_555_, 0, v_basePos_553_);
lean_ctor_set(v_res_555_, 1, v_nextStackPos_554_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 3, v___x_538_);
lean_ctor_set(v___x_510_, 2, v_nextStackPos_554_);
v___x_557_ = v___x_510_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_needle_505_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_table_506_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_nextStackPos_554_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v___x_538_);
v___x_557_ = v_reuseFailAlloc_560_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v_res_555_);
v___x_559_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_558_);
return v___x_559_;
}
}
}
else
{
lean_object* v_basePos_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v_nextStackPos_564_; lean_object* v_res_565_; lean_object* v___x_567_; 
lean_dec(v_basePos_518_);
lean_dec(v_needlePos_508_);
v_basePos_561_ = l_String_Slice_pos_x21(v_s_464_, v_stackPos_507_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_stackPos_507_, v___x_562_);
lean_dec(v_stackPos_507_);
v_nextStackPos_564_ = l_String_Slice_posGE___redArg(v_s_464_, v___x_563_);
lean_inc(v_nextStackPos_564_);
v_res_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_565_, 0, v_basePos_561_);
lean_ctor_set(v_res_565_, 1, v_nextStackPos_564_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 3, v___x_538_);
lean_ctor_set(v___x_510_, 2, v_nextStackPos_564_);
v___x_567_ = v___x_510_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_needle_505_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_table_506_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_nextStackPos_564_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v___x_538_);
v___x_567_ = v_reuseFailAlloc_570_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v_res_565_);
v___x_569_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_568_);
return v___x_569_;
}
}
}
else
{
lean_object* v___x_571_; lean_object* v_nextStackPos_572_; lean_object* v_nextNeedlePos_573_; uint8_t v_decide_574_; 
lean_dec(v_basePos_518_);
v___x_571_ = lean_unsigned_to_nat(1u);
v_nextStackPos_572_ = lean_nat_add(v_stackPos_507_, v___x_571_);
lean_dec(v_stackPos_507_);
v_nextNeedlePos_573_ = lean_nat_add(v_needlePos_508_, v___x_571_);
lean_dec(v_needlePos_508_);
v_decide_574_ = lean_nat_dec_eq(v_nextNeedlePos_573_, v___x_519_);
lean_dec(v___x_519_);
if (v_decide_574_ == 0)
{
lean_object* v___x_576_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 3, v_nextNeedlePos_573_);
lean_ctor_set(v___x_510_, 2, v_nextStackPos_572_);
v___x_576_ = v___x_510_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_needle_505_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_table_506_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_nextStackPos_572_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v_nextNeedlePos_573_);
v___x_576_ = v_reuseFailAlloc_579_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
v___x_578_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_577_);
return v___x_578_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_res_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_580_ = lean_nat_sub(v_nextStackPos_572_, v_nextNeedlePos_573_);
lean_dec(v_nextNeedlePos_573_);
v___x_581_ = l_String_Slice_pos_x21(v_s_464_, v___x_580_);
lean_dec(v___x_580_);
v___x_582_ = l_String_Slice_pos_x21(v_s_464_, v_nextStackPos_572_);
v_res_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_583_, 0, v___x_581_);
lean_ctor_set(v_res_583_, 1, v___x_582_);
v___x_584_ = lean_unsigned_to_nat(0u);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 3, v___x_584_);
lean_ctor_set(v___x_510_, 2, v_nextStackPos_572_);
v___x_586_ = v___x_510_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_needle_505_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_table_506_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_nextStackPos_572_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v___x_584_);
v___x_586_ = v_reuseFailAlloc_589_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_res_583_);
v___x_588_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_587_);
return v___x_588_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_box(2);
v___x_592_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_591_);
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed(lean_object* v___y_593_, lean_object* v_s_594_, lean_object* v_lift_595_, lean_object* v_it_596_, lean_object* v_acc_597_, lean_object* v_hP_598_, lean_object* v_recur_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(v___y_593_, v_s_594_, v_lift_595_, v_it_596_, v_acc_597_, v_hP_598_, v_recur_599_);
lean_dec_ref(v_s_594_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(lean_object* v_s_601_, lean_object* v_lift_602_, lean_object* v_00_u03b3_603_, lean_object* v_Pl_604_, lean_object* v_it_605_, lean_object* v_init_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___f_608_; lean_object* v___x_609_; 
v___f_608_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed), 7, 3);
lean_closure_set(v___f_608_, 0, v___y_607_);
lean_closure_set(v___f_608_, 1, v_s_601_);
lean_closure_set(v___f_608_, 2, v_lift_602_);
v___x_609_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_608_, v_it_605_, v_init_606_, lean_box(0));
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(lean_object* v_s_610_){
_start:
{
lean_object* v___f_611_; 
v___f_611_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2), 7, 1);
lean_closure_set(v___f_611_, 0, v_s_610_);
return v___f_611_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(lean_object* v_pat_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_613_, 0, v_pat_612_);
return v___x_613_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(lean_object* v_pat_614_, lean_object* v_s_615_){
_start:
{
lean_object* v_str_616_; lean_object* v_startInclusive_617_; lean_object* v_endExclusive_618_; lean_object* v_str_619_; lean_object* v_startInclusive_620_; lean_object* v_endExclusive_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_str_616_ = lean_ctor_get(v_pat_614_, 0);
v_startInclusive_617_ = lean_ctor_get(v_pat_614_, 1);
v_endExclusive_618_ = lean_ctor_get(v_pat_614_, 2);
v_str_619_ = lean_ctor_get(v_s_615_, 0);
v_startInclusive_620_ = lean_ctor_get(v_s_615_, 1);
v_endExclusive_621_ = lean_ctor_get(v_s_615_, 2);
v___x_622_ = lean_nat_sub(v_endExclusive_618_, v_startInclusive_617_);
v___x_623_ = lean_nat_sub(v_endExclusive_621_, v_startInclusive_620_);
v___x_624_ = lean_nat_dec_le(v___x_622_, v___x_623_);
lean_dec(v___x_623_);
if (v___x_624_ == 0)
{
lean_dec(v___x_622_);
return v___x_624_;
}
else
{
uint8_t v___x_625_; 
v___x_625_ = lean_string_memcmp(v_str_619_, v_str_616_, v_startInclusive_620_, v_startInclusive_617_, v___x_622_);
lean_dec(v___x_622_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(lean_object* v_pat_626_, lean_object* v_s_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(v_pat_626_, v_s_627_);
lean_dec_ref(v_s_627_);
lean_dec_ref(v_pat_626_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(lean_object* v_pat_630_, lean_object* v_s_631_){
_start:
{
lean_object* v_str_632_; lean_object* v_startInclusive_633_; lean_object* v_endExclusive_634_; lean_object* v_str_635_; lean_object* v_startInclusive_636_; lean_object* v_endExclusive_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_str_632_ = lean_ctor_get(v_pat_630_, 0);
v_startInclusive_633_ = lean_ctor_get(v_pat_630_, 1);
v_endExclusive_634_ = lean_ctor_get(v_pat_630_, 2);
v_str_635_ = lean_ctor_get(v_s_631_, 0);
v_startInclusive_636_ = lean_ctor_get(v_s_631_, 1);
v_endExclusive_637_ = lean_ctor_get(v_s_631_, 2);
v___x_638_ = lean_nat_sub(v_endExclusive_634_, v_startInclusive_633_);
v___x_639_ = lean_nat_sub(v_endExclusive_637_, v_startInclusive_636_);
v___x_640_ = lean_nat_dec_le(v___x_638_, v___x_639_);
lean_dec(v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
return v___x_641_;
}
else
{
uint8_t v___x_642_; 
v___x_642_ = lean_string_memcmp(v_str_635_, v_str_632_, v_startInclusive_636_, v_startInclusive_633_, v___x_638_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec(v___x_638_);
v___x_643_ = lean_box(0);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = l_String_Slice_pos_x21(v_s_631_, v___x_638_);
lean_dec(v___x_638_);
v___x_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed(lean_object* v_pat_646_, lean_object* v_s_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(v_pat_646_, v_s_647_);
lean_dec_ref(v_s_647_);
lean_dec_ref(v_pat_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(lean_object* v_pat_649_, lean_object* v_s_650_, lean_object* v_x_651_){
_start:
{
lean_object* v_str_652_; lean_object* v_startInclusive_653_; lean_object* v_endExclusive_654_; lean_object* v_str_655_; lean_object* v_startInclusive_656_; lean_object* v_endExclusive_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_str_652_ = lean_ctor_get(v_pat_649_, 0);
v_startInclusive_653_ = lean_ctor_get(v_pat_649_, 1);
v_endExclusive_654_ = lean_ctor_get(v_pat_649_, 2);
v_str_655_ = lean_ctor_get(v_s_650_, 0);
v_startInclusive_656_ = lean_ctor_get(v_s_650_, 1);
v_endExclusive_657_ = lean_ctor_get(v_s_650_, 2);
v___x_658_ = lean_nat_sub(v_endExclusive_654_, v_startInclusive_653_);
v___x_659_ = lean_nat_sub(v_endExclusive_657_, v_startInclusive_656_);
v___x_660_ = lean_nat_dec_le(v___x_658_, v___x_659_);
lean_dec(v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
return v___x_661_;
}
else
{
uint8_t v___x_662_; 
v___x_662_ = lean_string_memcmp(v_str_655_, v_str_652_, v_startInclusive_656_, v_startInclusive_653_, v___x_658_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec(v___x_658_);
v___x_663_ = lean_box(0);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = l_String_Slice_pos_x21(v_s_650_, v___x_658_);
lean_dec(v___x_658_);
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(lean_object* v_pat_666_, lean_object* v_s_667_, lean_object* v_x_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(v_pat_666_, v_s_667_, v_x_668_);
lean_dec_ref(v_s_667_);
lean_dec_ref(v_pat_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(lean_object* v_pat_670_){
_start:
{
lean_object* v___f_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_inc_ref_n(v_pat_670_, 2);
v___f_671_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_671_, 0, v_pat_670_);
v___x_672_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_672_, 0, v_pat_670_);
v___x_673_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_673_, 0, v_pat_670_);
v___x_674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___f_671_);
lean_ctor_set(v___x_674_, 2, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(lean_object* v_pat_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_string_utf8_byte_size(v_pat_675_);
v___x_678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_678_, 0, v_pat_675_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set(v___x_678_, 2, v___x_677_);
v___x_679_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(lean_object* v___x_680_, lean_object* v_pat_681_, lean_object* v___x_682_, lean_object* v_s_683_, lean_object* v_x_684_){
_start:
{
lean_object* v_str_685_; lean_object* v_startInclusive_686_; lean_object* v_endExclusive_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_str_685_ = lean_ctor_get(v_s_683_, 0);
v_startInclusive_686_ = lean_ctor_get(v_s_683_, 1);
v_endExclusive_687_ = lean_ctor_get(v_s_683_, 2);
v___x_688_ = lean_nat_sub(v_endExclusive_687_, v_startInclusive_686_);
v___x_689_ = lean_nat_dec_le(v___x_680_, v___x_688_);
lean_dec(v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
v___x_690_ = lean_box(0);
return v___x_690_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = lean_string_memcmp(v_str_685_, v_pat_681_, v_startInclusive_686_, v___x_682_, v___x_680_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; 
v___x_692_ = lean_box(0);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_String_Slice_pos_x21(v_s_683_, v___x_680_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(lean_object* v___x_695_, lean_object* v_pat_696_, lean_object* v___x_697_, lean_object* v_s_698_, lean_object* v_x_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(v___x_695_, v_pat_696_, v___x_697_, v_s_698_, v_x_699_);
lean_dec_ref(v_s_698_);
lean_dec(v___x_697_);
lean_dec_ref(v_pat_696_);
lean_dec(v___x_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(lean_object* v_pat_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___f_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_string_utf8_byte_size(v_pat_701_);
lean_inc_ref(v_pat_701_);
v___f_704_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_704_, 0, v___x_703_);
lean_closure_set(v___f_704_, 1, v_pat_701_);
lean_closure_set(v___f_704_, 2, v___x_702_);
v___x_705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_705_, 0, v_pat_701_);
lean_ctor_set(v___x_705_, 1, v___x_702_);
lean_ctor_set(v___x_705_, 2, v___x_703_);
lean_inc_ref(v___x_705_);
v___x_706_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_706_, 0, v___x_705_);
v___x_707_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_707_, 0, v___x_705_);
v___x_708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___f_704_);
lean_ctor_set(v___x_708_, 2, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(lean_object* v_pat_709_, lean_object* v_s_710_){
_start:
{
lean_object* v_str_711_; lean_object* v_startInclusive_712_; lean_object* v_endExclusive_713_; lean_object* v_str_714_; lean_object* v_startInclusive_715_; lean_object* v_endExclusive_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_str_711_ = lean_ctor_get(v_pat_709_, 0);
v_startInclusive_712_ = lean_ctor_get(v_pat_709_, 1);
v_endExclusive_713_ = lean_ctor_get(v_pat_709_, 2);
v_str_714_ = lean_ctor_get(v_s_710_, 0);
v_startInclusive_715_ = lean_ctor_get(v_s_710_, 1);
v_endExclusive_716_ = lean_ctor_get(v_s_710_, 2);
v___x_717_ = lean_nat_sub(v_endExclusive_713_, v_startInclusive_712_);
v___x_718_ = lean_nat_sub(v_endExclusive_716_, v_startInclusive_715_);
v___x_719_ = lean_nat_dec_le(v___x_717_, v___x_718_);
if (v___x_719_ == 0)
{
lean_dec(v___x_718_);
lean_dec(v___x_717_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_720_ = lean_nat_sub(v___x_718_, v___x_717_);
lean_dec(v___x_718_);
v___x_721_ = lean_nat_add(v_startInclusive_715_, v___x_720_);
lean_dec(v___x_720_);
v___x_722_ = lean_string_memcmp(v_str_714_, v_str_711_, v___x_721_, v_startInclusive_712_, v___x_717_);
lean_dec(v___x_717_);
lean_dec(v___x_721_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(lean_object* v_pat_723_, lean_object* v_s_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(v_pat_723_, v_s_724_);
lean_dec_ref(v_s_724_);
lean_dec_ref(v_pat_723_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(lean_object* v_pat_727_, lean_object* v_s_728_){
_start:
{
lean_object* v_str_729_; lean_object* v_startInclusive_730_; lean_object* v_endExclusive_731_; lean_object* v_str_732_; lean_object* v_startInclusive_733_; lean_object* v_endExclusive_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_str_729_ = lean_ctor_get(v_pat_727_, 0);
v_startInclusive_730_ = lean_ctor_get(v_pat_727_, 1);
v_endExclusive_731_ = lean_ctor_get(v_pat_727_, 2);
v_str_732_ = lean_ctor_get(v_s_728_, 0);
v_startInclusive_733_ = lean_ctor_get(v_s_728_, 1);
v_endExclusive_734_ = lean_ctor_get(v_s_728_, 2);
v___x_735_ = lean_nat_sub(v_endExclusive_731_, v_startInclusive_730_);
v___x_736_ = lean_nat_sub(v_endExclusive_734_, v_startInclusive_733_);
v___x_737_ = lean_nat_dec_le(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec(v___x_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
return v___x_738_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = lean_nat_sub(v___x_736_, v___x_735_);
lean_dec(v___x_736_);
v___x_740_ = lean_nat_add(v_startInclusive_733_, v___x_739_);
v___x_741_ = lean_string_memcmp(v_str_732_, v_str_729_, v___x_740_, v_startInclusive_730_, v___x_735_);
lean_dec(v___x_735_);
lean_dec(v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
return v___x_742_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = l_String_Slice_pos_x21(v_s_728_, v___x_739_);
lean_dec(v___x_739_);
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed(lean_object* v_pat_745_, lean_object* v_s_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(v_pat_745_, v_s_746_);
lean_dec_ref(v_s_746_);
lean_dec_ref(v_pat_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(lean_object* v_pat_748_, lean_object* v_s_749_, lean_object* v_x_750_){
_start:
{
lean_object* v_str_751_; lean_object* v_startInclusive_752_; lean_object* v_endExclusive_753_; lean_object* v_str_754_; lean_object* v_startInclusive_755_; lean_object* v_endExclusive_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_str_751_ = lean_ctor_get(v_pat_748_, 0);
v_startInclusive_752_ = lean_ctor_get(v_pat_748_, 1);
v_endExclusive_753_ = lean_ctor_get(v_pat_748_, 2);
v_str_754_ = lean_ctor_get(v_s_749_, 0);
v_startInclusive_755_ = lean_ctor_get(v_s_749_, 1);
v_endExclusive_756_ = lean_ctor_get(v_s_749_, 2);
v___x_757_ = lean_nat_sub(v_endExclusive_753_, v_startInclusive_752_);
v___x_758_ = lean_nat_sub(v_endExclusive_756_, v_startInclusive_755_);
v___x_759_ = lean_nat_dec_le(v___x_757_, v___x_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; 
lean_dec(v___x_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
return v___x_760_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = lean_nat_sub(v___x_758_, v___x_757_);
lean_dec(v___x_758_);
v___x_762_ = lean_nat_add(v_startInclusive_755_, v___x_761_);
v___x_763_ = lean_string_memcmp(v_str_754_, v_str_751_, v___x_762_, v_startInclusive_752_, v___x_757_);
lean_dec(v___x_757_);
lean_dec(v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
return v___x_764_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = l_String_Slice_pos_x21(v_s_749_, v___x_761_);
lean_dec(v___x_761_);
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(lean_object* v_pat_767_, lean_object* v_s_768_, lean_object* v_x_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(v_pat_767_, v_s_768_, v_x_769_);
lean_dec_ref(v_s_768_);
lean_dec_ref(v_pat_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(lean_object* v_pat_771_){
_start:
{
lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_inc_ref_n(v_pat_771_, 2);
v___f_772_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_772_, 0, v_pat_771_);
v___x_773_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_773_, 0, v_pat_771_);
v___x_774_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_774_, 0, v_pat_771_);
v___x_775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___f_772_);
lean_ctor_set(v___x_775_, 2, v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(lean_object* v___x_776_, lean_object* v_pat_777_, lean_object* v___x_778_, lean_object* v_s_779_, lean_object* v_x_780_){
_start:
{
lean_object* v_str_781_; lean_object* v_startInclusive_782_; lean_object* v_endExclusive_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_str_781_ = lean_ctor_get(v_s_779_, 0);
v_startInclusive_782_ = lean_ctor_get(v_s_779_, 1);
v_endExclusive_783_ = lean_ctor_get(v_s_779_, 2);
v___x_784_ = lean_nat_sub(v_endExclusive_783_, v_startInclusive_782_);
v___x_785_ = lean_nat_dec_le(v___x_776_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec(v___x_784_);
v___x_786_ = lean_box(0);
return v___x_786_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_787_ = lean_nat_sub(v___x_784_, v___x_776_);
lean_dec(v___x_784_);
v___x_788_ = lean_nat_add(v_startInclusive_782_, v___x_787_);
v___x_789_ = lean_string_memcmp(v_str_781_, v_pat_777_, v___x_788_, v___x_778_, v___x_776_);
lean_dec(v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
return v___x_790_;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = l_String_Slice_pos_x21(v_s_779_, v___x_787_);
lean_dec(v___x_787_);
v___x_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(lean_object* v___x_793_, lean_object* v_pat_794_, lean_object* v___x_795_, lean_object* v_s_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(v___x_793_, v_pat_794_, v___x_795_, v_s_796_, v_x_797_);
lean_dec_ref(v_s_796_);
lean_dec(v___x_795_);
lean_dec_ref(v_pat_794_);
lean_dec(v___x_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(lean_object* v_pat_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_string_utf8_byte_size(v_pat_799_);
lean_inc_ref(v_pat_799_);
v___f_802_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_802_, 0, v___x_801_);
lean_closure_set(v___f_802_, 1, v_pat_799_);
lean_closure_set(v___f_802_, 2, v___x_800_);
v___x_803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_803_, 0, v_pat_799_);
lean_ctor_set(v___x_803_, 1, v___x_800_);
lean_ctor_set(v___x_803_, 2, v___x_801_);
lean_inc_ref(v___x_803_);
v___x_804_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_804_, 0, v___x_803_);
v___x_805_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_805_, 0, v___x_803_);
v___x_806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___f_802_);
lean_ctor_set(v___x_806_, 2, v___x_805_);
return v___x_806_;
}
}
lean_object* runtime_initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Pattern_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Pattern_String(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Pattern_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Pattern_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Pattern_String(builtin);
}
#ifdef __cplusplus
}
#endif
