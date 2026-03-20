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
lean_dec(v_guess_4_);
v___x_14_ = lean_array_fget_borrowed(v_table_3_, v___x_13_);
lean_dec(v___x_13_);
lean_inc(v___x_14_);
v_guess_4_ = v___x_14_;
goto _start;
}
else
{
lean_dec(v_guess_4_);
return v___x_10_;
}
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_add(v_guess_4_, v___x_16_);
lean_dec(v_guess_4_);
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
lean_inc(v___x_53_);
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
lean_dec_ref(v_t_99_);
v___x_102_ = lean_apply_1(v_k_100_, v_pos_101_);
return v___x_102_;
}
case 1:
{
lean_object* v_pos_103_; lean_object* v___x_104_; 
v_pos_103_ = lean_ctor_get(v_t_99_, 0);
lean_inc(v_pos_103_);
lean_dec_ref(v_t_99_);
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
lean_dec_ref(v_t_99_);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0));
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___boxed(lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(v_a_188_);
lean_dec_ref(v_a_188_);
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
lean_object* v_res_222_; lean_object* v_startInclusive_223_; lean_object* v_endExclusive_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
lean_inc_n(v_pos_218_, 2);
v_res_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_222_, 0, v_pos_218_);
lean_ctor_set(v_res_222_, 1, v_pos_218_);
v_startInclusive_223_ = lean_ctor_get(v_s_216_, 1);
v_endExclusive_224_ = lean_ctor_get(v_s_216_, 2);
v___x_225_ = lean_nat_sub(v_endExclusive_224_, v_startInclusive_223_);
v___x_226_ = lean_nat_dec_eq(v_pos_218_, v___x_225_);
lean_dec(v___x_225_);
if (v___x_226_ == 0)
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
lean_object* v_needle_249_; lean_object* v_table_250_; lean_object* v_stackPos_251_; lean_object* v_needlePos_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_325_; 
v_needle_249_ = lean_ctor_get(v_x_217_, 0);
v_table_250_ = lean_ctor_get(v_x_217_, 1);
v_stackPos_251_ = lean_ctor_get(v_x_217_, 2);
v_needlePos_252_ = lean_ctor_get(v_x_217_, 3);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_217_);
if (v_isSharedCheck_325_ == 0)
{
v___x_254_ = v_x_217_;
v_isShared_255_ = v_isSharedCheck_325_;
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
v_isShared_255_ = v_isSharedCheck_325_;
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
uint8_t v___x_267_; 
lean_dec(v___x_263_);
lean_del_object(v___x_254_);
lean_dec(v_needlePos_252_);
lean_dec(v_stackPos_251_);
lean_dec_ref(v_table_250_);
lean_dec_ref(v_needle_249_);
v___x_267_ = lean_nat_dec_lt(v_basePos_262_, v___x_265_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec(v___x_265_);
lean_dec(v_basePos_262_);
v___x_268_ = lean_box(2);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v_res_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_269_ = l_String_Slice_pos_x21(v_s_216_, v_basePos_262_);
lean_dec(v_basePos_262_);
v_res_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_270_, 0, v___x_269_);
lean_ctor_set(v_res_270_, 1, v___x_265_);
v___x_271_ = lean_box(3);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_res_270_);
return v___x_272_;
}
}
else
{
lean_object* v___x_273_; uint8_t v_stackByte_274_; lean_object* v___x_275_; uint8_t v_patByte_276_; uint8_t v___x_277_; 
lean_dec(v___x_265_);
v___x_273_ = lean_nat_add(v_startInclusive_260_, v_stackPos_251_);
v_stackByte_274_ = lean_string_get_byte_fast(v_str_259_, v___x_273_);
v___x_275_ = lean_nat_add(v_startInclusive_257_, v_needlePos_252_);
v_patByte_276_ = lean_string_get_byte_fast(v_str_256_, v___x_275_);
v___x_277_ = lean_uint8_dec_eq(v_stackByte_274_, v_patByte_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; uint8_t v___x_279_; 
lean_dec(v___x_263_);
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_nat_dec_eq(v_needlePos_252_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_newNeedlePos_282_; uint8_t v___x_283_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_sub(v_needlePos_252_, v___x_280_);
lean_dec(v_needlePos_252_);
v_newNeedlePos_282_ = lean_array_fget_borrowed(v_table_250_, v___x_281_);
lean_dec(v___x_281_);
v___x_283_ = lean_nat_dec_eq(v_newNeedlePos_282_, v___x_278_);
if (v___x_283_ == 0)
{
lean_object* v_oldBasePos_284_; lean_object* v___x_285_; lean_object* v_newBasePos_286_; lean_object* v_res_287_; lean_object* v___x_289_; 
lean_inc(v_newNeedlePos_282_);
v_oldBasePos_284_ = l_String_Slice_pos_x21(v_s_216_, v_basePos_262_);
lean_dec(v_basePos_262_);
v___x_285_ = lean_nat_sub(v_stackPos_251_, v_newNeedlePos_282_);
v_newBasePos_286_ = l_String_Slice_pos_x21(v_s_216_, v___x_285_);
lean_dec(v___x_285_);
v_res_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_287_, 0, v_oldBasePos_284_);
lean_ctor_set(v_res_287_, 1, v_newBasePos_286_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v_newNeedlePos_282_);
v___x_289_ = v___x_254_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_needle_249_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_table_250_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_stackPos_251_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_newNeedlePos_282_);
v___x_289_ = v_reuseFailAlloc_291_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_res_287_);
return v___x_290_;
}
}
else
{
lean_object* v_basePos_292_; lean_object* v_nextStackPos_293_; lean_object* v_res_294_; lean_object* v___x_296_; 
v_basePos_292_ = l_String_Slice_pos_x21(v_s_216_, v_basePos_262_);
lean_dec(v_basePos_262_);
v_nextStackPos_293_ = l_String_Slice_posGE___redArg(v_s_216_, v_stackPos_251_);
lean_inc(v_nextStackPos_293_);
v_res_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_294_, 0, v_basePos_292_);
lean_ctor_set(v_res_294_, 1, v_nextStackPos_293_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v___x_278_);
lean_ctor_set(v___x_254_, 2, v_nextStackPos_293_);
v___x_296_ = v___x_254_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_needle_249_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_table_250_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_nextStackPos_293_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v___x_278_);
v___x_296_ = v_reuseFailAlloc_298_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_res_294_);
return v___x_297_;
}
}
}
else
{
lean_object* v_basePos_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_nextStackPos_302_; lean_object* v_res_303_; lean_object* v___x_305_; 
lean_dec(v_basePos_262_);
lean_dec(v_needlePos_252_);
v_basePos_299_ = l_String_Slice_pos_x21(v_s_216_, v_stackPos_251_);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_stackPos_251_, v___x_300_);
lean_dec(v_stackPos_251_);
v_nextStackPos_302_ = l_String_Slice_posGE___redArg(v_s_216_, v___x_301_);
lean_inc(v_nextStackPos_302_);
v_res_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_303_, 0, v_basePos_299_);
lean_ctor_set(v_res_303_, 1, v_nextStackPos_302_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v___x_278_);
lean_ctor_set(v___x_254_, 2, v_nextStackPos_302_);
v___x_305_ = v___x_254_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_needle_249_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_table_250_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_nextStackPos_302_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v___x_278_);
v___x_305_ = v_reuseFailAlloc_307_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_res_303_);
return v___x_306_;
}
}
}
else
{
lean_object* v___x_308_; lean_object* v_nextStackPos_309_; lean_object* v_nextNeedlePos_310_; uint8_t v___x_311_; 
lean_dec(v_basePos_262_);
v___x_308_ = lean_unsigned_to_nat(1u);
v_nextStackPos_309_ = lean_nat_add(v_stackPos_251_, v___x_308_);
lean_dec(v_stackPos_251_);
v_nextNeedlePos_310_ = lean_nat_add(v_needlePos_252_, v___x_308_);
lean_dec(v_needlePos_252_);
v___x_311_ = lean_nat_dec_eq(v_nextNeedlePos_310_, v___x_263_);
lean_dec(v___x_263_);
if (v___x_311_ == 0)
{
lean_object* v___x_313_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v_nextNeedlePos_310_);
lean_ctor_set(v___x_254_, 2, v_nextStackPos_309_);
v___x_313_ = v___x_254_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_needle_249_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_table_250_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_nextStackPos_309_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_nextNeedlePos_310_);
v___x_313_ = v_reuseFailAlloc_315_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; 
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_res_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_316_ = lean_nat_sub(v_nextStackPos_309_, v_nextNeedlePos_310_);
lean_dec(v_nextNeedlePos_310_);
v___x_317_ = l_String_Slice_pos_x21(v_s_216_, v___x_316_);
lean_dec(v___x_316_);
v___x_318_ = l_String_Slice_pos_x21(v_s_216_, v_nextStackPos_309_);
v_res_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_319_, 0, v___x_317_);
lean_ctor_set(v_res_319_, 1, v___x_318_);
v___x_320_ = lean_unsigned_to_nat(0u);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v___x_320_);
lean_ctor_set(v___x_254_, 2, v_nextStackPos_309_);
v___x_322_ = v___x_254_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_needle_249_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_table_250_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_nextStackPos_309_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v___x_320_);
v___x_322_ = v_reuseFailAlloc_324_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; 
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_res_319_);
return v___x_323_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_326_; 
v___x_326_ = lean_box(2);
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed(lean_object* v_s_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(v_s_327_, v_x_328_);
lean_dec_ref(v_s_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep(lean_object* v_s_330_){
_start:
{
lean_object* v___f_331_; 
v___f_331_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed), 2, 1);
lean_closure_set(v___f_331_, 0, v_s_330_);
return v___f_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(lean_object* v_s_332_, lean_object* v_x_333_){
_start:
{
switch(lean_obj_tag(v_x_333_))
{
case 0:
{
lean_object* v_pos_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_344_; 
v_pos_334_ = lean_ctor_get(v_x_333_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_344_ == 0)
{
v___x_336_ = v_x_333_;
v_isShared_337_ = v_isSharedCheck_344_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_pos_334_);
lean_dec(v_x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_344_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_338_ = l_String_Slice_Pos_remainingBytes(v_s_332_, v_pos_334_);
lean_dec(v_pos_334_);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 1);
lean_ctor_set(v___x_336_, 0, v___x_340_);
v___x_342_ = v___x_336_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
case 1:
{
lean_object* v_pos_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_355_; 
v_pos_345_ = lean_ctor_get(v_x_333_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_355_ == 0)
{
v___x_347_ = v_x_333_;
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_pos_345_);
lean_dec(v_x_333_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_349_ = l_String_Slice_Pos_remainingBytes(v_s_332_, v_pos_345_);
lean_dec(v_pos_345_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_351_);
v___x_353_ = v___x_347_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
case 2:
{
lean_object* v_stackPos_356_; lean_object* v_needlePos_357_; lean_object* v_startInclusive_358_; lean_object* v_endExclusive_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_stackPos_356_ = lean_ctor_get(v_x_333_, 2);
lean_inc(v_stackPos_356_);
v_needlePos_357_ = lean_ctor_get(v_x_333_, 3);
lean_inc(v_needlePos_357_);
lean_dec_ref(v_x_333_);
v_startInclusive_358_ = lean_ctor_get(v_s_332_, 1);
v_endExclusive_359_ = lean_ctor_get(v_s_332_, 2);
v___x_360_ = lean_nat_sub(v_endExclusive_359_, v_startInclusive_358_);
v___x_361_ = lean_nat_sub(v___x_360_, v_stackPos_356_);
lean_dec(v_stackPos_356_);
lean_dec(v___x_360_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v_needlePos_357_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
default: 
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(0);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption___boxed(lean_object* v_s_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(v_s_365_, v_x_366_);
lean_dec_ref(v_s_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(lean_object* v_s_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_box(0);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(lean_object* v_s_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(v_s_370_);
lean_dec_ref(v_s_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(lean_object* v_x_372_, lean_object* v_h__1_373_, lean_object* v_h__2_374_, lean_object* v_h__3_375_, lean_object* v_h__4_376_){
_start:
{
switch(lean_obj_tag(v_x_372_))
{
case 0:
{
lean_object* v_pos_377_; lean_object* v___x_378_; 
lean_dec(v_h__4_376_);
lean_dec(v_h__3_375_);
lean_dec(v_h__2_374_);
v_pos_377_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_pos_377_);
lean_dec_ref(v_x_372_);
v___x_378_ = lean_apply_1(v_h__1_373_, v_pos_377_);
return v___x_378_;
}
case 1:
{
lean_object* v_pos_379_; lean_object* v___x_380_; 
lean_dec(v_h__4_376_);
lean_dec(v_h__3_375_);
lean_dec(v_h__1_373_);
v_pos_379_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_pos_379_);
lean_dec_ref(v_x_372_);
v___x_380_ = lean_apply_2(v_h__2_374_, v_pos_379_, lean_box(0));
return v___x_380_;
}
case 2:
{
lean_object* v_needle_381_; lean_object* v_table_382_; lean_object* v_stackPos_383_; lean_object* v_needlePos_384_; lean_object* v___x_385_; 
lean_dec(v_h__4_376_);
lean_dec(v_h__2_374_);
lean_dec(v_h__1_373_);
v_needle_381_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_needle_381_);
v_table_382_ = lean_ctor_get(v_x_372_, 1);
lean_inc_ref(v_table_382_);
v_stackPos_383_ = lean_ctor_get(v_x_372_, 2);
lean_inc(v_stackPos_383_);
v_needlePos_384_ = lean_ctor_get(v_x_372_, 3);
lean_inc(v_needlePos_384_);
lean_dec_ref(v_x_372_);
v___x_385_ = lean_apply_6(v_h__3_375_, v_needle_381_, v_table_382_, lean_box(0), v_stackPos_383_, v_needlePos_384_, lean_box(0));
return v___x_385_;
}
default: 
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v_h__3_375_);
lean_dec(v_h__2_374_);
lean_dec(v_h__1_373_);
v___x_386_ = lean_box(0);
v___x_387_ = lean_apply_1(v_h__4_376_, v___x_386_);
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(lean_object* v_s_388_, lean_object* v_motive_389_, lean_object* v_x_390_, lean_object* v_h__1_391_, lean_object* v_h__2_392_, lean_object* v_h__3_393_, lean_object* v_h__4_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(v_x_390_, v_h__1_391_, v_h__2_392_, v_h__3_393_, v_h__4_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(lean_object* v_s_396_, lean_object* v_motive_397_, lean_object* v_x_398_, lean_object* v_h__1_399_, lean_object* v_h__2_400_, lean_object* v_h__3_401_, lean_object* v_h__4_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(v_s_396_, v_motive_397_, v_x_398_, v_h__1_399_, v_h__2_400_, v_h__3_401_, v_h__4_402_);
lean_dec_ref(v_s_396_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___redArg(lean_object* v_x_404_, lean_object* v_h__1_405_, lean_object* v_h__2_406_, lean_object* v_h__3_407_){
_start:
{
switch(lean_obj_tag(v_x_404_))
{
case 0:
{
lean_object* v_it_408_; lean_object* v_out_409_; lean_object* v___x_410_; 
lean_dec(v_h__3_407_);
lean_dec(v_h__2_406_);
v_it_408_ = lean_ctor_get(v_x_404_, 0);
lean_inc(v_it_408_);
v_out_409_ = lean_ctor_get(v_x_404_, 1);
lean_inc(v_out_409_);
lean_dec_ref(v_x_404_);
v___x_410_ = lean_apply_2(v_h__1_405_, v_it_408_, v_out_409_);
return v___x_410_;
}
case 1:
{
lean_object* v_it_411_; lean_object* v___x_412_; 
lean_dec(v_h__3_407_);
lean_dec(v_h__1_405_);
v_it_411_ = lean_ctor_get(v_x_404_, 0);
lean_inc(v_it_411_);
lean_dec_ref(v_x_404_);
v___x_412_ = lean_apply_1(v_h__2_406_, v_it_411_);
return v___x_412_;
}
default: 
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec(v_h__2_406_);
lean_dec(v_h__1_405_);
v___x_413_ = lean_box(0);
v___x_414_ = lean_apply_1(v_h__3_407_, v___x_413_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(lean_object* v_s_415_, lean_object* v_motive_416_, lean_object* v_x_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_, lean_object* v_h__3_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___redArg(v_x_417_, v_h__1_418_, v_h__2_419_, v_h__3_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___boxed(lean_object* v_s_422_, lean_object* v_motive_423_, lean_object* v_x_424_, lean_object* v_h__1_425_, lean_object* v_h__2_426_, lean_object* v_h__3_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(v_s_422_, v_motive_423_, v_x_424_, v_h__1_425_, v_h__2_426_, v_h__3_427_);
lean_dec_ref(v_s_422_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(lean_object* v_s_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_box(0);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(lean_object* v_s_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(v_s_431_);
lean_dec_ref(v_s_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(lean_object* v___y_433_, lean_object* v_acc_434_, lean_object* v_recur_435_, lean_object* v_s_436_){
_start:
{
switch(lean_obj_tag(v_s_436_))
{
case 0:
{
lean_object* v_it_437_; lean_object* v_out_438_; lean_object* v_val_439_; 
v_it_437_ = lean_ctor_get(v_s_436_, 0);
lean_inc(v_it_437_);
v_out_438_ = lean_ctor_get(v_s_436_, 1);
lean_inc(v_out_438_);
lean_dec_ref(v_s_436_);
v_val_439_ = lean_apply_3(v___y_433_, v_out_438_, lean_box(0), v_acc_434_);
if (lean_obj_tag(v_val_439_) == 0)
{
lean_object* v_a_440_; 
lean_dec(v_it_437_);
lean_dec(v_recur_435_);
v_a_440_ = lean_ctor_get(v_val_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref(v_val_439_);
return v_a_440_;
}
else
{
lean_object* v_a_441_; lean_object* v___x_442_; 
v_a_441_ = lean_ctor_get(v_val_439_, 0);
lean_inc(v_a_441_);
lean_dec_ref(v_val_439_);
v___x_442_ = lean_apply_4(v_recur_435_, v_it_437_, v_a_441_, lean_box(0), lean_box(0));
return v___x_442_;
}
}
case 1:
{
lean_object* v_it_443_; lean_object* v___x_444_; 
lean_dec_ref(v___y_433_);
v_it_443_ = lean_ctor_get(v_s_436_, 0);
lean_inc(v_it_443_);
lean_dec_ref(v_s_436_);
v___x_444_ = lean_apply_4(v_recur_435_, v_it_443_, v_acc_434_, lean_box(0), lean_box(0));
return v___x_444_;
}
default: 
{
lean_dec(v_recur_435_);
lean_dec_ref(v___y_433_);
return v_acc_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(lean_object* v___y_445_, lean_object* v_s_446_, lean_object* v_lift_447_, lean_object* v_it_448_, lean_object* v_acc_449_, lean_object* v_hP_450_, lean_object* v_recur_451_){
_start:
{
lean_object* v___f_452_; 
v___f_452_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0), 4, 3);
lean_closure_set(v___f_452_, 0, v___y_445_);
lean_closure_set(v___f_452_, 1, v_acc_449_);
lean_closure_set(v___f_452_, 2, v_recur_451_);
switch(lean_obj_tag(v_it_448_))
{
case 0:
{
lean_object* v_pos_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_470_; 
v_pos_453_ = lean_ctor_get(v_it_448_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_it_448_);
if (v_isSharedCheck_470_ == 0)
{
v___x_455_ = v_it_448_;
v_isShared_456_ = v_isSharedCheck_470_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_pos_453_);
lean_dec(v_it_448_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_470_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v_res_457_; lean_object* v_startInclusive_458_; lean_object* v_endExclusive_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
lean_inc_n(v_pos_453_, 2);
v_res_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_457_, 0, v_pos_453_);
lean_ctor_set(v_res_457_, 1, v_pos_453_);
v_startInclusive_458_ = lean_ctor_get(v_s_446_, 1);
v_endExclusive_459_ = lean_ctor_get(v_s_446_, 2);
v___x_460_ = lean_nat_sub(v_endExclusive_459_, v_startInclusive_458_);
v___x_461_ = lean_nat_dec_eq(v_pos_453_, v___x_460_);
lean_dec(v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_463_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set_tag(v___x_455_, 1);
v___x_463_ = v___x_455_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_pos_453_);
v___x_463_ = v_reuseFailAlloc_466_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v_res_457_);
v___x_465_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_464_);
return v___x_465_;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_del_object(v___x_455_);
lean_dec(v_pos_453_);
v___x_467_ = lean_box(3);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_res_457_);
v___x_469_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_468_);
return v___x_469_;
}
}
}
case 1:
{
lean_object* v_pos_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_486_; 
v_pos_471_ = lean_ctor_get(v_it_448_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v_it_448_);
if (v_isSharedCheck_486_ == 0)
{
v___x_473_ = v_it_448_;
v_isShared_474_ = v_isSharedCheck_486_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_pos_471_);
lean_dec(v_it_448_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_486_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_str_475_; lean_object* v_startInclusive_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_res_480_; lean_object* v___x_482_; 
v_str_475_ = lean_ctor_get(v_s_446_, 0);
v_startInclusive_476_ = lean_ctor_get(v_s_446_, 1);
v___x_477_ = lean_nat_add(v_startInclusive_476_, v_pos_471_);
v___x_478_ = lean_string_utf8_next_fast(v_str_475_, v___x_477_);
lean_dec(v___x_477_);
v___x_479_ = lean_nat_sub(v___x_478_, v_startInclusive_476_);
lean_inc(v___x_479_);
v_res_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_480_, 0, v_pos_471_);
lean_ctor_set(v_res_480_, 1, v___x_479_);
if (v_isShared_474_ == 0)
{
lean_ctor_set_tag(v___x_473_, 0);
lean_ctor_set(v___x_473_, 0, v___x_479_);
v___x_482_ = v___x_473_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_479_);
v___x_482_ = v_reuseFailAlloc_485_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v_res_480_);
v___x_484_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_483_);
return v___x_484_;
}
}
}
case 2:
{
lean_object* v_needle_487_; lean_object* v_table_488_; lean_object* v_stackPos_489_; lean_object* v_needlePos_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_570_; 
v_needle_487_ = lean_ctor_get(v_it_448_, 0);
v_table_488_ = lean_ctor_get(v_it_448_, 1);
v_stackPos_489_ = lean_ctor_get(v_it_448_, 2);
v_needlePos_490_ = lean_ctor_get(v_it_448_, 3);
v_isSharedCheck_570_ = !lean_is_exclusive(v_it_448_);
if (v_isSharedCheck_570_ == 0)
{
v___x_492_ = v_it_448_;
v_isShared_493_ = v_isSharedCheck_570_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_needlePos_490_);
lean_inc(v_stackPos_489_);
lean_inc(v_table_488_);
lean_inc(v_needle_487_);
lean_dec(v_it_448_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_570_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v_str_494_; lean_object* v_startInclusive_495_; lean_object* v_endExclusive_496_; lean_object* v_str_497_; lean_object* v_startInclusive_498_; lean_object* v_endExclusive_499_; lean_object* v_basePos_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v_str_494_ = lean_ctor_get(v_needle_487_, 0);
v_startInclusive_495_ = lean_ctor_get(v_needle_487_, 1);
v_endExclusive_496_ = lean_ctor_get(v_needle_487_, 2);
v_str_497_ = lean_ctor_get(v_s_446_, 0);
v_startInclusive_498_ = lean_ctor_get(v_s_446_, 1);
v_endExclusive_499_ = lean_ctor_get(v_s_446_, 2);
v_basePos_500_ = lean_nat_sub(v_stackPos_489_, v_needlePos_490_);
v___x_501_ = lean_nat_sub(v_endExclusive_496_, v_startInclusive_495_);
v___x_502_ = lean_nat_add(v_basePos_500_, v___x_501_);
v___x_503_ = lean_nat_sub(v_endExclusive_499_, v_startInclusive_498_);
v___x_504_ = lean_nat_dec_le(v___x_502_, v___x_503_);
lean_dec(v___x_502_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
lean_dec(v___x_501_);
lean_del_object(v___x_492_);
lean_dec(v_needlePos_490_);
lean_dec(v_stackPos_489_);
lean_dec_ref(v_table_488_);
lean_dec_ref(v_needle_487_);
v___x_505_ = lean_nat_dec_lt(v_basePos_500_, v___x_503_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v___x_503_);
lean_dec(v_basePos_500_);
v___x_506_ = lean_box(2);
v___x_507_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_506_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v_res_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_508_ = l_String_Slice_pos_x21(v_s_446_, v_basePos_500_);
lean_dec(v_basePos_500_);
v_res_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_509_, 0, v___x_508_);
lean_ctor_set(v_res_509_, 1, v___x_503_);
v___x_510_ = lean_box(3);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v_res_509_);
v___x_512_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_511_);
return v___x_512_;
}
}
else
{
lean_object* v___x_513_; uint8_t v_stackByte_514_; lean_object* v___x_515_; uint8_t v_patByte_516_; uint8_t v___x_517_; 
lean_dec(v___x_503_);
v___x_513_ = lean_nat_add(v_startInclusive_498_, v_stackPos_489_);
v_stackByte_514_ = lean_string_get_byte_fast(v_str_497_, v___x_513_);
v___x_515_ = lean_nat_add(v_startInclusive_495_, v_needlePos_490_);
v_patByte_516_ = lean_string_get_byte_fast(v_str_494_, v___x_515_);
v___x_517_ = lean_uint8_dec_eq(v_stackByte_514_, v_patByte_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; 
lean_dec(v___x_501_);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_nat_dec_eq(v_needlePos_490_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_newNeedlePos_522_; uint8_t v___x_523_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_sub(v_needlePos_490_, v___x_520_);
lean_dec(v_needlePos_490_);
v_newNeedlePos_522_ = lean_array_fget_borrowed(v_table_488_, v___x_521_);
lean_dec(v___x_521_);
v___x_523_ = lean_nat_dec_eq(v_newNeedlePos_522_, v___x_518_);
if (v___x_523_ == 0)
{
lean_object* v_oldBasePos_524_; lean_object* v___x_525_; lean_object* v_newBasePos_526_; lean_object* v_res_527_; lean_object* v___x_529_; 
lean_inc(v_newNeedlePos_522_);
v_oldBasePos_524_ = l_String_Slice_pos_x21(v_s_446_, v_basePos_500_);
lean_dec(v_basePos_500_);
v___x_525_ = lean_nat_sub(v_stackPos_489_, v_newNeedlePos_522_);
v_newBasePos_526_ = l_String_Slice_pos_x21(v_s_446_, v___x_525_);
lean_dec(v___x_525_);
v_res_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_527_, 0, v_oldBasePos_524_);
lean_ctor_set(v_res_527_, 1, v_newBasePos_526_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 3, v_newNeedlePos_522_);
v___x_529_ = v___x_492_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_needle_487_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_table_488_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_stackPos_489_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_newNeedlePos_522_);
v___x_529_ = v_reuseFailAlloc_532_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v_res_527_);
v___x_531_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_530_);
return v___x_531_;
}
}
else
{
lean_object* v_basePos_533_; lean_object* v_nextStackPos_534_; lean_object* v_res_535_; lean_object* v___x_537_; 
v_basePos_533_ = l_String_Slice_pos_x21(v_s_446_, v_basePos_500_);
lean_dec(v_basePos_500_);
v_nextStackPos_534_ = l_String_Slice_posGE___redArg(v_s_446_, v_stackPos_489_);
lean_inc(v_nextStackPos_534_);
v_res_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_535_, 0, v_basePos_533_);
lean_ctor_set(v_res_535_, 1, v_nextStackPos_534_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 3, v___x_518_);
lean_ctor_set(v___x_492_, 2, v_nextStackPos_534_);
v___x_537_ = v___x_492_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_needle_487_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_table_488_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v_nextStackPos_534_);
lean_ctor_set(v_reuseFailAlloc_540_, 3, v___x_518_);
v___x_537_ = v_reuseFailAlloc_540_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v_res_535_);
v___x_539_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_538_);
return v___x_539_;
}
}
}
else
{
lean_object* v_basePos_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_nextStackPos_544_; lean_object* v_res_545_; lean_object* v___x_547_; 
lean_dec(v_basePos_500_);
lean_dec(v_needlePos_490_);
v_basePos_541_ = l_String_Slice_pos_x21(v_s_446_, v_stackPos_489_);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_stackPos_489_, v___x_542_);
lean_dec(v_stackPos_489_);
v_nextStackPos_544_ = l_String_Slice_posGE___redArg(v_s_446_, v___x_543_);
lean_inc(v_nextStackPos_544_);
v_res_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_545_, 0, v_basePos_541_);
lean_ctor_set(v_res_545_, 1, v_nextStackPos_544_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 3, v___x_518_);
lean_ctor_set(v___x_492_, 2, v_nextStackPos_544_);
v___x_547_ = v___x_492_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_needle_487_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_table_488_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_nextStackPos_544_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v___x_518_);
v___x_547_ = v_reuseFailAlloc_550_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_res_545_);
v___x_549_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_548_);
return v___x_549_;
}
}
}
else
{
lean_object* v___x_551_; lean_object* v_nextStackPos_552_; lean_object* v_nextNeedlePos_553_; uint8_t v___x_554_; 
lean_dec(v_basePos_500_);
v___x_551_ = lean_unsigned_to_nat(1u);
v_nextStackPos_552_ = lean_nat_add(v_stackPos_489_, v___x_551_);
lean_dec(v_stackPos_489_);
v_nextNeedlePos_553_ = lean_nat_add(v_needlePos_490_, v___x_551_);
lean_dec(v_needlePos_490_);
v___x_554_ = lean_nat_dec_eq(v_nextNeedlePos_553_, v___x_501_);
lean_dec(v___x_501_);
if (v___x_554_ == 0)
{
lean_object* v___x_556_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 3, v_nextNeedlePos_553_);
lean_ctor_set(v___x_492_, 2, v_nextStackPos_552_);
v___x_556_ = v___x_492_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_needle_487_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_table_488_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_nextStackPos_552_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_nextNeedlePos_553_);
v___x_556_ = v_reuseFailAlloc_559_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_557_);
return v___x_558_;
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_res_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_560_ = lean_nat_sub(v_nextStackPos_552_, v_nextNeedlePos_553_);
lean_dec(v_nextNeedlePos_553_);
v___x_561_ = l_String_Slice_pos_x21(v_s_446_, v___x_560_);
lean_dec(v___x_560_);
v___x_562_ = l_String_Slice_pos_x21(v_s_446_, v_nextStackPos_552_);
v_res_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_563_, 0, v___x_561_);
lean_ctor_set(v_res_563_, 1, v___x_562_);
v___x_564_ = lean_unsigned_to_nat(0u);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 3, v___x_564_);
lean_ctor_set(v___x_492_, 2, v_nextStackPos_552_);
v___x_566_ = v___x_492_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_needle_487_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_table_488_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_nextStackPos_552_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v___x_564_);
v___x_566_ = v_reuseFailAlloc_569_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_res_563_);
v___x_568_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_567_);
return v___x_568_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_box(2);
v___x_572_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_571_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed(lean_object* v___y_573_, lean_object* v_s_574_, lean_object* v_lift_575_, lean_object* v_it_576_, lean_object* v_acc_577_, lean_object* v_hP_578_, lean_object* v_recur_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(v___y_573_, v_s_574_, v_lift_575_, v_it_576_, v_acc_577_, v_hP_578_, v_recur_579_);
lean_dec_ref(v_s_574_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(lean_object* v_s_581_, lean_object* v_lift_582_, lean_object* v_00_u03b3_583_, lean_object* v_Pl_584_, lean_object* v_it_585_, lean_object* v_init_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___f_588_; lean_object* v___x_589_; 
v___f_588_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed), 7, 3);
lean_closure_set(v___f_588_, 0, v___y_587_);
lean_closure_set(v___f_588_, 1, v_s_581_);
lean_closure_set(v___f_588_, 2, v_lift_582_);
v___x_589_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_588_, v_it_585_, v_init_586_, lean_box(0));
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(lean_object* v_s_590_){
_start:
{
lean_object* v___f_591_; 
v___f_591_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2), 7, 1);
lean_closure_set(v___f_591_, 0, v_s_590_);
return v___f_591_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(lean_object* v_pat_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_593_, 0, v_pat_592_);
return v___x_593_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(lean_object* v_pat_594_, lean_object* v_s_595_){
_start:
{
lean_object* v_str_596_; lean_object* v_startInclusive_597_; lean_object* v_endExclusive_598_; lean_object* v_str_599_; lean_object* v_startInclusive_600_; lean_object* v_endExclusive_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_str_596_ = lean_ctor_get(v_pat_594_, 0);
v_startInclusive_597_ = lean_ctor_get(v_pat_594_, 1);
v_endExclusive_598_ = lean_ctor_get(v_pat_594_, 2);
v_str_599_ = lean_ctor_get(v_s_595_, 0);
v_startInclusive_600_ = lean_ctor_get(v_s_595_, 1);
v_endExclusive_601_ = lean_ctor_get(v_s_595_, 2);
v___x_602_ = lean_nat_sub(v_endExclusive_598_, v_startInclusive_597_);
v___x_603_ = lean_nat_sub(v_endExclusive_601_, v_startInclusive_600_);
v___x_604_ = lean_nat_dec_le(v___x_602_, v___x_603_);
lean_dec(v___x_603_);
if (v___x_604_ == 0)
{
lean_dec(v___x_602_);
return v___x_604_;
}
else
{
uint8_t v___x_605_; 
v___x_605_ = lean_string_memcmp(v_str_599_, v_str_596_, v_startInclusive_600_, v_startInclusive_597_, v___x_602_);
lean_dec(v___x_602_);
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(lean_object* v_pat_606_, lean_object* v_s_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(v_pat_606_, v_s_607_);
lean_dec_ref(v_s_607_);
lean_dec_ref(v_pat_606_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(lean_object* v_pat_610_, lean_object* v_s_611_){
_start:
{
lean_object* v_str_612_; lean_object* v_startInclusive_613_; lean_object* v_endExclusive_614_; lean_object* v_str_615_; lean_object* v_startInclusive_616_; lean_object* v_endExclusive_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_str_612_ = lean_ctor_get(v_pat_610_, 0);
v_startInclusive_613_ = lean_ctor_get(v_pat_610_, 1);
v_endExclusive_614_ = lean_ctor_get(v_pat_610_, 2);
v_str_615_ = lean_ctor_get(v_s_611_, 0);
v_startInclusive_616_ = lean_ctor_get(v_s_611_, 1);
v_endExclusive_617_ = lean_ctor_get(v_s_611_, 2);
v___x_618_ = lean_nat_sub(v_endExclusive_614_, v_startInclusive_613_);
v___x_619_ = lean_nat_sub(v_endExclusive_617_, v_startInclusive_616_);
v___x_620_ = lean_nat_dec_le(v___x_618_, v___x_619_);
lean_dec(v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
else
{
uint8_t v___x_622_; 
v___x_622_ = lean_string_memcmp(v_str_615_, v_str_612_, v_startInclusive_616_, v_startInclusive_613_, v___x_618_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec(v___x_618_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = l_String_Slice_pos_x21(v_s_611_, v___x_618_);
lean_dec(v___x_618_);
v___x_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed(lean_object* v_pat_626_, lean_object* v_s_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(v_pat_626_, v_s_627_);
lean_dec_ref(v_s_627_);
lean_dec_ref(v_pat_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(lean_object* v_pat_629_, lean_object* v_s_630_, lean_object* v_x_631_){
_start:
{
lean_object* v_str_632_; lean_object* v_startInclusive_633_; lean_object* v_endExclusive_634_; lean_object* v_str_635_; lean_object* v_startInclusive_636_; lean_object* v_endExclusive_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_str_632_ = lean_ctor_get(v_pat_629_, 0);
v_startInclusive_633_ = lean_ctor_get(v_pat_629_, 1);
v_endExclusive_634_ = lean_ctor_get(v_pat_629_, 2);
v_str_635_ = lean_ctor_get(v_s_630_, 0);
v_startInclusive_636_ = lean_ctor_get(v_s_630_, 1);
v_endExclusive_637_ = lean_ctor_get(v_s_630_, 2);
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
v___x_644_ = l_String_Slice_pos_x21(v_s_630_, v___x_638_);
lean_dec(v___x_638_);
v___x_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(lean_object* v_pat_646_, lean_object* v_s_647_, lean_object* v_x_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(v_pat_646_, v_s_647_, v_x_648_);
lean_dec_ref(v_s_647_);
lean_dec_ref(v_pat_646_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(lean_object* v_pat_650_){
_start:
{
lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc_ref(v_pat_650_);
v___f_651_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_651_, 0, v_pat_650_);
lean_inc_ref(v_pat_650_);
v___x_652_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_652_, 0, v_pat_650_);
v___x_653_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_653_, 0, v_pat_650_);
v___x_654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___f_651_);
lean_ctor_set(v___x_654_, 2, v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(lean_object* v_pat_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_string_utf8_byte_size(v_pat_655_);
v___x_658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_658_, 0, v_pat_655_);
lean_ctor_set(v___x_658_, 1, v___x_656_);
lean_ctor_set(v___x_658_, 2, v___x_657_);
v___x_659_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(lean_object* v___x_660_, lean_object* v_pat_661_, lean_object* v___x_662_, lean_object* v_s_663_, lean_object* v_x_664_){
_start:
{
lean_object* v_str_665_; lean_object* v_startInclusive_666_; lean_object* v_endExclusive_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_str_665_ = lean_ctor_get(v_s_663_, 0);
v_startInclusive_666_ = lean_ctor_get(v_s_663_, 1);
v_endExclusive_667_ = lean_ctor_get(v_s_663_, 2);
v___x_668_ = lean_nat_sub(v_endExclusive_667_, v_startInclusive_666_);
v___x_669_ = lean_nat_dec_le(v___x_660_, v___x_668_);
lean_dec(v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_box(0);
return v___x_670_;
}
else
{
uint8_t v___x_671_; 
v___x_671_ = lean_string_memcmp(v_str_665_, v_pat_661_, v_startInclusive_666_, v___x_662_, v___x_660_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_box(0);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = l_String_Slice_pos_x21(v_s_663_, v___x_660_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(lean_object* v___x_675_, lean_object* v_pat_676_, lean_object* v___x_677_, lean_object* v_s_678_, lean_object* v_x_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(v___x_675_, v_pat_676_, v___x_677_, v_s_678_, v_x_679_);
lean_dec_ref(v_s_678_);
lean_dec(v___x_677_);
lean_dec_ref(v_pat_676_);
lean_dec(v___x_675_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(lean_object* v_pat_681_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_string_utf8_byte_size(v_pat_681_);
lean_inc_ref(v_pat_681_);
v___f_684_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_684_, 0, v___x_683_);
lean_closure_set(v___f_684_, 1, v_pat_681_);
lean_closure_set(v___f_684_, 2, v___x_682_);
v___x_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_685_, 0, v_pat_681_);
lean_ctor_set(v___x_685_, 1, v___x_682_);
lean_ctor_set(v___x_685_, 2, v___x_683_);
lean_inc_ref(v___x_685_);
v___x_686_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_686_, 0, v___x_685_);
v___x_687_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_687_, 0, v___x_685_);
v___x_688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___f_684_);
lean_ctor_set(v___x_688_, 2, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(lean_object* v_pat_689_, lean_object* v_s_690_){
_start:
{
lean_object* v_str_691_; lean_object* v_startInclusive_692_; lean_object* v_endExclusive_693_; lean_object* v_str_694_; lean_object* v_startInclusive_695_; lean_object* v_endExclusive_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_str_691_ = lean_ctor_get(v_pat_689_, 0);
v_startInclusive_692_ = lean_ctor_get(v_pat_689_, 1);
v_endExclusive_693_ = lean_ctor_get(v_pat_689_, 2);
v_str_694_ = lean_ctor_get(v_s_690_, 0);
v_startInclusive_695_ = lean_ctor_get(v_s_690_, 1);
v_endExclusive_696_ = lean_ctor_get(v_s_690_, 2);
v___x_697_ = lean_nat_sub(v_endExclusive_693_, v_startInclusive_692_);
v___x_698_ = lean_nat_sub(v_endExclusive_696_, v_startInclusive_695_);
v___x_699_ = lean_nat_dec_le(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec(v___x_698_);
lean_dec(v___x_697_);
return v___x_699_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_700_ = lean_nat_sub(v___x_698_, v___x_697_);
lean_dec(v___x_698_);
v___x_701_ = lean_nat_add(v_startInclusive_695_, v___x_700_);
lean_dec(v___x_700_);
v___x_702_ = lean_string_memcmp(v_str_694_, v_str_691_, v___x_701_, v_startInclusive_692_, v___x_697_);
lean_dec(v___x_697_);
lean_dec(v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(lean_object* v_pat_703_, lean_object* v_s_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(v_pat_703_, v_s_704_);
lean_dec_ref(v_s_704_);
lean_dec_ref(v_pat_703_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(lean_object* v_pat_707_, lean_object* v_s_708_){
_start:
{
lean_object* v_str_709_; lean_object* v_startInclusive_710_; lean_object* v_endExclusive_711_; lean_object* v_str_712_; lean_object* v_startInclusive_713_; lean_object* v_endExclusive_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_str_709_ = lean_ctor_get(v_pat_707_, 0);
v_startInclusive_710_ = lean_ctor_get(v_pat_707_, 1);
v_endExclusive_711_ = lean_ctor_get(v_pat_707_, 2);
v_str_712_ = lean_ctor_get(v_s_708_, 0);
v_startInclusive_713_ = lean_ctor_get(v_s_708_, 1);
v_endExclusive_714_ = lean_ctor_get(v_s_708_, 2);
v___x_715_ = lean_nat_sub(v_endExclusive_711_, v_startInclusive_710_);
v___x_716_ = lean_nat_sub(v_endExclusive_714_, v_startInclusive_713_);
v___x_717_ = lean_nat_dec_le(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec(v___x_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = lean_nat_sub(v___x_716_, v___x_715_);
lean_dec(v___x_716_);
v___x_720_ = lean_nat_add(v_startInclusive_713_, v___x_719_);
v___x_721_ = lean_string_memcmp(v_str_712_, v_str_709_, v___x_720_, v_startInclusive_710_, v___x_715_);
lean_dec(v___x_715_);
lean_dec(v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
return v___x_722_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = l_String_Slice_pos_x21(v_s_708_, v___x_719_);
lean_dec(v___x_719_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed(lean_object* v_pat_725_, lean_object* v_s_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(v_pat_725_, v_s_726_);
lean_dec_ref(v_s_726_);
lean_dec_ref(v_pat_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(lean_object* v_pat_728_, lean_object* v_s_729_, lean_object* v_x_730_){
_start:
{
lean_object* v_str_731_; lean_object* v_startInclusive_732_; lean_object* v_endExclusive_733_; lean_object* v_str_734_; lean_object* v_startInclusive_735_; lean_object* v_endExclusive_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_str_731_ = lean_ctor_get(v_pat_728_, 0);
v_startInclusive_732_ = lean_ctor_get(v_pat_728_, 1);
v_endExclusive_733_ = lean_ctor_get(v_pat_728_, 2);
v_str_734_ = lean_ctor_get(v_s_729_, 0);
v_startInclusive_735_ = lean_ctor_get(v_s_729_, 1);
v_endExclusive_736_ = lean_ctor_get(v_s_729_, 2);
v___x_737_ = lean_nat_sub(v_endExclusive_733_, v_startInclusive_732_);
v___x_738_ = lean_nat_sub(v_endExclusive_736_, v_startInclusive_735_);
v___x_739_ = lean_nat_dec_le(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v___x_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = lean_nat_sub(v___x_738_, v___x_737_);
lean_dec(v___x_738_);
v___x_742_ = lean_nat_add(v_startInclusive_735_, v___x_741_);
v___x_743_ = lean_string_memcmp(v_str_734_, v_str_731_, v___x_742_, v_startInclusive_732_, v___x_737_);
lean_dec(v___x_737_);
lean_dec(v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
return v___x_744_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = l_String_Slice_pos_x21(v_s_729_, v___x_741_);
lean_dec(v___x_741_);
v___x_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(lean_object* v_pat_747_, lean_object* v_s_748_, lean_object* v_x_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(v_pat_747_, v_s_748_, v_x_749_);
lean_dec_ref(v_s_748_);
lean_dec_ref(v_pat_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(lean_object* v_pat_751_){
_start:
{
lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_inc_ref(v_pat_751_);
v___f_752_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_752_, 0, v_pat_751_);
lean_inc_ref(v_pat_751_);
v___x_753_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_753_, 0, v_pat_751_);
v___x_754_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_754_, 0, v_pat_751_);
v___x_755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___f_752_);
lean_ctor_set(v___x_755_, 2, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(lean_object* v___x_756_, lean_object* v_pat_757_, lean_object* v___x_758_, lean_object* v_s_759_, lean_object* v_x_760_){
_start:
{
lean_object* v_str_761_; lean_object* v_startInclusive_762_; lean_object* v_endExclusive_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_str_761_ = lean_ctor_get(v_s_759_, 0);
v_startInclusive_762_ = lean_ctor_get(v_s_759_, 1);
v_endExclusive_763_ = lean_ctor_get(v_s_759_, 2);
v___x_764_ = lean_nat_sub(v_endExclusive_763_, v_startInclusive_762_);
v___x_765_ = lean_nat_dec_le(v___x_756_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
lean_dec(v___x_764_);
v___x_766_ = lean_box(0);
return v___x_766_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_767_ = lean_nat_sub(v___x_764_, v___x_756_);
lean_dec(v___x_764_);
v___x_768_ = lean_nat_add(v_startInclusive_762_, v___x_767_);
v___x_769_ = lean_string_memcmp(v_str_761_, v_pat_757_, v___x_768_, v___x_758_, v___x_756_);
lean_dec(v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
return v___x_770_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = l_String_Slice_pos_x21(v_s_759_, v___x_767_);
lean_dec(v___x_767_);
v___x_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(lean_object* v___x_773_, lean_object* v_pat_774_, lean_object* v___x_775_, lean_object* v_s_776_, lean_object* v_x_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(v___x_773_, v_pat_774_, v___x_775_, v_s_776_, v_x_777_);
lean_dec_ref(v_s_776_);
lean_dec(v___x_775_);
lean_dec_ref(v_pat_774_);
lean_dec(v___x_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(lean_object* v_pat_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___f_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_string_utf8_byte_size(v_pat_779_);
lean_inc_ref(v_pat_779_);
v___f_782_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_782_, 0, v___x_781_);
lean_closure_set(v___f_782_, 1, v_pat_779_);
lean_closure_set(v___f_782_, 2, v___x_780_);
v___x_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_783_, 0, v_pat_779_);
lean_ctor_set(v___x_783_, 1, v___x_780_);
lean_ctor_set(v___x_783_, 2, v___x_781_);
lean_inc_ref(v___x_783_);
v___x_784_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_784_, 0, v___x_783_);
v___x_785_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_785_, 0, v___x_783_);
v___x_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___f_782_);
lean_ctor_set(v___x_786_, 2, v___x_785_);
return v___x_786_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Pattern_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
