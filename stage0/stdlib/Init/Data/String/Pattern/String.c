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
static const lean_ctor_object l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0 = (const lean_object*)&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg(){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0));
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___boxed(lean_object* v___dummy_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg();
return v_res_189_;
}
}
static lean_object* _init_l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0(void){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg();
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(lean_object* v_s_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0, &l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_once, _init_l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___boxed(lean_object* v_s_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(v_s_193_);
lean_dec_ref(v_s_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg(){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0, &l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_once, _init_l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg___boxed(lean_object* v___dummy_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg();
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0, &l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_once, _init_l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___boxed(lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(v_a_201_);
lean_dec_ref(v_a_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___redArg(lean_object* v_pat_203_){
_start:
{
lean_object* v_startInclusive_204_; lean_object* v_endExclusive_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_startInclusive_204_ = lean_ctor_get(v_pat_203_, 1);
v_endExclusive_205_ = lean_ctor_get(v_pat_203_, 2);
v___x_206_ = lean_nat_sub(v_endExclusive_205_, v_startInclusive_204_);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_nat_dec_eq(v___x_206_, v___x_207_);
lean_dec(v___x_206_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_203_);
v___x_210_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_210_, 0, v_pat_203_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
lean_ctor_set(v___x_210_, 2, v___x_207_);
lean_ctor_set(v___x_210_, 3, v___x_207_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; 
lean_dec_ref(v_pat_203_);
v___x_211_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0));
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter(lean_object* v_pat_212_, lean_object* v_s_213_){
_start:
{
lean_object* v_startInclusive_214_; lean_object* v_endExclusive_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_startInclusive_214_ = lean_ctor_get(v_pat_212_, 1);
v_endExclusive_215_ = lean_ctor_get(v_pat_212_, 2);
v___x_216_ = lean_nat_sub(v_endExclusive_215_, v_startInclusive_214_);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_nat_dec_eq(v___x_216_, v___x_217_);
lean_dec(v___x_216_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_212_);
v___x_220_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_220_, 0, v_pat_212_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
lean_ctor_set(v___x_220_, 2, v___x_217_);
lean_ctor_set(v___x_220_, 3, v___x_217_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; 
lean_dec_ref(v_pat_212_);
v___x_221_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0));
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed(lean_object* v_pat_222_, lean_object* v_s_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_String_Slice_Pattern_ForwardSliceSearcher_iter(v_pat_222_, v_s_223_);
lean_dec_ref(v_s_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(lean_object* v_s_225_, lean_object* v_x_226_){
_start:
{
switch(lean_obj_tag(v_x_226_))
{
case 0:
{
lean_object* v_pos_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_242_; 
v_pos_227_ = lean_ctor_get(v_x_226_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_242_ == 0)
{
v___x_229_ = v_x_226_;
v_isShared_230_ = v_isSharedCheck_242_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_pos_227_);
lean_dec(v_x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_242_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_res_231_; lean_object* v_startInclusive_232_; lean_object* v_endExclusive_233_; lean_object* v___x_234_; uint8_t v_decide_235_; 
lean_inc_n(v_pos_227_, 2);
v_res_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_231_, 0, v_pos_227_);
lean_ctor_set(v_res_231_, 1, v_pos_227_);
v_startInclusive_232_ = lean_ctor_get(v_s_225_, 1);
v_endExclusive_233_ = lean_ctor_get(v_s_225_, 2);
v___x_234_ = lean_nat_sub(v_endExclusive_233_, v_startInclusive_232_);
v_decide_235_ = lean_nat_dec_eq(v_pos_227_, v___x_234_);
lean_dec(v___x_234_);
if (v_decide_235_ == 0)
{
lean_object* v___x_237_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set_tag(v___x_229_, 1);
v___x_237_ = v___x_229_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_pos_227_);
v___x_237_ = v_reuseFailAlloc_239_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_res_231_);
return v___x_238_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_del_object(v___x_229_);
lean_dec(v_pos_227_);
v___x_240_ = lean_box(3);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v_res_231_);
return v___x_241_;
}
}
}
case 1:
{
lean_object* v_pos_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_257_; 
v_pos_243_ = lean_ctor_get(v_x_226_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_257_ == 0)
{
v___x_245_ = v_x_226_;
v_isShared_246_ = v_isSharedCheck_257_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_pos_243_);
lean_dec(v_x_226_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_257_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_str_247_; lean_object* v_startInclusive_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_res_252_; lean_object* v___x_254_; 
v_str_247_ = lean_ctor_get(v_s_225_, 0);
v_startInclusive_248_ = lean_ctor_get(v_s_225_, 1);
v___x_249_ = lean_nat_add(v_startInclusive_248_, v_pos_243_);
v___x_250_ = lean_string_utf8_next_fast(v_str_247_, v___x_249_);
lean_dec(v___x_249_);
v___x_251_ = lean_nat_sub(v___x_250_, v_startInclusive_248_);
lean_inc(v___x_251_);
v_res_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_252_, 0, v_pos_243_);
lean_ctor_set(v_res_252_, 1, v___x_251_);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 0);
lean_ctor_set(v___x_245_, 0, v___x_251_);
v___x_254_ = v___x_245_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_251_);
v___x_254_ = v_reuseFailAlloc_256_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; 
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_res_252_);
return v___x_255_;
}
}
}
case 2:
{
lean_object* v_needle_258_; lean_object* v_table_259_; lean_object* v_stackPos_260_; lean_object* v_needlePos_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_336_; 
v_needle_258_ = lean_ctor_get(v_x_226_, 0);
v_table_259_ = lean_ctor_get(v_x_226_, 1);
v_stackPos_260_ = lean_ctor_get(v_x_226_, 2);
v_needlePos_261_ = lean_ctor_get(v_x_226_, 3);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_336_ == 0)
{
v___x_263_ = v_x_226_;
v_isShared_264_ = v_isSharedCheck_336_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_needlePos_261_);
lean_inc(v_stackPos_260_);
lean_inc(v_table_259_);
lean_inc(v_needle_258_);
lean_dec(v_x_226_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_336_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_str_265_; lean_object* v_startInclusive_266_; lean_object* v_endExclusive_267_; lean_object* v_str_268_; lean_object* v_startInclusive_269_; lean_object* v_endExclusive_270_; lean_object* v_basePos_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_str_265_ = lean_ctor_get(v_needle_258_, 0);
v_startInclusive_266_ = lean_ctor_get(v_needle_258_, 1);
v_endExclusive_267_ = lean_ctor_get(v_needle_258_, 2);
v_str_268_ = lean_ctor_get(v_s_225_, 0);
v_startInclusive_269_ = lean_ctor_get(v_s_225_, 1);
v_endExclusive_270_ = lean_ctor_get(v_s_225_, 2);
v_basePos_271_ = lean_nat_sub(v_stackPos_260_, v_needlePos_261_);
v___x_272_ = lean_nat_sub(v_endExclusive_267_, v_startInclusive_266_);
v___x_273_ = lean_nat_add(v_basePos_271_, v___x_272_);
v___x_274_ = lean_nat_sub(v_endExclusive_270_, v_startInclusive_269_);
v___x_275_ = lean_nat_dec_le(v___x_273_, v___x_274_);
lean_dec(v___x_273_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
lean_dec(v___x_272_);
lean_del_object(v___x_263_);
lean_dec(v_needlePos_261_);
lean_dec(v_stackPos_260_);
lean_dec_ref(v_table_259_);
lean_dec_ref(v_needle_258_);
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_add(v_basePos_271_, v___x_276_);
v___x_278_ = lean_nat_dec_le(v___x_277_, v___x_274_);
lean_dec(v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
lean_dec(v___x_274_);
lean_dec(v_basePos_271_);
v___x_279_ = lean_box(2);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v_res_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_280_ = l_String_Slice_pos_x21(v_s_225_, v_basePos_271_);
lean_dec(v_basePos_271_);
v_res_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_281_, 0, v___x_280_);
lean_ctor_set(v_res_281_, 1, v___x_274_);
v___x_282_ = lean_box(3);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_res_281_);
return v___x_283_;
}
}
else
{
lean_object* v___x_284_; uint8_t v_stackByte_285_; lean_object* v___x_286_; uint8_t v_patByte_287_; uint8_t v___x_288_; 
lean_dec(v___x_274_);
v___x_284_ = lean_nat_add(v_startInclusive_269_, v_stackPos_260_);
v_stackByte_285_ = lean_string_get_byte_fast(v_str_268_, v___x_284_);
v___x_286_ = lean_nat_add(v_startInclusive_266_, v_needlePos_261_);
v_patByte_287_ = lean_string_get_byte_fast(v_str_265_, v___x_286_);
v___x_288_ = lean_uint8_dec_eq(v_stackByte_285_, v_patByte_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; uint8_t v_decide_290_; 
lean_dec(v___x_272_);
v___x_289_ = lean_unsigned_to_nat(0u);
v_decide_290_ = lean_nat_dec_eq(v_needlePos_261_, v___x_289_);
if (v_decide_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_newNeedlePos_293_; uint8_t v___x_294_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_sub(v_needlePos_261_, v___x_291_);
lean_dec(v_needlePos_261_);
v_newNeedlePos_293_ = lean_array_fget_borrowed(v_table_259_, v___x_292_);
lean_dec(v___x_292_);
v___x_294_ = lean_nat_dec_eq(v_newNeedlePos_293_, v___x_289_);
if (v___x_294_ == 0)
{
lean_object* v_oldBasePos_295_; lean_object* v___x_296_; lean_object* v_newBasePos_297_; lean_object* v_res_298_; lean_object* v___x_300_; 
lean_inc(v_newNeedlePos_293_);
v_oldBasePos_295_ = l_String_Slice_pos_x21(v_s_225_, v_basePos_271_);
lean_dec(v_basePos_271_);
v___x_296_ = lean_nat_sub(v_stackPos_260_, v_newNeedlePos_293_);
v_newBasePos_297_ = l_String_Slice_pos_x21(v_s_225_, v___x_296_);
lean_dec(v___x_296_);
v_res_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_298_, 0, v_oldBasePos_295_);
lean_ctor_set(v_res_298_, 1, v_newBasePos_297_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 3, v_newNeedlePos_293_);
v___x_300_ = v___x_263_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_needle_258_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_table_259_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_stackPos_260_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_newNeedlePos_293_);
v___x_300_ = v_reuseFailAlloc_302_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; 
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_res_298_);
return v___x_301_;
}
}
else
{
lean_object* v_basePos_303_; lean_object* v_nextStackPos_304_; lean_object* v_res_305_; lean_object* v___x_307_; 
v_basePos_303_ = l_String_Slice_pos_x21(v_s_225_, v_basePos_271_);
lean_dec(v_basePos_271_);
v_nextStackPos_304_ = l_String_Slice_posGE___redArg(v_s_225_, v_stackPos_260_);
lean_inc(v_nextStackPos_304_);
v_res_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_305_, 0, v_basePos_303_);
lean_ctor_set(v_res_305_, 1, v_nextStackPos_304_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 3, v___x_289_);
lean_ctor_set(v___x_263_, 2, v_nextStackPos_304_);
v___x_307_ = v___x_263_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_needle_258_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_table_259_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_nextStackPos_304_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v___x_289_);
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
lean_object* v_basePos_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_nextStackPos_313_; lean_object* v_res_314_; lean_object* v___x_316_; 
lean_dec(v_basePos_271_);
lean_dec(v_needlePos_261_);
v_basePos_310_ = l_String_Slice_pos_x21(v_s_225_, v_stackPos_260_);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_add(v_stackPos_260_, v___x_311_);
lean_dec(v_stackPos_260_);
v_nextStackPos_313_ = l_String_Slice_posGE___redArg(v_s_225_, v___x_312_);
lean_inc(v_nextStackPos_313_);
v_res_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_314_, 0, v_basePos_310_);
lean_ctor_set(v_res_314_, 1, v_nextStackPos_313_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 3, v___x_289_);
lean_ctor_set(v___x_263_, 2, v_nextStackPos_313_);
v___x_316_ = v___x_263_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_needle_258_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_table_259_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_nextStackPos_313_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v___x_289_);
v___x_316_ = v_reuseFailAlloc_318_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_res_314_);
return v___x_317_;
}
}
}
else
{
lean_object* v___x_319_; lean_object* v_nextStackPos_320_; lean_object* v_nextNeedlePos_321_; uint8_t v_decide_322_; 
lean_dec(v_basePos_271_);
v___x_319_ = lean_unsigned_to_nat(1u);
v_nextStackPos_320_ = lean_nat_add(v_stackPos_260_, v___x_319_);
lean_dec(v_stackPos_260_);
v_nextNeedlePos_321_ = lean_nat_add(v_needlePos_261_, v___x_319_);
lean_dec(v_needlePos_261_);
v_decide_322_ = lean_nat_dec_eq(v_nextNeedlePos_321_, v___x_272_);
lean_dec(v___x_272_);
if (v_decide_322_ == 0)
{
lean_object* v___x_324_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 3, v_nextNeedlePos_321_);
lean_ctor_set(v___x_263_, 2, v_nextStackPos_320_);
v___x_324_ = v___x_263_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_needle_258_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_table_259_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_nextStackPos_320_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_nextNeedlePos_321_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v_res_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_327_ = lean_nat_sub(v_nextStackPos_320_, v_nextNeedlePos_321_);
lean_dec(v_nextNeedlePos_321_);
v___x_328_ = l_String_Slice_pos_x21(v_s_225_, v___x_327_);
lean_dec(v___x_327_);
v___x_329_ = l_String_Slice_pos_x21(v_s_225_, v_nextStackPos_320_);
v_res_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_330_, 0, v___x_328_);
lean_ctor_set(v_res_330_, 1, v___x_329_);
v___x_331_ = lean_unsigned_to_nat(0u);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 3, v___x_331_);
lean_ctor_set(v___x_263_, 2, v_nextStackPos_320_);
v___x_333_ = v___x_263_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_needle_258_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_table_259_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_nextStackPos_320_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v___x_331_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v_res_330_);
return v___x_334_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_337_; 
v___x_337_ = lean_box(2);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed(lean_object* v_s_338_, lean_object* v_x_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(v_s_338_, v_x_339_);
lean_dec_ref(v_s_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep(lean_object* v_s_341_){
_start:
{
lean_object* v___f_342_; 
v___f_342_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed), 2, 1);
lean_closure_set(v___f_342_, 0, v_s_341_);
return v___f_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(lean_object* v_s_343_, lean_object* v_x_344_){
_start:
{
switch(lean_obj_tag(v_x_344_))
{
case 0:
{
lean_object* v_pos_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_355_; 
v_pos_345_ = lean_ctor_get(v_x_344_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_344_);
if (v_isSharedCheck_355_ == 0)
{
v___x_347_ = v_x_344_;
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_pos_345_);
lean_dec(v_x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_349_ = l_String_Slice_Pos_remainingBytes(v_s_343_, v_pos_345_);
lean_dec(v_pos_345_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 1);
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
case 1:
{
lean_object* v_pos_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_366_; 
v_pos_356_ = lean_ctor_get(v_x_344_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_344_);
if (v_isSharedCheck_366_ == 0)
{
v___x_358_ = v_x_344_;
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_pos_356_);
lean_dec(v_x_344_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_360_ = l_String_Slice_Pos_remainingBytes(v_s_343_, v_pos_356_);
lean_dec(v_pos_356_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_362_);
v___x_364_ = v___x_358_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
case 2:
{
lean_object* v_stackPos_367_; lean_object* v_needlePos_368_; lean_object* v_startInclusive_369_; lean_object* v_endExclusive_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_stackPos_367_ = lean_ctor_get(v_x_344_, 2);
lean_inc(v_stackPos_367_);
v_needlePos_368_ = lean_ctor_get(v_x_344_, 3);
lean_inc(v_needlePos_368_);
lean_dec_ref_known(v_x_344_, 4);
v_startInclusive_369_ = lean_ctor_get(v_s_343_, 1);
v_endExclusive_370_ = lean_ctor_get(v_s_343_, 2);
v___x_371_ = lean_nat_sub(v_endExclusive_370_, v_startInclusive_369_);
v___x_372_ = lean_nat_sub(v___x_371_, v_stackPos_367_);
lean_dec(v_stackPos_367_);
lean_dec(v___x_371_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v_needlePos_368_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
default: 
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(0);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption___boxed(lean_object* v_s_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(v_s_376_, v_x_377_);
lean_dec_ref(v_s_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_box(0);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg();
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(lean_object* v_s_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(lean_object* v_s_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(v_s_385_);
lean_dec_ref(v_s_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(lean_object* v_x_387_, lean_object* v_h__1_388_, lean_object* v_h__2_389_, lean_object* v_h__3_390_, lean_object* v_h__4_391_){
_start:
{
switch(lean_obj_tag(v_x_387_))
{
case 0:
{
lean_object* v_pos_392_; lean_object* v___x_393_; 
lean_dec(v_h__4_391_);
lean_dec(v_h__3_390_);
lean_dec(v_h__2_389_);
v_pos_392_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_pos_392_);
lean_dec_ref_known(v_x_387_, 1);
v___x_393_ = lean_apply_1(v_h__1_388_, v_pos_392_);
return v___x_393_;
}
case 1:
{
lean_object* v_pos_394_; lean_object* v___x_395_; 
lean_dec(v_h__4_391_);
lean_dec(v_h__3_390_);
lean_dec(v_h__1_388_);
v_pos_394_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_pos_394_);
lean_dec_ref_known(v_x_387_, 1);
v___x_395_ = lean_apply_2(v_h__2_389_, v_pos_394_, lean_box(0));
return v___x_395_;
}
case 2:
{
lean_object* v_needle_396_; lean_object* v_table_397_; lean_object* v_stackPos_398_; lean_object* v_needlePos_399_; lean_object* v___x_400_; 
lean_dec(v_h__4_391_);
lean_dec(v_h__2_389_);
lean_dec(v_h__1_388_);
v_needle_396_ = lean_ctor_get(v_x_387_, 0);
lean_inc_ref(v_needle_396_);
v_table_397_ = lean_ctor_get(v_x_387_, 1);
lean_inc_ref(v_table_397_);
v_stackPos_398_ = lean_ctor_get(v_x_387_, 2);
lean_inc(v_stackPos_398_);
v_needlePos_399_ = lean_ctor_get(v_x_387_, 3);
lean_inc(v_needlePos_399_);
lean_dec_ref_known(v_x_387_, 4);
v___x_400_ = lean_apply_6(v_h__3_390_, v_needle_396_, v_table_397_, lean_box(0), v_stackPos_398_, v_needlePos_399_, lean_box(0));
return v___x_400_;
}
default: 
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec(v_h__3_390_);
lean_dec(v_h__2_389_);
lean_dec(v_h__1_388_);
v___x_401_ = lean_box(0);
v___x_402_ = lean_apply_1(v_h__4_391_, v___x_401_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(lean_object* v_s_403_, lean_object* v_motive_404_, lean_object* v_x_405_, lean_object* v_h__1_406_, lean_object* v_h__2_407_, lean_object* v_h__3_408_, lean_object* v_h__4_409_){
_start:
{
switch(lean_obj_tag(v_x_405_))
{
case 0:
{
lean_object* v_pos_410_; lean_object* v___x_411_; 
lean_dec(v_h__4_409_);
lean_dec(v_h__3_408_);
lean_dec(v_h__2_407_);
v_pos_410_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_pos_410_);
lean_dec_ref_known(v_x_405_, 1);
v___x_411_ = lean_apply_1(v_h__1_406_, v_pos_410_);
return v___x_411_;
}
case 1:
{
lean_object* v_pos_412_; lean_object* v___x_413_; 
lean_dec(v_h__4_409_);
lean_dec(v_h__3_408_);
lean_dec(v_h__1_406_);
v_pos_412_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_pos_412_);
lean_dec_ref_known(v_x_405_, 1);
v___x_413_ = lean_apply_2(v_h__2_407_, v_pos_412_, lean_box(0));
return v___x_413_;
}
case 2:
{
lean_object* v_needle_414_; lean_object* v_table_415_; lean_object* v_stackPos_416_; lean_object* v_needlePos_417_; lean_object* v___x_418_; 
lean_dec(v_h__4_409_);
lean_dec(v_h__2_407_);
lean_dec(v_h__1_406_);
v_needle_414_ = lean_ctor_get(v_x_405_, 0);
lean_inc_ref(v_needle_414_);
v_table_415_ = lean_ctor_get(v_x_405_, 1);
lean_inc_ref(v_table_415_);
v_stackPos_416_ = lean_ctor_get(v_x_405_, 2);
lean_inc(v_stackPos_416_);
v_needlePos_417_ = lean_ctor_get(v_x_405_, 3);
lean_inc(v_needlePos_417_);
lean_dec_ref_known(v_x_405_, 4);
v___x_418_ = lean_apply_6(v_h__3_408_, v_needle_414_, v_table_415_, lean_box(0), v_stackPos_416_, v_needlePos_417_, lean_box(0));
return v___x_418_;
}
default: 
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_h__3_408_);
lean_dec(v_h__2_407_);
lean_dec(v_h__1_406_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_apply_1(v_h__4_409_, v___x_419_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(lean_object* v_s_421_, lean_object* v_motive_422_, lean_object* v_x_423_, lean_object* v_h__1_424_, lean_object* v_h__2_425_, lean_object* v_h__3_426_, lean_object* v_h__4_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(v_s_421_, v_motive_422_, v_x_423_, v_h__1_424_, v_h__2_425_, v_h__3_426_, v_h__4_427_);
lean_dec_ref(v_s_421_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___redArg(lean_object* v_x_429_, lean_object* v_h__1_430_, lean_object* v_h__2_431_, lean_object* v_h__3_432_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(lean_object* v_s_440_, lean_object* v_motive_441_, lean_object* v_x_442_, lean_object* v_h__1_443_, lean_object* v_h__2_444_, lean_object* v_h__3_445_){
_start:
{
switch(lean_obj_tag(v_x_442_))
{
case 0:
{
lean_object* v_it_446_; lean_object* v_out_447_; lean_object* v___x_448_; 
lean_dec(v_h__3_445_);
lean_dec(v_h__2_444_);
v_it_446_ = lean_ctor_get(v_x_442_, 0);
lean_inc(v_it_446_);
v_out_447_ = lean_ctor_get(v_x_442_, 1);
lean_inc(v_out_447_);
lean_dec_ref_known(v_x_442_, 2);
v___x_448_ = lean_apply_2(v_h__1_443_, v_it_446_, v_out_447_);
return v___x_448_;
}
case 1:
{
lean_object* v_it_449_; lean_object* v___x_450_; 
lean_dec(v_h__3_445_);
lean_dec(v_h__1_443_);
v_it_449_ = lean_ctor_get(v_x_442_, 0);
lean_inc(v_it_449_);
lean_dec_ref_known(v_x_442_, 1);
v___x_450_ = lean_apply_1(v_h__2_444_, v_it_449_);
return v___x_450_;
}
default: 
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v_h__2_444_);
lean_dec(v_h__1_443_);
v___x_451_ = lean_box(0);
v___x_452_ = lean_apply_1(v_h__3_445_, v___x_451_);
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___boxed(lean_object* v_s_453_, lean_object* v_motive_454_, lean_object* v_x_455_, lean_object* v_h__1_456_, lean_object* v_h__2_457_, lean_object* v_h__3_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(v_s_453_, v_motive_454_, v_x_455_, v_h__1_456_, v_h__2_457_, v_h__3_458_);
lean_dec_ref(v_s_453_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = lean_box(0);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg();
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(lean_object* v_s_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_box(0);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(lean_object* v_s_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(v_s_466_);
lean_dec_ref(v_s_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(lean_object* v___y_468_, lean_object* v_acc_469_, lean_object* v_recur_470_, lean_object* v_s_471_){
_start:
{
switch(lean_obj_tag(v_s_471_))
{
case 0:
{
lean_object* v_it_472_; lean_object* v_out_473_; lean_object* v_val_474_; 
v_it_472_ = lean_ctor_get(v_s_471_, 0);
lean_inc(v_it_472_);
v_out_473_ = lean_ctor_get(v_s_471_, 1);
lean_inc(v_out_473_);
lean_dec_ref_known(v_s_471_, 2);
v_val_474_ = lean_apply_3(v___y_468_, v_out_473_, lean_box(0), v_acc_469_);
if (lean_obj_tag(v_val_474_) == 0)
{
lean_object* v_a_475_; 
lean_dec(v_it_472_);
lean_dec(v_recur_470_);
v_a_475_ = lean_ctor_get(v_val_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v_val_474_, 1);
return v_a_475_;
}
else
{
lean_object* v_a_476_; lean_object* v___x_477_; 
v_a_476_ = lean_ctor_get(v_val_474_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v_val_474_, 1);
v___x_477_ = lean_apply_4(v_recur_470_, v_it_472_, v_a_476_, lean_box(0), lean_box(0));
return v___x_477_;
}
}
case 1:
{
lean_object* v_it_478_; lean_object* v___x_479_; 
lean_dec_ref(v___y_468_);
v_it_478_ = lean_ctor_get(v_s_471_, 0);
lean_inc(v_it_478_);
lean_dec_ref_known(v_s_471_, 1);
v___x_479_ = lean_apply_4(v_recur_470_, v_it_478_, v_acc_469_, lean_box(0), lean_box(0));
return v___x_479_;
}
default: 
{
lean_dec(v_recur_470_);
lean_dec_ref(v___y_468_);
return v_acc_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(lean_object* v___y_480_, lean_object* v_s_481_, lean_object* v_lift_482_, lean_object* v_it_483_, lean_object* v_acc_484_, lean_object* v_hP_485_, lean_object* v_recur_486_){
_start:
{
lean_object* v___f_487_; 
v___f_487_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0), 4, 3);
lean_closure_set(v___f_487_, 0, v___y_480_);
lean_closure_set(v___f_487_, 1, v_acc_484_);
lean_closure_set(v___f_487_, 2, v_recur_486_);
switch(lean_obj_tag(v_it_483_))
{
case 0:
{
lean_object* v_pos_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_505_; 
v_pos_488_ = lean_ctor_get(v_it_483_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v_it_483_);
if (v_isSharedCheck_505_ == 0)
{
v___x_490_ = v_it_483_;
v_isShared_491_ = v_isSharedCheck_505_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_pos_488_);
lean_dec(v_it_483_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_505_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_res_492_; lean_object* v_startInclusive_493_; lean_object* v_endExclusive_494_; lean_object* v___x_495_; uint8_t v_decide_496_; 
lean_inc_n(v_pos_488_, 2);
v_res_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_492_, 0, v_pos_488_);
lean_ctor_set(v_res_492_, 1, v_pos_488_);
v_startInclusive_493_ = lean_ctor_get(v_s_481_, 1);
v_endExclusive_494_ = lean_ctor_get(v_s_481_, 2);
v___x_495_ = lean_nat_sub(v_endExclusive_494_, v_startInclusive_493_);
v_decide_496_ = lean_nat_dec_eq(v_pos_488_, v___x_495_);
lean_dec(v___x_495_);
if (v_decide_496_ == 0)
{
lean_object* v___x_498_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set_tag(v___x_490_, 1);
v___x_498_ = v___x_490_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_pos_488_);
v___x_498_ = v_reuseFailAlloc_501_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_res_492_);
v___x_500_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_499_);
return v___x_500_;
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_del_object(v___x_490_);
lean_dec(v_pos_488_);
v___x_502_ = lean_box(3);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v_res_492_);
v___x_504_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_503_);
return v___x_504_;
}
}
}
case 1:
{
lean_object* v_pos_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_521_; 
v_pos_506_ = lean_ctor_get(v_it_483_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_it_483_);
if (v_isSharedCheck_521_ == 0)
{
v___x_508_ = v_it_483_;
v_isShared_509_ = v_isSharedCheck_521_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_pos_506_);
lean_dec(v_it_483_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_521_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_str_510_; lean_object* v_startInclusive_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_res_515_; lean_object* v___x_517_; 
v_str_510_ = lean_ctor_get(v_s_481_, 0);
v_startInclusive_511_ = lean_ctor_get(v_s_481_, 1);
v___x_512_ = lean_nat_add(v_startInclusive_511_, v_pos_506_);
v___x_513_ = lean_string_utf8_next_fast(v_str_510_, v___x_512_);
lean_dec(v___x_512_);
v___x_514_ = lean_nat_sub(v___x_513_, v_startInclusive_511_);
lean_inc(v___x_514_);
v_res_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_515_, 0, v_pos_506_);
lean_ctor_set(v_res_515_, 1, v___x_514_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
lean_ctor_set(v___x_508_, 0, v___x_514_);
v___x_517_ = v___x_508_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_514_);
v___x_517_ = v_reuseFailAlloc_520_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v_res_515_);
v___x_519_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_518_);
return v___x_519_;
}
}
}
case 2:
{
lean_object* v_needle_522_; lean_object* v_table_523_; lean_object* v_stackPos_524_; lean_object* v_needlePos_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_607_; 
v_needle_522_ = lean_ctor_get(v_it_483_, 0);
v_table_523_ = lean_ctor_get(v_it_483_, 1);
v_stackPos_524_ = lean_ctor_get(v_it_483_, 2);
v_needlePos_525_ = lean_ctor_get(v_it_483_, 3);
v_isSharedCheck_607_ = !lean_is_exclusive(v_it_483_);
if (v_isSharedCheck_607_ == 0)
{
v___x_527_ = v_it_483_;
v_isShared_528_ = v_isSharedCheck_607_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_needlePos_525_);
lean_inc(v_stackPos_524_);
lean_inc(v_table_523_);
lean_inc(v_needle_522_);
lean_dec(v_it_483_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_607_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_str_529_; lean_object* v_startInclusive_530_; lean_object* v_endExclusive_531_; lean_object* v_str_532_; lean_object* v_startInclusive_533_; lean_object* v_endExclusive_534_; lean_object* v_basePos_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_str_529_ = lean_ctor_get(v_needle_522_, 0);
v_startInclusive_530_ = lean_ctor_get(v_needle_522_, 1);
v_endExclusive_531_ = lean_ctor_get(v_needle_522_, 2);
v_str_532_ = lean_ctor_get(v_s_481_, 0);
v_startInclusive_533_ = lean_ctor_get(v_s_481_, 1);
v_endExclusive_534_ = lean_ctor_get(v_s_481_, 2);
v_basePos_535_ = lean_nat_sub(v_stackPos_524_, v_needlePos_525_);
v___x_536_ = lean_nat_sub(v_endExclusive_531_, v_startInclusive_530_);
v___x_537_ = lean_nat_add(v_basePos_535_, v___x_536_);
v___x_538_ = lean_nat_sub(v_endExclusive_534_, v_startInclusive_533_);
v___x_539_ = lean_nat_dec_le(v___x_537_, v___x_538_);
lean_dec(v___x_537_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
lean_dec(v___x_536_);
lean_del_object(v___x_527_);
lean_dec(v_needlePos_525_);
lean_dec(v_stackPos_524_);
lean_dec_ref(v_table_523_);
lean_dec_ref(v_needle_522_);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_basePos_535_, v___x_540_);
v___x_542_ = lean_nat_dec_le(v___x_541_, v___x_538_);
lean_dec(v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec(v___x_538_);
lean_dec(v_basePos_535_);
v___x_543_ = lean_box(2);
v___x_544_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_543_);
return v___x_544_;
}
else
{
lean_object* v___x_545_; lean_object* v_res_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_545_ = l_String_Slice_pos_x21(v_s_481_, v_basePos_535_);
lean_dec(v_basePos_535_);
v_res_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_546_, 0, v___x_545_);
lean_ctor_set(v_res_546_, 1, v___x_538_);
v___x_547_ = lean_box(3);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_res_546_);
v___x_549_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_548_);
return v___x_549_;
}
}
else
{
lean_object* v___x_550_; uint8_t v_stackByte_551_; lean_object* v___x_552_; uint8_t v_patByte_553_; uint8_t v___x_554_; 
lean_dec(v___x_538_);
v___x_550_ = lean_nat_add(v_startInclusive_533_, v_stackPos_524_);
v_stackByte_551_ = lean_string_get_byte_fast(v_str_532_, v___x_550_);
v___x_552_ = lean_nat_add(v_startInclusive_530_, v_needlePos_525_);
v_patByte_553_ = lean_string_get_byte_fast(v_str_529_, v___x_552_);
v___x_554_ = lean_uint8_dec_eq(v_stackByte_551_, v_patByte_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; uint8_t v_decide_556_; 
lean_dec(v___x_536_);
v___x_555_ = lean_unsigned_to_nat(0u);
v_decide_556_ = lean_nat_dec_eq(v_needlePos_525_, v___x_555_);
if (v_decide_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_newNeedlePos_559_; uint8_t v___x_560_; 
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_sub(v_needlePos_525_, v___x_557_);
lean_dec(v_needlePos_525_);
v_newNeedlePos_559_ = lean_array_fget_borrowed(v_table_523_, v___x_558_);
lean_dec(v___x_558_);
v___x_560_ = lean_nat_dec_eq(v_newNeedlePos_559_, v___x_555_);
if (v___x_560_ == 0)
{
lean_object* v_oldBasePos_561_; lean_object* v___x_562_; lean_object* v_newBasePos_563_; lean_object* v_res_564_; lean_object* v___x_566_; 
lean_inc(v_newNeedlePos_559_);
v_oldBasePos_561_ = l_String_Slice_pos_x21(v_s_481_, v_basePos_535_);
lean_dec(v_basePos_535_);
v___x_562_ = lean_nat_sub(v_stackPos_524_, v_newNeedlePos_559_);
v_newBasePos_563_ = l_String_Slice_pos_x21(v_s_481_, v___x_562_);
lean_dec(v___x_562_);
v_res_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_564_, 0, v_oldBasePos_561_);
lean_ctor_set(v_res_564_, 1, v_newBasePos_563_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 3, v_newNeedlePos_559_);
v___x_566_ = v___x_527_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_needle_522_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_table_523_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_stackPos_524_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_newNeedlePos_559_);
v___x_566_ = v_reuseFailAlloc_569_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_res_564_);
v___x_568_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v_basePos_570_; lean_object* v_nextStackPos_571_; lean_object* v_res_572_; lean_object* v___x_574_; 
v_basePos_570_ = l_String_Slice_pos_x21(v_s_481_, v_basePos_535_);
lean_dec(v_basePos_535_);
v_nextStackPos_571_ = l_String_Slice_posGE___redArg(v_s_481_, v_stackPos_524_);
lean_inc(v_nextStackPos_571_);
v_res_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_572_, 0, v_basePos_570_);
lean_ctor_set(v_res_572_, 1, v_nextStackPos_571_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 3, v___x_555_);
lean_ctor_set(v___x_527_, 2, v_nextStackPos_571_);
v___x_574_ = v___x_527_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_needle_522_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_table_523_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_nextStackPos_571_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v___x_555_);
v___x_574_ = v_reuseFailAlloc_577_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_res_572_);
v___x_576_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_575_);
return v___x_576_;
}
}
}
else
{
lean_object* v_basePos_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_nextStackPos_581_; lean_object* v_res_582_; lean_object* v___x_584_; 
lean_dec(v_basePos_535_);
lean_dec(v_needlePos_525_);
v_basePos_578_ = l_String_Slice_pos_x21(v_s_481_, v_stackPos_524_);
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_stackPos_524_, v___x_579_);
lean_dec(v_stackPos_524_);
v_nextStackPos_581_ = l_String_Slice_posGE___redArg(v_s_481_, v___x_580_);
lean_inc(v_nextStackPos_581_);
v_res_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_582_, 0, v_basePos_578_);
lean_ctor_set(v_res_582_, 1, v_nextStackPos_581_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 3, v___x_555_);
lean_ctor_set(v___x_527_, 2, v_nextStackPos_581_);
v___x_584_ = v___x_527_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_needle_522_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_table_523_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_nextStackPos_581_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v___x_555_);
v___x_584_ = v_reuseFailAlloc_587_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v_res_582_);
v___x_586_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_585_);
return v___x_586_;
}
}
}
else
{
lean_object* v___x_588_; lean_object* v_nextStackPos_589_; lean_object* v_nextNeedlePos_590_; uint8_t v_decide_591_; 
lean_dec(v_basePos_535_);
v___x_588_ = lean_unsigned_to_nat(1u);
v_nextStackPos_589_ = lean_nat_add(v_stackPos_524_, v___x_588_);
lean_dec(v_stackPos_524_);
v_nextNeedlePos_590_ = lean_nat_add(v_needlePos_525_, v___x_588_);
lean_dec(v_needlePos_525_);
v_decide_591_ = lean_nat_dec_eq(v_nextNeedlePos_590_, v___x_536_);
lean_dec(v___x_536_);
if (v_decide_591_ == 0)
{
lean_object* v___x_593_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 3, v_nextNeedlePos_590_);
lean_ctor_set(v___x_527_, 2, v_nextStackPos_589_);
v___x_593_ = v___x_527_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_needle_522_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_table_523_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_nextStackPos_589_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v_nextNeedlePos_590_);
v___x_593_ = v_reuseFailAlloc_596_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
v___x_595_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_594_);
return v___x_595_;
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v_res_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_597_ = lean_nat_sub(v_nextStackPos_589_, v_nextNeedlePos_590_);
lean_dec(v_nextNeedlePos_590_);
v___x_598_ = l_String_Slice_pos_x21(v_s_481_, v___x_597_);
lean_dec(v___x_597_);
v___x_599_ = l_String_Slice_pos_x21(v_s_481_, v_nextStackPos_589_);
v_res_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_600_, 0, v___x_598_);
lean_ctor_set(v_res_600_, 1, v___x_599_);
v___x_601_ = lean_unsigned_to_nat(0u);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 3, v___x_601_);
lean_ctor_set(v___x_527_, 2, v_nextStackPos_589_);
v___x_603_ = v___x_527_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_needle_522_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_table_523_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_nextStackPos_589_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v___x_601_);
v___x_603_ = v_reuseFailAlloc_606_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v_res_600_);
v___x_605_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_604_);
return v___x_605_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_box(2);
v___x_609_ = lean_apply_4(v_lift_482_, lean_box(0), lean_box(0), v___f_487_, v___x_608_);
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed(lean_object* v___y_610_, lean_object* v_s_611_, lean_object* v_lift_612_, lean_object* v_it_613_, lean_object* v_acc_614_, lean_object* v_hP_615_, lean_object* v_recur_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(v___y_610_, v_s_611_, v_lift_612_, v_it_613_, v_acc_614_, v_hP_615_, v_recur_616_);
lean_dec_ref(v_s_611_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(lean_object* v_s_618_, lean_object* v_lift_619_, lean_object* v_00_u03b3_620_, lean_object* v_Pl_621_, lean_object* v_it_622_, lean_object* v_init_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___f_625_; lean_object* v___x_626_; 
v___f_625_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed), 7, 3);
lean_closure_set(v___f_625_, 0, v___y_624_);
lean_closure_set(v___f_625_, 1, v_s_618_);
lean_closure_set(v___f_625_, 2, v_lift_619_);
v___x_626_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_625_, v_it_622_, v_init_623_, lean_box(0));
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(lean_object* v_s_627_){
_start:
{
lean_object* v___f_628_; 
v___f_628_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2), 7, 1);
lean_closure_set(v___f_628_, 0, v_s_627_);
return v___f_628_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(lean_object* v_pat_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_630_, 0, v_pat_629_);
return v___x_630_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(lean_object* v_pat_631_, lean_object* v_s_632_){
_start:
{
lean_object* v_str_633_; lean_object* v_startInclusive_634_; lean_object* v_endExclusive_635_; lean_object* v_str_636_; lean_object* v_startInclusive_637_; lean_object* v_endExclusive_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_str_633_ = lean_ctor_get(v_pat_631_, 0);
v_startInclusive_634_ = lean_ctor_get(v_pat_631_, 1);
v_endExclusive_635_ = lean_ctor_get(v_pat_631_, 2);
v_str_636_ = lean_ctor_get(v_s_632_, 0);
v_startInclusive_637_ = lean_ctor_get(v_s_632_, 1);
v_endExclusive_638_ = lean_ctor_get(v_s_632_, 2);
v___x_639_ = lean_nat_sub(v_endExclusive_635_, v_startInclusive_634_);
v___x_640_ = lean_nat_sub(v_endExclusive_638_, v_startInclusive_637_);
v___x_641_ = lean_nat_dec_le(v___x_639_, v___x_640_);
lean_dec(v___x_640_);
if (v___x_641_ == 0)
{
lean_dec(v___x_639_);
return v___x_641_;
}
else
{
uint8_t v___x_642_; 
v___x_642_ = lean_string_memcmp(v_str_636_, v_str_633_, v_startInclusive_637_, v_startInclusive_634_, v___x_639_);
lean_dec(v___x_639_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(lean_object* v_pat_643_, lean_object* v_s_644_){
_start:
{
uint8_t v_res_645_; lean_object* v_r_646_; 
v_res_645_ = l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(v_pat_643_, v_s_644_);
lean_dec_ref(v_s_644_);
lean_dec_ref(v_pat_643_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(lean_object* v_pat_647_, lean_object* v_s_648_){
_start:
{
lean_object* v_str_649_; lean_object* v_startInclusive_650_; lean_object* v_endExclusive_651_; lean_object* v_str_652_; lean_object* v_startInclusive_653_; lean_object* v_endExclusive_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_str_649_ = lean_ctor_get(v_pat_647_, 0);
v_startInclusive_650_ = lean_ctor_get(v_pat_647_, 1);
v_endExclusive_651_ = lean_ctor_get(v_pat_647_, 2);
v_str_652_ = lean_ctor_get(v_s_648_, 0);
v_startInclusive_653_ = lean_ctor_get(v_s_648_, 1);
v_endExclusive_654_ = lean_ctor_get(v_s_648_, 2);
v___x_655_ = lean_nat_sub(v_endExclusive_651_, v_startInclusive_650_);
v___x_656_ = lean_nat_sub(v_endExclusive_654_, v_startInclusive_653_);
v___x_657_ = lean_nat_dec_le(v___x_655_, v___x_656_);
lean_dec(v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
return v___x_658_;
}
else
{
uint8_t v___x_659_; 
v___x_659_ = lean_string_memcmp(v_str_652_, v_str_649_, v_startInclusive_653_, v_startInclusive_650_, v___x_655_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec(v___x_655_);
v___x_660_ = lean_box(0);
return v___x_660_;
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = l_String_Slice_pos_x21(v_s_648_, v___x_655_);
lean_dec(v___x_655_);
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed(lean_object* v_pat_663_, lean_object* v_s_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(v_pat_663_, v_s_664_);
lean_dec_ref(v_s_664_);
lean_dec_ref(v_pat_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(lean_object* v_pat_666_, lean_object* v_s_667_, lean_object* v_x_668_){
_start:
{
lean_object* v_str_669_; lean_object* v_startInclusive_670_; lean_object* v_endExclusive_671_; lean_object* v_str_672_; lean_object* v_startInclusive_673_; lean_object* v_endExclusive_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_str_669_ = lean_ctor_get(v_pat_666_, 0);
v_startInclusive_670_ = lean_ctor_get(v_pat_666_, 1);
v_endExclusive_671_ = lean_ctor_get(v_pat_666_, 2);
v_str_672_ = lean_ctor_get(v_s_667_, 0);
v_startInclusive_673_ = lean_ctor_get(v_s_667_, 1);
v_endExclusive_674_ = lean_ctor_get(v_s_667_, 2);
v___x_675_ = lean_nat_sub(v_endExclusive_671_, v_startInclusive_670_);
v___x_676_ = lean_nat_sub(v_endExclusive_674_, v_startInclusive_673_);
v___x_677_ = lean_nat_dec_le(v___x_675_, v___x_676_);
lean_dec(v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; 
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
return v___x_678_;
}
else
{
uint8_t v___x_679_; 
v___x_679_ = lean_string_memcmp(v_str_672_, v_str_669_, v_startInclusive_673_, v_startInclusive_670_, v___x_675_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec(v___x_675_);
v___x_680_ = lean_box(0);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = l_String_Slice_pos_x21(v_s_667_, v___x_675_);
lean_dec(v___x_675_);
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(lean_object* v_pat_683_, lean_object* v_s_684_, lean_object* v_x_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(v_pat_683_, v_s_684_, v_x_685_);
lean_dec_ref(v_s_684_);
lean_dec_ref(v_pat_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(lean_object* v_pat_687_){
_start:
{
lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_inc_ref_n(v_pat_687_, 2);
v___f_688_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_688_, 0, v_pat_687_);
v___x_689_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_689_, 0, v_pat_687_);
v___x_690_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_690_, 0, v_pat_687_);
v___x_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___f_688_);
lean_ctor_set(v___x_691_, 2, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(lean_object* v_pat_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_string_utf8_byte_size(v_pat_692_);
v___x_695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_695_, 0, v_pat_692_);
lean_ctor_set(v___x_695_, 1, v___x_693_);
lean_ctor_set(v___x_695_, 2, v___x_694_);
v___x_696_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(lean_object* v___x_697_, lean_object* v_pat_698_, lean_object* v___x_699_, lean_object* v_s_700_, lean_object* v_x_701_){
_start:
{
lean_object* v_str_702_; lean_object* v_startInclusive_703_; lean_object* v_endExclusive_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_str_702_ = lean_ctor_get(v_s_700_, 0);
v_startInclusive_703_ = lean_ctor_get(v_s_700_, 1);
v_endExclusive_704_ = lean_ctor_get(v_s_700_, 2);
v___x_705_ = lean_nat_sub(v_endExclusive_704_, v_startInclusive_703_);
v___x_706_ = lean_nat_dec_le(v___x_697_, v___x_705_);
lean_dec(v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_box(0);
return v___x_707_;
}
else
{
uint8_t v___x_708_; 
v___x_708_ = lean_string_memcmp(v_str_702_, v_pat_698_, v_startInclusive_703_, v___x_699_, v___x_697_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_box(0);
return v___x_709_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = l_String_Slice_pos_x21(v_s_700_, v___x_697_);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(lean_object* v___x_712_, lean_object* v_pat_713_, lean_object* v___x_714_, lean_object* v_s_715_, lean_object* v_x_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(v___x_712_, v_pat_713_, v___x_714_, v_s_715_, v_x_716_);
lean_dec_ref(v_s_715_);
lean_dec(v___x_714_);
lean_dec_ref(v_pat_713_);
lean_dec(v___x_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(lean_object* v_pat_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___f_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_string_utf8_byte_size(v_pat_718_);
lean_inc_ref(v_pat_718_);
v___f_721_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_721_, 0, v___x_720_);
lean_closure_set(v___f_721_, 1, v_pat_718_);
lean_closure_set(v___f_721_, 2, v___x_719_);
v___x_722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_722_, 0, v_pat_718_);
lean_ctor_set(v___x_722_, 1, v___x_719_);
lean_ctor_set(v___x_722_, 2, v___x_720_);
lean_inc_ref(v___x_722_);
v___x_723_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_723_, 0, v___x_722_);
v___x_724_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_724_, 0, v___x_722_);
v___x_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___f_721_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(lean_object* v_pat_726_, lean_object* v_s_727_){
_start:
{
lean_object* v_str_728_; lean_object* v_startInclusive_729_; lean_object* v_endExclusive_730_; lean_object* v_str_731_; lean_object* v_startInclusive_732_; lean_object* v_endExclusive_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_str_728_ = lean_ctor_get(v_pat_726_, 0);
v_startInclusive_729_ = lean_ctor_get(v_pat_726_, 1);
v_endExclusive_730_ = lean_ctor_get(v_pat_726_, 2);
v_str_731_ = lean_ctor_get(v_s_727_, 0);
v_startInclusive_732_ = lean_ctor_get(v_s_727_, 1);
v_endExclusive_733_ = lean_ctor_get(v_s_727_, 2);
v___x_734_ = lean_nat_sub(v_endExclusive_730_, v_startInclusive_729_);
v___x_735_ = lean_nat_sub(v_endExclusive_733_, v_startInclusive_732_);
v___x_736_ = lean_nat_dec_le(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v___x_735_);
lean_dec(v___x_734_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_nat_sub(v___x_735_, v___x_734_);
lean_dec(v___x_735_);
v___x_738_ = lean_nat_add(v_startInclusive_732_, v___x_737_);
lean_dec(v___x_737_);
v___x_739_ = lean_string_memcmp(v_str_731_, v_str_728_, v___x_738_, v_startInclusive_729_, v___x_734_);
lean_dec(v___x_734_);
lean_dec(v___x_738_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(lean_object* v_pat_740_, lean_object* v_s_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(v_pat_740_, v_s_741_);
lean_dec_ref(v_s_741_);
lean_dec_ref(v_pat_740_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(lean_object* v_pat_744_, lean_object* v_s_745_){
_start:
{
lean_object* v_str_746_; lean_object* v_startInclusive_747_; lean_object* v_endExclusive_748_; lean_object* v_str_749_; lean_object* v_startInclusive_750_; lean_object* v_endExclusive_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_str_746_ = lean_ctor_get(v_pat_744_, 0);
v_startInclusive_747_ = lean_ctor_get(v_pat_744_, 1);
v_endExclusive_748_ = lean_ctor_get(v_pat_744_, 2);
v_str_749_ = lean_ctor_get(v_s_745_, 0);
v_startInclusive_750_ = lean_ctor_get(v_s_745_, 1);
v_endExclusive_751_ = lean_ctor_get(v_s_745_, 2);
v___x_752_ = lean_nat_sub(v_endExclusive_748_, v_startInclusive_747_);
v___x_753_ = lean_nat_sub(v_endExclusive_751_, v_startInclusive_750_);
v___x_754_ = lean_nat_dec_le(v___x_752_, v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_dec(v___x_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
return v___x_755_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_756_ = lean_nat_sub(v___x_753_, v___x_752_);
lean_dec(v___x_753_);
v___x_757_ = lean_nat_add(v_startInclusive_750_, v___x_756_);
v___x_758_ = lean_string_memcmp(v_str_749_, v_str_746_, v___x_757_, v_startInclusive_747_, v___x_752_);
lean_dec(v___x_752_);
lean_dec(v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = l_String_Slice_pos_x21(v_s_745_, v___x_756_);
lean_dec(v___x_756_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed(lean_object* v_pat_762_, lean_object* v_s_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(v_pat_762_, v_s_763_);
lean_dec_ref(v_s_763_);
lean_dec_ref(v_pat_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(lean_object* v_pat_765_, lean_object* v_s_766_, lean_object* v_x_767_){
_start:
{
lean_object* v_str_768_; lean_object* v_startInclusive_769_; lean_object* v_endExclusive_770_; lean_object* v_str_771_; lean_object* v_startInclusive_772_; lean_object* v_endExclusive_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_str_768_ = lean_ctor_get(v_pat_765_, 0);
v_startInclusive_769_ = lean_ctor_get(v_pat_765_, 1);
v_endExclusive_770_ = lean_ctor_get(v_pat_765_, 2);
v_str_771_ = lean_ctor_get(v_s_766_, 0);
v_startInclusive_772_ = lean_ctor_get(v_s_766_, 1);
v_endExclusive_773_ = lean_ctor_get(v_s_766_, 2);
v___x_774_ = lean_nat_sub(v_endExclusive_770_, v_startInclusive_769_);
v___x_775_ = lean_nat_sub(v_endExclusive_773_, v_startInclusive_772_);
v___x_776_ = lean_nat_dec_le(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
lean_dec(v___x_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
return v___x_777_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_nat_sub(v___x_775_, v___x_774_);
lean_dec(v___x_775_);
v___x_779_ = lean_nat_add(v_startInclusive_772_, v___x_778_);
v___x_780_ = lean_string_memcmp(v_str_771_, v_str_768_, v___x_779_, v_startInclusive_769_, v___x_774_);
lean_dec(v___x_774_);
lean_dec(v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
return v___x_781_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = l_String_Slice_pos_x21(v_s_766_, v___x_778_);
lean_dec(v___x_778_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(lean_object* v_pat_784_, lean_object* v_s_785_, lean_object* v_x_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(v_pat_784_, v_s_785_, v_x_786_);
lean_dec_ref(v_s_785_);
lean_dec_ref(v_pat_784_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(lean_object* v_pat_788_){
_start:
{
lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_inc_ref_n(v_pat_788_, 2);
v___f_789_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_789_, 0, v_pat_788_);
v___x_790_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_790_, 0, v_pat_788_);
v___x_791_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_791_, 0, v_pat_788_);
v___x_792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___f_789_);
lean_ctor_set(v___x_792_, 2, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(lean_object* v___x_793_, lean_object* v_pat_794_, lean_object* v___x_795_, lean_object* v_s_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_str_798_; lean_object* v_startInclusive_799_; lean_object* v_endExclusive_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_str_798_ = lean_ctor_get(v_s_796_, 0);
v_startInclusive_799_ = lean_ctor_get(v_s_796_, 1);
v_endExclusive_800_ = lean_ctor_get(v_s_796_, 2);
v___x_801_ = lean_nat_sub(v_endExclusive_800_, v_startInclusive_799_);
v___x_802_ = lean_nat_dec_le(v___x_793_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
lean_dec(v___x_801_);
v___x_803_ = lean_box(0);
return v___x_803_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_804_ = lean_nat_sub(v___x_801_, v___x_793_);
lean_dec(v___x_801_);
v___x_805_ = lean_nat_add(v_startInclusive_799_, v___x_804_);
v___x_806_ = lean_string_memcmp(v_str_798_, v_pat_794_, v___x_805_, v___x_795_, v___x_793_);
lean_dec(v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
return v___x_807_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = l_String_Slice_pos_x21(v_s_796_, v___x_804_);
lean_dec(v___x_804_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(lean_object* v___x_810_, lean_object* v_pat_811_, lean_object* v___x_812_, lean_object* v_s_813_, lean_object* v_x_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(v___x_810_, v_pat_811_, v___x_812_, v_s_813_, v_x_814_);
lean_dec_ref(v_s_813_);
lean_dec(v___x_812_);
lean_dec_ref(v_pat_811_);
lean_dec(v___x_810_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(lean_object* v_pat_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___f_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_string_utf8_byte_size(v_pat_816_);
lean_inc_ref(v_pat_816_);
v___f_819_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_819_, 0, v___x_818_);
lean_closure_set(v___f_819_, 1, v_pat_816_);
lean_closure_set(v___f_819_, 2, v___x_817_);
v___x_820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_820_, 0, v_pat_816_);
lean_ctor_set(v___x_820_, 1, v___x_817_);
lean_ctor_set(v___x_820_, 2, v___x_818_);
lean_inc_ref(v___x_820_);
v___x_821_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_821_, 0, v___x_820_);
v___x_822_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_822_, 0, v___x_820_);
v___x_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___f_819_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
return v___x_823_;
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
