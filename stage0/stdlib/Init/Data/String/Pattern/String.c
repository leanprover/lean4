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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___redArg(lean_object* v_x_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_tag_nat(v_x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___redArg___boxed(lean_object* v_x_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___redArg(v_x_88_);
lean_dec(v_x_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl(lean_object* v_s_90_, lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_tag_nat(v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___boxed(lean_object* v_s_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl(v_s_93_, v_x_94_);
lean_dec(v_x_94_);
lean_dec_ref(v_s_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(lean_object* v_t_96_, lean_object* v_k_97_){
_start:
{
switch(lean_obj_tag(v_t_96_))
{
case 0:
{
lean_object* v_pos_98_; lean_object* v___x_99_; 
v_pos_98_ = lean_ctor_get(v_t_96_, 0);
lean_inc(v_pos_98_);
lean_dec_ref_known(v_t_96_, 1);
v___x_99_ = lean_apply_1(v_k_97_, v_pos_98_);
return v___x_99_;
}
case 1:
{
lean_object* v_pos_100_; lean_object* v___x_101_; 
v_pos_100_ = lean_ctor_get(v_t_96_, 0);
lean_inc(v_pos_100_);
lean_dec_ref_known(v_t_96_, 1);
v___x_101_ = lean_apply_2(v_k_97_, v_pos_100_, lean_box(0));
return v___x_101_;
}
case 2:
{
lean_object* v_needle_102_; lean_object* v_table_103_; lean_object* v_stackPos_104_; lean_object* v_needlePos_105_; lean_object* v___x_106_; 
v_needle_102_ = lean_ctor_get(v_t_96_, 0);
lean_inc_ref(v_needle_102_);
v_table_103_ = lean_ctor_get(v_t_96_, 1);
lean_inc_ref(v_table_103_);
v_stackPos_104_ = lean_ctor_get(v_t_96_, 2);
lean_inc(v_stackPos_104_);
v_needlePos_105_ = lean_ctor_get(v_t_96_, 3);
lean_inc(v_needlePos_105_);
lean_dec_ref_known(v_t_96_, 4);
v___x_106_ = lean_apply_6(v_k_97_, v_needle_102_, v_table_103_, lean_box(0), v_stackPos_104_, v_needlePos_105_, lean_box(0));
return v___x_106_;
}
default: 
{
return v_k_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(lean_object* v_s_107_, lean_object* v_motive_108_, lean_object* v_ctorIdx_109_, lean_object* v_t_110_, lean_object* v_h_111_, lean_object* v_k_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_110_, v_k_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___boxed(lean_object* v_s_114_, lean_object* v_motive_115_, lean_object* v_ctorIdx_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_k_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(v_s_114_, v_motive_115_, v_ctorIdx_116_, v_t_117_, v_h_118_, v_k_119_);
lean_dec(v_ctorIdx_116_);
lean_dec_ref(v_s_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___redArg(lean_object* v_t_121_, lean_object* v_emptyBefore_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_121_, v_emptyBefore_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(lean_object* v_s_124_, lean_object* v_motive_125_, lean_object* v_t_126_, lean_object* v_h_127_, lean_object* v_emptyBefore_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_126_, v_emptyBefore_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___boxed(lean_object* v_s_130_, lean_object* v_motive_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_emptyBefore_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(v_s_130_, v_motive_131_, v_t_132_, v_h_133_, v_emptyBefore_134_);
lean_dec_ref(v_s_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___redArg(lean_object* v_t_136_, lean_object* v_emptyAt_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_136_, v_emptyAt_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(lean_object* v_s_139_, lean_object* v_motive_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_emptyAt_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_141_, v_emptyAt_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___boxed(lean_object* v_s_145_, lean_object* v_motive_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_emptyAt_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(v_s_145_, v_motive_146_, v_t_147_, v_h_148_, v_emptyAt_149_);
lean_dec_ref(v_s_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___redArg(lean_object* v_t_151_, lean_object* v_proper_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_151_, v_proper_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(lean_object* v_s_154_, lean_object* v_motive_155_, lean_object* v_t_156_, lean_object* v_h_157_, lean_object* v_proper_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_156_, v_proper_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___boxed(lean_object* v_s_160_, lean_object* v_motive_161_, lean_object* v_t_162_, lean_object* v_h_163_, lean_object* v_proper_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(v_s_160_, v_motive_161_, v_t_162_, v_h_163_, v_proper_164_);
lean_dec_ref(v_s_160_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___redArg(lean_object* v_t_166_, lean_object* v_atEnd_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_166_, v_atEnd_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(lean_object* v_s_169_, lean_object* v_motive_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_atEnd_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_171_, v_atEnd_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___boxed(lean_object* v_s_175_, lean_object* v_motive_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_atEnd_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(v_s_175_, v_motive_176_, v_t_177_, v_h_178_, v_atEnd_179_);
lean_dec_ref(v_s_175_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg(){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0));
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___boxed(lean_object* v___dummy_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg();
return v_res_186_;
}
}
static lean_object* _init_l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0(void){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg();
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(lean_object* v_s_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0, &l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_once, _init_l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___boxed(lean_object* v_s_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(v_s_190_);
lean_dec_ref(v_s_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg(){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0, &l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_once, _init_l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg___boxed(lean_object* v___dummy_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg();
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(lean_object* v_a_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_obj_once(&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0, &l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_once, _init_l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___boxed(lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(v_a_198_);
lean_dec_ref(v_a_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___redArg(lean_object* v_pat_200_){
_start:
{
lean_object* v_startInclusive_201_; lean_object* v_endExclusive_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_startInclusive_201_ = lean_ctor_get(v_pat_200_, 1);
v_endExclusive_202_ = lean_ctor_get(v_pat_200_, 2);
v___x_203_ = lean_nat_sub(v_endExclusive_202_, v_startInclusive_201_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_nat_dec_eq(v___x_203_, v___x_204_);
lean_dec(v___x_203_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_200_);
v___x_207_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_207_, 0, v_pat_200_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_ctor_set(v___x_207_, 2, v___x_204_);
lean_ctor_set(v___x_207_, 3, v___x_204_);
return v___x_207_;
}
else
{
lean_object* v___x_208_; 
lean_dec_ref(v_pat_200_);
v___x_208_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0));
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter(lean_object* v_pat_209_, lean_object* v_s_210_){
_start:
{
lean_object* v_startInclusive_211_; lean_object* v_endExclusive_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_startInclusive_211_ = lean_ctor_get(v_pat_209_, 1);
v_endExclusive_212_ = lean_ctor_get(v_pat_209_, 2);
v___x_213_ = lean_nat_sub(v_endExclusive_212_, v_startInclusive_211_);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_nat_dec_eq(v___x_213_, v___x_214_);
lean_dec(v___x_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_209_);
v___x_217_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_217_, 0, v_pat_209_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
lean_ctor_set(v___x_217_, 2, v___x_214_);
lean_ctor_set(v___x_217_, 3, v___x_214_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; 
lean_dec_ref(v_pat_209_);
v___x_218_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0));
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed(lean_object* v_pat_219_, lean_object* v_s_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_String_Slice_Pattern_ForwardSliceSearcher_iter(v_pat_219_, v_s_220_);
lean_dec_ref(v_s_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(lean_object* v_s_222_, lean_object* v_x_223_){
_start:
{
switch(lean_obj_tag(v_x_223_))
{
case 0:
{
lean_object* v_pos_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_239_; 
v_pos_224_ = lean_ctor_get(v_x_223_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_239_ == 0)
{
v___x_226_ = v_x_223_;
v_isShared_227_ = v_isSharedCheck_239_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_pos_224_);
lean_dec(v_x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_239_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_res_228_; lean_object* v_startInclusive_229_; lean_object* v_endExclusive_230_; lean_object* v___x_231_; uint8_t v_decide_232_; 
lean_inc_n(v_pos_224_, 2);
v_res_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_228_, 0, v_pos_224_);
lean_ctor_set(v_res_228_, 1, v_pos_224_);
v_startInclusive_229_ = lean_ctor_get(v_s_222_, 1);
v_endExclusive_230_ = lean_ctor_get(v_s_222_, 2);
v___x_231_ = lean_nat_sub(v_endExclusive_230_, v_startInclusive_229_);
v_decide_232_ = lean_nat_dec_eq(v_pos_224_, v___x_231_);
lean_dec(v___x_231_);
if (v_decide_232_ == 0)
{
lean_object* v___x_234_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 1);
v___x_234_ = v___x_226_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_pos_224_);
v___x_234_ = v_reuseFailAlloc_236_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_res_228_);
return v___x_235_;
}
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_del_object(v___x_226_);
lean_dec(v_pos_224_);
v___x_237_ = lean_box(3);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_res_228_);
return v___x_238_;
}
}
}
case 1:
{
lean_object* v_pos_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_254_; 
v_pos_240_ = lean_ctor_get(v_x_223_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_254_ == 0)
{
v___x_242_ = v_x_223_;
v_isShared_243_ = v_isSharedCheck_254_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_pos_240_);
lean_dec(v_x_223_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_254_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_str_244_; lean_object* v_startInclusive_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_res_249_; lean_object* v___x_251_; 
v_str_244_ = lean_ctor_get(v_s_222_, 0);
v_startInclusive_245_ = lean_ctor_get(v_s_222_, 1);
v___x_246_ = lean_nat_add(v_startInclusive_245_, v_pos_240_);
v___x_247_ = lean_string_utf8_next_fast(v_str_244_, v___x_246_);
lean_dec(v___x_246_);
v___x_248_ = lean_nat_sub(v___x_247_, v_startInclusive_245_);
lean_inc(v___x_248_);
v_res_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_249_, 0, v_pos_240_);
lean_ctor_set(v_res_249_, 1, v___x_248_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
lean_ctor_set(v___x_242_, 0, v___x_248_);
v___x_251_ = v___x_242_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_248_);
v___x_251_ = v_reuseFailAlloc_253_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v_res_249_);
return v___x_252_;
}
}
}
case 2:
{
lean_object* v_needle_255_; lean_object* v_table_256_; lean_object* v_stackPos_257_; lean_object* v_needlePos_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_333_; 
v_needle_255_ = lean_ctor_get(v_x_223_, 0);
v_table_256_ = lean_ctor_get(v_x_223_, 1);
v_stackPos_257_ = lean_ctor_get(v_x_223_, 2);
v_needlePos_258_ = lean_ctor_get(v_x_223_, 3);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_333_ == 0)
{
v___x_260_ = v_x_223_;
v_isShared_261_ = v_isSharedCheck_333_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_needlePos_258_);
lean_inc(v_stackPos_257_);
lean_inc(v_table_256_);
lean_inc(v_needle_255_);
lean_dec(v_x_223_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_333_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v_str_262_; lean_object* v_startInclusive_263_; lean_object* v_endExclusive_264_; lean_object* v_str_265_; lean_object* v_startInclusive_266_; lean_object* v_endExclusive_267_; lean_object* v_basePos_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_str_262_ = lean_ctor_get(v_needle_255_, 0);
v_startInclusive_263_ = lean_ctor_get(v_needle_255_, 1);
v_endExclusive_264_ = lean_ctor_get(v_needle_255_, 2);
v_str_265_ = lean_ctor_get(v_s_222_, 0);
v_startInclusive_266_ = lean_ctor_get(v_s_222_, 1);
v_endExclusive_267_ = lean_ctor_get(v_s_222_, 2);
v_basePos_268_ = lean_nat_sub(v_stackPos_257_, v_needlePos_258_);
v___x_269_ = lean_nat_sub(v_endExclusive_264_, v_startInclusive_263_);
v___x_270_ = lean_nat_add(v_basePos_268_, v___x_269_);
v___x_271_ = lean_nat_sub(v_endExclusive_267_, v_startInclusive_266_);
v___x_272_ = lean_nat_dec_le(v___x_270_, v___x_271_);
lean_dec(v___x_270_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
lean_dec(v___x_269_);
lean_del_object(v___x_260_);
lean_dec(v_needlePos_258_);
lean_dec(v_stackPos_257_);
lean_dec_ref(v_table_256_);
lean_dec_ref(v_needle_255_);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_add(v_basePos_268_, v___x_273_);
v___x_275_ = lean_nat_dec_le(v___x_274_, v___x_271_);
lean_dec(v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec(v___x_271_);
lean_dec(v_basePos_268_);
v___x_276_ = lean_box(2);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v_res_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = l_String_Slice_pos_x21(v_s_222_, v_basePos_268_);
lean_dec(v_basePos_268_);
v_res_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_278_, 0, v___x_277_);
lean_ctor_set(v_res_278_, 1, v___x_271_);
v___x_279_ = lean_box(3);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v_res_278_);
return v___x_280_;
}
}
else
{
lean_object* v___x_281_; uint8_t v_stackByte_282_; lean_object* v___x_283_; uint8_t v_patByte_284_; uint8_t v___x_285_; 
lean_dec(v___x_271_);
v___x_281_ = lean_nat_add(v_startInclusive_266_, v_stackPos_257_);
v_stackByte_282_ = lean_string_get_byte_fast(v_str_265_, v___x_281_);
v___x_283_ = lean_nat_add(v_startInclusive_263_, v_needlePos_258_);
v_patByte_284_ = lean_string_get_byte_fast(v_str_262_, v___x_283_);
v___x_285_ = lean_uint8_dec_eq(v_stackByte_282_, v_patByte_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; uint8_t v_decide_287_; 
lean_dec(v___x_269_);
v___x_286_ = lean_unsigned_to_nat(0u);
v_decide_287_ = lean_nat_dec_eq(v_needlePos_258_, v___x_286_);
if (v_decide_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_newNeedlePos_290_; uint8_t v___x_291_; 
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_sub(v_needlePos_258_, v___x_288_);
lean_dec(v_needlePos_258_);
v_newNeedlePos_290_ = lean_array_fget_borrowed(v_table_256_, v___x_289_);
lean_dec(v___x_289_);
v___x_291_ = lean_nat_dec_eq(v_newNeedlePos_290_, v___x_286_);
if (v___x_291_ == 0)
{
lean_object* v_oldBasePos_292_; lean_object* v___x_293_; lean_object* v_newBasePos_294_; lean_object* v_res_295_; lean_object* v___x_297_; 
lean_inc(v_newNeedlePos_290_);
v_oldBasePos_292_ = l_String_Slice_pos_x21(v_s_222_, v_basePos_268_);
lean_dec(v_basePos_268_);
v___x_293_ = lean_nat_sub(v_stackPos_257_, v_newNeedlePos_290_);
v_newBasePos_294_ = l_String_Slice_pos_x21(v_s_222_, v___x_293_);
lean_dec(v___x_293_);
v_res_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_295_, 0, v_oldBasePos_292_);
lean_ctor_set(v_res_295_, 1, v_newBasePos_294_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 3, v_newNeedlePos_290_);
v___x_297_ = v___x_260_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_needle_255_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_table_256_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_stackPos_257_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v_newNeedlePos_290_);
v___x_297_ = v_reuseFailAlloc_299_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; 
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_res_295_);
return v___x_298_;
}
}
else
{
lean_object* v_basePos_300_; lean_object* v_nextStackPos_301_; lean_object* v_res_302_; lean_object* v___x_304_; 
v_basePos_300_ = l_String_Slice_pos_x21(v_s_222_, v_basePos_268_);
lean_dec(v_basePos_268_);
v_nextStackPos_301_ = l_String_Slice_posGE___redArg(v_s_222_, v_stackPos_257_);
lean_inc(v_nextStackPos_301_);
v_res_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_302_, 0, v_basePos_300_);
lean_ctor_set(v_res_302_, 1, v_nextStackPos_301_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 3, v___x_286_);
lean_ctor_set(v___x_260_, 2, v_nextStackPos_301_);
v___x_304_ = v___x_260_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_needle_255_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_table_256_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_nextStackPos_301_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v___x_286_);
v___x_304_ = v_reuseFailAlloc_306_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_res_302_);
return v___x_305_;
}
}
}
else
{
lean_object* v_basePos_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_nextStackPos_310_; lean_object* v_res_311_; lean_object* v___x_313_; 
lean_dec(v_basePos_268_);
lean_dec(v_needlePos_258_);
v_basePos_307_ = l_String_Slice_pos_x21(v_s_222_, v_stackPos_257_);
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_stackPos_257_, v___x_308_);
lean_dec(v_stackPos_257_);
v_nextStackPos_310_ = l_String_Slice_posGE___redArg(v_s_222_, v___x_309_);
lean_inc(v_nextStackPos_310_);
v_res_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_311_, 0, v_basePos_307_);
lean_ctor_set(v_res_311_, 1, v_nextStackPos_310_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 3, v___x_286_);
lean_ctor_set(v___x_260_, 2, v_nextStackPos_310_);
v___x_313_ = v___x_260_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_needle_255_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_table_256_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_nextStackPos_310_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v___x_286_);
v___x_313_ = v_reuseFailAlloc_315_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; 
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_res_311_);
return v___x_314_;
}
}
}
else
{
lean_object* v___x_316_; lean_object* v_nextStackPos_317_; lean_object* v_nextNeedlePos_318_; uint8_t v_decide_319_; 
lean_dec(v_basePos_268_);
v___x_316_ = lean_unsigned_to_nat(1u);
v_nextStackPos_317_ = lean_nat_add(v_stackPos_257_, v___x_316_);
lean_dec(v_stackPos_257_);
v_nextNeedlePos_318_ = lean_nat_add(v_needlePos_258_, v___x_316_);
lean_dec(v_needlePos_258_);
v_decide_319_ = lean_nat_dec_eq(v_nextNeedlePos_318_, v___x_269_);
lean_dec(v___x_269_);
if (v_decide_319_ == 0)
{
lean_object* v___x_321_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 3, v_nextNeedlePos_318_);
lean_ctor_set(v___x_260_, 2, v_nextStackPos_317_);
v___x_321_ = v___x_260_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_needle_255_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_table_256_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_nextStackPos_317_);
lean_ctor_set(v_reuseFailAlloc_323_, 3, v_nextNeedlePos_318_);
v___x_321_ = v_reuseFailAlloc_323_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; 
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_res_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_324_ = lean_nat_sub(v_nextStackPos_317_, v_nextNeedlePos_318_);
lean_dec(v_nextNeedlePos_318_);
v___x_325_ = l_String_Slice_pos_x21(v_s_222_, v___x_324_);
lean_dec(v___x_324_);
v___x_326_ = l_String_Slice_pos_x21(v_s_222_, v_nextStackPos_317_);
v_res_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_327_, 0, v___x_325_);
lean_ctor_set(v_res_327_, 1, v___x_326_);
v___x_328_ = lean_unsigned_to_nat(0u);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 3, v___x_328_);
lean_ctor_set(v___x_260_, 2, v_nextStackPos_317_);
v___x_330_ = v___x_260_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_needle_255_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_table_256_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_nextStackPos_317_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v___x_328_);
v___x_330_ = v_reuseFailAlloc_332_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_res_327_);
return v___x_331_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_334_; 
v___x_334_ = lean_box(2);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed(lean_object* v_s_335_, lean_object* v_x_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(v_s_335_, v_x_336_);
lean_dec_ref(v_s_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep(lean_object* v_s_338_){
_start:
{
lean_object* v___f_339_; 
v___f_339_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed), 2, 1);
lean_closure_set(v___f_339_, 0, v_s_338_);
return v___f_339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(lean_object* v_s_340_, lean_object* v_x_341_){
_start:
{
switch(lean_obj_tag(v_x_341_))
{
case 0:
{
lean_object* v_pos_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_352_; 
v_pos_342_ = lean_ctor_get(v_x_341_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_352_ == 0)
{
v___x_344_ = v_x_341_;
v_isShared_345_ = v_isSharedCheck_352_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_pos_342_);
lean_dec(v_x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_352_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_346_ = l_String_Slice_Pos_remainingBytes(v_s_340_, v_pos_342_);
lean_dec(v_pos_342_);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 1);
lean_ctor_set(v___x_344_, 0, v___x_348_);
v___x_350_ = v___x_344_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
case 1:
{
lean_object* v_pos_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_363_; 
v_pos_353_ = lean_ctor_get(v_x_341_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_363_ == 0)
{
v___x_355_ = v_x_341_;
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_pos_353_);
lean_dec(v_x_341_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_357_ = l_String_Slice_Pos_remainingBytes(v_s_340_, v_pos_353_);
lean_dec(v_pos_353_);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_359_);
v___x_361_ = v___x_355_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
case 2:
{
lean_object* v_stackPos_364_; lean_object* v_needlePos_365_; lean_object* v_startInclusive_366_; lean_object* v_endExclusive_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_stackPos_364_ = lean_ctor_get(v_x_341_, 2);
lean_inc(v_stackPos_364_);
v_needlePos_365_ = lean_ctor_get(v_x_341_, 3);
lean_inc(v_needlePos_365_);
lean_dec_ref_known(v_x_341_, 4);
v_startInclusive_366_ = lean_ctor_get(v_s_340_, 1);
v_endExclusive_367_ = lean_ctor_get(v_s_340_, 2);
v___x_368_ = lean_nat_sub(v_endExclusive_367_, v_startInclusive_366_);
v___x_369_ = lean_nat_sub(v___x_368_, v_stackPos_364_);
lean_dec(v_stackPos_364_);
lean_dec(v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_needlePos_365_);
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
default: 
{
lean_object* v___x_372_; 
v___x_372_ = lean_box(0);
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption___boxed(lean_object* v_s_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(v_s_373_, v_x_374_);
lean_dec_ref(v_s_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg();
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(lean_object* v_s_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(lean_object* v_s_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(v_s_382_);
lean_dec_ref(v_s_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(lean_object* v_x_384_, lean_object* v_h__1_385_, lean_object* v_h__2_386_, lean_object* v_h__3_387_, lean_object* v_h__4_388_){
_start:
{
switch(lean_obj_tag(v_x_384_))
{
case 0:
{
lean_object* v_pos_389_; lean_object* v___x_390_; 
lean_dec(v_h__4_388_);
lean_dec(v_h__3_387_);
lean_dec(v_h__2_386_);
v_pos_389_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_pos_389_);
lean_dec_ref_known(v_x_384_, 1);
v___x_390_ = lean_apply_1(v_h__1_385_, v_pos_389_);
return v___x_390_;
}
case 1:
{
lean_object* v_pos_391_; lean_object* v___x_392_; 
lean_dec(v_h__4_388_);
lean_dec(v_h__3_387_);
lean_dec(v_h__1_385_);
v_pos_391_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_pos_391_);
lean_dec_ref_known(v_x_384_, 1);
v___x_392_ = lean_apply_2(v_h__2_386_, v_pos_391_, lean_box(0));
return v___x_392_;
}
case 2:
{
lean_object* v_needle_393_; lean_object* v_table_394_; lean_object* v_stackPos_395_; lean_object* v_needlePos_396_; lean_object* v___x_397_; 
lean_dec(v_h__4_388_);
lean_dec(v_h__2_386_);
lean_dec(v_h__1_385_);
v_needle_393_ = lean_ctor_get(v_x_384_, 0);
lean_inc_ref(v_needle_393_);
v_table_394_ = lean_ctor_get(v_x_384_, 1);
lean_inc_ref(v_table_394_);
v_stackPos_395_ = lean_ctor_get(v_x_384_, 2);
lean_inc(v_stackPos_395_);
v_needlePos_396_ = lean_ctor_get(v_x_384_, 3);
lean_inc(v_needlePos_396_);
lean_dec_ref_known(v_x_384_, 4);
v___x_397_ = lean_apply_6(v_h__3_387_, v_needle_393_, v_table_394_, lean_box(0), v_stackPos_395_, v_needlePos_396_, lean_box(0));
return v___x_397_;
}
default: 
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v_h__3_387_);
lean_dec(v_h__2_386_);
lean_dec(v_h__1_385_);
v___x_398_ = lean_box(0);
v___x_399_ = lean_apply_1(v_h__4_388_, v___x_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(lean_object* v_s_400_, lean_object* v_motive_401_, lean_object* v_x_402_, lean_object* v_h__1_403_, lean_object* v_h__2_404_, lean_object* v_h__3_405_, lean_object* v_h__4_406_){
_start:
{
switch(lean_obj_tag(v_x_402_))
{
case 0:
{
lean_object* v_pos_407_; lean_object* v___x_408_; 
lean_dec(v_h__4_406_);
lean_dec(v_h__3_405_);
lean_dec(v_h__2_404_);
v_pos_407_ = lean_ctor_get(v_x_402_, 0);
lean_inc(v_pos_407_);
lean_dec_ref_known(v_x_402_, 1);
v___x_408_ = lean_apply_1(v_h__1_403_, v_pos_407_);
return v___x_408_;
}
case 1:
{
lean_object* v_pos_409_; lean_object* v___x_410_; 
lean_dec(v_h__4_406_);
lean_dec(v_h__3_405_);
lean_dec(v_h__1_403_);
v_pos_409_ = lean_ctor_get(v_x_402_, 0);
lean_inc(v_pos_409_);
lean_dec_ref_known(v_x_402_, 1);
v___x_410_ = lean_apply_2(v_h__2_404_, v_pos_409_, lean_box(0));
return v___x_410_;
}
case 2:
{
lean_object* v_needle_411_; lean_object* v_table_412_; lean_object* v_stackPos_413_; lean_object* v_needlePos_414_; lean_object* v___x_415_; 
lean_dec(v_h__4_406_);
lean_dec(v_h__2_404_);
lean_dec(v_h__1_403_);
v_needle_411_ = lean_ctor_get(v_x_402_, 0);
lean_inc_ref(v_needle_411_);
v_table_412_ = lean_ctor_get(v_x_402_, 1);
lean_inc_ref(v_table_412_);
v_stackPos_413_ = lean_ctor_get(v_x_402_, 2);
lean_inc(v_stackPos_413_);
v_needlePos_414_ = lean_ctor_get(v_x_402_, 3);
lean_inc(v_needlePos_414_);
lean_dec_ref_known(v_x_402_, 4);
v___x_415_ = lean_apply_6(v_h__3_405_, v_needle_411_, v_table_412_, lean_box(0), v_stackPos_413_, v_needlePos_414_, lean_box(0));
return v___x_415_;
}
default: 
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec(v_h__3_405_);
lean_dec(v_h__2_404_);
lean_dec(v_h__1_403_);
v___x_416_ = lean_box(0);
v___x_417_ = lean_apply_1(v_h__4_406_, v___x_416_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(lean_object* v_s_418_, lean_object* v_motive_419_, lean_object* v_x_420_, lean_object* v_h__1_421_, lean_object* v_h__2_422_, lean_object* v_h__3_423_, lean_object* v_h__4_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(v_s_418_, v_motive_419_, v_x_420_, v_h__1_421_, v_h__2_422_, v_h__3_423_, v_h__4_424_);
lean_dec_ref(v_s_418_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___redArg(lean_object* v_x_426_, lean_object* v_h__1_427_, lean_object* v_h__2_428_, lean_object* v_h__3_429_){
_start:
{
switch(lean_obj_tag(v_x_426_))
{
case 0:
{
lean_object* v_it_430_; lean_object* v_out_431_; lean_object* v___x_432_; 
lean_dec(v_h__3_429_);
lean_dec(v_h__2_428_);
v_it_430_ = lean_ctor_get(v_x_426_, 0);
lean_inc(v_it_430_);
v_out_431_ = lean_ctor_get(v_x_426_, 1);
lean_inc(v_out_431_);
lean_dec_ref_known(v_x_426_, 2);
v___x_432_ = lean_apply_2(v_h__1_427_, v_it_430_, v_out_431_);
return v___x_432_;
}
case 1:
{
lean_object* v_it_433_; lean_object* v___x_434_; 
lean_dec(v_h__3_429_);
lean_dec(v_h__1_427_);
v_it_433_ = lean_ctor_get(v_x_426_, 0);
lean_inc(v_it_433_);
lean_dec_ref_known(v_x_426_, 1);
v___x_434_ = lean_apply_1(v_h__2_428_, v_it_433_);
return v___x_434_;
}
default: 
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_h__2_428_);
lean_dec(v_h__1_427_);
v___x_435_ = lean_box(0);
v___x_436_ = lean_apply_1(v_h__3_429_, v___x_435_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(lean_object* v_s_437_, lean_object* v_motive_438_, lean_object* v_x_439_, lean_object* v_h__1_440_, lean_object* v_h__2_441_, lean_object* v_h__3_442_){
_start:
{
switch(lean_obj_tag(v_x_439_))
{
case 0:
{
lean_object* v_it_443_; lean_object* v_out_444_; lean_object* v___x_445_; 
lean_dec(v_h__3_442_);
lean_dec(v_h__2_441_);
v_it_443_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_it_443_);
v_out_444_ = lean_ctor_get(v_x_439_, 1);
lean_inc(v_out_444_);
lean_dec_ref_known(v_x_439_, 2);
v___x_445_ = lean_apply_2(v_h__1_440_, v_it_443_, v_out_444_);
return v___x_445_;
}
case 1:
{
lean_object* v_it_446_; lean_object* v___x_447_; 
lean_dec(v_h__3_442_);
lean_dec(v_h__1_440_);
v_it_446_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_it_446_);
lean_dec_ref_known(v_x_439_, 1);
v___x_447_ = lean_apply_1(v_h__2_441_, v_it_446_);
return v___x_447_;
}
default: 
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v_h__2_441_);
lean_dec(v_h__1_440_);
v___x_448_ = lean_box(0);
v___x_449_ = lean_apply_1(v_h__3_442_, v___x_448_);
return v___x_449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___boxed(lean_object* v_s_450_, lean_object* v_motive_451_, lean_object* v_x_452_, lean_object* v_h__1_453_, lean_object* v_h__2_454_, lean_object* v_h__3_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(v_s_450_, v_motive_451_, v_x_452_, v_h__1_453_, v_h__2_454_, v_h__3_455_);
lean_dec_ref(v_s_450_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg();
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(lean_object* v_s_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_box(0);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(lean_object* v_s_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(v_s_463_);
lean_dec_ref(v_s_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(lean_object* v___y_465_, lean_object* v_acc_466_, lean_object* v_recur_467_, lean_object* v_s_468_){
_start:
{
switch(lean_obj_tag(v_s_468_))
{
case 0:
{
lean_object* v_it_469_; lean_object* v_out_470_; lean_object* v_val_471_; 
v_it_469_ = lean_ctor_get(v_s_468_, 0);
lean_inc(v_it_469_);
v_out_470_ = lean_ctor_get(v_s_468_, 1);
lean_inc(v_out_470_);
lean_dec_ref_known(v_s_468_, 2);
v_val_471_ = lean_apply_3(v___y_465_, v_out_470_, lean_box(0), v_acc_466_);
if (lean_obj_tag(v_val_471_) == 0)
{
lean_object* v_a_472_; 
lean_dec(v_it_469_);
lean_dec(v_recur_467_);
v_a_472_ = lean_ctor_get(v_val_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v_val_471_, 1);
return v_a_472_;
}
else
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v_val_471_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v_val_471_, 1);
v___x_474_ = lean_apply_4(v_recur_467_, v_it_469_, v_a_473_, lean_box(0), lean_box(0));
return v___x_474_;
}
}
case 1:
{
lean_object* v_it_475_; lean_object* v___x_476_; 
lean_dec_ref(v___y_465_);
v_it_475_ = lean_ctor_get(v_s_468_, 0);
lean_inc(v_it_475_);
lean_dec_ref_known(v_s_468_, 1);
v___x_476_ = lean_apply_4(v_recur_467_, v_it_475_, v_acc_466_, lean_box(0), lean_box(0));
return v___x_476_;
}
default: 
{
lean_dec(v_recur_467_);
lean_dec_ref(v___y_465_);
return v_acc_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(lean_object* v___y_477_, lean_object* v_s_478_, lean_object* v_lift_479_, lean_object* v_it_480_, lean_object* v_acc_481_, lean_object* v_hP_482_, lean_object* v_recur_483_){
_start:
{
lean_object* v___f_484_; 
v___f_484_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0), 4, 3);
lean_closure_set(v___f_484_, 0, v___y_477_);
lean_closure_set(v___f_484_, 1, v_acc_481_);
lean_closure_set(v___f_484_, 2, v_recur_483_);
switch(lean_obj_tag(v_it_480_))
{
case 0:
{
lean_object* v_pos_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_502_; 
v_pos_485_ = lean_ctor_get(v_it_480_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_it_480_);
if (v_isSharedCheck_502_ == 0)
{
v___x_487_ = v_it_480_;
v_isShared_488_ = v_isSharedCheck_502_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_pos_485_);
lean_dec(v_it_480_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_502_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v_res_489_; lean_object* v_startInclusive_490_; lean_object* v_endExclusive_491_; lean_object* v___x_492_; uint8_t v_decide_493_; 
lean_inc_n(v_pos_485_, 2);
v_res_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_489_, 0, v_pos_485_);
lean_ctor_set(v_res_489_, 1, v_pos_485_);
v_startInclusive_490_ = lean_ctor_get(v_s_478_, 1);
v_endExclusive_491_ = lean_ctor_get(v_s_478_, 2);
v___x_492_ = lean_nat_sub(v_endExclusive_491_, v_startInclusive_490_);
v_decide_493_ = lean_nat_dec_eq(v_pos_485_, v___x_492_);
lean_dec(v___x_492_);
if (v_decide_493_ == 0)
{
lean_object* v___x_495_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set_tag(v___x_487_, 1);
v___x_495_ = v___x_487_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_pos_485_);
v___x_495_ = v_reuseFailAlloc_498_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v_res_489_);
v___x_497_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_496_);
return v___x_497_;
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_del_object(v___x_487_);
lean_dec(v_pos_485_);
v___x_499_ = lean_box(3);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v_res_489_);
v___x_501_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_500_);
return v___x_501_;
}
}
}
case 1:
{
lean_object* v_pos_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_518_; 
v_pos_503_ = lean_ctor_get(v_it_480_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_it_480_);
if (v_isSharedCheck_518_ == 0)
{
v___x_505_ = v_it_480_;
v_isShared_506_ = v_isSharedCheck_518_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_pos_503_);
lean_dec(v_it_480_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_518_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_str_507_; lean_object* v_startInclusive_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_res_512_; lean_object* v___x_514_; 
v_str_507_ = lean_ctor_get(v_s_478_, 0);
v_startInclusive_508_ = lean_ctor_get(v_s_478_, 1);
v___x_509_ = lean_nat_add(v_startInclusive_508_, v_pos_503_);
v___x_510_ = lean_string_utf8_next_fast(v_str_507_, v___x_509_);
lean_dec(v___x_509_);
v___x_511_ = lean_nat_sub(v___x_510_, v_startInclusive_508_);
lean_inc(v___x_511_);
v_res_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_512_, 0, v_pos_503_);
lean_ctor_set(v_res_512_, 1, v___x_511_);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 0);
lean_ctor_set(v___x_505_, 0, v___x_511_);
v___x_514_ = v___x_505_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_511_);
v___x_514_ = v_reuseFailAlloc_517_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_res_512_);
v___x_516_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_515_);
return v___x_516_;
}
}
}
case 2:
{
lean_object* v_needle_519_; lean_object* v_table_520_; lean_object* v_stackPos_521_; lean_object* v_needlePos_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_604_; 
v_needle_519_ = lean_ctor_get(v_it_480_, 0);
v_table_520_ = lean_ctor_get(v_it_480_, 1);
v_stackPos_521_ = lean_ctor_get(v_it_480_, 2);
v_needlePos_522_ = lean_ctor_get(v_it_480_, 3);
v_isSharedCheck_604_ = !lean_is_exclusive(v_it_480_);
if (v_isSharedCheck_604_ == 0)
{
v___x_524_ = v_it_480_;
v_isShared_525_ = v_isSharedCheck_604_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_needlePos_522_);
lean_inc(v_stackPos_521_);
lean_inc(v_table_520_);
lean_inc(v_needle_519_);
lean_dec(v_it_480_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_604_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_str_526_; lean_object* v_startInclusive_527_; lean_object* v_endExclusive_528_; lean_object* v_str_529_; lean_object* v_startInclusive_530_; lean_object* v_endExclusive_531_; lean_object* v_basePos_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_str_526_ = lean_ctor_get(v_needle_519_, 0);
v_startInclusive_527_ = lean_ctor_get(v_needle_519_, 1);
v_endExclusive_528_ = lean_ctor_get(v_needle_519_, 2);
v_str_529_ = lean_ctor_get(v_s_478_, 0);
v_startInclusive_530_ = lean_ctor_get(v_s_478_, 1);
v_endExclusive_531_ = lean_ctor_get(v_s_478_, 2);
v_basePos_532_ = lean_nat_sub(v_stackPos_521_, v_needlePos_522_);
v___x_533_ = lean_nat_sub(v_endExclusive_528_, v_startInclusive_527_);
v___x_534_ = lean_nat_add(v_basePos_532_, v___x_533_);
v___x_535_ = lean_nat_sub(v_endExclusive_531_, v_startInclusive_530_);
v___x_536_ = lean_nat_dec_le(v___x_534_, v___x_535_);
lean_dec(v___x_534_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
lean_dec(v___x_533_);
lean_del_object(v___x_524_);
lean_dec(v_needlePos_522_);
lean_dec(v_stackPos_521_);
lean_dec_ref(v_table_520_);
lean_dec_ref(v_needle_519_);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_basePos_532_, v___x_537_);
v___x_539_ = lean_nat_dec_le(v___x_538_, v___x_535_);
lean_dec(v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v___x_535_);
lean_dec(v_basePos_532_);
v___x_540_ = lean_box(2);
v___x_541_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_540_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v_res_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_542_ = l_String_Slice_pos_x21(v_s_478_, v_basePos_532_);
lean_dec(v_basePos_532_);
v_res_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_543_, 0, v___x_542_);
lean_ctor_set(v_res_543_, 1, v___x_535_);
v___x_544_ = lean_box(3);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_res_543_);
v___x_546_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_545_);
return v___x_546_;
}
}
else
{
lean_object* v___x_547_; uint8_t v_stackByte_548_; lean_object* v___x_549_; uint8_t v_patByte_550_; uint8_t v___x_551_; 
lean_dec(v___x_535_);
v___x_547_ = lean_nat_add(v_startInclusive_530_, v_stackPos_521_);
v_stackByte_548_ = lean_string_get_byte_fast(v_str_529_, v___x_547_);
v___x_549_ = lean_nat_add(v_startInclusive_527_, v_needlePos_522_);
v_patByte_550_ = lean_string_get_byte_fast(v_str_526_, v___x_549_);
v___x_551_ = lean_uint8_dec_eq(v_stackByte_548_, v_patByte_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; uint8_t v_decide_553_; 
lean_dec(v___x_533_);
v___x_552_ = lean_unsigned_to_nat(0u);
v_decide_553_ = lean_nat_dec_eq(v_needlePos_522_, v___x_552_);
if (v_decide_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_newNeedlePos_556_; uint8_t v___x_557_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_sub(v_needlePos_522_, v___x_554_);
lean_dec(v_needlePos_522_);
v_newNeedlePos_556_ = lean_array_fget_borrowed(v_table_520_, v___x_555_);
lean_dec(v___x_555_);
v___x_557_ = lean_nat_dec_eq(v_newNeedlePos_556_, v___x_552_);
if (v___x_557_ == 0)
{
lean_object* v_oldBasePos_558_; lean_object* v___x_559_; lean_object* v_newBasePos_560_; lean_object* v_res_561_; lean_object* v___x_563_; 
lean_inc(v_newNeedlePos_556_);
v_oldBasePos_558_ = l_String_Slice_pos_x21(v_s_478_, v_basePos_532_);
lean_dec(v_basePos_532_);
v___x_559_ = lean_nat_sub(v_stackPos_521_, v_newNeedlePos_556_);
v_newBasePos_560_ = l_String_Slice_pos_x21(v_s_478_, v___x_559_);
lean_dec(v___x_559_);
v_res_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_561_, 0, v_oldBasePos_558_);
lean_ctor_set(v_res_561_, 1, v_newBasePos_560_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 3, v_newNeedlePos_556_);
v___x_563_ = v___x_524_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_needle_519_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_table_520_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_stackPos_521_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_newNeedlePos_556_);
v___x_563_ = v_reuseFailAlloc_566_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_res_561_);
v___x_565_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_564_);
return v___x_565_;
}
}
else
{
lean_object* v_basePos_567_; lean_object* v_nextStackPos_568_; lean_object* v_res_569_; lean_object* v___x_571_; 
v_basePos_567_ = l_String_Slice_pos_x21(v_s_478_, v_basePos_532_);
lean_dec(v_basePos_532_);
v_nextStackPos_568_ = l_String_Slice_posGE___redArg(v_s_478_, v_stackPos_521_);
lean_inc(v_nextStackPos_568_);
v_res_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_569_, 0, v_basePos_567_);
lean_ctor_set(v_res_569_, 1, v_nextStackPos_568_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 3, v___x_552_);
lean_ctor_set(v___x_524_, 2, v_nextStackPos_568_);
v___x_571_ = v___x_524_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_needle_519_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_table_520_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_nextStackPos_568_);
lean_ctor_set(v_reuseFailAlloc_574_, 3, v___x_552_);
v___x_571_ = v_reuseFailAlloc_574_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_res_569_);
v___x_573_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_572_);
return v___x_573_;
}
}
}
else
{
lean_object* v_basePos_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_nextStackPos_578_; lean_object* v_res_579_; lean_object* v___x_581_; 
lean_dec(v_basePos_532_);
lean_dec(v_needlePos_522_);
v_basePos_575_ = l_String_Slice_pos_x21(v_s_478_, v_stackPos_521_);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_stackPos_521_, v___x_576_);
lean_dec(v_stackPos_521_);
v_nextStackPos_578_ = l_String_Slice_posGE___redArg(v_s_478_, v___x_577_);
lean_inc(v_nextStackPos_578_);
v_res_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_579_, 0, v_basePos_575_);
lean_ctor_set(v_res_579_, 1, v_nextStackPos_578_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 3, v___x_552_);
lean_ctor_set(v___x_524_, 2, v_nextStackPos_578_);
v___x_581_ = v___x_524_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_needle_519_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_table_520_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_nextStackPos_578_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v___x_552_);
v___x_581_ = v_reuseFailAlloc_584_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v_res_579_);
v___x_583_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_582_);
return v___x_583_;
}
}
}
else
{
lean_object* v___x_585_; lean_object* v_nextStackPos_586_; lean_object* v_nextNeedlePos_587_; uint8_t v_decide_588_; 
lean_dec(v_basePos_532_);
v___x_585_ = lean_unsigned_to_nat(1u);
v_nextStackPos_586_ = lean_nat_add(v_stackPos_521_, v___x_585_);
lean_dec(v_stackPos_521_);
v_nextNeedlePos_587_ = lean_nat_add(v_needlePos_522_, v___x_585_);
lean_dec(v_needlePos_522_);
v_decide_588_ = lean_nat_dec_eq(v_nextNeedlePos_587_, v___x_533_);
lean_dec(v___x_533_);
if (v_decide_588_ == 0)
{
lean_object* v___x_590_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 3, v_nextNeedlePos_587_);
lean_ctor_set(v___x_524_, 2, v_nextStackPos_586_);
v___x_590_ = v___x_524_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_needle_519_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_table_520_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_nextStackPos_586_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_nextNeedlePos_587_);
v___x_590_ = v_reuseFailAlloc_593_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
v___x_592_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_591_);
return v___x_592_;
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v_res_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_594_ = lean_nat_sub(v_nextStackPos_586_, v_nextNeedlePos_587_);
lean_dec(v_nextNeedlePos_587_);
v___x_595_ = l_String_Slice_pos_x21(v_s_478_, v___x_594_);
lean_dec(v___x_594_);
v___x_596_ = l_String_Slice_pos_x21(v_s_478_, v_nextStackPos_586_);
v_res_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_597_, 0, v___x_595_);
lean_ctor_set(v_res_597_, 1, v___x_596_);
v___x_598_ = lean_unsigned_to_nat(0u);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 3, v___x_598_);
lean_ctor_set(v___x_524_, 2, v_nextStackPos_586_);
v___x_600_ = v___x_524_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_needle_519_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_table_520_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_nextStackPos_586_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v___x_598_);
v___x_600_ = v_reuseFailAlloc_603_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v_res_597_);
v___x_602_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_601_);
return v___x_602_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_box(2);
v___x_606_ = lean_apply_4(v_lift_479_, lean_box(0), lean_box(0), v___f_484_, v___x_605_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed(lean_object* v___y_607_, lean_object* v_s_608_, lean_object* v_lift_609_, lean_object* v_it_610_, lean_object* v_acc_611_, lean_object* v_hP_612_, lean_object* v_recur_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(v___y_607_, v_s_608_, v_lift_609_, v_it_610_, v_acc_611_, v_hP_612_, v_recur_613_);
lean_dec_ref(v_s_608_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(lean_object* v_s_615_, lean_object* v_lift_616_, lean_object* v_00_u03b3_617_, lean_object* v_Pl_618_, lean_object* v_it_619_, lean_object* v_init_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___f_622_; lean_object* v___x_623_; 
v___f_622_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed), 7, 3);
lean_closure_set(v___f_622_, 0, v___y_621_);
lean_closure_set(v___f_622_, 1, v_s_615_);
lean_closure_set(v___f_622_, 2, v_lift_616_);
v___x_623_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_622_, v_it_619_, v_init_620_, lean_box(0));
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(lean_object* v_s_624_){
_start:
{
lean_object* v___f_625_; 
v___f_625_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2), 7, 1);
lean_closure_set(v___f_625_, 0, v_s_624_);
return v___f_625_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(lean_object* v_pat_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_627_, 0, v_pat_626_);
return v___x_627_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(lean_object* v_pat_628_, lean_object* v_s_629_){
_start:
{
lean_object* v_str_630_; lean_object* v_startInclusive_631_; lean_object* v_endExclusive_632_; lean_object* v_str_633_; lean_object* v_startInclusive_634_; lean_object* v_endExclusive_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_str_630_ = lean_ctor_get(v_pat_628_, 0);
v_startInclusive_631_ = lean_ctor_get(v_pat_628_, 1);
v_endExclusive_632_ = lean_ctor_get(v_pat_628_, 2);
v_str_633_ = lean_ctor_get(v_s_629_, 0);
v_startInclusive_634_ = lean_ctor_get(v_s_629_, 1);
v_endExclusive_635_ = lean_ctor_get(v_s_629_, 2);
v___x_636_ = lean_nat_sub(v_endExclusive_632_, v_startInclusive_631_);
v___x_637_ = lean_nat_sub(v_endExclusive_635_, v_startInclusive_634_);
v___x_638_ = lean_nat_dec_le(v___x_636_, v___x_637_);
lean_dec(v___x_637_);
if (v___x_638_ == 0)
{
lean_dec(v___x_636_);
return v___x_638_;
}
else
{
uint8_t v___x_639_; 
v___x_639_ = lean_string_memcmp(v_str_633_, v_str_630_, v_startInclusive_634_, v_startInclusive_631_, v___x_636_);
lean_dec(v___x_636_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(lean_object* v_pat_640_, lean_object* v_s_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(v_pat_640_, v_s_641_);
lean_dec_ref(v_s_641_);
lean_dec_ref(v_pat_640_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(lean_object* v_pat_644_, lean_object* v_s_645_){
_start:
{
lean_object* v_str_646_; lean_object* v_startInclusive_647_; lean_object* v_endExclusive_648_; lean_object* v_str_649_; lean_object* v_startInclusive_650_; lean_object* v_endExclusive_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_str_646_ = lean_ctor_get(v_pat_644_, 0);
v_startInclusive_647_ = lean_ctor_get(v_pat_644_, 1);
v_endExclusive_648_ = lean_ctor_get(v_pat_644_, 2);
v_str_649_ = lean_ctor_get(v_s_645_, 0);
v_startInclusive_650_ = lean_ctor_get(v_s_645_, 1);
v_endExclusive_651_ = lean_ctor_get(v_s_645_, 2);
v___x_652_ = lean_nat_sub(v_endExclusive_648_, v_startInclusive_647_);
v___x_653_ = lean_nat_sub(v_endExclusive_651_, v_startInclusive_650_);
v___x_654_ = lean_nat_dec_le(v___x_652_, v___x_653_);
lean_dec(v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
return v___x_655_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = lean_string_memcmp(v_str_649_, v_str_646_, v_startInclusive_650_, v_startInclusive_647_, v___x_652_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec(v___x_652_);
v___x_657_ = lean_box(0);
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = l_String_Slice_pos_x21(v_s_645_, v___x_652_);
lean_dec(v___x_652_);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed(lean_object* v_pat_660_, lean_object* v_s_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(v_pat_660_, v_s_661_);
lean_dec_ref(v_s_661_);
lean_dec_ref(v_pat_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(lean_object* v_pat_663_, lean_object* v_s_664_, lean_object* v_x_665_){
_start:
{
lean_object* v_str_666_; lean_object* v_startInclusive_667_; lean_object* v_endExclusive_668_; lean_object* v_str_669_; lean_object* v_startInclusive_670_; lean_object* v_endExclusive_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_str_666_ = lean_ctor_get(v_pat_663_, 0);
v_startInclusive_667_ = lean_ctor_get(v_pat_663_, 1);
v_endExclusive_668_ = lean_ctor_get(v_pat_663_, 2);
v_str_669_ = lean_ctor_get(v_s_664_, 0);
v_startInclusive_670_ = lean_ctor_get(v_s_664_, 1);
v_endExclusive_671_ = lean_ctor_get(v_s_664_, 2);
v___x_672_ = lean_nat_sub(v_endExclusive_668_, v_startInclusive_667_);
v___x_673_ = lean_nat_sub(v_endExclusive_671_, v_startInclusive_670_);
v___x_674_ = lean_nat_dec_le(v___x_672_, v___x_673_);
lean_dec(v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = lean_string_memcmp(v_str_669_, v_str_666_, v_startInclusive_670_, v_startInclusive_667_, v___x_672_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec(v___x_672_);
v___x_677_ = lean_box(0);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = l_String_Slice_pos_x21(v_s_664_, v___x_672_);
lean_dec(v___x_672_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(lean_object* v_pat_680_, lean_object* v_s_681_, lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(v_pat_680_, v_s_681_, v_x_682_);
lean_dec_ref(v_s_681_);
lean_dec_ref(v_pat_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(lean_object* v_pat_684_){
_start:
{
lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_inc_ref_n(v_pat_684_, 2);
v___f_685_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_685_, 0, v_pat_684_);
v___x_686_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_686_, 0, v_pat_684_);
v___x_687_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_687_, 0, v_pat_684_);
v___x_688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___f_685_);
lean_ctor_set(v___x_688_, 2, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(lean_object* v_pat_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_string_utf8_byte_size(v_pat_689_);
v___x_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_692_, 0, v_pat_689_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
lean_ctor_set(v___x_692_, 2, v___x_691_);
v___x_693_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(lean_object* v___x_694_, lean_object* v_pat_695_, lean_object* v___x_696_, lean_object* v_s_697_, lean_object* v_x_698_){
_start:
{
lean_object* v_str_699_; lean_object* v_startInclusive_700_; lean_object* v_endExclusive_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_str_699_ = lean_ctor_get(v_s_697_, 0);
v_startInclusive_700_ = lean_ctor_get(v_s_697_, 1);
v_endExclusive_701_ = lean_ctor_get(v_s_697_, 2);
v___x_702_ = lean_nat_sub(v_endExclusive_701_, v_startInclusive_700_);
v___x_703_ = lean_nat_dec_le(v___x_694_, v___x_702_);
lean_dec(v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_box(0);
return v___x_704_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = lean_string_memcmp(v_str_699_, v_pat_695_, v_startInclusive_700_, v___x_696_, v___x_694_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
v___x_706_ = lean_box(0);
return v___x_706_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = l_String_Slice_pos_x21(v_s_697_, v___x_694_);
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(lean_object* v___x_709_, lean_object* v_pat_710_, lean_object* v___x_711_, lean_object* v_s_712_, lean_object* v_x_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(v___x_709_, v_pat_710_, v___x_711_, v_s_712_, v_x_713_);
lean_dec_ref(v_s_712_);
lean_dec(v___x_711_);
lean_dec_ref(v_pat_710_);
lean_dec(v___x_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(lean_object* v_pat_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___f_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_string_utf8_byte_size(v_pat_715_);
lean_inc_ref(v_pat_715_);
v___f_718_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_718_, 0, v___x_717_);
lean_closure_set(v___f_718_, 1, v_pat_715_);
lean_closure_set(v___f_718_, 2, v___x_716_);
v___x_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_719_, 0, v_pat_715_);
lean_ctor_set(v___x_719_, 1, v___x_716_);
lean_ctor_set(v___x_719_, 2, v___x_717_);
lean_inc_ref(v___x_719_);
v___x_720_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_720_, 0, v___x_719_);
v___x_721_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_721_, 0, v___x_719_);
v___x_722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___f_718_);
lean_ctor_set(v___x_722_, 2, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(lean_object* v_pat_723_, lean_object* v_s_724_){
_start:
{
lean_object* v_str_725_; lean_object* v_startInclusive_726_; lean_object* v_endExclusive_727_; lean_object* v_str_728_; lean_object* v_startInclusive_729_; lean_object* v_endExclusive_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_str_725_ = lean_ctor_get(v_pat_723_, 0);
v_startInclusive_726_ = lean_ctor_get(v_pat_723_, 1);
v_endExclusive_727_ = lean_ctor_get(v_pat_723_, 2);
v_str_728_ = lean_ctor_get(v_s_724_, 0);
v_startInclusive_729_ = lean_ctor_get(v_s_724_, 1);
v_endExclusive_730_ = lean_ctor_get(v_s_724_, 2);
v___x_731_ = lean_nat_sub(v_endExclusive_727_, v_startInclusive_726_);
v___x_732_ = lean_nat_sub(v_endExclusive_730_, v_startInclusive_729_);
v___x_733_ = lean_nat_dec_le(v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_dec(v___x_732_);
lean_dec(v___x_731_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_nat_sub(v___x_732_, v___x_731_);
lean_dec(v___x_732_);
v___x_735_ = lean_nat_add(v_startInclusive_729_, v___x_734_);
lean_dec(v___x_734_);
v___x_736_ = lean_string_memcmp(v_str_728_, v_str_725_, v___x_735_, v_startInclusive_726_, v___x_731_);
lean_dec(v___x_731_);
lean_dec(v___x_735_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(lean_object* v_pat_737_, lean_object* v_s_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(v_pat_737_, v_s_738_);
lean_dec_ref(v_s_738_);
lean_dec_ref(v_pat_737_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(lean_object* v_pat_741_, lean_object* v_s_742_){
_start:
{
lean_object* v_str_743_; lean_object* v_startInclusive_744_; lean_object* v_endExclusive_745_; lean_object* v_str_746_; lean_object* v_startInclusive_747_; lean_object* v_endExclusive_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_str_743_ = lean_ctor_get(v_pat_741_, 0);
v_startInclusive_744_ = lean_ctor_get(v_pat_741_, 1);
v_endExclusive_745_ = lean_ctor_get(v_pat_741_, 2);
v_str_746_ = lean_ctor_get(v_s_742_, 0);
v_startInclusive_747_ = lean_ctor_get(v_s_742_, 1);
v_endExclusive_748_ = lean_ctor_get(v_s_742_, 2);
v___x_749_ = lean_nat_sub(v_endExclusive_745_, v_startInclusive_744_);
v___x_750_ = lean_nat_sub(v_endExclusive_748_, v_startInclusive_747_);
v___x_751_ = lean_nat_dec_le(v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_dec(v___x_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
return v___x_752_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_753_ = lean_nat_sub(v___x_750_, v___x_749_);
lean_dec(v___x_750_);
v___x_754_ = lean_nat_add(v_startInclusive_747_, v___x_753_);
v___x_755_ = lean_string_memcmp(v_str_746_, v_str_743_, v___x_754_, v_startInclusive_744_, v___x_749_);
lean_dec(v___x_749_);
lean_dec(v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
return v___x_756_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = l_String_Slice_pos_x21(v_s_742_, v___x_753_);
lean_dec(v___x_753_);
v___x_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed(lean_object* v_pat_759_, lean_object* v_s_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(v_pat_759_, v_s_760_);
lean_dec_ref(v_s_760_);
lean_dec_ref(v_pat_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(lean_object* v_pat_762_, lean_object* v_s_763_, lean_object* v_x_764_){
_start:
{
lean_object* v_str_765_; lean_object* v_startInclusive_766_; lean_object* v_endExclusive_767_; lean_object* v_str_768_; lean_object* v_startInclusive_769_; lean_object* v_endExclusive_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_str_765_ = lean_ctor_get(v_pat_762_, 0);
v_startInclusive_766_ = lean_ctor_get(v_pat_762_, 1);
v_endExclusive_767_ = lean_ctor_get(v_pat_762_, 2);
v_str_768_ = lean_ctor_get(v_s_763_, 0);
v_startInclusive_769_ = lean_ctor_get(v_s_763_, 1);
v_endExclusive_770_ = lean_ctor_get(v_s_763_, 2);
v___x_771_ = lean_nat_sub(v_endExclusive_767_, v_startInclusive_766_);
v___x_772_ = lean_nat_sub(v_endExclusive_770_, v_startInclusive_769_);
v___x_773_ = lean_nat_dec_le(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
lean_dec(v___x_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
return v___x_774_;
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_775_ = lean_nat_sub(v___x_772_, v___x_771_);
lean_dec(v___x_772_);
v___x_776_ = lean_nat_add(v_startInclusive_769_, v___x_775_);
v___x_777_ = lean_string_memcmp(v_str_768_, v_str_765_, v___x_776_, v_startInclusive_766_, v___x_771_);
lean_dec(v___x_771_);
lean_dec(v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
return v___x_778_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = l_String_Slice_pos_x21(v_s_763_, v___x_775_);
lean_dec(v___x_775_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(lean_object* v_pat_781_, lean_object* v_s_782_, lean_object* v_x_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(v_pat_781_, v_s_782_, v_x_783_);
lean_dec_ref(v_s_782_);
lean_dec_ref(v_pat_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(lean_object* v_pat_785_){
_start:
{
lean_object* v___f_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_inc_ref_n(v_pat_785_, 2);
v___f_786_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_786_, 0, v_pat_785_);
v___x_787_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_787_, 0, v_pat_785_);
v___x_788_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_788_, 0, v_pat_785_);
v___x_789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___f_786_);
lean_ctor_set(v___x_789_, 2, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(lean_object* v___x_790_, lean_object* v_pat_791_, lean_object* v___x_792_, lean_object* v_s_793_, lean_object* v_x_794_){
_start:
{
lean_object* v_str_795_; lean_object* v_startInclusive_796_; lean_object* v_endExclusive_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_str_795_ = lean_ctor_get(v_s_793_, 0);
v_startInclusive_796_ = lean_ctor_get(v_s_793_, 1);
v_endExclusive_797_ = lean_ctor_get(v_s_793_, 2);
v___x_798_ = lean_nat_sub(v_endExclusive_797_, v_startInclusive_796_);
v___x_799_ = lean_nat_dec_le(v___x_790_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec(v___x_798_);
v___x_800_ = lean_box(0);
return v___x_800_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_801_ = lean_nat_sub(v___x_798_, v___x_790_);
lean_dec(v___x_798_);
v___x_802_ = lean_nat_add(v_startInclusive_796_, v___x_801_);
v___x_803_ = lean_string_memcmp(v_str_795_, v_pat_791_, v___x_802_, v___x_792_, v___x_790_);
lean_dec(v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = l_String_Slice_pos_x21(v_s_793_, v___x_801_);
lean_dec(v___x_801_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(lean_object* v___x_807_, lean_object* v_pat_808_, lean_object* v___x_809_, lean_object* v_s_810_, lean_object* v_x_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(v___x_807_, v_pat_808_, v___x_809_, v_s_810_, v_x_811_);
lean_dec_ref(v_s_810_);
lean_dec(v___x_809_);
lean_dec_ref(v_pat_808_);
lean_dec(v___x_807_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(lean_object* v_pat_813_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_string_utf8_byte_size(v_pat_813_);
lean_inc_ref(v_pat_813_);
v___f_816_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_816_, 0, v___x_815_);
lean_closure_set(v___f_816_, 1, v_pat_813_);
lean_closure_set(v___f_816_, 2, v___x_814_);
v___x_817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_817_, 0, v_pat_813_);
lean_ctor_set(v___x_817_, 1, v___x_814_);
lean_ctor_set(v___x_817_, 2, v___x_815_);
lean_inc_ref(v___x_817_);
v___x_818_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_818_, 0, v___x_817_);
v___x_819_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_819_, 0, v___x_817_);
v___x_820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___f_816_);
lean_ctor_set(v___x_820_, 2, v___x_819_);
return v___x_820_;
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
