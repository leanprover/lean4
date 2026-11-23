// Lean compiler output
// Module: Init.Data.String.Pattern.String
// Imports: public import Init.Data.String.Pattern.Basic public import Init.Data.String.Pattern.Memcmp public import Init.Data.Vector.Basic public import Init.Data.String.FindPos import Init.Data.String.Termination import Init.Data.String.Lemmas.FindPos import Init.ByCases import Init.Data.Array.Lemmas import Init.Data.Option.Lemmas import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__Option_lt_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__Option_lt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__Option_lt_match__1_splitter___redArg(lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_h__1_459_, lean_object* v_h__2_460_, lean_object* v_h__3_461_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_dec(v_h__2_460_);
if (lean_obj_tag(v_x_458_) == 1)
{
lean_object* v_val_462_; lean_object* v___x_463_; 
lean_dec(v_h__3_461_);
v_val_462_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_val_462_);
lean_dec_ref_known(v_x_458_, 1);
v___x_463_ = lean_apply_1(v_h__1_459_, v_val_462_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; 
lean_dec(v_h__1_459_);
v___x_464_ = lean_apply_4(v_h__3_461_, v_x_457_, v_x_458_, lean_box(0), lean_box(0));
return v___x_464_;
}
}
else
{
lean_dec(v_h__1_459_);
if (lean_obj_tag(v_x_458_) == 1)
{
lean_object* v_val_465_; lean_object* v_val_466_; lean_object* v___x_467_; 
lean_dec(v_h__3_461_);
v_val_465_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v_x_457_, 1);
v_val_466_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v_x_458_, 1);
v___x_467_ = lean_apply_2(v_h__2_460_, v_val_465_, v_val_466_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
lean_dec(v_h__2_460_);
v___x_468_ = lean_apply_4(v_h__3_461_, v_x_457_, v_x_458_, lean_box(0), lean_box(0));
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__Option_lt_match__1_splitter(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_motive_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_, lean_object* v_h__3_476_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_dec(v_h__2_475_);
if (lean_obj_tag(v_x_473_) == 1)
{
lean_object* v_val_477_; lean_object* v___x_478_; 
lean_dec(v_h__3_476_);
v_val_477_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_val_477_);
lean_dec_ref_known(v_x_473_, 1);
v___x_478_ = lean_apply_1(v_h__1_474_, v_val_477_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
lean_dec(v_h__1_474_);
v___x_479_ = lean_apply_4(v_h__3_476_, v_x_472_, v_x_473_, lean_box(0), lean_box(0));
return v___x_479_;
}
}
else
{
lean_dec(v_h__1_474_);
if (lean_obj_tag(v_x_473_) == 1)
{
lean_object* v_val_480_; lean_object* v_val_481_; lean_object* v___x_482_; 
lean_dec(v_h__3_476_);
v_val_480_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_val_480_);
lean_dec_ref_known(v_x_472_, 1);
v_val_481_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v_x_473_, 1);
v___x_482_ = lean_apply_2(v_h__2_475_, v_val_480_, v_val_481_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; 
lean_dec(v_h__2_475_);
v___x_483_ = lean_apply_4(v_h__3_476_, v_x_472_, v_x_473_, lean_box(0), lean_box(0));
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = lean_box(0);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg();
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(lean_object* v_s_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = lean_box(0);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(lean_object* v_s_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(v_s_490_);
lean_dec_ref(v_s_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(lean_object* v___y_492_, lean_object* v_acc_493_, lean_object* v_recur_494_, lean_object* v_s_495_){
_start:
{
switch(lean_obj_tag(v_s_495_))
{
case 0:
{
lean_object* v_it_496_; lean_object* v_out_497_; lean_object* v_val_498_; 
v_it_496_ = lean_ctor_get(v_s_495_, 0);
lean_inc(v_it_496_);
v_out_497_ = lean_ctor_get(v_s_495_, 1);
lean_inc(v_out_497_);
lean_dec_ref_known(v_s_495_, 2);
v_val_498_ = lean_apply_3(v___y_492_, v_out_497_, lean_box(0), v_acc_493_);
if (lean_obj_tag(v_val_498_) == 0)
{
lean_object* v_a_499_; 
lean_dec(v_it_496_);
lean_dec(v_recur_494_);
v_a_499_ = lean_ctor_get(v_val_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v_val_498_, 1);
return v_a_499_;
}
else
{
lean_object* v_a_500_; lean_object* v___x_501_; 
v_a_500_ = lean_ctor_get(v_val_498_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v_val_498_, 1);
v___x_501_ = lean_apply_4(v_recur_494_, v_it_496_, v_a_500_, lean_box(0), lean_box(0));
return v___x_501_;
}
}
case 1:
{
lean_object* v_it_502_; lean_object* v___x_503_; 
lean_dec_ref(v___y_492_);
v_it_502_ = lean_ctor_get(v_s_495_, 0);
lean_inc(v_it_502_);
lean_dec_ref_known(v_s_495_, 1);
v___x_503_ = lean_apply_4(v_recur_494_, v_it_502_, v_acc_493_, lean_box(0), lean_box(0));
return v___x_503_;
}
default: 
{
lean_dec(v_recur_494_);
lean_dec_ref(v___y_492_);
return v_acc_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(lean_object* v___y_504_, lean_object* v_s_505_, lean_object* v_lift_506_, lean_object* v_it_507_, lean_object* v_acc_508_, lean_object* v_hP_509_, lean_object* v_recur_510_){
_start:
{
lean_object* v___f_511_; 
v___f_511_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0), 4, 3);
lean_closure_set(v___f_511_, 0, v___y_504_);
lean_closure_set(v___f_511_, 1, v_acc_508_);
lean_closure_set(v___f_511_, 2, v_recur_510_);
switch(lean_obj_tag(v_it_507_))
{
case 0:
{
lean_object* v_pos_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_529_; 
v_pos_512_ = lean_ctor_get(v_it_507_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_it_507_);
if (v_isSharedCheck_529_ == 0)
{
v___x_514_ = v_it_507_;
v_isShared_515_ = v_isSharedCheck_529_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_pos_512_);
lean_dec(v_it_507_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_529_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_res_516_; lean_object* v_startInclusive_517_; lean_object* v_endExclusive_518_; lean_object* v___x_519_; uint8_t v_decide_520_; 
lean_inc_n(v_pos_512_, 2);
v_res_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_516_, 0, v_pos_512_);
lean_ctor_set(v_res_516_, 1, v_pos_512_);
v_startInclusive_517_ = lean_ctor_get(v_s_505_, 1);
v_endExclusive_518_ = lean_ctor_get(v_s_505_, 2);
v___x_519_ = lean_nat_sub(v_endExclusive_518_, v_startInclusive_517_);
v_decide_520_ = lean_nat_dec_eq(v_pos_512_, v___x_519_);
lean_dec(v___x_519_);
if (v_decide_520_ == 0)
{
lean_object* v___x_522_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set_tag(v___x_514_, 1);
v___x_522_ = v___x_514_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_pos_512_);
v___x_522_ = v_reuseFailAlloc_525_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v_res_516_);
v___x_524_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_523_);
return v___x_524_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_del_object(v___x_514_);
lean_dec(v_pos_512_);
v___x_526_ = lean_box(3);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_res_516_);
v___x_528_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_527_);
return v___x_528_;
}
}
}
case 1:
{
lean_object* v_pos_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_545_; 
v_pos_530_ = lean_ctor_get(v_it_507_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_it_507_);
if (v_isSharedCheck_545_ == 0)
{
v___x_532_ = v_it_507_;
v_isShared_533_ = v_isSharedCheck_545_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_pos_530_);
lean_dec(v_it_507_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_545_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_str_534_; lean_object* v_startInclusive_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_res_539_; lean_object* v___x_541_; 
v_str_534_ = lean_ctor_get(v_s_505_, 0);
v_startInclusive_535_ = lean_ctor_get(v_s_505_, 1);
v___x_536_ = lean_nat_add(v_startInclusive_535_, v_pos_530_);
v___x_537_ = lean_string_utf8_next_fast(v_str_534_, v___x_536_);
lean_dec(v___x_536_);
v___x_538_ = lean_nat_sub(v___x_537_, v_startInclusive_535_);
lean_inc(v___x_538_);
v_res_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_539_, 0, v_pos_530_);
lean_ctor_set(v_res_539_, 1, v___x_538_);
if (v_isShared_533_ == 0)
{
lean_ctor_set_tag(v___x_532_, 0);
lean_ctor_set(v___x_532_, 0, v___x_538_);
v___x_541_ = v___x_532_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_538_);
v___x_541_ = v_reuseFailAlloc_544_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_res_539_);
v___x_543_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_542_);
return v___x_543_;
}
}
}
case 2:
{
lean_object* v_needle_546_; lean_object* v_table_547_; lean_object* v_stackPos_548_; lean_object* v_needlePos_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_631_; 
v_needle_546_ = lean_ctor_get(v_it_507_, 0);
v_table_547_ = lean_ctor_get(v_it_507_, 1);
v_stackPos_548_ = lean_ctor_get(v_it_507_, 2);
v_needlePos_549_ = lean_ctor_get(v_it_507_, 3);
v_isSharedCheck_631_ = !lean_is_exclusive(v_it_507_);
if (v_isSharedCheck_631_ == 0)
{
v___x_551_ = v_it_507_;
v_isShared_552_ = v_isSharedCheck_631_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_needlePos_549_);
lean_inc(v_stackPos_548_);
lean_inc(v_table_547_);
lean_inc(v_needle_546_);
lean_dec(v_it_507_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_631_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_str_553_; lean_object* v_startInclusive_554_; lean_object* v_endExclusive_555_; lean_object* v_str_556_; lean_object* v_startInclusive_557_; lean_object* v_endExclusive_558_; lean_object* v_basePos_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_str_553_ = lean_ctor_get(v_needle_546_, 0);
v_startInclusive_554_ = lean_ctor_get(v_needle_546_, 1);
v_endExclusive_555_ = lean_ctor_get(v_needle_546_, 2);
v_str_556_ = lean_ctor_get(v_s_505_, 0);
v_startInclusive_557_ = lean_ctor_get(v_s_505_, 1);
v_endExclusive_558_ = lean_ctor_get(v_s_505_, 2);
v_basePos_559_ = lean_nat_sub(v_stackPos_548_, v_needlePos_549_);
v___x_560_ = lean_nat_sub(v_endExclusive_555_, v_startInclusive_554_);
v___x_561_ = lean_nat_add(v_basePos_559_, v___x_560_);
v___x_562_ = lean_nat_sub(v_endExclusive_558_, v_startInclusive_557_);
v___x_563_ = lean_nat_dec_le(v___x_561_, v___x_562_);
lean_dec(v___x_561_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
lean_dec(v___x_560_);
lean_del_object(v___x_551_);
lean_dec(v_needlePos_549_);
lean_dec(v_stackPos_548_);
lean_dec_ref(v_table_547_);
lean_dec_ref(v_needle_546_);
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = lean_nat_add(v_basePos_559_, v___x_564_);
v___x_566_ = lean_nat_dec_le(v___x_565_, v___x_562_);
lean_dec(v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_562_);
lean_dec(v_basePos_559_);
v___x_567_ = lean_box(2);
v___x_568_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_567_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; lean_object* v_res_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_569_ = l_String_Slice_pos_x21(v_s_505_, v_basePos_559_);
lean_dec(v_basePos_559_);
v_res_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_570_, 0, v___x_569_);
lean_ctor_set(v_res_570_, 1, v___x_562_);
v___x_571_ = lean_box(3);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_res_570_);
v___x_573_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_572_);
return v___x_573_;
}
}
else
{
lean_object* v___x_574_; uint8_t v_stackByte_575_; lean_object* v___x_576_; uint8_t v_patByte_577_; uint8_t v___x_578_; 
lean_dec(v___x_562_);
v___x_574_ = lean_nat_add(v_startInclusive_557_, v_stackPos_548_);
v_stackByte_575_ = lean_string_get_byte_fast(v_str_556_, v___x_574_);
v___x_576_ = lean_nat_add(v_startInclusive_554_, v_needlePos_549_);
v_patByte_577_ = lean_string_get_byte_fast(v_str_553_, v___x_576_);
v___x_578_ = lean_uint8_dec_eq(v_stackByte_575_, v_patByte_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; uint8_t v_decide_580_; 
lean_dec(v___x_560_);
v___x_579_ = lean_unsigned_to_nat(0u);
v_decide_580_ = lean_nat_dec_eq(v_needlePos_549_, v___x_579_);
if (v_decide_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_newNeedlePos_583_; uint8_t v___x_584_; 
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_sub(v_needlePos_549_, v___x_581_);
lean_dec(v_needlePos_549_);
v_newNeedlePos_583_ = lean_array_fget_borrowed(v_table_547_, v___x_582_);
lean_dec(v___x_582_);
v___x_584_ = lean_nat_dec_eq(v_newNeedlePos_583_, v___x_579_);
if (v___x_584_ == 0)
{
lean_object* v_oldBasePos_585_; lean_object* v___x_586_; lean_object* v_newBasePos_587_; lean_object* v_res_588_; lean_object* v___x_590_; 
lean_inc(v_newNeedlePos_583_);
v_oldBasePos_585_ = l_String_Slice_pos_x21(v_s_505_, v_basePos_559_);
lean_dec(v_basePos_559_);
v___x_586_ = lean_nat_sub(v_stackPos_548_, v_newNeedlePos_583_);
v_newBasePos_587_ = l_String_Slice_pos_x21(v_s_505_, v___x_586_);
lean_dec(v___x_586_);
v_res_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_588_, 0, v_oldBasePos_585_);
lean_ctor_set(v_res_588_, 1, v_newBasePos_587_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 3, v_newNeedlePos_583_);
v___x_590_ = v___x_551_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_needle_546_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_table_547_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_stackPos_548_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_newNeedlePos_583_);
v___x_590_ = v_reuseFailAlloc_593_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v_res_588_);
v___x_592_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_591_);
return v___x_592_;
}
}
else
{
lean_object* v_basePos_594_; lean_object* v_nextStackPos_595_; lean_object* v_res_596_; lean_object* v___x_598_; 
v_basePos_594_ = l_String_Slice_pos_x21(v_s_505_, v_basePos_559_);
lean_dec(v_basePos_559_);
v_nextStackPos_595_ = l_String_Slice_posGE___redArg(v_s_505_, v_stackPos_548_);
lean_inc(v_nextStackPos_595_);
v_res_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_596_, 0, v_basePos_594_);
lean_ctor_set(v_res_596_, 1, v_nextStackPos_595_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 3, v___x_579_);
lean_ctor_set(v___x_551_, 2, v_nextStackPos_595_);
v___x_598_ = v___x_551_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_needle_546_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_table_547_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_nextStackPos_595_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v___x_579_);
v___x_598_ = v_reuseFailAlloc_601_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v_res_596_);
v___x_600_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_599_);
return v___x_600_;
}
}
}
else
{
lean_object* v_basePos_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_nextStackPos_605_; lean_object* v_res_606_; lean_object* v___x_608_; 
lean_dec(v_basePos_559_);
lean_dec(v_needlePos_549_);
v_basePos_602_ = l_String_Slice_pos_x21(v_s_505_, v_stackPos_548_);
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_add(v_stackPos_548_, v___x_603_);
lean_dec(v_stackPos_548_);
v_nextStackPos_605_ = l_String_Slice_posGE___redArg(v_s_505_, v___x_604_);
lean_inc(v_nextStackPos_605_);
v_res_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_606_, 0, v_basePos_602_);
lean_ctor_set(v_res_606_, 1, v_nextStackPos_605_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 3, v___x_579_);
lean_ctor_set(v___x_551_, 2, v_nextStackPos_605_);
v___x_608_ = v___x_551_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_needle_546_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_table_547_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_nextStackPos_605_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v___x_579_);
v___x_608_ = v_reuseFailAlloc_611_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v_res_606_);
v___x_610_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_609_);
return v___x_610_;
}
}
}
else
{
lean_object* v___x_612_; lean_object* v_nextStackPos_613_; lean_object* v_nextNeedlePos_614_; uint8_t v_decide_615_; 
lean_dec(v_basePos_559_);
v___x_612_ = lean_unsigned_to_nat(1u);
v_nextStackPos_613_ = lean_nat_add(v_stackPos_548_, v___x_612_);
lean_dec(v_stackPos_548_);
v_nextNeedlePos_614_ = lean_nat_add(v_needlePos_549_, v___x_612_);
lean_dec(v_needlePos_549_);
v_decide_615_ = lean_nat_dec_eq(v_nextNeedlePos_614_, v___x_560_);
lean_dec(v___x_560_);
if (v_decide_615_ == 0)
{
lean_object* v___x_617_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 3, v_nextNeedlePos_614_);
lean_ctor_set(v___x_551_, 2, v_nextStackPos_613_);
v___x_617_ = v___x_551_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_needle_546_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_table_547_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_nextStackPos_613_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_nextNeedlePos_614_);
v___x_617_ = v_reuseFailAlloc_620_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
v___x_619_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_618_);
return v___x_619_;
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_res_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_621_ = lean_nat_sub(v_nextStackPos_613_, v_nextNeedlePos_614_);
lean_dec(v_nextNeedlePos_614_);
v___x_622_ = l_String_Slice_pos_x21(v_s_505_, v___x_621_);
lean_dec(v___x_621_);
v___x_623_ = l_String_Slice_pos_x21(v_s_505_, v_nextStackPos_613_);
v_res_624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_624_, 0, v___x_622_);
lean_ctor_set(v_res_624_, 1, v___x_623_);
v___x_625_ = lean_unsigned_to_nat(0u);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 3, v___x_625_);
lean_ctor_set(v___x_551_, 2, v_nextStackPos_613_);
v___x_627_ = v___x_551_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_needle_546_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_table_547_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_nextStackPos_613_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v___x_625_);
v___x_627_ = v_reuseFailAlloc_630_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_res_624_);
v___x_629_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_628_);
return v___x_629_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_box(2);
v___x_633_ = lean_apply_4(v_lift_506_, lean_box(0), lean_box(0), v___f_511_, v___x_632_);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed(lean_object* v___y_634_, lean_object* v_s_635_, lean_object* v_lift_636_, lean_object* v_it_637_, lean_object* v_acc_638_, lean_object* v_hP_639_, lean_object* v_recur_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(v___y_634_, v_s_635_, v_lift_636_, v_it_637_, v_acc_638_, v_hP_639_, v_recur_640_);
lean_dec_ref(v_s_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(lean_object* v_s_642_, lean_object* v_lift_643_, lean_object* v_00_u03b3_644_, lean_object* v_Pl_645_, lean_object* v_it_646_, lean_object* v_init_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___f_649_; lean_object* v___x_650_; 
v___f_649_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed), 7, 3);
lean_closure_set(v___f_649_, 0, v___y_648_);
lean_closure_set(v___f_649_, 1, v_s_642_);
lean_closure_set(v___f_649_, 2, v_lift_643_);
v___x_650_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_649_, v_it_646_, v_init_647_, lean_box(0));
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(lean_object* v_s_651_){
_start:
{
lean_object* v___f_652_; 
v___f_652_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2), 7, 1);
lean_closure_set(v___f_652_, 0, v_s_651_);
return v___f_652_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(lean_object* v_pat_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_654_, 0, v_pat_653_);
return v___x_654_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(lean_object* v_pat_655_, lean_object* v_s_656_){
_start:
{
lean_object* v_str_657_; lean_object* v_startInclusive_658_; lean_object* v_endExclusive_659_; lean_object* v_str_660_; lean_object* v_startInclusive_661_; lean_object* v_endExclusive_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_str_657_ = lean_ctor_get(v_pat_655_, 0);
v_startInclusive_658_ = lean_ctor_get(v_pat_655_, 1);
v_endExclusive_659_ = lean_ctor_get(v_pat_655_, 2);
v_str_660_ = lean_ctor_get(v_s_656_, 0);
v_startInclusive_661_ = lean_ctor_get(v_s_656_, 1);
v_endExclusive_662_ = lean_ctor_get(v_s_656_, 2);
v___x_663_ = lean_nat_sub(v_endExclusive_659_, v_startInclusive_658_);
v___x_664_ = lean_nat_sub(v_endExclusive_662_, v_startInclusive_661_);
v___x_665_ = lean_nat_dec_le(v___x_663_, v___x_664_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
lean_dec(v___x_663_);
return v___x_665_;
}
else
{
uint8_t v___x_666_; 
v___x_666_ = lean_string_memcmp(v_str_660_, v_str_657_, v_startInclusive_661_, v_startInclusive_658_, v___x_663_);
lean_dec(v___x_663_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(lean_object* v_pat_667_, lean_object* v_s_668_){
_start:
{
uint8_t v_res_669_; lean_object* v_r_670_; 
v_res_669_ = l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(v_pat_667_, v_s_668_);
lean_dec_ref(v_s_668_);
lean_dec_ref(v_pat_667_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(lean_object* v_pat_671_, lean_object* v_s_672_){
_start:
{
lean_object* v_str_673_; lean_object* v_startInclusive_674_; lean_object* v_endExclusive_675_; lean_object* v_str_676_; lean_object* v_startInclusive_677_; lean_object* v_endExclusive_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_str_673_ = lean_ctor_get(v_pat_671_, 0);
v_startInclusive_674_ = lean_ctor_get(v_pat_671_, 1);
v_endExclusive_675_ = lean_ctor_get(v_pat_671_, 2);
v_str_676_ = lean_ctor_get(v_s_672_, 0);
v_startInclusive_677_ = lean_ctor_get(v_s_672_, 1);
v_endExclusive_678_ = lean_ctor_get(v_s_672_, 2);
v___x_679_ = lean_nat_sub(v_endExclusive_675_, v_startInclusive_674_);
v___x_680_ = lean_nat_sub(v_endExclusive_678_, v_startInclusive_677_);
v___x_681_ = lean_nat_dec_le(v___x_679_, v___x_680_);
lean_dec(v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
return v___x_682_;
}
else
{
uint8_t v___x_683_; 
v___x_683_ = lean_string_memcmp(v_str_676_, v_str_673_, v_startInclusive_677_, v_startInclusive_674_, v___x_679_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec(v___x_679_);
v___x_684_ = lean_box(0);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = l_String_Slice_pos_x21(v_s_672_, v___x_679_);
lean_dec(v___x_679_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed(lean_object* v_pat_687_, lean_object* v_s_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(v_pat_687_, v_s_688_);
lean_dec_ref(v_s_688_);
lean_dec_ref(v_pat_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(lean_object* v_pat_690_, lean_object* v_s_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_str_693_; lean_object* v_startInclusive_694_; lean_object* v_endExclusive_695_; lean_object* v_str_696_; lean_object* v_startInclusive_697_; lean_object* v_endExclusive_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_str_693_ = lean_ctor_get(v_pat_690_, 0);
v_startInclusive_694_ = lean_ctor_get(v_pat_690_, 1);
v_endExclusive_695_ = lean_ctor_get(v_pat_690_, 2);
v_str_696_ = lean_ctor_get(v_s_691_, 0);
v_startInclusive_697_ = lean_ctor_get(v_s_691_, 1);
v_endExclusive_698_ = lean_ctor_get(v_s_691_, 2);
v___x_699_ = lean_nat_sub(v_endExclusive_695_, v_startInclusive_694_);
v___x_700_ = lean_nat_sub(v_endExclusive_698_, v_startInclusive_697_);
v___x_701_ = lean_nat_dec_le(v___x_699_, v___x_700_);
lean_dec(v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
return v___x_702_;
}
else
{
uint8_t v___x_703_; 
v___x_703_ = lean_string_memcmp(v_str_696_, v_str_693_, v_startInclusive_697_, v_startInclusive_694_, v___x_699_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
lean_dec(v___x_699_);
v___x_704_ = lean_box(0);
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = l_String_Slice_pos_x21(v_s_691_, v___x_699_);
lean_dec(v___x_699_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(lean_object* v_pat_707_, lean_object* v_s_708_, lean_object* v_x_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(v_pat_707_, v_s_708_, v_x_709_);
lean_dec_ref(v_s_708_);
lean_dec_ref(v_pat_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(lean_object* v_pat_711_){
_start:
{
lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_inc_ref_n(v_pat_711_, 2);
v___f_712_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_712_, 0, v_pat_711_);
v___x_713_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_713_, 0, v_pat_711_);
v___x_714_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_714_, 0, v_pat_711_);
v___x_715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___f_712_);
lean_ctor_set(v___x_715_, 2, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(lean_object* v_pat_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_string_utf8_byte_size(v_pat_716_);
v___x_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_719_, 0, v_pat_716_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
v___x_720_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(lean_object* v___x_721_, lean_object* v_pat_722_, lean_object* v___x_723_, lean_object* v_s_724_, lean_object* v_x_725_){
_start:
{
lean_object* v_str_726_; lean_object* v_startInclusive_727_; lean_object* v_endExclusive_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_str_726_ = lean_ctor_get(v_s_724_, 0);
v_startInclusive_727_ = lean_ctor_get(v_s_724_, 1);
v_endExclusive_728_ = lean_ctor_get(v_s_724_, 2);
v___x_729_ = lean_nat_sub(v_endExclusive_728_, v_startInclusive_727_);
v___x_730_ = lean_nat_dec_le(v___x_721_, v___x_729_);
lean_dec(v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(0);
return v___x_731_;
}
else
{
uint8_t v___x_732_; 
v___x_732_ = lean_string_memcmp(v_str_726_, v_pat_722_, v_startInclusive_727_, v___x_723_, v___x_721_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
v___x_733_ = lean_box(0);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = l_String_Slice_pos_x21(v_s_724_, v___x_721_);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(lean_object* v___x_736_, lean_object* v_pat_737_, lean_object* v___x_738_, lean_object* v_s_739_, lean_object* v_x_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(v___x_736_, v_pat_737_, v___x_738_, v_s_739_, v_x_740_);
lean_dec_ref(v_s_739_);
lean_dec(v___x_738_);
lean_dec_ref(v_pat_737_);
lean_dec(v___x_736_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(lean_object* v_pat_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_string_utf8_byte_size(v_pat_742_);
lean_inc_ref(v_pat_742_);
v___f_745_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_745_, 0, v___x_744_);
lean_closure_set(v___f_745_, 1, v_pat_742_);
lean_closure_set(v___f_745_, 2, v___x_743_);
v___x_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_746_, 0, v_pat_742_);
lean_ctor_set(v___x_746_, 1, v___x_743_);
lean_ctor_set(v___x_746_, 2, v___x_744_);
lean_inc_ref(v___x_746_);
v___x_747_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_747_, 0, v___x_746_);
v___x_748_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_748_, 0, v___x_746_);
v___x_749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___f_745_);
lean_ctor_set(v___x_749_, 2, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(lean_object* v_pat_750_, lean_object* v_s_751_){
_start:
{
lean_object* v_str_752_; lean_object* v_startInclusive_753_; lean_object* v_endExclusive_754_; lean_object* v_str_755_; lean_object* v_startInclusive_756_; lean_object* v_endExclusive_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_str_752_ = lean_ctor_get(v_pat_750_, 0);
v_startInclusive_753_ = lean_ctor_get(v_pat_750_, 1);
v_endExclusive_754_ = lean_ctor_get(v_pat_750_, 2);
v_str_755_ = lean_ctor_get(v_s_751_, 0);
v_startInclusive_756_ = lean_ctor_get(v_s_751_, 1);
v_endExclusive_757_ = lean_ctor_get(v_s_751_, 2);
v___x_758_ = lean_nat_sub(v_endExclusive_754_, v_startInclusive_753_);
v___x_759_ = lean_nat_sub(v_endExclusive_757_, v_startInclusive_756_);
v___x_760_ = lean_nat_dec_le(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v___x_759_);
lean_dec(v___x_758_);
return v___x_760_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = lean_nat_sub(v___x_759_, v___x_758_);
lean_dec(v___x_759_);
v___x_762_ = lean_nat_add(v_startInclusive_756_, v___x_761_);
lean_dec(v___x_761_);
v___x_763_ = lean_string_memcmp(v_str_755_, v_str_752_, v___x_762_, v_startInclusive_753_, v___x_758_);
lean_dec(v___x_758_);
lean_dec(v___x_762_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(lean_object* v_pat_764_, lean_object* v_s_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(v_pat_764_, v_s_765_);
lean_dec_ref(v_s_765_);
lean_dec_ref(v_pat_764_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(lean_object* v_pat_768_, lean_object* v_s_769_){
_start:
{
lean_object* v_str_770_; lean_object* v_startInclusive_771_; lean_object* v_endExclusive_772_; lean_object* v_str_773_; lean_object* v_startInclusive_774_; lean_object* v_endExclusive_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_str_770_ = lean_ctor_get(v_pat_768_, 0);
v_startInclusive_771_ = lean_ctor_get(v_pat_768_, 1);
v_endExclusive_772_ = lean_ctor_get(v_pat_768_, 2);
v_str_773_ = lean_ctor_get(v_s_769_, 0);
v_startInclusive_774_ = lean_ctor_get(v_s_769_, 1);
v_endExclusive_775_ = lean_ctor_get(v_s_769_, 2);
v___x_776_ = lean_nat_sub(v_endExclusive_772_, v_startInclusive_771_);
v___x_777_ = lean_nat_sub(v_endExclusive_775_, v_startInclusive_774_);
v___x_778_ = lean_nat_dec_le(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v___x_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
return v___x_779_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_780_ = lean_nat_sub(v___x_777_, v___x_776_);
lean_dec(v___x_777_);
v___x_781_ = lean_nat_add(v_startInclusive_774_, v___x_780_);
v___x_782_ = lean_string_memcmp(v_str_773_, v_str_770_, v___x_781_, v_startInclusive_771_, v___x_776_);
lean_dec(v___x_776_);
lean_dec(v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
return v___x_783_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = l_String_Slice_pos_x21(v_s_769_, v___x_780_);
lean_dec(v___x_780_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed(lean_object* v_pat_786_, lean_object* v_s_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(v_pat_786_, v_s_787_);
lean_dec_ref(v_s_787_);
lean_dec_ref(v_pat_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(lean_object* v_pat_789_, lean_object* v_s_790_, lean_object* v_x_791_){
_start:
{
lean_object* v_str_792_; lean_object* v_startInclusive_793_; lean_object* v_endExclusive_794_; lean_object* v_str_795_; lean_object* v_startInclusive_796_; lean_object* v_endExclusive_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_str_792_ = lean_ctor_get(v_pat_789_, 0);
v_startInclusive_793_ = lean_ctor_get(v_pat_789_, 1);
v_endExclusive_794_ = lean_ctor_get(v_pat_789_, 2);
v_str_795_ = lean_ctor_get(v_s_790_, 0);
v_startInclusive_796_ = lean_ctor_get(v_s_790_, 1);
v_endExclusive_797_ = lean_ctor_get(v_s_790_, 2);
v___x_798_ = lean_nat_sub(v_endExclusive_794_, v_startInclusive_793_);
v___x_799_ = lean_nat_sub(v_endExclusive_797_, v_startInclusive_796_);
v___x_800_ = lean_nat_dec_le(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
lean_dec(v___x_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
return v___x_801_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = lean_nat_sub(v___x_799_, v___x_798_);
lean_dec(v___x_799_);
v___x_803_ = lean_nat_add(v_startInclusive_796_, v___x_802_);
v___x_804_ = lean_string_memcmp(v_str_795_, v_str_792_, v___x_803_, v_startInclusive_793_, v___x_798_);
lean_dec(v___x_798_);
lean_dec(v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = l_String_Slice_pos_x21(v_s_790_, v___x_802_);
lean_dec(v___x_802_);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(lean_object* v_pat_808_, lean_object* v_s_809_, lean_object* v_x_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(v_pat_808_, v_s_809_, v_x_810_);
lean_dec_ref(v_s_809_);
lean_dec_ref(v_pat_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(lean_object* v_pat_812_){
_start:
{
lean_object* v___f_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_inc_ref_n(v_pat_812_, 2);
v___f_813_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_813_, 0, v_pat_812_);
v___x_814_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_814_, 0, v_pat_812_);
v___x_815_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_815_, 0, v_pat_812_);
v___x_816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___f_813_);
lean_ctor_set(v___x_816_, 2, v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(lean_object* v___x_817_, lean_object* v_pat_818_, lean_object* v___x_819_, lean_object* v_s_820_, lean_object* v_x_821_){
_start:
{
lean_object* v_str_822_; lean_object* v_startInclusive_823_; lean_object* v_endExclusive_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_str_822_ = lean_ctor_get(v_s_820_, 0);
v_startInclusive_823_ = lean_ctor_get(v_s_820_, 1);
v_endExclusive_824_ = lean_ctor_get(v_s_820_, 2);
v___x_825_ = lean_nat_sub(v_endExclusive_824_, v_startInclusive_823_);
v___x_826_ = lean_nat_dec_le(v___x_817_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
lean_dec(v___x_825_);
v___x_827_ = lean_box(0);
return v___x_827_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_828_ = lean_nat_sub(v___x_825_, v___x_817_);
lean_dec(v___x_825_);
v___x_829_ = lean_nat_add(v_startInclusive_823_, v___x_828_);
v___x_830_ = lean_string_memcmp(v_str_822_, v_pat_818_, v___x_829_, v___x_819_, v___x_817_);
lean_dec(v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
return v___x_831_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = l_String_Slice_pos_x21(v_s_820_, v___x_828_);
lean_dec(v___x_828_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(lean_object* v___x_834_, lean_object* v_pat_835_, lean_object* v___x_836_, lean_object* v_s_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(v___x_834_, v_pat_835_, v___x_836_, v_s_837_, v_x_838_);
lean_dec_ref(v_s_837_);
lean_dec(v___x_836_);
lean_dec_ref(v_pat_835_);
lean_dec(v___x_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(lean_object* v_pat_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___f_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = lean_string_utf8_byte_size(v_pat_840_);
lean_inc_ref(v_pat_840_);
v___f_843_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_843_, 0, v___x_842_);
lean_closure_set(v___f_843_, 1, v_pat_840_);
lean_closure_set(v___f_843_, 2, v___x_841_);
v___x_844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_844_, 0, v_pat_840_);
lean_ctor_set(v___x_844_, 1, v___x_841_);
lean_ctor_set(v___x_844_, 2, v___x_842_);
lean_inc_ref(v___x_844_);
v___x_845_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_845_, 0, v___x_844_);
v___x_846_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_846_, 0, v___x_844_);
v___x_847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___f_843_);
lean_ctor_set(v___x_847_, 2, v___x_846_);
return v___x_847_;
}
}
lean_object* runtime_initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Pattern_Memcmp(builtin);
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
lean_object* initialize_Init_Data_String_Pattern_Memcmp(uint8_t builtin);
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
res = initialize_Init_Data_String_Pattern_Memcmp(builtin);
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
