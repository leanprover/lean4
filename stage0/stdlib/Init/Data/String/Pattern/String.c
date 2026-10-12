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
lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(lean_object* v_pat_1_, uint8_t v_patByte_2_, lean_object* v_table_3_, lean_object* v_guess_4_){
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
LEAN_EXPORT void l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_pat_1_ = stack[0].m_obj;
uint8_t v_patByte_2_ = stack[1].m_num;
lean_object* v_table_3_ = stack[2].m_obj;
lean_object* v_guess_4_ = stack[3].m_obj;
lean_object* v_res_18_;
v_res_18_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_1_, v_patByte_2_, v_table_3_, v_guess_4_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg___boxed(lean_object* v_pat_19_, lean_object* v_patByte_20_, lean_object* v_table_21_, lean_object* v_guess_22_){
_start:
{
uint8_t v_patByte_boxed_23_; lean_object* v_res_24_; 
v_patByte_boxed_23_ = lean_unbox(v_patByte_20_);
v_res_24_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_19_, v_patByte_boxed_23_, v_table_21_, v_guess_22_);
lean_dec(v_guess_22_);
lean_dec_ref(v_table_21_);
lean_dec_ref(v_pat_19_);
return v_res_24_;
}
}
lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(lean_object* v_pat_25_, uint8_t v_patByte_26_, lean_object* v_table_27_, lean_object* v_ht_28_, lean_object* v_h_29_, lean_object* v_guess_30_, lean_object* v_hg_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_25_, v_patByte_26_, v_table_27_, v_guess_30_);
return v___x_32_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance_0interp(lean_interpreter_value* stack)
{
lean_object* v_pat_25_ = stack[0].m_obj;
uint8_t v_patByte_26_ = stack[1].m_num;
lean_object* v_table_27_ = stack[2].m_obj;
lean_object* v_guess_30_ = stack[5].m_obj;
lean_object* v_res_33_;
v_res_33_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(v_pat_25_, v_patByte_26_, v_table_27_, lean_box(0), lean_box(0), v_guess_30_, lean_box(0));
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___boxed(lean_object* v_pat_34_, lean_object* v_patByte_35_, lean_object* v_table_36_, lean_object* v_ht_37_, lean_object* v_h_38_, lean_object* v_guess_39_, lean_object* v_hg_40_){
_start:
{
uint8_t v_patByte_boxed_41_; lean_object* v_res_42_; 
v_patByte_boxed_41_ = lean_unbox(v_patByte_35_);
v_res_42_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(v_pat_34_, v_patByte_boxed_41_, v_table_36_, v_ht_37_, v_h_38_, v_guess_39_, v_hg_40_);
lean_dec(v_guess_39_);
lean_dec_ref(v_table_36_);
lean_dec_ref(v_pat_34_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(lean_object* v_pat_43_, lean_object* v_table_44_){
_start:
{
lean_object* v_str_45_; lean_object* v_startInclusive_46_; lean_object* v_endExclusive_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v_str_45_ = lean_ctor_get(v_pat_43_, 0);
v_startInclusive_46_ = lean_ctor_get(v_pat_43_, 1);
v_endExclusive_47_ = lean_ctor_get(v_pat_43_, 2);
v___x_48_ = lean_array_get_size(v_table_44_);
v___x_49_ = lean_nat_sub(v_endExclusive_47_, v_startInclusive_46_);
v___x_50_ = lean_nat_dec_lt(v___x_48_, v___x_49_);
lean_dec(v___x_49_);
if (v___x_50_ == 0)
{
return v_table_44_;
}
else
{
lean_object* v___x_51_; uint8_t v_patByte_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v_dist_56_; lean_object* v___x_57_; 
v___x_51_ = lean_nat_add(v_startInclusive_46_, v___x_48_);
v_patByte_52_ = lean_string_get_byte_fast(v_str_45_, v___x_51_);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_sub(v___x_48_, v___x_53_);
v___x_55_ = lean_array_fget_borrowed(v_table_44_, v___x_54_);
lean_dec(v___x_54_);
v_dist_56_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_43_, v_patByte_52_, v_table_44_, v___x_55_);
v___x_57_ = lean_array_push(v_table_44_, v_dist_56_);
v_table_44_ = v___x_57_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg___boxed(lean_object* v_pat_59_, lean_object* v_table_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_59_, v_table_60_);
lean_dec_ref(v_pat_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(lean_object* v_pat_62_, lean_object* v_table_63_, lean_object* v_ht_u2080_64_, lean_object* v_ht_65_, lean_object* v_h_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_62_, v_table_63_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___boxed(lean_object* v_pat_68_, lean_object* v_table_69_, lean_object* v_ht_u2080_70_, lean_object* v_ht_71_, lean_object* v_h_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(v_pat_68_, v_table_69_, v_ht_u2080_70_, v_ht_71_, v_h_72_);
lean_dec_ref(v_pat_68_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object* v_pat_76_){
_start:
{
lean_object* v_startInclusive_77_; lean_object* v_endExclusive_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_startInclusive_77_ = lean_ctor_get(v_pat_76_, 1);
v_endExclusive_78_ = lean_ctor_get(v_pat_76_, 2);
v___x_79_ = lean_nat_sub(v_endExclusive_78_, v_startInclusive_77_);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_nat_dec_eq(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v_arr_82_; lean_object* v_arr_x27_83_; lean_object* v___x_84_; 
v_arr_82_ = lean_mk_empty_array_with_capacity(v___x_79_);
lean_dec(v___x_79_);
v_arr_x27_83_ = lean_array_push(v_arr_82_, v___x_80_);
v___x_84_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_76_, v_arr_x27_83_);
return v___x_84_;
}
else
{
lean_object* v___x_85_; 
lean_dec(v___x_79_);
v___x_85_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0));
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___boxed(lean_object* v_pat_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_86_);
lean_dec_ref(v_pat_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___redArg(lean_object* v_x_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_tag_nat(v_x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___redArg___boxed(lean_object* v_x_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___redArg(v_x_90_);
lean_dec(v_x_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl(lean_object* v_s_92_, lean_object* v_x_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_tag_nat(v_x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl___boxed(lean_object* v_s_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___impl(v_s_95_, v_x_96_);
lean_dec(v_x_96_);
lean_dec_ref(v_s_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(lean_object* v_t_98_, lean_object* v_k_99_){
_start:
{
switch(lean_obj_tag(v_t_98_))
{
case 0:
{
lean_object* v_pos_100_; lean_object* v___x_101_; 
v_pos_100_ = lean_ctor_get(v_t_98_, 0);
lean_inc(v_pos_100_);
lean_dec_ref_known(v_t_98_, 1);
v___x_101_ = lean_apply_1(v_k_99_, v_pos_100_);
return v___x_101_;
}
case 1:
{
lean_object* v_pos_102_; lean_object* v___x_103_; 
v_pos_102_ = lean_ctor_get(v_t_98_, 0);
lean_inc(v_pos_102_);
lean_dec_ref_known(v_t_98_, 1);
v___x_103_ = lean_apply_2(v_k_99_, v_pos_102_, lean_box(0));
return v___x_103_;
}
case 2:
{
lean_object* v_needle_104_; lean_object* v_table_105_; lean_object* v_stackPos_106_; lean_object* v_needlePos_107_; lean_object* v___x_108_; 
v_needle_104_ = lean_ctor_get(v_t_98_, 0);
lean_inc_ref(v_needle_104_);
v_table_105_ = lean_ctor_get(v_t_98_, 1);
lean_inc_ref(v_table_105_);
v_stackPos_106_ = lean_ctor_get(v_t_98_, 2);
lean_inc(v_stackPos_106_);
v_needlePos_107_ = lean_ctor_get(v_t_98_, 3);
lean_inc(v_needlePos_107_);
lean_dec_ref_known(v_t_98_, 4);
v___x_108_ = lean_apply_6(v_k_99_, v_needle_104_, v_table_105_, lean_box(0), v_stackPos_106_, v_needlePos_107_, lean_box(0));
return v___x_108_;
}
default: 
{
return v_k_99_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(lean_object* v_s_109_, lean_object* v_motive_110_, lean_object* v_ctorIdx_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_k_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_112_, v_k_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___boxed(lean_object* v_s_116_, lean_object* v_motive_117_, lean_object* v_ctorIdx_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_k_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(v_s_116_, v_motive_117_, v_ctorIdx_118_, v_t_119_, v_h_120_, v_k_121_);
lean_dec(v_ctorIdx_118_);
lean_dec_ref(v_s_116_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___redArg(lean_object* v_t_123_, lean_object* v_emptyBefore_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_123_, v_emptyBefore_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(lean_object* v_s_126_, lean_object* v_motive_127_, lean_object* v_t_128_, lean_object* v_h_129_, lean_object* v_emptyBefore_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_128_, v_emptyBefore_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___boxed(lean_object* v_s_132_, lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_emptyBefore_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(v_s_132_, v_motive_133_, v_t_134_, v_h_135_, v_emptyBefore_136_);
lean_dec_ref(v_s_132_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___redArg(lean_object* v_t_138_, lean_object* v_emptyAt_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_138_, v_emptyAt_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(lean_object* v_s_141_, lean_object* v_motive_142_, lean_object* v_t_143_, lean_object* v_h_144_, lean_object* v_emptyAt_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_143_, v_emptyAt_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___boxed(lean_object* v_s_147_, lean_object* v_motive_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_emptyAt_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(v_s_147_, v_motive_148_, v_t_149_, v_h_150_, v_emptyAt_151_);
lean_dec_ref(v_s_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___redArg(lean_object* v_t_153_, lean_object* v_proper_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_153_, v_proper_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(lean_object* v_s_156_, lean_object* v_motive_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_proper_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_158_, v_proper_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___boxed(lean_object* v_s_162_, lean_object* v_motive_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_proper_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(v_s_162_, v_motive_163_, v_t_164_, v_h_165_, v_proper_166_);
lean_dec_ref(v_s_162_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___redArg(lean_object* v_t_168_, lean_object* v_atEnd_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_168_, v_atEnd_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(lean_object* v_s_171_, lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_atEnd_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_173_, v_atEnd_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___boxed(lean_object* v_s_177_, lean_object* v_motive_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_atEnd_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(v_s_177_, v_motive_178_, v_t_179_, v_h_180_, v_atEnd_181_);
lean_dec_ref(v_s_177_);
return v_res_182_;
}
}
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg(){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0));
return v___x_186_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_187_;
v_res_187_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg();
stack->m_obj
 = v_res_187_;
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
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg(){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0, &l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_once, _init_l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0);
return v___x_196_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_197_;
v_res_197_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg();
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg___boxed(lean_object* v___dummy_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___redArg();
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(lean_object* v_a_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_obj_once(&l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0, &l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_once, _init_l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___boxed(lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(v_a_202_);
lean_dec_ref(v_a_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___redArg(lean_object* v_pat_204_){
_start:
{
lean_object* v_startInclusive_205_; lean_object* v_endExclusive_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_startInclusive_205_ = lean_ctor_get(v_pat_204_, 1);
v_endExclusive_206_ = lean_ctor_get(v_pat_204_, 2);
v___x_207_ = lean_nat_sub(v_endExclusive_206_, v_startInclusive_205_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_nat_dec_eq(v___x_207_, v___x_208_);
lean_dec(v___x_207_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_204_);
v___x_211_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_211_, 0, v_pat_204_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
lean_ctor_set(v___x_211_, 2, v___x_208_);
lean_ctor_set(v___x_211_, 3, v___x_208_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; 
lean_dec_ref(v_pat_204_);
v___x_212_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0));
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter(lean_object* v_pat_213_, lean_object* v_s_214_){
_start:
{
lean_object* v_startInclusive_215_; lean_object* v_endExclusive_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_startInclusive_215_ = lean_ctor_get(v_pat_213_, 1);
v_endExclusive_216_ = lean_ctor_get(v_pat_213_, 2);
v___x_217_ = lean_nat_sub(v_endExclusive_216_, v_startInclusive_215_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_nat_dec_eq(v___x_217_, v___x_218_);
lean_dec(v___x_217_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_213_);
v___x_221_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_221_, 0, v_pat_213_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
lean_ctor_set(v___x_221_, 2, v___x_218_);
lean_ctor_set(v___x_221_, 3, v___x_218_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; 
lean_dec_ref(v_pat_213_);
v___x_222_ = ((lean_object*)(l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___redArg___closed__0));
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed(lean_object* v_pat_223_, lean_object* v_s_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_String_Slice_Pattern_ForwardSliceSearcher_iter(v_pat_223_, v_s_224_);
lean_dec_ref(v_s_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(lean_object* v_s_226_, lean_object* v_x_227_){
_start:
{
switch(lean_obj_tag(v_x_227_))
{
case 0:
{
lean_object* v_pos_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_243_; 
v_pos_228_ = lean_ctor_get(v_x_227_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_243_ == 0)
{
v___x_230_ = v_x_227_;
v_isShared_231_ = v_isSharedCheck_243_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_pos_228_);
lean_dec(v_x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_243_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_res_232_; lean_object* v_startInclusive_233_; lean_object* v_endExclusive_234_; lean_object* v___x_235_; uint8_t v_decide_236_; 
lean_inc_n(v_pos_228_, 2);
v_res_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_232_, 0, v_pos_228_);
lean_ctor_set(v_res_232_, 1, v_pos_228_);
v_startInclusive_233_ = lean_ctor_get(v_s_226_, 1);
v_endExclusive_234_ = lean_ctor_get(v_s_226_, 2);
v___x_235_ = lean_nat_sub(v_endExclusive_234_, v_startInclusive_233_);
v_decide_236_ = lean_nat_dec_eq(v_pos_228_, v___x_235_);
lean_dec(v___x_235_);
if (v_decide_236_ == 0)
{
lean_object* v___x_238_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 1);
v___x_238_ = v___x_230_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_pos_228_);
v___x_238_ = v_reuseFailAlloc_240_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_res_232_);
return v___x_239_;
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_del_object(v___x_230_);
lean_dec(v_pos_228_);
v___x_241_ = lean_box(3);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_res_232_);
return v___x_242_;
}
}
}
case 1:
{
lean_object* v_pos_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_258_; 
v_pos_244_ = lean_ctor_get(v_x_227_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_258_ == 0)
{
v___x_246_ = v_x_227_;
v_isShared_247_ = v_isSharedCheck_258_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_pos_244_);
lean_dec(v_x_227_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_258_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_str_248_; lean_object* v_startInclusive_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_res_253_; lean_object* v___x_255_; 
v_str_248_ = lean_ctor_get(v_s_226_, 0);
v_startInclusive_249_ = lean_ctor_get(v_s_226_, 1);
v___x_250_ = lean_nat_add(v_startInclusive_249_, v_pos_244_);
v___x_251_ = lean_string_utf8_next_fast(v_str_248_, v___x_250_);
lean_dec(v___x_250_);
v___x_252_ = lean_nat_sub(v___x_251_, v_startInclusive_249_);
lean_inc(v___x_252_);
v_res_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_253_, 0, v_pos_244_);
lean_ctor_set(v_res_253_, 1, v___x_252_);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
lean_ctor_set(v___x_246_, 0, v___x_252_);
v___x_255_ = v___x_246_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_252_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_res_253_);
return v___x_256_;
}
}
}
case 2:
{
lean_object* v_needle_259_; lean_object* v_table_260_; lean_object* v_stackPos_261_; lean_object* v_needlePos_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_337_; 
v_needle_259_ = lean_ctor_get(v_x_227_, 0);
v_table_260_ = lean_ctor_get(v_x_227_, 1);
v_stackPos_261_ = lean_ctor_get(v_x_227_, 2);
v_needlePos_262_ = lean_ctor_get(v_x_227_, 3);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_337_ == 0)
{
v___x_264_ = v_x_227_;
v_isShared_265_ = v_isSharedCheck_337_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_needlePos_262_);
lean_inc(v_stackPos_261_);
lean_inc(v_table_260_);
lean_inc(v_needle_259_);
lean_dec(v_x_227_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_337_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v_str_266_; lean_object* v_startInclusive_267_; lean_object* v_endExclusive_268_; lean_object* v_str_269_; lean_object* v_startInclusive_270_; lean_object* v_endExclusive_271_; lean_object* v_basePos_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_str_266_ = lean_ctor_get(v_needle_259_, 0);
v_startInclusive_267_ = lean_ctor_get(v_needle_259_, 1);
v_endExclusive_268_ = lean_ctor_get(v_needle_259_, 2);
v_str_269_ = lean_ctor_get(v_s_226_, 0);
v_startInclusive_270_ = lean_ctor_get(v_s_226_, 1);
v_endExclusive_271_ = lean_ctor_get(v_s_226_, 2);
v_basePos_272_ = lean_nat_sub(v_stackPos_261_, v_needlePos_262_);
v___x_273_ = lean_nat_sub(v_endExclusive_268_, v_startInclusive_267_);
v___x_274_ = lean_nat_add(v_basePos_272_, v___x_273_);
v___x_275_ = lean_nat_sub(v_endExclusive_271_, v_startInclusive_270_);
v___x_276_ = lean_nat_dec_le(v___x_274_, v___x_275_);
lean_dec(v___x_274_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
lean_dec(v___x_273_);
lean_del_object(v___x_264_);
lean_dec(v_needlePos_262_);
lean_dec(v_stackPos_261_);
lean_dec_ref(v_table_260_);
lean_dec_ref(v_needle_259_);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_add(v_basePos_272_, v___x_277_);
v___x_279_ = lean_nat_dec_le(v___x_278_, v___x_275_);
lean_dec(v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
lean_dec(v___x_275_);
lean_dec(v_basePos_272_);
v___x_280_ = lean_box(2);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v_res_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_281_ = l_String_Slice_pos_x21(v_s_226_, v_basePos_272_);
lean_dec(v_basePos_272_);
v_res_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_282_, 0, v___x_281_);
lean_ctor_set(v_res_282_, 1, v___x_275_);
v___x_283_ = lean_box(3);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_res_282_);
return v___x_284_;
}
}
else
{
lean_object* v___x_285_; uint8_t v_stackByte_286_; lean_object* v___x_287_; uint8_t v_patByte_288_; uint8_t v___x_289_; 
lean_dec(v___x_275_);
v___x_285_ = lean_nat_add(v_startInclusive_270_, v_stackPos_261_);
v_stackByte_286_ = lean_string_get_byte_fast(v_str_269_, v___x_285_);
v___x_287_ = lean_nat_add(v_startInclusive_267_, v_needlePos_262_);
v_patByte_288_ = lean_string_get_byte_fast(v_str_266_, v___x_287_);
v___x_289_ = lean_uint8_dec_eq(v_stackByte_286_, v_patByte_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; uint8_t v_decide_291_; 
lean_dec(v___x_273_);
v___x_290_ = lean_unsigned_to_nat(0u);
v_decide_291_ = lean_nat_dec_eq(v_needlePos_262_, v___x_290_);
if (v_decide_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_newNeedlePos_294_; uint8_t v___x_295_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_sub(v_needlePos_262_, v___x_292_);
lean_dec(v_needlePos_262_);
v_newNeedlePos_294_ = lean_array_fget_borrowed(v_table_260_, v___x_293_);
lean_dec(v___x_293_);
v___x_295_ = lean_nat_dec_eq(v_newNeedlePos_294_, v___x_290_);
if (v___x_295_ == 0)
{
lean_object* v_oldBasePos_296_; lean_object* v___x_297_; lean_object* v_newBasePos_298_; lean_object* v_res_299_; lean_object* v___x_301_; 
lean_inc(v_newNeedlePos_294_);
v_oldBasePos_296_ = l_String_Slice_pos_x21(v_s_226_, v_basePos_272_);
lean_dec(v_basePos_272_);
v___x_297_ = lean_nat_sub(v_stackPos_261_, v_newNeedlePos_294_);
v_newBasePos_298_ = l_String_Slice_pos_x21(v_s_226_, v___x_297_);
lean_dec(v___x_297_);
v_res_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_299_, 0, v_oldBasePos_296_);
lean_ctor_set(v_res_299_, 1, v_newBasePos_298_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 3, v_newNeedlePos_294_);
v___x_301_ = v___x_264_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_needle_259_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_table_260_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_stackPos_261_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_newNeedlePos_294_);
v___x_301_ = v_reuseFailAlloc_303_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; 
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v_res_299_);
return v___x_302_;
}
}
else
{
lean_object* v_basePos_304_; lean_object* v_nextStackPos_305_; lean_object* v_res_306_; lean_object* v___x_308_; 
v_basePos_304_ = l_String_Slice_pos_x21(v_s_226_, v_basePos_272_);
lean_dec(v_basePos_272_);
v_nextStackPos_305_ = l_String_Slice_posGE___redArg(v_s_226_, v_stackPos_261_);
lean_inc(v_nextStackPos_305_);
v_res_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_306_, 0, v_basePos_304_);
lean_ctor_set(v_res_306_, 1, v_nextStackPos_305_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 3, v___x_290_);
lean_ctor_set(v___x_264_, 2, v_nextStackPos_305_);
v___x_308_ = v___x_264_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_needle_259_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_table_260_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_nextStackPos_305_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v___x_290_);
v___x_308_ = v_reuseFailAlloc_310_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_res_306_);
return v___x_309_;
}
}
}
else
{
lean_object* v_basePos_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_nextStackPos_314_; lean_object* v_res_315_; lean_object* v___x_317_; 
lean_dec(v_basePos_272_);
lean_dec(v_needlePos_262_);
v_basePos_311_ = l_String_Slice_pos_x21(v_s_226_, v_stackPos_261_);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_stackPos_261_, v___x_312_);
lean_dec(v_stackPos_261_);
v_nextStackPos_314_ = l_String_Slice_posGE___redArg(v_s_226_, v___x_313_);
lean_inc(v_nextStackPos_314_);
v_res_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_315_, 0, v_basePos_311_);
lean_ctor_set(v_res_315_, 1, v_nextStackPos_314_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 3, v___x_290_);
lean_ctor_set(v___x_264_, 2, v_nextStackPos_314_);
v___x_317_ = v___x_264_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_needle_259_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_table_260_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_nextStackPos_314_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v___x_290_);
v___x_317_ = v_reuseFailAlloc_319_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; 
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_res_315_);
return v___x_318_;
}
}
}
else
{
lean_object* v___x_320_; lean_object* v_nextStackPos_321_; lean_object* v_nextNeedlePos_322_; uint8_t v_decide_323_; 
lean_dec(v_basePos_272_);
v___x_320_ = lean_unsigned_to_nat(1u);
v_nextStackPos_321_ = lean_nat_add(v_stackPos_261_, v___x_320_);
lean_dec(v_stackPos_261_);
v_nextNeedlePos_322_ = lean_nat_add(v_needlePos_262_, v___x_320_);
lean_dec(v_needlePos_262_);
v_decide_323_ = lean_nat_dec_eq(v_nextNeedlePos_322_, v___x_273_);
lean_dec(v___x_273_);
if (v_decide_323_ == 0)
{
lean_object* v___x_325_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 3, v_nextNeedlePos_322_);
lean_ctor_set(v___x_264_, 2, v_nextStackPos_321_);
v___x_325_ = v___x_264_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_needle_259_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_table_260_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_nextStackPos_321_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_nextNeedlePos_322_);
v___x_325_ = v_reuseFailAlloc_327_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; 
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_res_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_328_ = lean_nat_sub(v_nextStackPos_321_, v_nextNeedlePos_322_);
lean_dec(v_nextNeedlePos_322_);
v___x_329_ = l_String_Slice_pos_x21(v_s_226_, v___x_328_);
lean_dec(v___x_328_);
v___x_330_ = l_String_Slice_pos_x21(v_s_226_, v_nextStackPos_321_);
v_res_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_331_, 0, v___x_329_);
lean_ctor_set(v_res_331_, 1, v___x_330_);
v___x_332_ = lean_unsigned_to_nat(0u);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 3, v___x_332_);
lean_ctor_set(v___x_264_, 2, v_nextStackPos_321_);
v___x_334_ = v___x_264_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_needle_259_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_table_260_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_nextStackPos_321_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v___x_332_);
v___x_334_ = v_reuseFailAlloc_336_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_res_331_);
return v___x_335_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_338_; 
v___x_338_ = lean_box(2);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed(lean_object* v_s_339_, lean_object* v_x_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(v_s_339_, v_x_340_);
lean_dec_ref(v_s_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep(lean_object* v_s_342_){
_start:
{
lean_object* v___f_343_; 
v___f_343_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed), 2, 1);
lean_closure_set(v___f_343_, 0, v_s_342_);
return v___f_343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(lean_object* v_s_344_, lean_object* v_x_345_){
_start:
{
switch(lean_obj_tag(v_x_345_))
{
case 0:
{
lean_object* v_pos_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_356_; 
v_pos_346_ = lean_ctor_get(v_x_345_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_345_);
if (v_isSharedCheck_356_ == 0)
{
v___x_348_ = v_x_345_;
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_pos_346_);
lean_dec(v_x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_350_ = l_String_Slice_Pos_remainingBytes(v_s_344_, v_pos_346_);
lean_dec(v_pos_346_);
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 1);
lean_ctor_set(v___x_348_, 0, v___x_352_);
v___x_354_ = v___x_348_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
case 1:
{
lean_object* v_pos_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_367_; 
v_pos_357_ = lean_ctor_get(v_x_345_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_345_);
if (v_isSharedCheck_367_ == 0)
{
v___x_359_ = v_x_345_;
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_pos_357_);
lean_dec(v_x_345_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_361_ = l_String_Slice_Pos_remainingBytes(v_s_344_, v_pos_357_);
lean_dec(v_pos_357_);
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_363_);
v___x_365_ = v___x_359_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
case 2:
{
lean_object* v_stackPos_368_; lean_object* v_needlePos_369_; lean_object* v_startInclusive_370_; lean_object* v_endExclusive_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_stackPos_368_ = lean_ctor_get(v_x_345_, 2);
lean_inc(v_stackPos_368_);
v_needlePos_369_ = lean_ctor_get(v_x_345_, 3);
lean_inc(v_needlePos_369_);
lean_dec_ref_known(v_x_345_, 4);
v_startInclusive_370_ = lean_ctor_get(v_s_344_, 1);
v_endExclusive_371_ = lean_ctor_get(v_s_344_, 2);
v___x_372_ = lean_nat_sub(v_endExclusive_371_, v_startInclusive_370_);
v___x_373_ = lean_nat_sub(v___x_372_, v_stackPos_368_);
lean_dec(v_stackPos_368_);
lean_dec(v___x_372_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v_needlePos_369_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
default: 
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption___boxed(lean_object* v_s_377_, lean_object* v_x_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(v_s_377_, v_x_378_);
lean_dec_ref(v_s_377_);
return v_res_379_;
}
}
lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
return v___x_381_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_382_;
v_res_382_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg();
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___redArg();
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(lean_object* v_s_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_box(0);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(lean_object* v_s_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(v_s_387_);
lean_dec_ref(v_s_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(lean_object* v_x_389_, lean_object* v_h__1_390_, lean_object* v_h__2_391_, lean_object* v_h__3_392_, lean_object* v_h__4_393_){
_start:
{
switch(lean_obj_tag(v_x_389_))
{
case 0:
{
lean_object* v_pos_394_; lean_object* v___x_395_; 
lean_dec(v_h__4_393_);
lean_dec(v_h__3_392_);
lean_dec(v_h__2_391_);
v_pos_394_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_pos_394_);
lean_dec_ref_known(v_x_389_, 1);
v___x_395_ = lean_apply_1(v_h__1_390_, v_pos_394_);
return v___x_395_;
}
case 1:
{
lean_object* v_pos_396_; lean_object* v___x_397_; 
lean_dec(v_h__4_393_);
lean_dec(v_h__3_392_);
lean_dec(v_h__1_390_);
v_pos_396_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_pos_396_);
lean_dec_ref_known(v_x_389_, 1);
v___x_397_ = lean_apply_2(v_h__2_391_, v_pos_396_, lean_box(0));
return v___x_397_;
}
case 2:
{
lean_object* v_needle_398_; lean_object* v_table_399_; lean_object* v_stackPos_400_; lean_object* v_needlePos_401_; lean_object* v___x_402_; 
lean_dec(v_h__4_393_);
lean_dec(v_h__2_391_);
lean_dec(v_h__1_390_);
v_needle_398_ = lean_ctor_get(v_x_389_, 0);
lean_inc_ref(v_needle_398_);
v_table_399_ = lean_ctor_get(v_x_389_, 1);
lean_inc_ref(v_table_399_);
v_stackPos_400_ = lean_ctor_get(v_x_389_, 2);
lean_inc(v_stackPos_400_);
v_needlePos_401_ = lean_ctor_get(v_x_389_, 3);
lean_inc(v_needlePos_401_);
lean_dec_ref_known(v_x_389_, 4);
v___x_402_ = lean_apply_6(v_h__3_392_, v_needle_398_, v_table_399_, lean_box(0), v_stackPos_400_, v_needlePos_401_, lean_box(0));
return v___x_402_;
}
default: 
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_h__3_392_);
lean_dec(v_h__2_391_);
lean_dec(v_h__1_390_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_apply_1(v_h__4_393_, v___x_403_);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(lean_object* v_s_405_, lean_object* v_motive_406_, lean_object* v_x_407_, lean_object* v_h__1_408_, lean_object* v_h__2_409_, lean_object* v_h__3_410_, lean_object* v_h__4_411_){
_start:
{
switch(lean_obj_tag(v_x_407_))
{
case 0:
{
lean_object* v_pos_412_; lean_object* v___x_413_; 
lean_dec(v_h__4_411_);
lean_dec(v_h__3_410_);
lean_dec(v_h__2_409_);
v_pos_412_ = lean_ctor_get(v_x_407_, 0);
lean_inc(v_pos_412_);
lean_dec_ref_known(v_x_407_, 1);
v___x_413_ = lean_apply_1(v_h__1_408_, v_pos_412_);
return v___x_413_;
}
case 1:
{
lean_object* v_pos_414_; lean_object* v___x_415_; 
lean_dec(v_h__4_411_);
lean_dec(v_h__3_410_);
lean_dec(v_h__1_408_);
v_pos_414_ = lean_ctor_get(v_x_407_, 0);
lean_inc(v_pos_414_);
lean_dec_ref_known(v_x_407_, 1);
v___x_415_ = lean_apply_2(v_h__2_409_, v_pos_414_, lean_box(0));
return v___x_415_;
}
case 2:
{
lean_object* v_needle_416_; lean_object* v_table_417_; lean_object* v_stackPos_418_; lean_object* v_needlePos_419_; lean_object* v___x_420_; 
lean_dec(v_h__4_411_);
lean_dec(v_h__2_409_);
lean_dec(v_h__1_408_);
v_needle_416_ = lean_ctor_get(v_x_407_, 0);
lean_inc_ref(v_needle_416_);
v_table_417_ = lean_ctor_get(v_x_407_, 1);
lean_inc_ref(v_table_417_);
v_stackPos_418_ = lean_ctor_get(v_x_407_, 2);
lean_inc(v_stackPos_418_);
v_needlePos_419_ = lean_ctor_get(v_x_407_, 3);
lean_inc(v_needlePos_419_);
lean_dec_ref_known(v_x_407_, 4);
v___x_420_ = lean_apply_6(v_h__3_410_, v_needle_416_, v_table_417_, lean_box(0), v_stackPos_418_, v_needlePos_419_, lean_box(0));
return v___x_420_;
}
default: 
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v_h__3_410_);
lean_dec(v_h__2_409_);
lean_dec(v_h__1_408_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_apply_1(v_h__4_411_, v___x_421_);
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(lean_object* v_s_423_, lean_object* v_motive_424_, lean_object* v_x_425_, lean_object* v_h__1_426_, lean_object* v_h__2_427_, lean_object* v_h__3_428_, lean_object* v_h__4_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(v_s_423_, v_motive_424_, v_x_425_, v_h__1_426_, v_h__2_427_, v_h__3_428_, v_h__4_429_);
lean_dec_ref(v_s_423_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___redArg(lean_object* v_x_431_, lean_object* v_h__1_432_, lean_object* v_h__2_433_, lean_object* v_h__3_434_){
_start:
{
switch(lean_obj_tag(v_x_431_))
{
case 0:
{
lean_object* v_it_435_; lean_object* v_out_436_; lean_object* v___x_437_; 
lean_dec(v_h__3_434_);
lean_dec(v_h__2_433_);
v_it_435_ = lean_ctor_get(v_x_431_, 0);
lean_inc(v_it_435_);
v_out_436_ = lean_ctor_get(v_x_431_, 1);
lean_inc(v_out_436_);
lean_dec_ref_known(v_x_431_, 2);
v___x_437_ = lean_apply_2(v_h__1_432_, v_it_435_, v_out_436_);
return v___x_437_;
}
case 1:
{
lean_object* v_it_438_; lean_object* v___x_439_; 
lean_dec(v_h__3_434_);
lean_dec(v_h__1_432_);
v_it_438_ = lean_ctor_get(v_x_431_, 0);
lean_inc(v_it_438_);
lean_dec_ref_known(v_x_431_, 1);
v___x_439_ = lean_apply_1(v_h__2_433_, v_it_438_);
return v___x_439_;
}
default: 
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v_h__2_433_);
lean_dec(v_h__1_432_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_apply_1(v_h__3_434_, v___x_440_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(lean_object* v_s_442_, lean_object* v_motive_443_, lean_object* v_x_444_, lean_object* v_h__1_445_, lean_object* v_h__2_446_, lean_object* v_h__3_447_){
_start:
{
switch(lean_obj_tag(v_x_444_))
{
case 0:
{
lean_object* v_it_448_; lean_object* v_out_449_; lean_object* v___x_450_; 
lean_dec(v_h__3_447_);
lean_dec(v_h__2_446_);
v_it_448_ = lean_ctor_get(v_x_444_, 0);
lean_inc(v_it_448_);
v_out_449_ = lean_ctor_get(v_x_444_, 1);
lean_inc(v_out_449_);
lean_dec_ref_known(v_x_444_, 2);
v___x_450_ = lean_apply_2(v_h__1_445_, v_it_448_, v_out_449_);
return v___x_450_;
}
case 1:
{
lean_object* v_it_451_; lean_object* v___x_452_; 
lean_dec(v_h__3_447_);
lean_dec(v_h__1_445_);
v_it_451_ = lean_ctor_get(v_x_444_, 0);
lean_inc(v_it_451_);
lean_dec_ref_known(v_x_444_, 1);
v___x_452_ = lean_apply_1(v_h__2_446_, v_it_451_);
return v___x_452_;
}
default: 
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v_h__2_446_);
lean_dec(v_h__1_445_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_apply_1(v_h__3_447_, v___x_453_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___boxed(lean_object* v_s_455_, lean_object* v_motive_456_, lean_object* v_x_457_, lean_object* v_h__1_458_, lean_object* v_h__2_459_, lean_object* v_h__3_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(v_s_455_, v_motive_456_, v_x_457_, v_h__1_458_, v_h__2_459_, v_h__3_460_);
lean_dec_ref(v_s_455_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__Option_lt_match__1_splitter___redArg(lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_h__1_464_, lean_object* v_h__2_465_, lean_object* v_h__3_466_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_dec(v_h__2_465_);
if (lean_obj_tag(v_x_463_) == 1)
{
lean_object* v_val_467_; lean_object* v___x_468_; 
lean_dec(v_h__3_466_);
v_val_467_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v_x_463_, 1);
v___x_468_ = lean_apply_1(v_h__1_464_, v_val_467_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v_h__1_464_);
v___x_469_ = lean_apply_4(v_h__3_466_, v_x_462_, v_x_463_, lean_box(0), lean_box(0));
return v___x_469_;
}
}
else
{
lean_dec(v_h__1_464_);
if (lean_obj_tag(v_x_463_) == 1)
{
lean_object* v_val_470_; lean_object* v_val_471_; lean_object* v___x_472_; 
lean_dec(v_h__3_466_);
v_val_470_ = lean_ctor_get(v_x_462_, 0);
lean_inc(v_val_470_);
lean_dec_ref_known(v_x_462_, 1);
v_val_471_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v_x_463_, 1);
v___x_472_ = lean_apply_2(v_h__2_465_, v_val_470_, v_val_471_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; 
lean_dec(v_h__2_465_);
v___x_473_ = lean_apply_4(v_h__3_466_, v_x_462_, v_x_463_, lean_box(0), lean_box(0));
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__Option_lt_match__1_splitter(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_motive_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_h__1_479_, lean_object* v_h__2_480_, lean_object* v_h__3_481_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_dec(v_h__2_480_);
if (lean_obj_tag(v_x_478_) == 1)
{
lean_object* v_val_482_; lean_object* v___x_483_; 
lean_dec(v_h__3_481_);
v_val_482_ = lean_ctor_get(v_x_478_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v_x_478_, 1);
v___x_483_ = lean_apply_1(v_h__1_479_, v_val_482_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; 
lean_dec(v_h__1_479_);
v___x_484_ = lean_apply_4(v_h__3_481_, v_x_477_, v_x_478_, lean_box(0), lean_box(0));
return v___x_484_;
}
}
else
{
lean_dec(v_h__1_479_);
if (lean_obj_tag(v_x_478_) == 1)
{
lean_object* v_val_485_; lean_object* v_val_486_; lean_object* v___x_487_; 
lean_dec(v_h__3_481_);
v_val_485_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_val_485_);
lean_dec_ref_known(v_x_477_, 1);
v_val_486_ = lean_ctor_get(v_x_478_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v_x_478_, 1);
v___x_487_ = lean_apply_2(v_h__2_480_, v_val_485_, v_val_486_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; 
lean_dec(v_h__2_480_);
v___x_488_ = lean_apply_4(v_h__3_481_, v_x_477_, v_x_478_, lean_box(0), lean_box(0));
return v___x_488_;
}
}
}
}
lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = lean_box(0);
return v___x_490_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_491_;
v_res_491_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg();
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg___boxed(lean_object* v___dummy_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___redArg();
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(lean_object* v_s_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_box(0);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(lean_object* v_s_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(v_s_496_);
lean_dec_ref(v_s_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(lean_object* v___y_498_, lean_object* v_acc_499_, lean_object* v_recur_500_, lean_object* v_s_501_){
_start:
{
switch(lean_obj_tag(v_s_501_))
{
case 0:
{
lean_object* v_it_502_; lean_object* v_out_503_; lean_object* v_val_504_; 
v_it_502_ = lean_ctor_get(v_s_501_, 0);
lean_inc(v_it_502_);
v_out_503_ = lean_ctor_get(v_s_501_, 1);
lean_inc(v_out_503_);
lean_dec_ref_known(v_s_501_, 2);
v_val_504_ = lean_apply_3(v___y_498_, v_out_503_, lean_box(0), v_acc_499_);
if (lean_obj_tag(v_val_504_) == 0)
{
lean_object* v_a_505_; 
lean_dec(v_it_502_);
lean_dec(v_recur_500_);
v_a_505_ = lean_ctor_get(v_val_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v_val_504_, 1);
return v_a_505_;
}
else
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v_val_504_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v_val_504_, 1);
v___x_507_ = lean_apply_4(v_recur_500_, v_it_502_, v_a_506_, lean_box(0), lean_box(0));
return v___x_507_;
}
}
case 1:
{
lean_object* v_it_508_; lean_object* v___x_509_; 
lean_dec_ref(v___y_498_);
v_it_508_ = lean_ctor_get(v_s_501_, 0);
lean_inc(v_it_508_);
lean_dec_ref_known(v_s_501_, 1);
v___x_509_ = lean_apply_4(v_recur_500_, v_it_508_, v_acc_499_, lean_box(0), lean_box(0));
return v___x_509_;
}
default: 
{
lean_dec(v_recur_500_);
lean_dec_ref(v___y_498_);
return v_acc_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(lean_object* v___y_510_, lean_object* v_s_511_, lean_object* v_lift_512_, lean_object* v_it_513_, lean_object* v_acc_514_, lean_object* v_hP_515_, lean_object* v_recur_516_){
_start:
{
lean_object* v___f_517_; 
v___f_517_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0), 4, 3);
lean_closure_set(v___f_517_, 0, v___y_510_);
lean_closure_set(v___f_517_, 1, v_acc_514_);
lean_closure_set(v___f_517_, 2, v_recur_516_);
switch(lean_obj_tag(v_it_513_))
{
case 0:
{
lean_object* v_pos_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_535_; 
v_pos_518_ = lean_ctor_get(v_it_513_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_it_513_);
if (v_isSharedCheck_535_ == 0)
{
v___x_520_ = v_it_513_;
v_isShared_521_ = v_isSharedCheck_535_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_pos_518_);
lean_dec(v_it_513_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_535_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_res_522_; lean_object* v_startInclusive_523_; lean_object* v_endExclusive_524_; lean_object* v___x_525_; uint8_t v_decide_526_; 
lean_inc_n(v_pos_518_, 2);
v_res_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_522_, 0, v_pos_518_);
lean_ctor_set(v_res_522_, 1, v_pos_518_);
v_startInclusive_523_ = lean_ctor_get(v_s_511_, 1);
v_endExclusive_524_ = lean_ctor_get(v_s_511_, 2);
v___x_525_ = lean_nat_sub(v_endExclusive_524_, v_startInclusive_523_);
v_decide_526_ = lean_nat_dec_eq(v_pos_518_, v___x_525_);
lean_dec(v___x_525_);
if (v_decide_526_ == 0)
{
lean_object* v___x_528_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 1);
v___x_528_ = v___x_520_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_pos_518_);
v___x_528_ = v_reuseFailAlloc_531_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v_res_522_);
v___x_530_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_529_);
return v___x_530_;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_del_object(v___x_520_);
lean_dec(v_pos_518_);
v___x_532_ = lean_box(3);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_res_522_);
v___x_534_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_533_);
return v___x_534_;
}
}
}
case 1:
{
lean_object* v_pos_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_551_; 
v_pos_536_ = lean_ctor_get(v_it_513_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_it_513_);
if (v_isSharedCheck_551_ == 0)
{
v___x_538_ = v_it_513_;
v_isShared_539_ = v_isSharedCheck_551_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_pos_536_);
lean_dec(v_it_513_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_551_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v_str_540_; lean_object* v_startInclusive_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_res_545_; lean_object* v___x_547_; 
v_str_540_ = lean_ctor_get(v_s_511_, 0);
v_startInclusive_541_ = lean_ctor_get(v_s_511_, 1);
v___x_542_ = lean_nat_add(v_startInclusive_541_, v_pos_536_);
v___x_543_ = lean_string_utf8_next_fast(v_str_540_, v___x_542_);
lean_dec(v___x_542_);
v___x_544_ = lean_nat_sub(v___x_543_, v_startInclusive_541_);
lean_inc(v___x_544_);
v_res_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_545_, 0, v_pos_536_);
lean_ctor_set(v_res_545_, 1, v___x_544_);
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 0);
lean_ctor_set(v___x_538_, 0, v___x_544_);
v___x_547_ = v___x_538_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_544_);
v___x_547_ = v_reuseFailAlloc_550_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_res_545_);
v___x_549_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_548_);
return v___x_549_;
}
}
}
case 2:
{
lean_object* v_needle_552_; lean_object* v_table_553_; lean_object* v_stackPos_554_; lean_object* v_needlePos_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_637_; 
v_needle_552_ = lean_ctor_get(v_it_513_, 0);
v_table_553_ = lean_ctor_get(v_it_513_, 1);
v_stackPos_554_ = lean_ctor_get(v_it_513_, 2);
v_needlePos_555_ = lean_ctor_get(v_it_513_, 3);
v_isSharedCheck_637_ = !lean_is_exclusive(v_it_513_);
if (v_isSharedCheck_637_ == 0)
{
v___x_557_ = v_it_513_;
v_isShared_558_ = v_isSharedCheck_637_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_needlePos_555_);
lean_inc(v_stackPos_554_);
lean_inc(v_table_553_);
lean_inc(v_needle_552_);
lean_dec(v_it_513_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_637_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_str_559_; lean_object* v_startInclusive_560_; lean_object* v_endExclusive_561_; lean_object* v_str_562_; lean_object* v_startInclusive_563_; lean_object* v_endExclusive_564_; lean_object* v_basePos_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_str_559_ = lean_ctor_get(v_needle_552_, 0);
v_startInclusive_560_ = lean_ctor_get(v_needle_552_, 1);
v_endExclusive_561_ = lean_ctor_get(v_needle_552_, 2);
v_str_562_ = lean_ctor_get(v_s_511_, 0);
v_startInclusive_563_ = lean_ctor_get(v_s_511_, 1);
v_endExclusive_564_ = lean_ctor_get(v_s_511_, 2);
v_basePos_565_ = lean_nat_sub(v_stackPos_554_, v_needlePos_555_);
v___x_566_ = lean_nat_sub(v_endExclusive_561_, v_startInclusive_560_);
v___x_567_ = lean_nat_add(v_basePos_565_, v___x_566_);
v___x_568_ = lean_nat_sub(v_endExclusive_564_, v_startInclusive_563_);
v___x_569_ = lean_nat_dec_le(v___x_567_, v___x_568_);
lean_dec(v___x_567_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
lean_dec(v___x_566_);
lean_del_object(v___x_557_);
lean_dec(v_needlePos_555_);
lean_dec(v_stackPos_554_);
lean_dec_ref(v_table_553_);
lean_dec_ref(v_needle_552_);
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_add(v_basePos_565_, v___x_570_);
v___x_572_ = lean_nat_dec_le(v___x_571_, v___x_568_);
lean_dec(v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_568_);
lean_dec(v_basePos_565_);
v___x_573_ = lean_box(2);
v___x_574_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v_res_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_575_ = l_String_Slice_pos_x21(v_s_511_, v_basePos_565_);
lean_dec(v_basePos_565_);
v_res_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_576_, 0, v___x_575_);
lean_ctor_set(v_res_576_, 1, v___x_568_);
v___x_577_ = lean_box(3);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v_res_576_);
v___x_579_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_578_);
return v___x_579_;
}
}
else
{
lean_object* v___x_580_; uint8_t v_stackByte_581_; lean_object* v___x_582_; uint8_t v_patByte_583_; uint8_t v___x_584_; 
lean_dec(v___x_568_);
v___x_580_ = lean_nat_add(v_startInclusive_563_, v_stackPos_554_);
v_stackByte_581_ = lean_string_get_byte_fast(v_str_562_, v___x_580_);
v___x_582_ = lean_nat_add(v_startInclusive_560_, v_needlePos_555_);
v_patByte_583_ = lean_string_get_byte_fast(v_str_559_, v___x_582_);
v___x_584_ = lean_uint8_dec_eq(v_stackByte_581_, v_patByte_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; uint8_t v_decide_586_; 
lean_dec(v___x_566_);
v___x_585_ = lean_unsigned_to_nat(0u);
v_decide_586_ = lean_nat_dec_eq(v_needlePos_555_, v___x_585_);
if (v_decide_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_newNeedlePos_589_; uint8_t v___x_590_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_nat_sub(v_needlePos_555_, v___x_587_);
lean_dec(v_needlePos_555_);
v_newNeedlePos_589_ = lean_array_fget_borrowed(v_table_553_, v___x_588_);
lean_dec(v___x_588_);
v___x_590_ = lean_nat_dec_eq(v_newNeedlePos_589_, v___x_585_);
if (v___x_590_ == 0)
{
lean_object* v_oldBasePos_591_; lean_object* v___x_592_; lean_object* v_newBasePos_593_; lean_object* v_res_594_; lean_object* v___x_596_; 
lean_inc(v_newNeedlePos_589_);
v_oldBasePos_591_ = l_String_Slice_pos_x21(v_s_511_, v_basePos_565_);
lean_dec(v_basePos_565_);
v___x_592_ = lean_nat_sub(v_stackPos_554_, v_newNeedlePos_589_);
v_newBasePos_593_ = l_String_Slice_pos_x21(v_s_511_, v___x_592_);
lean_dec(v___x_592_);
v_res_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_594_, 0, v_oldBasePos_591_);
lean_ctor_set(v_res_594_, 1, v_newBasePos_593_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 3, v_newNeedlePos_589_);
v___x_596_ = v___x_557_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_needle_552_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_table_553_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_stackPos_554_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_newNeedlePos_589_);
v___x_596_ = v_reuseFailAlloc_599_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v_res_594_);
v___x_598_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_597_);
return v___x_598_;
}
}
else
{
lean_object* v_basePos_600_; lean_object* v_nextStackPos_601_; lean_object* v_res_602_; lean_object* v___x_604_; 
v_basePos_600_ = l_String_Slice_pos_x21(v_s_511_, v_basePos_565_);
lean_dec(v_basePos_565_);
v_nextStackPos_601_ = l_String_Slice_posGE___redArg(v_s_511_, v_stackPos_554_);
lean_inc(v_nextStackPos_601_);
v_res_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_602_, 0, v_basePos_600_);
lean_ctor_set(v_res_602_, 1, v_nextStackPos_601_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 3, v___x_585_);
lean_ctor_set(v___x_557_, 2, v_nextStackPos_601_);
v___x_604_ = v___x_557_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_needle_552_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_table_553_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_nextStackPos_601_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v___x_585_);
v___x_604_ = v_reuseFailAlloc_607_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v_res_602_);
v___x_606_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_605_);
return v___x_606_;
}
}
}
else
{
lean_object* v_basePos_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_nextStackPos_611_; lean_object* v_res_612_; lean_object* v___x_614_; 
lean_dec(v_basePos_565_);
lean_dec(v_needlePos_555_);
v_basePos_608_ = l_String_Slice_pos_x21(v_s_511_, v_stackPos_554_);
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_stackPos_554_, v___x_609_);
lean_dec(v_stackPos_554_);
v_nextStackPos_611_ = l_String_Slice_posGE___redArg(v_s_511_, v___x_610_);
lean_inc(v_nextStackPos_611_);
v_res_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_res_612_, 0, v_basePos_608_);
lean_ctor_set(v_res_612_, 1, v_nextStackPos_611_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 3, v___x_585_);
lean_ctor_set(v___x_557_, 2, v_nextStackPos_611_);
v___x_614_ = v___x_557_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_needle_552_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_table_553_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_nextStackPos_611_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v___x_585_);
v___x_614_ = v_reuseFailAlloc_617_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_res_612_);
v___x_616_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_615_);
return v___x_616_;
}
}
}
else
{
lean_object* v___x_618_; lean_object* v_nextStackPos_619_; lean_object* v_nextNeedlePos_620_; uint8_t v_decide_621_; 
lean_dec(v_basePos_565_);
v___x_618_ = lean_unsigned_to_nat(1u);
v_nextStackPos_619_ = lean_nat_add(v_stackPos_554_, v___x_618_);
lean_dec(v_stackPos_554_);
v_nextNeedlePos_620_ = lean_nat_add(v_needlePos_555_, v___x_618_);
lean_dec(v_needlePos_555_);
v_decide_621_ = lean_nat_dec_eq(v_nextNeedlePos_620_, v___x_566_);
lean_dec(v___x_566_);
if (v_decide_621_ == 0)
{
lean_object* v___x_623_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 3, v_nextNeedlePos_620_);
lean_ctor_set(v___x_557_, 2, v_nextStackPos_619_);
v___x_623_ = v___x_557_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_needle_552_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_table_553_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_nextStackPos_619_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_nextNeedlePos_620_);
v___x_623_ = v_reuseFailAlloc_626_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
v___x_625_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_624_);
return v___x_625_;
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v_res_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_627_ = lean_nat_sub(v_nextStackPos_619_, v_nextNeedlePos_620_);
lean_dec(v_nextNeedlePos_620_);
v___x_628_ = l_String_Slice_pos_x21(v_s_511_, v___x_627_);
lean_dec(v___x_627_);
v___x_629_ = l_String_Slice_pos_x21(v_s_511_, v_nextStackPos_619_);
v_res_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_res_630_, 0, v___x_628_);
lean_ctor_set(v_res_630_, 1, v___x_629_);
v___x_631_ = lean_unsigned_to_nat(0u);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 3, v___x_631_);
lean_ctor_set(v___x_557_, 2, v_nextStackPos_619_);
v___x_633_ = v___x_557_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_needle_552_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_table_553_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_nextStackPos_619_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v___x_631_);
v___x_633_ = v_reuseFailAlloc_636_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v_res_630_);
v___x_635_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_634_);
return v___x_635_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box(2);
v___x_639_ = lean_apply_4(v_lift_512_, lean_box(0), lean_box(0), v___f_517_, v___x_638_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed(lean_object* v___y_640_, lean_object* v_s_641_, lean_object* v_lift_642_, lean_object* v_it_643_, lean_object* v_acc_644_, lean_object* v_hP_645_, lean_object* v_recur_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(v___y_640_, v_s_641_, v_lift_642_, v_it_643_, v_acc_644_, v_hP_645_, v_recur_646_);
lean_dec_ref(v_s_641_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(lean_object* v_s_648_, lean_object* v_lift_649_, lean_object* v_00_u03b3_650_, lean_object* v_Pl_651_, lean_object* v_it_652_, lean_object* v_init_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___f_655_; lean_object* v___x_656_; 
v___f_655_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed), 7, 3);
lean_closure_set(v___f_655_, 0, v___y_654_);
lean_closure_set(v___f_655_, 1, v_s_648_);
lean_closure_set(v___f_655_, 2, v_lift_649_);
v___x_656_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_655_, v_it_652_, v_init_653_, lean_box(0));
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(lean_object* v_s_657_){
_start:
{
lean_object* v___f_658_; 
v___f_658_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2), 7, 1);
lean_closure_set(v___f_658_, 0, v_s_657_);
return v___f_658_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(lean_object* v_pat_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_660_, 0, v_pat_659_);
return v___x_660_;
}
}
uint8_t l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(lean_object* v_pat_661_, lean_object* v_s_662_){
_start:
{
lean_object* v_str_663_; lean_object* v_startInclusive_664_; lean_object* v_endExclusive_665_; lean_object* v_str_666_; lean_object* v_startInclusive_667_; lean_object* v_endExclusive_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_str_663_ = lean_ctor_get(v_pat_661_, 0);
v_startInclusive_664_ = lean_ctor_get(v_pat_661_, 1);
v_endExclusive_665_ = lean_ctor_get(v_pat_661_, 2);
v_str_666_ = lean_ctor_get(v_s_662_, 0);
v_startInclusive_667_ = lean_ctor_get(v_s_662_, 1);
v_endExclusive_668_ = lean_ctor_get(v_s_662_, 2);
v___x_669_ = lean_nat_sub(v_endExclusive_665_, v_startInclusive_664_);
v___x_670_ = lean_nat_sub(v_endExclusive_668_, v_startInclusive_667_);
v___x_671_ = lean_nat_dec_le(v___x_669_, v___x_670_);
lean_dec(v___x_670_);
if (v___x_671_ == 0)
{
lean_dec(v___x_669_);
return v___x_671_;
}
else
{
uint8_t v___x_672_; 
v___x_672_ = lean_string_memcmp(v_str_666_, v_str_663_, v_startInclusive_667_, v_startInclusive_664_, v___x_669_);
lean_dec(v___x_669_);
return v___x_672_;
}
}
}
LEAN_EXPORT void l_String_Slice_Pattern_ForwardSliceSearcher_startsWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_pat_661_ = stack[0].m_obj;
lean_object* v_s_662_ = stack[1].m_obj;
uint8_t v_res_673_;
v_res_673_ = l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(v_pat_661_, v_s_662_);
stack->m_num = v_res_673_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(lean_object* v_pat_674_, lean_object* v_s_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(v_pat_674_, v_s_675_);
lean_dec_ref(v_s_675_);
lean_dec_ref(v_pat_674_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(lean_object* v_pat_678_, lean_object* v_s_679_){
_start:
{
lean_object* v_str_680_; lean_object* v_startInclusive_681_; lean_object* v_endExclusive_682_; lean_object* v_str_683_; lean_object* v_startInclusive_684_; lean_object* v_endExclusive_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_str_680_ = lean_ctor_get(v_pat_678_, 0);
v_startInclusive_681_ = lean_ctor_get(v_pat_678_, 1);
v_endExclusive_682_ = lean_ctor_get(v_pat_678_, 2);
v_str_683_ = lean_ctor_get(v_s_679_, 0);
v_startInclusive_684_ = lean_ctor_get(v_s_679_, 1);
v_endExclusive_685_ = lean_ctor_get(v_s_679_, 2);
v___x_686_ = lean_nat_sub(v_endExclusive_682_, v_startInclusive_681_);
v___x_687_ = lean_nat_sub(v_endExclusive_685_, v_startInclusive_684_);
v___x_688_ = lean_nat_dec_le(v___x_686_, v___x_687_);
lean_dec(v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
return v___x_689_;
}
else
{
uint8_t v___x_690_; 
v___x_690_ = lean_string_memcmp(v_str_683_, v_str_680_, v_startInclusive_684_, v_startInclusive_681_, v___x_686_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
lean_dec(v___x_686_);
v___x_691_ = lean_box(0);
return v___x_691_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = l_String_Slice_pos_x21(v_s_679_, v___x_686_);
lean_dec(v___x_686_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed(lean_object* v_pat_694_, lean_object* v_s_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(v_pat_694_, v_s_695_);
lean_dec_ref(v_s_695_);
lean_dec_ref(v_pat_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(lean_object* v_pat_697_, lean_object* v_s_698_, lean_object* v_x_699_){
_start:
{
lean_object* v_str_700_; lean_object* v_startInclusive_701_; lean_object* v_endExclusive_702_; lean_object* v_str_703_; lean_object* v_startInclusive_704_; lean_object* v_endExclusive_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_str_700_ = lean_ctor_get(v_pat_697_, 0);
v_startInclusive_701_ = lean_ctor_get(v_pat_697_, 1);
v_endExclusive_702_ = lean_ctor_get(v_pat_697_, 2);
v_str_703_ = lean_ctor_get(v_s_698_, 0);
v_startInclusive_704_ = lean_ctor_get(v_s_698_, 1);
v_endExclusive_705_ = lean_ctor_get(v_s_698_, 2);
v___x_706_ = lean_nat_sub(v_endExclusive_702_, v_startInclusive_701_);
v___x_707_ = lean_nat_sub(v_endExclusive_705_, v_startInclusive_704_);
v___x_708_ = lean_nat_dec_le(v___x_706_, v___x_707_);
lean_dec(v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
return v___x_709_;
}
else
{
uint8_t v___x_710_; 
v___x_710_ = lean_string_memcmp(v_str_703_, v_str_700_, v_startInclusive_704_, v_startInclusive_701_, v___x_706_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
lean_dec(v___x_706_);
v___x_711_ = lean_box(0);
return v___x_711_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = l_String_Slice_pos_x21(v_s_698_, v___x_706_);
lean_dec(v___x_706_);
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(lean_object* v_pat_714_, lean_object* v_s_715_, lean_object* v_x_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(v_pat_714_, v_s_715_, v_x_716_);
lean_dec_ref(v_s_715_);
lean_dec_ref(v_pat_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(lean_object* v_pat_718_){
_start:
{
lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_inc_ref_n(v_pat_718_, 2);
v___f_719_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_719_, 0, v_pat_718_);
v___x_720_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_720_, 0, v_pat_718_);
v___x_721_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_721_, 0, v_pat_718_);
v___x_722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___f_719_);
lean_ctor_set(v___x_722_, 2, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(lean_object* v_pat_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_string_utf8_byte_size(v_pat_723_);
v___x_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_726_, 0, v_pat_723_);
lean_ctor_set(v___x_726_, 1, v___x_724_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
v___x_727_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed), 2, 1);
lean_closure_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(lean_object* v___x_728_, lean_object* v_pat_729_, lean_object* v___x_730_, lean_object* v_s_731_, lean_object* v_x_732_){
_start:
{
lean_object* v_str_733_; lean_object* v_startInclusive_734_; lean_object* v_endExclusive_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_str_733_ = lean_ctor_get(v_s_731_, 0);
v_startInclusive_734_ = lean_ctor_get(v_s_731_, 1);
v_endExclusive_735_ = lean_ctor_get(v_s_731_, 2);
v___x_736_ = lean_nat_sub(v_endExclusive_735_, v_startInclusive_734_);
v___x_737_ = lean_nat_dec_le(v___x_728_, v___x_736_);
lean_dec(v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
v___x_738_ = lean_box(0);
return v___x_738_;
}
else
{
uint8_t v___x_739_; 
v___x_739_ = lean_string_memcmp(v_str_733_, v_pat_729_, v_startInclusive_734_, v___x_730_, v___x_728_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_box(0);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = l_String_Slice_pos_x21(v_s_731_, v___x_728_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(lean_object* v___x_743_, lean_object* v_pat_744_, lean_object* v___x_745_, lean_object* v_s_746_, lean_object* v_x_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(v___x_743_, v_pat_744_, v___x_745_, v_s_746_, v_x_747_);
lean_dec_ref(v_s_746_);
lean_dec(v___x_745_);
lean_dec_ref(v_pat_744_);
lean_dec(v___x_743_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(lean_object* v_pat_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_string_utf8_byte_size(v_pat_749_);
lean_inc_ref(v_pat_749_);
v___f_752_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_752_, 0, v___x_751_);
lean_closure_set(v___f_752_, 1, v_pat_749_);
lean_closure_set(v___f_752_, 2, v___x_750_);
v___x_753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_753_, 0, v_pat_749_);
lean_ctor_set(v___x_753_, 1, v___x_750_);
lean_ctor_set(v___x_753_, 2, v___x_751_);
lean_inc_ref(v___x_753_);
v___x_754_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed), 2, 1);
lean_closure_set(v___x_754_, 0, v___x_753_);
v___x_755_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed), 2, 1);
lean_closure_set(v___x_755_, 0, v___x_753_);
v___x_756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___f_752_);
lean_ctor_set(v___x_756_, 2, v___x_755_);
return v___x_756_;
}
}
uint8_t l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(lean_object* v_pat_757_, lean_object* v_s_758_){
_start:
{
lean_object* v_str_759_; lean_object* v_startInclusive_760_; lean_object* v_endExclusive_761_; lean_object* v_str_762_; lean_object* v_startInclusive_763_; lean_object* v_endExclusive_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_str_759_ = lean_ctor_get(v_pat_757_, 0);
v_startInclusive_760_ = lean_ctor_get(v_pat_757_, 1);
v_endExclusive_761_ = lean_ctor_get(v_pat_757_, 2);
v_str_762_ = lean_ctor_get(v_s_758_, 0);
v_startInclusive_763_ = lean_ctor_get(v_s_758_, 1);
v_endExclusive_764_ = lean_ctor_get(v_s_758_, 2);
v___x_765_ = lean_nat_sub(v_endExclusive_761_, v_startInclusive_760_);
v___x_766_ = lean_nat_sub(v_endExclusive_764_, v_startInclusive_763_);
v___x_767_ = lean_nat_dec_le(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec(v___x_766_);
lean_dec(v___x_765_);
return v___x_767_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_nat_sub(v___x_766_, v___x_765_);
lean_dec(v___x_766_);
v___x_769_ = lean_nat_add(v_startInclusive_763_, v___x_768_);
lean_dec(v___x_768_);
v___x_770_ = lean_string_memcmp(v_str_762_, v_str_759_, v___x_769_, v_startInclusive_760_, v___x_765_);
lean_dec(v___x_765_);
lean_dec(v___x_769_);
return v___x_770_;
}
}
}
LEAN_EXPORT void l_String_Slice_Pattern_BackwardSliceSearcher_endsWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_pat_757_ = stack[0].m_obj;
lean_object* v_s_758_ = stack[1].m_obj;
uint8_t v_res_771_;
v_res_771_ = l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(v_pat_757_, v_s_758_);
stack->m_num = v_res_771_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(lean_object* v_pat_772_, lean_object* v_s_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(v_pat_772_, v_s_773_);
lean_dec_ref(v_s_773_);
lean_dec_ref(v_pat_772_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(lean_object* v_pat_776_, lean_object* v_s_777_){
_start:
{
lean_object* v_str_778_; lean_object* v_startInclusive_779_; lean_object* v_endExclusive_780_; lean_object* v_str_781_; lean_object* v_startInclusive_782_; lean_object* v_endExclusive_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_str_778_ = lean_ctor_get(v_pat_776_, 0);
v_startInclusive_779_ = lean_ctor_get(v_pat_776_, 1);
v_endExclusive_780_ = lean_ctor_get(v_pat_776_, 2);
v_str_781_ = lean_ctor_get(v_s_777_, 0);
v_startInclusive_782_ = lean_ctor_get(v_s_777_, 1);
v_endExclusive_783_ = lean_ctor_get(v_s_777_, 2);
v___x_784_ = lean_nat_sub(v_endExclusive_780_, v_startInclusive_779_);
v___x_785_ = lean_nat_sub(v_endExclusive_783_, v_startInclusive_782_);
v___x_786_ = lean_nat_dec_le(v___x_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
lean_dec(v___x_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
return v___x_787_;
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = lean_nat_sub(v___x_785_, v___x_784_);
lean_dec(v___x_785_);
v___x_789_ = lean_nat_add(v_startInclusive_782_, v___x_788_);
v___x_790_ = lean_string_memcmp(v_str_781_, v_str_778_, v___x_789_, v_startInclusive_779_, v___x_784_);
lean_dec(v___x_784_);
lean_dec(v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
return v___x_791_;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = l_String_Slice_pos_x21(v_s_777_, v___x_788_);
lean_dec(v___x_788_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed(lean_object* v_pat_794_, lean_object* v_s_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(v_pat_794_, v_s_795_);
lean_dec_ref(v_s_795_);
lean_dec_ref(v_pat_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(lean_object* v_pat_797_, lean_object* v_s_798_, lean_object* v_x_799_){
_start:
{
lean_object* v_str_800_; lean_object* v_startInclusive_801_; lean_object* v_endExclusive_802_; lean_object* v_str_803_; lean_object* v_startInclusive_804_; lean_object* v_endExclusive_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_str_800_ = lean_ctor_get(v_pat_797_, 0);
v_startInclusive_801_ = lean_ctor_get(v_pat_797_, 1);
v_endExclusive_802_ = lean_ctor_get(v_pat_797_, 2);
v_str_803_ = lean_ctor_get(v_s_798_, 0);
v_startInclusive_804_ = lean_ctor_get(v_s_798_, 1);
v_endExclusive_805_ = lean_ctor_get(v_s_798_, 2);
v___x_806_ = lean_nat_sub(v_endExclusive_802_, v_startInclusive_801_);
v___x_807_ = lean_nat_sub(v_endExclusive_805_, v_startInclusive_804_);
v___x_808_ = lean_nat_dec_le(v___x_806_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v___x_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = lean_nat_sub(v___x_807_, v___x_806_);
lean_dec(v___x_807_);
v___x_811_ = lean_nat_add(v_startInclusive_804_, v___x_810_);
v___x_812_ = lean_string_memcmp(v_str_803_, v_str_800_, v___x_811_, v_startInclusive_801_, v___x_806_);
lean_dec(v___x_806_);
lean_dec(v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
return v___x_813_;
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = l_String_Slice_pos_x21(v_s_798_, v___x_810_);
lean_dec(v___x_810_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(lean_object* v_pat_816_, lean_object* v_s_817_, lean_object* v_x_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(v_pat_816_, v_s_817_, v_x_818_);
lean_dec_ref(v_s_817_);
lean_dec_ref(v_pat_816_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(lean_object* v_pat_820_){
_start:
{
lean_object* v___f_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_inc_ref_n(v_pat_820_, 2);
v___f_821_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed), 3, 1);
lean_closure_set(v___f_821_, 0, v_pat_820_);
v___x_822_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_822_, 0, v_pat_820_);
v___x_823_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_823_, 0, v_pat_820_);
v___x_824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___f_821_);
lean_ctor_set(v___x_824_, 2, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(lean_object* v___x_825_, lean_object* v_pat_826_, lean_object* v___x_827_, lean_object* v_s_828_, lean_object* v_x_829_){
_start:
{
lean_object* v_str_830_; lean_object* v_startInclusive_831_; lean_object* v_endExclusive_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_str_830_ = lean_ctor_get(v_s_828_, 0);
v_startInclusive_831_ = lean_ctor_get(v_s_828_, 1);
v_endExclusive_832_ = lean_ctor_get(v_s_828_, 2);
v___x_833_ = lean_nat_sub(v_endExclusive_832_, v_startInclusive_831_);
v___x_834_ = lean_nat_dec_le(v___x_825_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_dec(v___x_833_);
v___x_835_ = lean_box(0);
return v___x_835_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_836_ = lean_nat_sub(v___x_833_, v___x_825_);
lean_dec(v___x_833_);
v___x_837_ = lean_nat_add(v_startInclusive_831_, v___x_836_);
v___x_838_ = lean_string_memcmp(v_str_830_, v_pat_826_, v___x_837_, v___x_827_, v___x_825_);
lean_dec(v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; 
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = l_String_Slice_pos_x21(v_s_828_, v___x_836_);
lean_dec(v___x_836_);
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(lean_object* v___x_842_, lean_object* v_pat_843_, lean_object* v___x_844_, lean_object* v_s_845_, lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(v___x_842_, v_pat_843_, v___x_844_, v_s_845_, v_x_846_);
lean_dec_ref(v_s_845_);
lean_dec(v___x_844_);
lean_dec_ref(v_pat_843_);
lean_dec(v___x_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(lean_object* v_pat_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___f_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_string_utf8_byte_size(v_pat_848_);
lean_inc_ref(v_pat_848_);
v___f_851_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_851_, 0, v___x_850_);
lean_closure_set(v___f_851_, 1, v_pat_848_);
lean_closure_set(v___f_851_, 2, v___x_849_);
v___x_852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_852_, 0, v_pat_848_);
lean_ctor_set(v___x_852_, 1, v___x_849_);
lean_ctor_set(v___x_852_, 2, v___x_850_);
lean_inc_ref(v___x_852_);
v___x_853_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed), 2, 1);
lean_closure_set(v___x_853_, 0, v___x_852_);
v___x_854_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed), 2, 1);
lean_closure_set(v___x_854_, 0, v___x_852_);
v___x_855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___f_851_);
lean_ctor_set(v___x_855_, 2, v___x_854_);
return v___x_855_;
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
