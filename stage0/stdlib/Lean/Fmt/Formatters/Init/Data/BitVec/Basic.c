// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Data.BitVec.Basic
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Data.BitVec.Basic import Init.Data
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBitVecLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Fmt_fmtBitVecLit___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBitVecLit___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtBitVecLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term__#__"};
static const lean_object* l_Lean_Fmt_fmtBitVecLit___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBitVecLit___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtBitVecLit___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtBitVecLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Fmt_fmtBitVecLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBitVecLit___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBitVecLit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(14, 106, 244, 245, 0, 94, 14, 228)}};
static const lean_object* l_Lean_Fmt_fmtBitVecLit___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtBitVecLit___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtBitVecLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtBitVecLit___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtBitVecLit___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtBitVecLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtBitVecLit___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtBitVecLit___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtBitVecLit___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBitVecLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBitVecLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtBitVecLit"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 148, 243, 98, 240, 216, 134, 209)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBitVecLitLT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term__#'__"};
static const lean_object* l_Lean_Fmt_fmtBitVecLitLT___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBitVecLitLT___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBitVecLitLT___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtBitVecLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Fmt_fmtBitVecLitLT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBitVecLitLT___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBitVecLitLT___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 111, 91, 190, 189, 100, 156, 31)}};
static const lean_object* l_Lean_Fmt_fmtBitVecLitLT___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBitVecLitLT___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBitVecLitLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBitVecLitLT___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtBitVecLitLT"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 113, 140, 228, 105, 0, 177, 134)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBitVecLit(lean_object* v_x_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; uint8_t v___x_13_; 
v___x_12_ = ((lean_object*)(l_Lean_Fmt_fmtBitVecLit___closed__2));
lean_inc(v_x_9_);
v___x_13_ = l_Lean_Syntax_isOfKind(v_x_9_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_x_9_);
v___x_14_ = l_Lean_Fmt_Error_partialFormatter;
v___x_15_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_a_11_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = l_Lean_Syntax_getArg(v_x_9_, v___x_16_);
v___x_18_ = ((lean_object*)(l_Lean_Fmt_fmtBitVecLit___closed__4));
lean_inc(v___x_17_);
v___x_19_ = l_Lean_Syntax_isOfKind(v___x_17_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v___x_17_);
lean_dec(v_x_9_);
v___x_20_ = l_Lean_Fmt_Error_partialFormatter;
v___x_21_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v_a_11_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Fmt_fmt(v___x_17_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v_a_24_; lean_object* v___x_25_; lean_object* v_hashTk_26_; lean_object* v___x_27_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc(v_a_23_);
v_a_24_ = lean_ctor_get(v___x_22_, 1);
lean_inc(v_a_24_);
lean_dec_ref_known(v___x_22_, 2);
v___x_25_ = lean_unsigned_to_nat(1u);
v_hashTk_26_ = l_Lean_Syntax_getArg(v_x_9_, v___x_25_);
v___x_27_ = l_Lean_Fmt_fmt(v_hashTk_26_, v_a_10_, v_a_24_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v_a_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_28_);
v_a_29_ = lean_ctor_get(v___x_27_, 1);
lean_inc(v_a_29_);
lean_dec_ref_known(v___x_27_, 2);
v___x_30_ = lean_unsigned_to_nat(2u);
v___x_31_ = l_Lean_Syntax_getArg(v_x_9_, v___x_30_);
lean_dec(v_x_9_);
v___x_32_ = l_Lean_Fmt_fmt(v___x_31_, v_a_10_, v_a_29_);
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v_a_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_49_; 
v_a_33_ = lean_ctor_get(v___x_32_, 0);
v_a_34_ = lean_ctor_get(v___x_32_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_49_ == 0)
{
v___x_36_ = v___x_32_;
v_isShared_37_ = v_isSharedCheck_49_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_inc(v_a_33_);
lean_dec(v___x_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_49_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_38_ = lean_unsigned_to_nat(3u);
v___x_39_ = lean_mk_empty_array_with_capacity(v___x_38_);
v___x_40_ = lean_array_push(v___x_39_, v_a_23_);
v___x_41_ = lean_array_push(v___x_40_, v_a_28_);
v___x_42_ = lean_array_push(v___x_41_, v_a_33_);
v___x_43_ = l_Lean_Fmt_Layouts_atomicInfixOperator(v___x_42_);
lean_dec_ref(v___x_42_);
v___x_44_ = 0;
v___x_45_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_43_, v___x_44_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v___x_45_);
v___x_47_ = v___x_36_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_a_34_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
else
{
lean_dec(v_a_28_);
lean_dec(v_a_23_);
return v___x_32_;
}
}
else
{
lean_dec(v_a_23_);
lean_dec(v_x_9_);
return v___x_27_;
}
}
else
{
lean_dec(v_x_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBitVecLit___boxed(lean_object* v_x_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Fmt_fmtBitVecLit(v_x_50_, v_a_51_, v_a_52_);
lean_dec_ref(v_a_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1(){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_62_ = l_Lean_Fmt_fmtAttribute;
v___x_63_ = ((lean_object*)(l_Lean_Fmt_fmtBitVecLit___closed__2));
v___x_64_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___closed__3));
v___x_65_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBitVecLit___boxed), 3, 0);
v___x_66_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_62_, v___x_63_, v___x_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1___boxed(lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1();
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBitVecLitLT(lean_object* v_x_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lean_Fmt_fmtBitVecLitLT___closed__1));
lean_inc(v_x_73_);
v___x_77_ = l_Lean_Syntax_isOfKind(v_x_73_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_x_73_);
v___x_78_ = l_Lean_Fmt_Error_partialFormatter;
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v_a_75_);
return v___x_79_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_73_, v___x_80_);
v___x_82_ = l_Lean_Fmt_fmt(v___x_81_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v_a_84_; lean_object* v___x_85_; lean_object* v_hashTk_86_; lean_object* v___x_87_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
v_a_84_ = lean_ctor_get(v___x_82_, 1);
lean_inc(v_a_84_);
lean_dec_ref_known(v___x_82_, 2);
v___x_85_ = lean_unsigned_to_nat(1u);
v_hashTk_86_ = l_Lean_Syntax_getArg(v_x_73_, v___x_85_);
v___x_87_ = l_Lean_Fmt_fmt(v_hashTk_86_, v_a_74_, v_a_84_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v_a_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
v_a_89_ = lean_ctor_get(v___x_87_, 1);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_87_, 2);
v___x_90_ = lean_unsigned_to_nat(2u);
v___x_91_ = l_Lean_Syntax_getArg(v_x_73_, v___x_90_);
lean_dec(v_x_73_);
v___x_92_ = l_Lean_Fmt_fmt(v___x_91_, v_a_74_, v_a_89_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_109_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_a_94_ = lean_ctor_get(v___x_92_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_109_ == 0)
{
v___x_96_ = v___x_92_;
v_isShared_97_ = v_isSharedCheck_109_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_109_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_98_ = lean_unsigned_to_nat(3u);
v___x_99_ = lean_mk_empty_array_with_capacity(v___x_98_);
v___x_100_ = lean_array_push(v___x_99_, v_a_83_);
v___x_101_ = lean_array_push(v___x_100_, v_a_88_);
v___x_102_ = lean_array_push(v___x_101_, v_a_93_);
v___x_103_ = l_Lean_Fmt_Layouts_atomicInfixOperator(v___x_102_);
lean_dec_ref(v___x_102_);
v___x_104_ = 0;
v___x_105_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_103_, v___x_104_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_105_);
v___x_107_ = v___x_96_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_a_94_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
else
{
lean_dec(v_a_88_);
lean_dec(v_a_83_);
return v___x_92_;
}
}
else
{
lean_dec(v_a_83_);
lean_dec(v_x_73_);
return v___x_87_;
}
}
else
{
lean_dec(v_x_73_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBitVecLitLT___boxed(lean_object* v_x_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Fmt_fmtBitVecLitLT(v_x_110_, v_a_111_, v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1(){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_120_ = l_Lean_Fmt_fmtAttribute;
v___x_121_ = ((lean_object*)(l_Lean_Fmt_fmtBitVecLitLT___closed__1));
v___x_122_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___closed__1));
v___x_123_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBitVecLitLT___boxed), 3, 0);
v___x_124_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_120_, v___x_121_, v___x_122_, v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1___boxed(lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1();
return v_res_126_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Data_BitVec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLit___regBuiltin_Lean_Fmt_fmtBitVecLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_BitVec_Basic_0__Lean_Fmt_fmtBitVecLitLT___regBuiltin_Lean_Fmt_fmtBitVecLitLT__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Data_BitVec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Data_BitVec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Data_BitVec_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
