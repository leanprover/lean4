// Lean compiler output
// Module: Lean.Parser.StrInterpolation
// Imports: public import Lean.Parser.Basic
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
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t);
lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharForStrInterpolant(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "interpolatedStrLitKind"};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__0 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 181, 130, 246, 88, 58, 26, 43)}};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1_value;
static const lean_string_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'}'"};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__2 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__2_value;
static const lean_string_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__3 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__3_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4_value;
static const lean_closure_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_isQuotableCharForStrInterpolant___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__5 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__5_value;
static const lean_closure_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_quotedCharCoreFn___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__6 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__6_value;
static const lean_string_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unterminated string literal"};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__7 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_interpolatedStrFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolated string"};
static const lean_object* l_Lean_Parser_interpolatedStrFn___closed__0 = (const lean_object*)&l_Lean_Parser_interpolatedStrFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_interpolatedStrNoAntiquot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Lean_Parser_interpolatedStrNoAntiquot___closed__0 = (const lean_object*)&l_Lean_Parser_interpolatedStrNoAntiquot___closed__0_value;
static lean_once_cell_t l_Lean_Parser_interpolatedStrNoAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrNoAntiquot(lean_object*);
static lean_once_cell_t l_Lean_Parser_interpolatedStr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_interpolatedStr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
static const lean_string_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_interpolatedStrNoAntiquot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 182, 82, 21, 251, 127, 209, 38)}};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value;
static const lean_string_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 840, .m_capacity = 840, .m_length = 839, .m_data = "The parser `interpolatedStr(p)` parses a string literal like `\"foo\"` (see `str`), but the string\nmay also contain `{}` escapes, and within the escapes the parser `p` is used. For example,\n`interpolatedStr(term)` will parse `\"foo {2 + 2}\"`, where `2 + 2` is parsed as a term rather than\nas a string. Note that the full Lean term grammar is available here, including string literals,\nso for example `\"foo {\"bar\" ++ \"baz\"}\"` is a legal interpolated string (which evaluates to\n`foo barbaz`).\n\nThis parser has arity 1, and returns a `interpolatedStrKind` with an odd number of arguments,\nalternating between chunks of literal text and results from `p`. The literal chunks contain\nuninterpreted substrings of the input. For example, `\"foo\\n{2 + 2}\"` would have three arguments:\nan atom `\"foo\\n{`, the parsed `2 + 2` term, and then the atom `}\"`."};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___boxed(lean_object*);
uint8_t l_Lean_Parser_isQuotableCharForStrInterpolant(uint32_t v_c_1_){
_start:
{
uint32_t v___x_2_; uint8_t v___x_3_; 
v___x_2_ = 123;
v___x_3_ = lean_uint32_dec_eq(v_c_1_, v___x_2_);
if (v___x_3_ == 0)
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Parser_isQuotableCharDefault(v_c_1_);
return v___x_4_;
}
else
{
return v___x_3_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_isQuotableCharForStrInterpolant_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1_ = stack[0].m_num;
uint8_t v_res_5_;
v_res_5_ = l_Lean_Parser_isQuotableCharForStrInterpolant(v_c_1_);
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(lean_object* v_c_6_){
_start:
{
uint32_t v_c_boxed_7_; uint8_t v_res_8_; lean_object* v_r_9_; 
v_c_boxed_7_ = lean_unbox_uint32(v_c_6_);
lean_dec(v_c_6_);
v_res_8_ = l_Lean_Parser_isQuotableCharForStrInterpolant(v_c_boxed_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
uint8_t l_instBEqOption_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
if (lean_obj_tag(v_x_11_) == 0)
{
uint8_t v___x_12_; 
v___x_12_ = 1;
return v___x_12_;
}
else
{
uint8_t v___x_13_; 
v___x_13_ = 0;
return v___x_13_;
}
}
else
{
if (lean_obj_tag(v_x_11_) == 0)
{
uint8_t v___x_14_; 
v___x_14_ = 0;
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v_val_16_; uint8_t v___x_17_; 
v_val_15_ = lean_ctor_get(v_x_10_, 0);
v_val_16_ = lean_ctor_get(v_x_11_, 0);
v___x_17_ = l_Lean_Parser_instBEqError_beq(v_val_15_, v_val_16_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_10_ = stack[0].m_obj;
lean_object* v_x_11_ = stack[1].m_obj;
uint8_t v_res_18_;
v_res_18_ = l_instBEqOption_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(v_x_10_, v_x_11_);
stack->m_num = v_res_18_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0___boxed(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_instBEqOption_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(v_x_19_, v_x_20_);
lean_dec(v_x_20_);
lean_dec(v_x_19_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse(lean_object* v_p_36_, lean_object* v_stackSize_37_, lean_object* v_startPos_38_, lean_object* v_c_39_, lean_object* v_s_40_){
_start:
{
lean_object* v_pos_41_; lean_object* v_toInputContext_42_; uint8_t v___x_43_; 
v_pos_41_ = lean_ctor_get(v_s_40_, 2);
v_toInputContext_42_ = lean_ctor_get(v_c_39_, 0);
v___x_43_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_42_, v_pos_41_);
if (v___x_43_ == 0)
{
lean_object* v_inputString_44_; uint8_t v___x_45_; uint32_t v_curr_46_; lean_object* v___x_47_; lean_object* v_s_48_; uint32_t v___x_49_; uint8_t v___x_50_; 
v_inputString_44_ = lean_ctor_get(v_toInputContext_42_, 0);
v___x_45_ = 1;
v_curr_46_ = lean_string_utf8_get(v_inputString_44_, v_pos_41_);
v___x_47_ = lean_string_utf8_next(v_inputString_44_, v_pos_41_);
v_s_48_ = l_Lean_Parser_ParserState_setPos(v_s_40_, v___x_47_);
v___x_49_ = 34;
v___x_50_ = lean_uint32_dec_eq(v_curr_46_, v___x_49_);
if (v___x_50_ == 0)
{
uint32_t v___x_51_; uint8_t v___x_52_; 
v___x_51_ = 92;
v___x_52_ = lean_uint32_dec_eq(v_curr_46_, v___x_51_);
if (v___x_52_ == 0)
{
uint32_t v___x_53_; uint8_t v___x_54_; 
v___x_53_ = 123;
v___x_54_ = lean_uint32_dec_eq(v_curr_46_, v___x_53_);
if (v___x_54_ == 0)
{
v_s_40_ = v_s_48_;
goto _start;
}
else
{
lean_object* v___x_56_; lean_object* v_s_57_; lean_object* v_s_58_; lean_object* v_pos_59_; lean_object* v_errorMsg_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1));
lean_inc_ref_n(v_c_39_, 2);
v_s_57_ = l_Lean_Parser_mkNodeToken(v___x_56_, v_startPos_38_, v___x_45_, v_c_39_, v_s_48_);
lean_inc_ref(v_p_36_);
v_s_58_ = lean_apply_2(v_p_36_, v_c_39_, v_s_57_);
v_pos_59_ = lean_ctor_get(v_s_58_, 2);
lean_inc(v_pos_59_);
v_errorMsg_60_ = lean_ctor_get(v_s_58_, 4);
lean_inc(v_errorMsg_60_);
v___x_61_ = lean_box(0);
v___x_62_ = l_instBEqOption_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(v_errorMsg_60_, v___x_61_);
lean_dec(v_errorMsg_60_);
if (v___x_62_ == 0)
{
lean_dec(v_pos_59_);
lean_dec_ref(v_c_39_);
lean_dec(v_stackSize_37_);
lean_dec_ref(v_p_36_);
return v_s_58_;
}
else
{
uint32_t v_curr_63_; uint32_t v___x_64_; uint8_t v___x_65_; 
v_curr_63_ = lean_string_utf8_get(v_inputString_44_, v_pos_59_);
v___x_64_ = 125;
v___x_65_ = lean_uint32_dec_eq(v_curr_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v_s_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_pos_59_);
lean_dec_ref(v_c_39_);
lean_dec_ref(v_p_36_);
v___x_66_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__2));
v_s_67_ = l_Lean_Parser_ParserState_mkError(v_s_58_, v___x_66_);
v___x_68_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4));
v___x_69_ = l_Lean_Parser_ParserState_mkNode(v_s_67_, v___x_68_, v_stackSize_37_);
lean_dec(v_stackSize_37_);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v_s_71_; 
v___x_70_ = lean_string_utf8_next(v_inputString_44_, v_pos_59_);
v_s_71_ = l_Lean_Parser_ParserState_setPos(v_s_58_, v___x_70_);
v_startPos_38_ = v_pos_59_;
v_s_40_ = v_s_71_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__6));
v___x_74_ = lean_alloc_closure((void*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse), 5, 3);
lean_closure_set(v___x_74_, 0, v_p_36_);
lean_closure_set(v___x_74_, 1, v_stackSize_37_);
lean_closure_set(v___x_74_, 2, v_startPos_38_);
v___x_75_ = l_Lean_Parser_andthenFn(v___x_73_, v___x_74_, v_c_39_, v_s_48_);
return v___x_75_;
}
}
else
{
lean_object* v___x_76_; lean_object* v_s_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec_ref(v_p_36_);
v___x_76_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1));
v_s_77_ = l_Lean_Parser_mkNodeToken(v___x_76_, v_startPos_38_, v___x_45_, v_c_39_, v_s_48_);
v___x_78_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4));
v___x_79_ = l_Lean_Parser_ParserState_mkNode(v_s_77_, v___x_78_, v_stackSize_37_);
lean_dec(v_stackSize_37_);
return v___x_79_;
}
}
else
{
lean_object* v___x_80_; lean_object* v_s_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec_ref(v_c_39_);
lean_dec(v_startPos_38_);
lean_dec_ref(v_p_36_);
v___x_80_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__7));
v_s_81_ = l_Lean_Parser_ParserState_mkError(v_s_40_, v___x_80_);
v___x_82_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4));
v___x_83_ = l_Lean_Parser_ParserState_mkNode(v_s_81_, v___x_82_, v_stackSize_37_);
lean_dec(v_stackSize_37_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn(lean_object* v_p_85_, lean_object* v_c_86_, lean_object* v_s_87_){
_start:
{
lean_object* v_pos_91_; lean_object* v_toInputContext_92_; uint8_t v___x_93_; 
v_pos_91_ = lean_ctor_get(v_s_87_, 2);
v_toInputContext_92_ = lean_ctor_get(v_c_86_, 0);
v___x_93_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_92_, v_pos_91_);
if (v___x_93_ == 0)
{
lean_object* v_inputString_94_; uint32_t v_curr_95_; uint32_t v___x_96_; uint8_t v___x_97_; 
v_inputString_94_ = lean_ctor_get(v_toInputContext_92_, 0);
v_curr_95_ = lean_string_utf8_get(v_inputString_94_, v_pos_91_);
v___x_96_ = 34;
v___x_97_ = lean_uint32_dec_eq(v_curr_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_dec_ref(v_c_86_);
lean_dec_ref(v_p_85_);
goto v___jp_88_;
}
else
{
if (v___x_93_ == 0)
{
lean_object* v_stackSize_98_; lean_object* v_s_99_; lean_object* v___x_100_; 
lean_inc(v_pos_91_);
v_stackSize_98_ = l_Lean_Parser_ParserState_stackSize(v_s_87_);
v_s_99_ = l_Lean_Parser_ParserState_next(v_s_87_, v_c_86_, v_pos_91_);
v___x_100_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse(v_p_85_, v_stackSize_98_, v_pos_91_, v_c_86_, v_s_99_);
return v___x_100_;
}
else
{
lean_dec_ref(v_c_86_);
lean_dec_ref(v_p_85_);
goto v___jp_88_;
}
}
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec_ref(v_c_86_);
lean_dec_ref(v_p_85_);
v___x_101_ = lean_box(0);
v___x_102_ = l_Lean_Parser_ParserState_mkEOIError(v_s_87_, v___x_101_);
return v___x_102_;
}
v___jp_88_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_Parser_interpolatedStrFn___closed__0));
v___x_90_ = l_Lean_Parser_ParserState_mkError(v_s_87_, v___x_89_);
return v___x_90_;
}
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(l_Lean_Parser_interpolatedStrNoAntiquot___closed__0));
v___x_105_ = l_Lean_Parser_mkAtomicInfo(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrNoAntiquot(lean_object* v_p_106_){
_start:
{
lean_object* v___x_107_; lean_object* v_fn_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_117_; 
v___x_107_ = l_Lean_Parser_withoutPosition(v_p_106_);
v_fn_108_ = lean_ctor_get(v___x_107_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_117_ == 0)
{
lean_object* v_unused_118_; 
v_unused_118_ = lean_ctor_get(v___x_107_, 0);
lean_dec(v_unused_118_);
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_117_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_fn_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_117_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_112_ = lean_obj_once(&l_Lean_Parser_interpolatedStrNoAntiquot___closed__1, &l_Lean_Parser_interpolatedStrNoAntiquot___closed__1_once, _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1);
v___x_113_ = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(v___x_113_, 0, v_fn_108_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_113_);
lean_ctor_set(v___x_110_, 0, v___x_112_);
v___x_115_ = v___x_110_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___closed__0(void){
_start:
{
uint8_t v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_119_ = 0;
v___x_120_ = 1;
v___x_121_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4));
v___x_122_ = ((lean_object*)(l_Lean_Parser_interpolatedStrNoAntiquot___closed__0));
v___x_123_ = l_Lean_Parser_mkAntiquot(v___x_122_, v___x_121_, v___x_120_, v___x_119_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr(lean_object* v_p_124_){
_start:
{
lean_object* v___x_125_; lean_object* v_fn_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_137_; 
v___x_125_ = l_Lean_Parser_withoutPosition(v_p_124_);
v_fn_126_ = lean_ctor_get(v___x_125_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v___x_125_, 0);
lean_dec(v_unused_138_);
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_137_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_fn_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_137_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_130_ = lean_obj_once(&l_Lean_Parser_interpolatedStr___closed__0, &l_Lean_Parser_interpolatedStr___closed__0_once, _init_l_Lean_Parser_interpolatedStr___closed__0);
v___x_131_ = lean_obj_once(&l_Lean_Parser_interpolatedStrNoAntiquot___closed__1, &l_Lean_Parser_interpolatedStrNoAntiquot___closed__1_once, _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1);
v___x_132_ = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(v___x_132_, 0, v_fn_126_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v___x_132_);
lean_ctor_set(v___x_128_, 0, v___x_131_);
v___x_134_ = v___x_128_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_136_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Parser_withAntiquot(v___x_130_, v___x_134_);
return v___x_135_;
}
}
}
}
lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1(){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2));
v___x_148_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3));
v___x_149_ = l_Lean_addBuiltinDocString(v___x_147_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_150_;
v_res_150_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1();
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___boxed(lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1();
return v_res_152_;
}
}
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_StrInterpolation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_StrInterpolation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_StrInterpolation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_StrInterpolation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_StrInterpolation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_StrInterpolation(builtin);
}
#ifdef __cplusplus
}
#endif
