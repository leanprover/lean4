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
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 841, .m_capacity = 841, .m_length = 840, .m_data = "The parser `interpolatedStr(p)` parses a string literal like `\"foo\"` (see `str`), but the string\nmay also contain `{}` escapes, and within the escapes the parser `p` is used. For example,\n`interpolatedStr(term)` will parse `\"foo {2 + 2}\"`, where `2 + 2` is parsed as a term rather than\nas a string. Note that the full Lean term grammar is available here, including string literals,\nso for example `\"foo {\"bar\" ++ \"baz\"}\"` is a legal interpolated string (which evaluates to\n`foo barbaz`).\n\nThis parser has arity 1, and returns a `interpolatedStrKind` with an odd number of arguments,\nalternating between chunks of literal text and results from `p`. The literal chunks contain\nuninterpreted substrings of the input. For example, `\"foo\\n{2 + 2}\"` would have three arguments:\nan atom `\"foo\\n{`, the parsed `2 + 2` term, and then the atom `}\"`. "};
static const lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3 = (const lean_object*)&l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharForStrInterpolant(uint32_t v_c_1_){
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
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(lean_object* v_c_5_){
_start:
{
uint32_t v_c_boxed_6_; uint8_t v_res_7_; lean_object* v_r_8_; 
v_c_boxed_6_ = lean_unbox_uint32(v_c_5_);
lean_dec(v_c_5_);
v_res_7_ = l_Lean_Parser_isQuotableCharForStrInterpolant(v_c_boxed_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
if (lean_obj_tag(v_x_10_) == 0)
{
uint8_t v___x_11_; 
v___x_11_ = 1;
return v___x_11_;
}
else
{
uint8_t v___x_12_; 
lean_dec_ref_known(v_x_10_, 1);
v___x_12_ = 0;
return v___x_12_;
}
}
else
{
if (lean_obj_tag(v_x_10_) == 0)
{
uint8_t v___x_13_; 
lean_dec_ref_known(v_x_9_, 1);
v___x_13_ = 0;
return v___x_13_;
}
else
{
lean_object* v_val_14_; lean_object* v_val_15_; uint8_t v___x_16_; 
v_val_14_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_val_14_);
lean_dec_ref_known(v_x_9_, 1);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = l_Lean_Parser_instBEqError_beq(v_val_14_, v_val_15_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0___boxed(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Option_instBEq_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(v_x_17_, v_x_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse(lean_object* v_p_34_, lean_object* v_stackSize_35_, lean_object* v_startPos_36_, lean_object* v_c_37_, lean_object* v_s_38_){
_start:
{
lean_object* v_pos_39_; lean_object* v_toInputContext_40_; uint8_t v___x_41_; 
v_pos_39_ = lean_ctor_get(v_s_38_, 2);
v_toInputContext_40_ = lean_ctor_get(v_c_37_, 0);
v___x_41_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_40_, v_pos_39_);
if (v___x_41_ == 0)
{
lean_object* v_inputString_42_; uint8_t v___x_43_; uint32_t v_curr_44_; lean_object* v___x_45_; lean_object* v_s_46_; uint32_t v___x_47_; uint8_t v___x_48_; 
v_inputString_42_ = lean_ctor_get(v_toInputContext_40_, 0);
v___x_43_ = 1;
v_curr_44_ = lean_string_utf8_get(v_inputString_42_, v_pos_39_);
v___x_45_ = lean_string_utf8_next(v_inputString_42_, v_pos_39_);
v_s_46_ = l_Lean_Parser_ParserState_setPos(v_s_38_, v___x_45_);
v___x_47_ = 34;
v___x_48_ = lean_uint32_dec_eq(v_curr_44_, v___x_47_);
if (v___x_48_ == 0)
{
uint32_t v___x_49_; uint8_t v___x_50_; 
v___x_49_ = 92;
v___x_50_ = lean_uint32_dec_eq(v_curr_44_, v___x_49_);
if (v___x_50_ == 0)
{
uint32_t v___x_51_; uint8_t v___x_52_; 
v___x_51_ = 123;
v___x_52_ = lean_uint32_dec_eq(v_curr_44_, v___x_51_);
if (v___x_52_ == 0)
{
v_s_38_ = v_s_46_;
goto _start;
}
else
{
lean_object* v___x_54_; lean_object* v_s_55_; lean_object* v_s_56_; lean_object* v_pos_57_; lean_object* v_errorMsg_58_; lean_object* v___x_59_; uint8_t v___x_60_; uint8_t v___x_61_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1));
lean_inc_ref_n(v_c_37_, 2);
v_s_55_ = l_Lean_Parser_mkNodeToken(v___x_54_, v_startPos_36_, v___x_43_, v_c_37_, v_s_46_);
lean_inc_ref(v_p_34_);
v_s_56_ = lean_apply_2(v_p_34_, v_c_37_, v_s_55_);
v_pos_57_ = lean_ctor_get(v_s_56_, 2);
lean_inc(v_pos_57_);
v_errorMsg_58_ = lean_ctor_get(v_s_56_, 4);
lean_inc(v_errorMsg_58_);
v___x_59_ = lean_box(0);
v___x_60_ = l_Option_instBEq_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(v_errorMsg_58_, v___x_59_);
v___x_61_ = lean_bool_not(v___x_60_);
if (v___x_61_ == 0)
{
uint32_t v_curr_62_; uint32_t v___x_63_; uint8_t v___x_64_; 
v_curr_62_ = lean_string_utf8_get(v_inputString_42_, v_pos_57_);
v___x_63_ = 125;
v___x_64_ = lean_uint32_dec_eq(v_curr_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v_s_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_pos_57_);
lean_dec_ref(v_c_37_);
lean_dec_ref(v_p_34_);
v___x_65_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__2));
v_s_66_ = l_Lean_Parser_ParserState_mkError(v_s_56_, v___x_65_);
v___x_67_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4));
v___x_68_ = l_Lean_Parser_ParserState_mkNode(v_s_66_, v___x_67_, v_stackSize_35_);
lean_dec(v_stackSize_35_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v_s_70_; 
v___x_69_ = lean_string_utf8_next(v_inputString_42_, v_pos_57_);
v_s_70_ = l_Lean_Parser_ParserState_setPos(v_s_56_, v___x_69_);
v_startPos_36_ = v_pos_57_;
v_s_38_ = v_s_70_;
goto _start;
}
}
else
{
lean_dec(v_pos_57_);
lean_dec_ref(v_c_37_);
lean_dec(v_stackSize_35_);
lean_dec_ref(v_p_34_);
return v_s_56_;
}
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__6));
v___x_73_ = lean_alloc_closure((void*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse), 5, 3);
lean_closure_set(v___x_73_, 0, v_p_34_);
lean_closure_set(v___x_73_, 1, v_stackSize_35_);
lean_closure_set(v___x_73_, 2, v_startPos_36_);
v___x_74_ = l_Lean_Parser_andthenFn(v___x_72_, v___x_73_, v_c_37_, v_s_46_);
return v___x_74_;
}
}
else
{
lean_object* v___x_75_; lean_object* v_s_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec_ref(v_p_34_);
v___x_75_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1));
v_s_76_ = l_Lean_Parser_mkNodeToken(v___x_75_, v_startPos_36_, v___x_43_, v_c_37_, v_s_46_);
v___x_77_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4));
v___x_78_ = l_Lean_Parser_ParserState_mkNode(v_s_76_, v___x_77_, v_stackSize_35_);
lean_dec(v_stackSize_35_);
return v___x_78_;
}
}
else
{
lean_object* v___x_79_; lean_object* v_s_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec_ref(v_c_37_);
lean_dec(v_startPos_36_);
lean_dec_ref(v_p_34_);
v___x_79_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__7));
v_s_80_ = l_Lean_Parser_ParserState_mkError(v_s_38_, v___x_79_);
v___x_81_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4));
v___x_82_ = l_Lean_Parser_ParserState_mkNode(v_s_80_, v___x_81_, v_stackSize_35_);
lean_dec(v_stackSize_35_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn(lean_object* v_p_84_, lean_object* v_c_85_, lean_object* v_s_86_){
_start:
{
lean_object* v_pos_87_; lean_object* v_toInputContext_88_; uint8_t v___x_89_; 
v_pos_87_ = lean_ctor_get(v_s_86_, 2);
v_toInputContext_88_ = lean_ctor_get(v_c_85_, 0);
v___x_89_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_88_, v_pos_87_);
if (v___x_89_ == 0)
{
lean_object* v_inputString_90_; uint32_t v_curr_91_; uint32_t v___x_92_; uint8_t v___x_93_; uint8_t v___x_94_; 
v_inputString_90_ = lean_ctor_get(v_toInputContext_88_, 0);
v_curr_91_ = lean_string_utf8_get(v_inputString_90_, v_pos_87_);
v___x_92_ = 34;
v___x_93_ = lean_uint32_dec_eq(v_curr_91_, v___x_92_);
v___x_94_ = lean_bool_not(v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v_stackSize_95_; lean_object* v_s_96_; lean_object* v___x_97_; 
lean_inc(v_pos_87_);
v_stackSize_95_ = l_Lean_Parser_ParserState_stackSize(v_s_86_);
v_s_96_ = l_Lean_Parser_ParserState_next(v_s_86_, v_c_85_, v_pos_87_);
v___x_97_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse(v_p_84_, v_stackSize_95_, v_pos_87_, v_c_85_, v_s_96_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec_ref(v_c_85_);
lean_dec_ref(v_p_84_);
v___x_98_ = ((lean_object*)(l_Lean_Parser_interpolatedStrFn___closed__0));
v___x_99_ = l_Lean_Parser_ParserState_mkError(v_s_86_, v___x_98_);
return v___x_99_;
}
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec_ref(v_c_85_);
lean_dec_ref(v_p_84_);
v___x_100_ = lean_box(0);
v___x_101_ = l_Lean_Parser_ParserState_mkEOIError(v_s_86_, v___x_100_);
return v___x_101_;
}
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = ((lean_object*)(l_Lean_Parser_interpolatedStrNoAntiquot___closed__0));
v___x_104_ = l_Lean_Parser_mkAtomicInfo(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrNoAntiquot(lean_object* v_p_105_){
_start:
{
lean_object* v___x_106_; lean_object* v_fn_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_116_; 
v___x_106_ = l_Lean_Parser_withoutPosition(v_p_105_);
v_fn_107_ = lean_ctor_get(v___x_106_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; 
v_unused_117_ = lean_ctor_get(v___x_106_, 0);
lean_dec(v_unused_117_);
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_116_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_fn_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_116_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_111_ = lean_obj_once(&l_Lean_Parser_interpolatedStrNoAntiquot___closed__1, &l_Lean_Parser_interpolatedStrNoAntiquot___closed__1_once, _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1);
v___x_112_ = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(v___x_112_, 0, v_fn_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_112_);
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_114_ = v___x_109_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___closed__0(void){
_start:
{
uint8_t v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_118_ = 0;
v___x_119_ = 1;
v___x_120_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4));
v___x_121_ = ((lean_object*)(l_Lean_Parser_interpolatedStrNoAntiquot___closed__0));
v___x_122_ = l_Lean_Parser_mkAntiquot(v___x_121_, v___x_120_, v___x_119_, v___x_118_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr(lean_object* v_p_123_){
_start:
{
lean_object* v___x_124_; lean_object* v_fn_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_136_; 
v___x_124_ = l_Lean_Parser_withoutPosition(v_p_123_);
v_fn_125_ = lean_ctor_get(v___x_124_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_124_, 0);
lean_dec(v_unused_137_);
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_136_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_fn_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_136_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_129_ = lean_obj_once(&l_Lean_Parser_interpolatedStr___closed__0, &l_Lean_Parser_interpolatedStr___closed__0_once, _init_l_Lean_Parser_interpolatedStr___closed__0);
v___x_130_ = lean_obj_once(&l_Lean_Parser_interpolatedStrNoAntiquot___closed__1, &l_Lean_Parser_interpolatedStrNoAntiquot___closed__1_once, _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1);
v___x_131_ = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(v___x_131_, 0, v_fn_125_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_131_);
lean_ctor_set(v___x_127_, 0, v___x_130_);
v___x_133_ = v___x_127_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_135_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Parser_withAntiquot(v___x_129_, v___x_133_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1(){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2));
v___x_147_ = ((lean_object*)(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3));
v___x_148_ = l_Lean_addBuiltinDocString(v___x_146_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___boxed(lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1();
return v_res_150_;
}
}
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_StrInterpolation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
