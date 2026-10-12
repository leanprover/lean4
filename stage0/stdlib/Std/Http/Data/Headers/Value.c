// Lean compiler output
// Module: Std.Http.Data.Headers.Value
// Imports: public import Init.Data.ToString public import Std.Http.Internal
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_toListImpl(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_List_getLast_x3f___redArg(lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value;
static const lean_string_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value;
static const lean_string_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value;
static const lean_string_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__3 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__3_value;
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_0),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_1),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_2),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value;
static const lean_array_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5_value;
static const lean_string_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__6 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__6_value;
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_0),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_1),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_2),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value;
static const lean_string_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__8 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__8_value;
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__9 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__9_value;
static const lean_string_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__10 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__10_value;
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_0),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_1),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_2),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13;
static const lean_string_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__14 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__14_value;
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_0),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_1),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_2),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value;
static const lean_ctor_object l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__9_value),((lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5_value)}};
static const lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__16 = (const lean_object*)&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__16_value;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25;
static lean_once_cell_t l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26;
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_isValidHeaderValue___autoParam;
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqValue_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqValue_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instBEqValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instBEqValue_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instBEqValue___closed__0 = (const lean_object*)&l_Std_Http_Header_instBEqValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instBEqValue = (const lean_object*)&l_Std_Http_Header_instBEqValue___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Header_instDecidableEqValue_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instDecidableEqValue_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Header_instDecidableEqValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instDecidableEqValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprValue_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Header_instReprValue_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Header_instReprValue_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_instReprValue_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Header_instReprValue_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Header_instReprValue_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Header_instReprValue_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_Header_instReprValue_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__3_value),((lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Header_instReprValue_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_Header_instReprValue_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Header_instReprValue_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_Header_instReprValue_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "isValidHeaderValue"};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Http_Header_instReprValue_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Http_Header_instReprValue_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__12 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Http_Header_instReprValue_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__13 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__13_value;
static const lean_string_object l_Std_Http_Header_instReprValue_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__14 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__14_value;
static lean_once_cell_t l_Std_Http_Header_instReprValue_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__15;
static lean_once_cell_t l_Std_Http_Header_instReprValue_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__16;
static const lean_ctor_object l_Std_Http_Header_instReprValue_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__17 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__17_value;
static const lean_ctor_object l_Std_Http_Header_instReprValue_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__14_value)}};
static const lean_object* l_Std_Http_Header_instReprValue_repr___redArg___closed__18 = (const lean_object*)&l_Std_Http_Header_instReprValue_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprValue_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprValue_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprValue_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instReprValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instReprValue_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instReprValue___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instReprValue = (const lean_object*)&l_Std_Http_Header_instReprValue___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_instHashableValue___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instHashableValue___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Header_instHashableValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instHashableValue___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instHashableValue___closed__0 = (const lean_object*)&l_Std_Http_Header_instHashableValue___closed__0_value;
static const lean_closure_object l_Std_Http_Header_instHashableValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instHashableValue___closed__1 = (const lean_object*)&l_Std_Http_Header_instHashableValue___closed__1_value;
static const lean_closure_object l_Std_Http_Header_instHashableValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_instHashableValue___closed__1_value),((lean_object*)&l_Std_Http_Header_instHashableValue___closed__0_value)} };
static const lean_object* l_Std_Http_Header_instHashableValue___closed__2 = (const lean_object*)&l_Std_Http_Header_instHashableValue___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instHashableValue = (const lean_object*)&l_Std_Http_Header_instHashableValue___closed__2_value;
static const lean_string_object l_Std_Http_Header_instInhabitedValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Header_instInhabitedValue___closed__0 = (const lean_object*)&l_Std_Http_Header_instInhabitedValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instInhabitedValue = (const lean_object*)&l_Std_Http_Header_instInhabitedValue___closed__0_value;
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Header_Value_ofString_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Header_Value_ofString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Http.Data.Headers.Value"};
static const lean_object* l_Std_Http_Header_Value_ofString_x21___closed__0 = (const lean_object*)&l_Std_Http_Header_Value_ofString_x21___closed__0_value;
static const lean_string_object l_Std_Http_Header_Value_ofString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Http.Header.Value.ofString!"};
static const lean_object* l_Std_Http_Header_Value_ofString_x21___closed__1 = (const lean_object*)&l_Std_Http_Header_Value_ofString_x21___closed__1_value;
static const lean_string_object l_Std_Http_Header_Value_ofString_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid header value: "};
static const lean_object* l_Std_Http_Header_Value_ofString_x21___closed__2 = (const lean_object*)&l_Std_Http_Header_Value_ofString_x21___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Header_Value_is_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Header_Value_is(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_is___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Header_Value_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Value_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Value_instToString___closed__0 = (const lean_object*)&l_Std_Http_Header_Value_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Value_instToString = (const lean_object*)&l_Std_Http_Header_Value_instToString___closed__0_value;
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12);
v___x_30_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__16));
v___x_43_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5));
v___x_44_ = lean_array_push(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17);
v___x_46_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15));
v___x_47_ = lean_box(2);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18);
v___x_50_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19);
v___x_53_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11));
v___x_54_ = lean_box(2);
v___x_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20);
v___x_57_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21);
v___x_60_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__9));
v___x_61_ = lean_box(2);
v___x_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22);
v___x_64_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5));
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23);
v___x_67_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7));
v___x_68_ = lean_box(2);
v___x_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24);
v___x_71_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5));
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25);
v___x_74_ = ((lean_object*)(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4));
v___x_75_ = lean_box(2);
v___x_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26, &l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26_once, _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26);
return v___x_77_;
}
}
uint8_t l_Std_Http_Header_instBEqValue_beq(lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = lean_string_dec_eq(v_x_78_, v_x_79_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Std_Http_Header_instBEqValue_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_78_ = stack[0].m_obj;
lean_object* v_x_79_ = stack[1].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Std_Http_Header_instBEqValue_beq(v_x_78_, v_x_79_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqValue_beq___boxed(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Std_Http_Header_instBEqValue_beq(v_x_82_, v_x_83_);
lean_dec_ref(v_x_83_);
lean_dec_ref(v_x_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
uint8_t l_Std_Http_Header_instDecidableEqValue_decEq(lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_string_dec_eq(v_x_88_, v_x_89_);
return v___x_90_;
}
}
LEAN_EXPORT void l_Std_Http_Header_instDecidableEqValue_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_88_ = stack[0].m_obj;
lean_object* v_x_89_ = stack[1].m_obj;
uint8_t v_res_91_;
v_res_91_ = l_Std_Http_Header_instDecidableEqValue_decEq(v_x_88_, v_x_89_);
stack->m_num = v_res_91_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instDecidableEqValue_decEq___boxed(lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Std_Http_Header_instDecidableEqValue_decEq(v_x_92_, v_x_93_);
lean_dec_ref(v_x_93_);
lean_dec_ref(v_x_92_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
uint8_t l_Std_Http_Header_instDecidableEqValue(lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = lean_string_dec_eq(v_x_96_, v_x_97_);
return v___x_98_;
}
}
LEAN_EXPORT void l_Std_Http_Header_instDecidableEqValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_96_ = stack[0].m_obj;
lean_object* v_x_97_ = stack[1].m_obj;
uint8_t v_res_99_;
v_res_99_ = l_Std_Http_Header_instDecidableEqValue(v_x_96_, v_x_97_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instDecidableEqValue___boxed(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Std_Http_Header_instDecidableEqValue(v_x_100_, v_x_101_);
lean_dec_ref(v_x_101_);
lean_dec_ref(v_x_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprValue_repr_spec__0(lean_object* v_a_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_nat_to_int(v_a_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(9u);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__0));
v___x_132_ = lean_string_length(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_obj_once(&l_Std_Http_Header_instReprValue_repr___redArg___closed__15, &l_Std_Http_Header_instReprValue_repr___redArg___closed__15_once, _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__15);
v___x_134_ = lean_nat_to_int(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprValue_repr___redArg(lean_object* v_x_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_140_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__5));
v___x_141_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__6));
v___x_142_ = lean_obj_once(&l_Std_Http_Header_instReprValue_repr___redArg___closed__7, &l_Std_Http_Header_instReprValue_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__7);
v___x_143_ = l_String_quote(v_x_139_);
v___x_144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
v___x_145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_142_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = 0;
v___x_147_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*1, v___x_146_);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_141_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__9));
v___x_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = lean_box(1);
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__11));
v___x_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_140_);
v___x_156_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__13));
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_obj_once(&l_Std_Http_Header_instReprValue_repr___redArg___closed__16, &l_Std_Http_Header_instReprValue_repr___redArg___closed__16_once, _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__16);
v___x_159_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__17));
v___x_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_157_);
v___x_161_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__18));
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_158_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*1, v___x_146_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprValue_repr(lean_object* v_x_165_, lean_object* v_prec_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Std_Http_Header_instReprValue_repr___redArg(v_x_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprValue_repr___boxed(lean_object* v_x_168_, lean_object* v_prec_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_Http_Header_instReprValue_repr(v_x_168_, v_prec_169_);
lean_dec(v_prec_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instHashableValue___lam__0(lean_object* v_self_173_){
_start:
{
lean_inc_ref(v_self_173_);
return v_self_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instHashableValue___lam__0___boxed(lean_object* v_self_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_Http_Header_instHashableValue___lam__0(v_self_174_);
lean_dec_ref(v_self_174_);
return v_res_175_;
}
}
uint8_t l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0(lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
uint8_t v___x_185_; 
v___x_185_ = 1;
return v___x_185_;
}
else
{
lean_object* v_head_186_; lean_object* v_tail_187_; uint32_t v___x_197_; uint32_t v___x_198_; uint8_t v___x_199_; 
v_head_186_ = lean_ctor_get(v_x_184_, 0);
v_tail_187_ = lean_ctor_get(v_x_184_, 1);
v___x_197_ = 33;
v___x_198_ = lean_unbox_uint32(v_head_186_);
v___x_199_ = lean_uint32_dec_le(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
goto v___jp_188_;
}
else
{
uint32_t v___x_200_; uint32_t v___x_201_; uint8_t v___x_202_; 
v___x_200_ = 126;
v___x_201_ = lean_unbox_uint32(v_head_186_);
v___x_202_ = lean_uint32_dec_le(v___x_201_, v___x_200_);
if (v___x_202_ == 0)
{
goto v___jp_188_;
}
else
{
v_x_184_ = v_tail_187_;
goto _start;
}
}
v___jp_188_:
{
uint32_t v___x_189_; uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_189_ = 32;
v___x_190_ = lean_unbox_uint32(v_head_186_);
v___x_191_ = lean_uint32_dec_eq(v___x_190_, v___x_189_);
if (v___x_191_ == 0)
{
uint32_t v___x_192_; uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_192_ = 9;
v___x_193_ = lean_unbox_uint32(v_head_186_);
v___x_194_ = lean_uint32_dec_eq(v___x_193_, v___x_192_);
if (v___x_194_ == 0)
{
return v___x_194_;
}
else
{
v_x_184_ = v_tail_187_;
goto _start;
}
}
else
{
v_x_184_ = v_tail_187_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_184_ = stack[0].m_obj;
uint8_t v_res_204_;
v_res_204_ = l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0(v_x_184_);
stack->m_num = v_res_204_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0___boxed(lean_object* v_x_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0(v_x_205_);
lean_dec(v_x_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_ofString_x3f(lean_object* v_s_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_val_213_; uint8_t v___y_215_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_string_utf8_byte_size(v_s_208_);
v___x_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_211_, 0, v_s_208_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
lean_ctor_set(v___x_211_, 2, v___x_210_);
v___x_212_ = l_String_Slice_trimAscii(v___x_211_);
v_val_213_ = l_String_Slice_toString(v___x_212_);
lean_dec_ref(v___x_212_);
lean_inc_ref(v_val_213_);
v___x_218_ = l_String_toListImpl(v_val_213_);
v___x_219_ = l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0(v___x_218_);
if (v___x_219_ == 0)
{
lean_dec(v___x_218_);
v___y_215_ = v___x_219_;
goto v___jp_214_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = l_List_head_x3f___redArg(v___x_218_);
if (lean_obj_tag(v___x_230_) == 0)
{
goto v___jp_220_;
}
else
{
lean_object* v_val_231_; uint32_t v___x_232_; uint32_t v___x_233_; uint8_t v___x_234_; 
v_val_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = 33;
v___x_233_ = lean_unbox_uint32(v_val_231_);
v___x_234_ = lean_uint32_dec_le(v___x_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
lean_dec(v_val_231_);
lean_dec(v___x_218_);
lean_dec_ref(v_val_213_);
v___x_235_ = lean_box(0);
return v___x_235_;
}
else
{
uint32_t v___x_236_; uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_236_ = 126;
v___x_237_ = lean_unbox_uint32(v_val_231_);
lean_dec(v_val_231_);
v___x_238_ = lean_uint32_dec_le(v___x_237_, v___x_236_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec(v___x_218_);
lean_dec_ref(v_val_213_);
v___x_239_ = lean_box(0);
return v___x_239_;
}
else
{
goto v___jp_220_;
}
}
}
}
v___jp_214_:
{
if (v___y_215_ == 0)
{
lean_object* v___x_216_; 
lean_dec_ref(v_val_213_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v_val_213_);
return v___x_217_;
}
}
v___jp_220_:
{
lean_object* v___x_221_; 
v___x_221_ = l_List_getLast_x3f___redArg(v___x_218_);
lean_dec(v___x_218_);
if (lean_obj_tag(v___x_221_) == 0)
{
v___y_215_ = v___x_219_;
goto v___jp_214_;
}
else
{
lean_object* v_val_222_; uint32_t v___x_223_; uint32_t v___x_224_; uint8_t v___x_225_; 
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_221_, 1);
v___x_223_ = 33;
v___x_224_ = lean_unbox_uint32(v_val_222_);
v___x_225_ = lean_uint32_dec_le(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_dec(v_val_222_);
lean_dec_ref(v_val_213_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
uint32_t v___x_227_; uint32_t v___x_228_; uint8_t v___x_229_; 
v___x_227_ = 126;
v___x_228_ = lean_unbox_uint32(v_val_222_);
lean_dec(v_val_222_);
v___x_229_ = lean_uint32_dec_le(v___x_228_, v___x_227_);
v___y_215_ = v___x_229_;
goto v___jp_214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Header_Value_ofString_x21_spec__0(lean_object* v_msg_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Std_Http_Header_instInhabitedValue___closed__0));
v___x_242_ = lean_panic_fn_borrowed(v___x_241_, v_msg_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object* v_s_246_){
_start:
{
lean_object* v___x_247_; 
lean_inc_ref(v_s_246_);
v___x_247_ = l_Std_Http_Header_Value_ofString_x3f(v_s_246_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_248_ = ((lean_object*)(l_Std_Http_Header_Value_ofString_x21___closed__0));
v___x_249_ = ((lean_object*)(l_Std_Http_Header_Value_ofString_x21___closed__1));
v___x_250_ = lean_unsigned_to_nat(91u);
v___x_251_ = lean_unsigned_to_nat(12u);
v___x_252_ = ((lean_object*)(l_Std_Http_Header_Value_ofString_x21___closed__2));
v___x_253_ = l_String_quote(v_s_246_);
v___x_254_ = lean_string_append(v___x_252_, v___x_253_);
lean_dec_ref(v___x_253_);
v___x_255_ = l_mkPanicMessageWithDecl(v___x_248_, v___x_249_, v___x_250_, v___x_251_, v___x_254_);
lean_dec_ref(v___x_254_);
v___x_256_ = l_panic___at___00Std_Http_Header_Value_ofString_x21_spec__0(v___x_255_);
return v___x_256_;
}
else
{
lean_object* v_val_257_; 
lean_dec_ref(v_s_246_);
v_val_257_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_val_257_);
lean_dec_ref_known(v___x_247_, 1);
return v_val_257_;
}
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Header_Value_is_spec__0(lean_object* v_s_258_, lean_object* v_p_259_){
_start:
{
uint32_t v___y_261_; lean_object* v___x_266_; uint8_t v_decide_267_; 
v___x_266_ = lean_string_utf8_byte_size(v_s_258_);
v_decide_267_ = lean_nat_dec_eq(v_p_259_, v___x_266_);
if (v_decide_267_ == 0)
{
uint32_t v___x_268_; uint32_t v___x_269_; uint8_t v___x_270_; 
v___x_268_ = lean_string_utf8_get_fast(v_s_258_, v_p_259_);
v___x_269_ = 65;
v___x_270_ = lean_uint32_dec_le(v___x_269_, v___x_268_);
if (v___x_270_ == 0)
{
v___y_261_ = v___x_268_;
goto v___jp_260_;
}
else
{
uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = 90;
v___x_272_ = lean_uint32_dec_le(v___x_268_, v___x_271_);
if (v___x_272_ == 0)
{
v___y_261_ = v___x_268_;
goto v___jp_260_;
}
else
{
uint32_t v___x_273_; uint32_t v___x_274_; 
v___x_273_ = 32;
v___x_274_ = lean_uint32_add(v___x_268_, v___x_273_);
v___y_261_ = v___x_274_;
goto v___jp_260_;
}
}
}
else
{
lean_dec(v_p_259_);
return v_s_258_;
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
lean_inc(v_p_259_);
v___x_262_ = lean_string_utf8_set(v_s_258_, v_p_259_, v___y_261_);
v___x_263_ = l_Char_utf8Size(v___y_261_);
v___x_264_ = lean_nat_add(v_p_259_, v___x_263_);
lean_dec(v___x_263_);
lean_dec(v_p_259_);
v_s_258_ = v___x_262_;
v_p_259_ = v___x_264_;
goto _start;
}
}
}
uint8_t l_Std_Http_Header_Value_is(lean_object* v_s_275_, lean_object* v_h_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_String_mapAux___at___00Std_Http_Header_Value_is_spec__0(v_s_275_, v___x_277_);
v___x_279_ = l_String_mapAux___at___00Std_Http_Header_Value_is_spec__0(v_h_276_, v___x_277_);
v___x_280_ = lean_string_dec_eq(v___x_278_, v___x_279_);
lean_dec_ref(v___x_279_);
lean_dec_ref(v___x_278_);
return v___x_280_;
}
}
LEAN_EXPORT void l_Std_Http_Header_Value_is_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_275_ = stack[0].m_obj;
lean_object* v_h_276_ = stack[1].m_obj;
uint8_t v_res_281_;
v_res_281_ = l_Std_Http_Header_Value_is(v_s_275_, v_h_276_);
stack->m_num = v_res_281_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_is___boxed(lean_object* v_s_282_, lean_object* v_h_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Std_Http_Header_Value_is(v_s_282_, v_h_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_instToString___lam__0(lean_object* v_v_286_){
_start:
{
lean_inc_ref(v_v_286_);
return v_v_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_instToString___lam__0___boxed(lean_object* v_v_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Http_Header_Value_instToString___lam__0(v_v_287_);
lean_dec_ref(v_v_287_);
return v_res_288_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Headers_Value(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Headers_Value(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Http_Header_Value_isValidHeaderValue___autoParam = _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam();
lean_mark_persistent(l_Std_Http_Header_Value_isValidHeaderValue___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Std_Http_Internal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Headers_Value(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Headers_Value(builtin);
}
#ifdef __cplusplus
}
#endif
