// Lean compiler output
// Module: Std.Http.Data.Headers.Name
// Imports: public import Init.Data.ToString public import Std.Http.Internal import Init.Data.String.Search import Init.Data.String.Iter
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t l_Std_Http_Internal_isToken(lean_object*);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
static const lean_string_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value;
static const lean_string_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value;
static const lean_string_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__3 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__3_value;
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_0),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_1),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_2),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value;
static const lean_array_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5_value;
static const lean_string_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__6 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__6_value;
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_0),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_1),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_2),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value;
static const lean_string_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__8 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__8_value;
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__9 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__9_value;
static const lean_string_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__10 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__10_value;
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_0),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_1),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_2),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13;
static const lean_string_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__14 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__14_value;
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_0),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_1),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_2),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value;
static const lean_ctor_object l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__9_value),((lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5_value)}};
static const lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__16 = (const lean_object*)&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__16_value;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25;
static lean_once_cell_t l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26;
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_isValidHeaderValue___autoParam;
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_isLowerCase___autoParam;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprName_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Header_instReprName_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Header_instReprName_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_instReprName_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Header_instReprName_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Header_instReprName_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Header_instReprName_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_Header_instReprName_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__3_value),((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Header_instReprName_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_Header_instReprName_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Header_instReprName_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_Header_instReprName_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "isValidHeaderValue"};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Http_Header_instReprName_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Http_Header_instReprName_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__12 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Http_Header_instReprName_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__13 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__13_value;
static const lean_string_object l_Std_Http_Header_instReprName_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "isLowerCase"};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__14 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__14_value;
static const lean_ctor_object l_Std_Http_Header_instReprName_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__14_value)}};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__15 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__15_value;
static const lean_string_object l_Std_Http_Header_instReprName_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__16 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__16_value;
static lean_once_cell_t l_Std_Http_Header_instReprName_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__17;
static lean_once_cell_t l_Std_Http_Header_instReprName_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__18;
static const lean_ctor_object l_Std_Http_Header_instReprName_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__19 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__19_value;
static const lean_ctor_object l_Std_Http_Header_instReprName_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__16_value)}};
static const lean_object* l_Std_Http_Header_instReprName_repr___redArg___closed__20 = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__20_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprName_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprName_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprName_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instReprName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instReprName_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instReprName___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprName___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instReprName = (const lean_object*)&l_Std_Http_Header_instReprName___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Header_instDecidableEqName_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instDecidableEqName_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Header_instDecidableEqName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instDecidableEqName___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_Name_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Name_instBEq___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_instBEq = (const lean_object*)&l_Std_Http_Header_Name_instBEq___closed__0_value;
static const lean_closure_object l_Std_Http_Header_Name_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Name_instHashable___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_instHashable = (const lean_object*)&l_Std_Http_Header_Name_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_instInhabited = (const lean_object*)&l_Std_Http_Header_instReprName_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Header_Name_ofString_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Header_Name_ofString_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Header_Name_ofString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Http.Data.Headers.Name"};
static const lean_object* l_Std_Http_Header_Name_ofString_x21___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_ofString_x21___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_ofString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Std.Http.Header.Name.ofString!"};
static const lean_object* l_Std_Http_Header_Name_ofString_x21___closed__1 = (const lean_object*)&l_Std_Http_Header_Name_ofString_x21___closed__1_value;
static const lean_string_object l_Std_Http_Header_Name_ofString_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid header name: "};
static const lean_object* l_Std_Http_Header_Name_ofString_x21___closed__2 = (const lean_object*)&l_Std_Http_Header_Name_ofString_x21___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_toCanonical___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_toCanonical___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_Name_toCanonical___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Name_toCanonical___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_toCanonical___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_toCanonical___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Header_Name_toCanonical___closed__1 = (const lean_object*)&l_Std_Http_Header_Name_toCanonical___closed__1_value;
static lean_once_cell_t l_Std_Http_Header_Name_toCanonical___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Name_toCanonical___closed__2;
static const lean_string_object l_Std_Http_Header_Name_toCanonical___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Header_Name_toCanonical___closed__3 = (const lean_object*)&l_Std_Http_Header_Name_toCanonical___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_toCanonical(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Header_Name_is(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_is___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_instToString___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_instToString___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_instToString___lam__1(lean_object*);
static const lean_closure_object l_Std_Http_Header_Name_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Name_instToString___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Name_instToString___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_instToString = (const lean_object*)&l_Std_Http_Header_Name_instToString___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_contentType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "content-type"};
static const lean_object* l_Std_Http_Header_Name_contentType___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_contentType___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_contentType = (const lean_object*)&l_Std_Http_Header_Name_contentType___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_contentLength___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "content-length"};
static const lean_object* l_Std_Http_Header_Name_contentLength___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_contentLength___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_contentLength = (const lean_object*)&l_Std_Http_Header_Name_contentLength___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_host___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "host"};
static const lean_object* l_Std_Http_Header_Name_host___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_host___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_host = (const lean_object*)&l_Std_Http_Header_Name_host___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_authorization___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "authorization"};
static const lean_object* l_Std_Http_Header_Name_authorization___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_authorization___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_authorization = (const lean_object*)&l_Std_Http_Header_Name_authorization___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_userAgent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "user-agent"};
static const lean_object* l_Std_Http_Header_Name_userAgent___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_userAgent___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_userAgent = (const lean_object*)&l_Std_Http_Header_Name_userAgent___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_accept___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "accept"};
static const lean_object* l_Std_Http_Header_Name_accept___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_accept___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_accept = (const lean_object*)&l_Std_Http_Header_Name_accept___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_connection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "connection"};
static const lean_object* l_Std_Http_Header_Name_connection___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_connection___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_connection = (const lean_object*)&l_Std_Http_Header_Name_connection___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_transferEncoding___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "transfer-encoding"};
static const lean_object* l_Std_Http_Header_Name_transferEncoding___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_transferEncoding___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_transferEncoding = (const lean_object*)&l_Std_Http_Header_Name_transferEncoding___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_server___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "server"};
static const lean_object* l_Std_Http_Header_Name_server___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_server___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_server = (const lean_object*)&l_Std_Http_Header_Name_server___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_date___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "date"};
static const lean_object* l_Std_Http_Header_Name_date___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_date___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_date = (const lean_object*)&l_Std_Http_Header_Name_date___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_expect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expect"};
static const lean_object* l_Std_Http_Header_Name_expect___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_expect___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_expect = (const lean_object*)&l_Std_Http_Header_Name_expect___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_cookie___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cookie"};
static const lean_object* l_Std_Http_Header_Name_cookie___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_cookie___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_cookie = (const lean_object*)&l_Std_Http_Header_Name_cookie___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_setCookie___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "set-cookie"};
static const lean_object* l_Std_Http_Header_Name_setCookie___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_setCookie___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_setCookie = (const lean_object*)&l_Std_Http_Header_Name_setCookie___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_location___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Std_Http_Header_Name_location___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_location___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_location = (const lean_object*)&l_Std_Http_Header_Name_location___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_proxyAuthorization___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "proxy-authorization"};
static const lean_object* l_Std_Http_Header_Name_proxyAuthorization___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_proxyAuthorization___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_proxyAuthorization = (const lean_object*)&l_Std_Http_Header_Name_proxyAuthorization___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_contentEncoding___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "content-encoding"};
static const lean_object* l_Std_Http_Header_Name_contentEncoding___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_contentEncoding___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_contentEncoding = (const lean_object*)&l_Std_Http_Header_Name_contentEncoding___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_contentLanguage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "content-language"};
static const lean_object* l_Std_Http_Header_Name_contentLanguage___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_contentLanguage___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_contentLanguage = (const lean_object*)&l_Std_Http_Header_Name_contentLanguage___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_contentLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "content-location"};
static const lean_object* l_Std_Http_Header_Name_contentLocation___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_contentLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_contentLocation = (const lean_object*)&l_Std_Http_Header_Name_contentLocation___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_lastModified___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "last-modified"};
static const lean_object* l_Std_Http_Header_Name_lastModified___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_lastModified___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_lastModified = (const lean_object*)&l_Std_Http_Header_Name_lastModified___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_referer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "referer"};
static const lean_object* l_Std_Http_Header_Name_referer___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_referer___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_referer = (const lean_object*)&l_Std_Http_Header_Name_referer___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_origin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Std_Http_Header_Name_origin___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_origin___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_origin = (const lean_object*)&l_Std_Http_Header_Name_origin___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_keepAlive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "keep-alive"};
static const lean_object* l_Std_Http_Header_Name_keepAlive___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_keepAlive___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_keepAlive = (const lean_object*)&l_Std_Http_Header_Name_keepAlive___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_ifNoneMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "if-none-match"};
static const lean_object* l_Std_Http_Header_Name_ifNoneMatch___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_ifNoneMatch___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_ifNoneMatch = (const lean_object*)&l_Std_Http_Header_Name_ifNoneMatch___closed__0_value;
static const lean_string_object l_Std_Http_Header_Name_ifModifiedSince___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "if-modified-since"};
static const lean_object* l_Std_Http_Header_Name_ifModifiedSince___closed__0 = (const lean_object*)&l_Std_Http_Header_Name_ifModifiedSince___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Name_ifModifiedSince = (const lean_object*)&l_Std_Http_Header_Name_ifModifiedSince___closed__0_value;
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12);
v___x_30_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__16));
v___x_43_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5));
v___x_44_ = lean_array_push(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17);
v___x_46_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15));
v___x_47_ = lean_box(2);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18);
v___x_50_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19);
v___x_53_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11));
v___x_54_ = lean_box(2);
v___x_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20);
v___x_57_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21);
v___x_60_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__9));
v___x_61_ = lean_box(2);
v___x_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22);
v___x_64_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5));
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23);
v___x_67_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7));
v___x_68_ = lean_box(2);
v___x_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24);
v___x_71_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5));
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25);
v___x_74_ = ((lean_object*)(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4));
v___x_75_ = lean_box(2);
v___x_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26);
return v___x_77_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_isLowerCase___autoParam(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26, &l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26_once, _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprName_repr_spec__0(lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_nat_to_int(v_a_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprName_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(9u);
v___x_95_ = lean_nat_to_int(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprName_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Std_Http_Header_instReprName_repr___redArg___closed__0));
v___x_110_ = lean_string_length(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprName_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_Std_Http_Header_instReprName_repr___redArg___closed__17, &l_Std_Http_Header_instReprName_repr___redArg___closed__17_once, _init_l_Std_Http_Header_instReprName_repr___redArg___closed__17);
v___x_112_ = lean_nat_to_int(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprName_repr___redArg(lean_object* v_x_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_118_ = ((lean_object*)(l_Std_Http_Header_instReprName_repr___redArg___closed__5));
v___x_119_ = ((lean_object*)(l_Std_Http_Header_instReprName_repr___redArg___closed__6));
v___x_120_ = lean_obj_once(&l_Std_Http_Header_instReprName_repr___redArg___closed__7, &l_Std_Http_Header_instReprName_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprName_repr___redArg___closed__7);
v___x_121_ = l_String_quote(v_x_117_);
v___x_122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_120_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_119_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = ((lean_object*)(l_Std_Http_Header_instReprName_repr___redArg___closed__9));
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = lean_box(1);
v___x_130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = ((lean_object*)(l_Std_Http_Header_instReprName_repr___redArg___closed__11));
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_118_);
v___x_134_ = ((lean_object*)(l_Std_Http_Header_instReprName_repr___redArg___closed__13));
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_127_);
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_129_);
v___x_138_ = ((lean_object*)(l_Std_Http_Header_instReprName_repr___redArg___closed__15));
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
v___x_140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_118_);
v___x_141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_134_);
v___x_142_ = lean_obj_once(&l_Std_Http_Header_instReprName_repr___redArg___closed__18, &l_Std_Http_Header_instReprName_repr___redArg___closed__18_once, _init_l_Std_Http_Header_instReprName_repr___redArg___closed__18);
v___x_143_ = ((lean_object*)(l_Std_Http_Header_instReprName_repr___redArg___closed__19));
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_141_);
v___x_145_ = ((lean_object*)(l_Std_Http_Header_instReprName_repr___redArg___closed__20));
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_142_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*1, v___x_124_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprName_repr(lean_object* v_x_149_, lean_object* v_prec_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Std_Http_Header_instReprName_repr___redArg(v_x_149_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprName_repr___boxed(lean_object* v_x_152_, lean_object* v_prec_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_Http_Header_instReprName_repr(v_x_152_, v_prec_153_);
lean_dec(v_prec_153_);
return v_res_154_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instDecidableEqName_decEq(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = lean_string_dec_eq(v_x_157_, v_x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instDecidableEqName_decEq___boxed(lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Std_Http_Header_instDecidableEqName_decEq(v_x_160_, v_x_161_);
lean_dec_ref(v_x_161_);
lean_dec_ref(v_x_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instDecidableEqName(lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lean_string_dec_eq(v_x_164_, v_x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instDecidableEqName___boxed(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_Http_Header_instDecidableEqName(v_x_167_, v_x_168_);
lean_dec_ref(v_x_168_);
lean_dec_ref(v_x_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Header_Name_ofString_x3f_spec__0(lean_object* v_s_176_, lean_object* v_p_177_){
_start:
{
uint32_t v___y_179_; lean_object* v___x_184_; uint8_t v_decide_185_; 
v___x_184_ = lean_string_utf8_byte_size(v_s_176_);
v_decide_185_ = lean_nat_dec_eq(v_p_177_, v___x_184_);
if (v_decide_185_ == 0)
{
uint32_t v___x_186_; uint8_t v___y_188_; uint32_t v___x_191_; uint8_t v___x_192_; 
v___x_186_ = lean_string_utf8_get_fast(v_s_176_, v_p_177_);
v___x_191_ = 65;
v___x_192_ = lean_uint32_dec_le(v___x_191_, v___x_186_);
if (v___x_192_ == 0)
{
v___y_188_ = v___x_192_;
goto v___jp_187_;
}
else
{
uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_193_ = 90;
v___x_194_ = lean_uint32_dec_le(v___x_186_, v___x_193_);
v___y_188_ = v___x_194_;
goto v___jp_187_;
}
v___jp_187_:
{
if (v___y_188_ == 0)
{
v___y_179_ = v___x_186_;
goto v___jp_178_;
}
else
{
uint32_t v___x_189_; uint32_t v___x_190_; 
v___x_189_ = 32;
v___x_190_ = lean_uint32_add(v___x_186_, v___x_189_);
v___y_179_ = v___x_190_;
goto v___jp_178_;
}
}
}
else
{
lean_dec(v_p_177_);
return v_s_176_;
}
v___jp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_inc(v_p_177_);
v___x_180_ = lean_string_utf8_set(v_s_176_, v_p_177_, v___y_179_);
v___x_181_ = l_Char_utf8Size(v___y_179_);
v___x_182_ = lean_nat_add(v_p_177_, v___x_181_);
lean_dec(v___x_181_);
lean_dec(v_p_177_);
v_s_176_ = v___x_180_;
v_p_177_ = v___x_182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object* v_s_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_val_201_; uint8_t v___y_203_; uint8_t v___x_206_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_string_utf8_byte_size(v_s_195_);
v___x_198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_198_, 0, v_s_195_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
lean_ctor_set(v___x_198_, 2, v___x_197_);
v___x_199_ = l_String_Slice_trimAscii(v___x_198_);
v___x_200_ = l_String_Slice_toString(v___x_199_);
lean_dec_ref(v___x_199_);
v_val_201_ = l_String_mapAux___at___00Std_Http_Header_Name_ofString_x3f_spec__0(v___x_200_, v___x_196_);
lean_inc_ref(v_val_201_);
v___x_206_ = l_Std_Http_Internal_isToken(v_val_201_);
if (v___x_206_ == 0)
{
v___y_203_ = v___x_206_;
goto v___jp_202_;
}
else
{
uint8_t v___x_207_; 
lean_inc_ref(v_val_201_);
v___x_207_ = l_Std_Http_Internal_instDecidableIsLowerCase(v_val_201_);
v___y_203_ = v___x_207_;
goto v___jp_202_;
}
v___jp_202_:
{
if (v___y_203_ == 0)
{
lean_object* v___x_204_; 
lean_dec_ref(v_val_201_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v_val_201_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Header_Name_ofString_x21_spec__0(lean_object* v_msg_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Std_Http_Header_instReprName_repr___redArg___closed__12));
v___x_210_ = lean_panic_fn_borrowed(v___x_209_, v_msg_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object* v_s_214_){
_start:
{
lean_object* v___x_215_; 
lean_inc_ref(v_s_214_);
v___x_215_ = l_Std_Http_Header_Name_ofString_x3f(v_s_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_216_ = ((lean_object*)(l_Std_Http_Header_Name_ofString_x21___closed__0));
v___x_217_ = ((lean_object*)(l_Std_Http_Header_Name_ofString_x21___closed__1));
v___x_218_ = lean_unsigned_to_nat(107u);
v___x_219_ = lean_unsigned_to_nat(12u);
v___x_220_ = ((lean_object*)(l_Std_Http_Header_Name_ofString_x21___closed__2));
v___x_221_ = l_String_quote(v_s_214_);
v___x_222_ = lean_string_append(v___x_220_, v___x_221_);
lean_dec_ref(v___x_221_);
v___x_223_ = l_mkPanicMessageWithDecl(v___x_216_, v___x_217_, v___x_218_, v___x_219_, v___x_222_);
lean_dec_ref(v___x_222_);
v___x_224_ = l_panic___at___00Std_Http_Header_Name_ofString_x21_spec__0(v___x_223_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; 
lean_dec_ref(v_s_214_);
v_val_225_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_215_, 1);
return v_val_225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_toCanonical___lam__0(lean_object* v___x_226_, lean_object* v___x_227_, lean_object* v___x_228_, lean_object* v_name_229_, lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v_it_232_, lean_object* v_acc_233_, lean_object* v_hP_234_, lean_object* v_recur_235_){
_start:
{
lean_object* v_it_237_; lean_object* v_out_238_; uint32_t v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; uint8_t v___y_258_; lean_object* v_it_264_; lean_object* v_startInclusive_265_; lean_object* v_endExclusive_266_; 
if (lean_obj_tag(v_it_232_) == 0)
{
lean_object* v_currPos_274_; lean_object* v_searcher_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_298_; 
v_currPos_274_ = lean_ctor_get(v_it_232_, 0);
v_searcher_275_ = lean_ctor_get(v_it_232_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_it_232_);
if (v_isSharedCheck_298_ == 0)
{
v___x_277_ = v_it_232_;
v_isShared_278_ = v_isSharedCheck_298_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_searcher_275_);
lean_inc(v_currPos_274_);
lean_dec(v_it_232_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_298_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
uint8_t v_decide_279_; 
v_decide_279_ = lean_nat_dec_eq(v_searcher_275_, v___x_230_);
if (v_decide_279_ == 0)
{
uint32_t v___x_280_; uint32_t v___x_281_; uint8_t v___x_282_; 
lean_dec(v___x_230_);
v___x_280_ = lean_string_utf8_get_fast(v_name_229_, v_searcher_275_);
v___x_281_ = 45;
v___x_282_ = lean_uint32_dec_eq(v___x_280_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_string_utf8_next_fast(v_name_229_, v_searcher_275_);
lean_dec(v_searcher_275_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v___x_283_);
v___x_285_ = v___x_277_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_currPos_274_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_283_);
v___x_285_ = v_reuseFailAlloc_287_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; 
v___x_286_ = lean_apply_4(v_recur_235_, v___x_285_, v_acc_233_, lean_box(0), lean_box(0));
return v___x_286_;
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_slice_291_; lean_object* v_nextIt_293_; 
v___x_288_ = lean_string_utf8_next_fast(v_name_229_, v_searcher_275_);
v___x_289_ = lean_nat_sub(v___x_288_, v_searcher_275_);
v___x_290_ = lean_nat_add(v_searcher_275_, v___x_289_);
lean_dec(v___x_289_);
v_slice_291_ = l_String_Slice_subslice_x21(v___x_231_, v_currPos_274_, v_searcher_275_);
lean_inc(v___x_290_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v___x_290_);
lean_ctor_set(v___x_277_, 0, v___x_290_);
v_nextIt_293_ = v___x_277_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_290_);
v_nextIt_293_ = v_reuseFailAlloc_296_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v_startInclusive_294_; lean_object* v_endExclusive_295_; 
v_startInclusive_294_ = lean_ctor_get(v_slice_291_, 0);
lean_inc(v_startInclusive_294_);
v_endExclusive_295_ = lean_ctor_get(v_slice_291_, 1);
lean_inc(v_endExclusive_295_);
lean_dec_ref(v_slice_291_);
v_it_264_ = v_nextIt_293_;
v_startInclusive_265_ = v_startInclusive_294_;
v_endExclusive_266_ = v_endExclusive_295_;
goto v___jp_263_;
}
}
}
else
{
lean_object* v___x_297_; 
lean_del_object(v___x_277_);
lean_dec(v_searcher_275_);
v___x_297_ = lean_box(1);
v_it_264_ = v___x_297_;
v_startInclusive_265_ = v_currPos_274_;
v_endExclusive_266_ = v___x_230_;
goto v___jp_263_;
}
}
}
else
{
lean_dec_ref(v_recur_235_);
lean_dec(v___x_230_);
return v_acc_233_;
}
v___jp_236_:
{
if (lean_obj_tag(v_acc_233_) == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v_out_238_);
v___x_240_ = lean_apply_4(v_recur_235_, v_it_237_, v___x_239_, lean_box(0), lean_box(0));
return v___x_240_;
}
else
{
lean_object* v_val_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_252_; 
v_val_241_ = lean_ctor_get(v_acc_233_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_acc_233_);
if (v_isSharedCheck_252_ == 0)
{
v___x_243_ = v_acc_233_;
v_isShared_244_ = v_isSharedCheck_252_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_val_241_);
lean_dec(v_acc_233_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_252_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_245_ = lean_string_utf8_extract_fast(v___x_226_, v___x_227_, v___x_228_);
v___x_246_ = lean_string_append(v_val_241_, v___x_245_);
lean_dec_ref(v___x_245_);
v___x_247_ = lean_string_append(v___x_246_, v_out_238_);
lean_dec_ref(v_out_238_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_247_);
v___x_249_ = v___x_243_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_251_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; 
v___x_250_ = lean_apply_4(v_recur_235_, v_it_237_, v___x_249_, lean_box(0), lean_box(0));
return v___x_250_;
}
}
}
}
v___jp_253_:
{
if (v___y_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_string_utf8_set(v___y_255_, v___y_257_, v___y_254_);
v_it_237_ = v___y_256_;
v_out_238_ = v___x_259_;
goto v___jp_236_;
}
else
{
uint32_t v___x_260_; uint32_t v___x_261_; lean_object* v___x_262_; 
v___x_260_ = 4294967264;
v___x_261_ = lean_uint32_add(v___y_254_, v___x_260_);
v___x_262_ = lean_string_utf8_set(v___y_255_, v___y_257_, v___x_261_);
v_it_237_ = v___y_256_;
v_out_238_ = v___x_262_;
goto v___jp_236_;
}
}
v___jp_263_:
{
lean_object* v___x_267_; lean_object* v___x_268_; uint32_t v___x_269_; uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_267_ = lean_string_utf8_extract_fast(v_name_229_, v_startInclusive_265_, v_endExclusive_266_);
lean_dec(v_endExclusive_266_);
lean_dec(v_startInclusive_265_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_string_utf8_get(v___x_267_, v___x_268_);
v___x_270_ = 97;
v___x_271_ = lean_uint32_dec_le(v___x_270_, v___x_269_);
if (v___x_271_ == 0)
{
v___y_254_ = v___x_269_;
v___y_255_ = v___x_267_;
v___y_256_ = v_it_264_;
v___y_257_ = v___x_268_;
v___y_258_ = v___x_271_;
goto v___jp_253_;
}
else
{
uint32_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = 122;
v___x_273_ = lean_uint32_dec_le(v___x_269_, v___x_272_);
v___y_254_ = v___x_269_;
v___y_255_ = v___x_267_;
v___y_256_ = v_it_264_;
v___y_257_ = v___x_268_;
v___y_258_ = v___x_273_;
goto v___jp_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_toCanonical___lam__0___boxed(lean_object* v___x_299_, lean_object* v___x_300_, lean_object* v___x_301_, lean_object* v_name_302_, lean_object* v___x_303_, lean_object* v___x_304_, lean_object* v_it_305_, lean_object* v_acc_306_, lean_object* v_hP_307_, lean_object* v_recur_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Http_Header_Name_toCanonical___lam__0(v___x_299_, v___x_300_, v___x_301_, v_name_302_, v___x_303_, v___x_304_, v_it_305_, v_acc_306_, v_hP_307_, v_recur_308_);
lean_dec_ref(v___x_304_);
lean_dec_ref(v_name_302_);
lean_dec(v___x_301_);
lean_dec(v___x_300_);
lean_dec_ref(v___x_299_);
return v_res_309_;
}
}
static lean_object* _init_l_Std_Http_Header_Name_toCanonical___closed__2(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_Std_Http_Header_Name_toCanonical___closed__1));
v___x_313_ = lean_string_utf8_byte_size(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_toCanonical(lean_object* v_name_315_){
_start:
{
lean_object* v___f_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_it_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___f_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___f_316_ = ((lean_object*)(l_Std_Http_Header_Name_toCanonical___closed__0));
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_string_utf8_byte_size(v_name_315_);
lean_inc_ref(v_name_315_);
v___x_319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_319_, 0, v_name_315_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_inc_ref(v___x_319_);
v_it_320_ = l_String_Slice_splitToSubslice___redArg(v___x_319_, v___f_316_);
v___x_321_ = ((lean_object*)(l_Std_Http_Header_Name_toCanonical___closed__1));
v___x_322_ = lean_obj_once(&l_Std_Http_Header_Name_toCanonical___closed__2, &l_Std_Http_Header_Name_toCanonical___closed__2_once, _init_l_Std_Http_Header_Name_toCanonical___closed__2);
v___f_323_ = lean_alloc_closure((void*)(l_Std_Http_Header_Name_toCanonical___lam__0___boxed), 10, 6);
lean_closure_set(v___f_323_, 0, v___x_321_);
lean_closure_set(v___f_323_, 1, v___x_317_);
lean_closure_set(v___f_323_, 2, v___x_322_);
lean_closure_set(v___f_323_, 3, v_name_315_);
lean_closure_set(v___f_323_, 4, v___x_318_);
lean_closure_set(v___f_323_, 5, v___x_319_);
v___x_324_ = lean_box(0);
v___x_325_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_323_, v_it_320_, v___x_324_, lean_box(0));
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_326_; 
v___x_326_ = ((lean_object*)(l_Std_Http_Header_Name_toCanonical___closed__3));
return v___x_326_;
}
else
{
lean_object* v_val_327_; 
v_val_327_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_327_);
lean_dec_ref_known(v___x_325_, 1);
return v_val_327_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Name_is(lean_object* v_name_328_, lean_object* v_s_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = l_String_mapAux___at___00Std_Http_Header_Name_ofString_x3f_spec__0(v_s_329_, v___x_330_);
v___x_332_ = lean_string_dec_eq(v_name_328_, v___x_331_);
lean_dec_ref(v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_is___boxed(lean_object* v_name_333_, lean_object* v_s_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Std_Http_Header_Name_is(v_name_333_, v_s_334_);
lean_dec_ref(v_name_333_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_instToString___lam__0(lean_object* v___x_337_, lean_object* v___x_338_, lean_object* v___x_339_, lean_object* v_name_340_, lean_object* v___x_341_, lean_object* v___x_342_, lean_object* v_it_343_, lean_object* v_acc_344_, lean_object* v_hP_345_, lean_object* v_recur_346_){
_start:
{
lean_object* v_it_348_; lean_object* v_out_349_; lean_object* v___y_365_; lean_object* v___y_366_; uint32_t v___y_367_; lean_object* v___y_368_; uint8_t v___y_369_; lean_object* v_it_375_; lean_object* v_startInclusive_376_; lean_object* v_endExclusive_377_; 
if (lean_obj_tag(v_it_343_) == 0)
{
lean_object* v_currPos_385_; lean_object* v_searcher_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_409_; 
v_currPos_385_ = lean_ctor_get(v_it_343_, 0);
v_searcher_386_ = lean_ctor_get(v_it_343_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_it_343_);
if (v_isSharedCheck_409_ == 0)
{
v___x_388_ = v_it_343_;
v_isShared_389_ = v_isSharedCheck_409_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_searcher_386_);
lean_inc(v_currPos_385_);
lean_dec(v_it_343_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_409_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
uint8_t v_decide_390_; 
v_decide_390_ = lean_nat_dec_eq(v_searcher_386_, v___x_341_);
if (v_decide_390_ == 0)
{
uint32_t v___x_391_; uint32_t v___x_392_; uint8_t v___x_393_; 
lean_dec(v___x_341_);
v___x_391_ = lean_string_utf8_get_fast(v_name_340_, v_searcher_386_);
v___x_392_ = 45;
v___x_393_ = lean_uint32_dec_eq(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_string_utf8_next_fast(v_name_340_, v_searcher_386_);
lean_dec(v_searcher_386_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_394_);
v___x_396_ = v___x_388_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_currPos_385_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_398_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; 
v___x_397_ = lean_apply_4(v_recur_346_, v___x_396_, v_acc_344_, lean_box(0), lean_box(0));
return v___x_397_;
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_slice_402_; lean_object* v_nextIt_404_; 
v___x_399_ = lean_string_utf8_next_fast(v_name_340_, v_searcher_386_);
v___x_400_ = lean_nat_sub(v___x_399_, v_searcher_386_);
v___x_401_ = lean_nat_add(v_searcher_386_, v___x_400_);
lean_dec(v___x_400_);
v_slice_402_ = l_String_Slice_subslice_x21(v___x_342_, v_currPos_385_, v_searcher_386_);
lean_inc(v___x_401_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_401_);
lean_ctor_set(v___x_388_, 0, v___x_401_);
v_nextIt_404_ = v___x_388_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_401_);
v_nextIt_404_ = v_reuseFailAlloc_407_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v_startInclusive_405_; lean_object* v_endExclusive_406_; 
v_startInclusive_405_ = lean_ctor_get(v_slice_402_, 0);
lean_inc(v_startInclusive_405_);
v_endExclusive_406_ = lean_ctor_get(v_slice_402_, 1);
lean_inc(v_endExclusive_406_);
lean_dec_ref(v_slice_402_);
v_it_375_ = v_nextIt_404_;
v_startInclusive_376_ = v_startInclusive_405_;
v_endExclusive_377_ = v_endExclusive_406_;
goto v___jp_374_;
}
}
}
else
{
lean_object* v___x_408_; 
lean_del_object(v___x_388_);
lean_dec(v_searcher_386_);
v___x_408_ = lean_box(1);
v_it_375_ = v___x_408_;
v_startInclusive_376_ = v_currPos_385_;
v_endExclusive_377_ = v___x_341_;
goto v___jp_374_;
}
}
}
else
{
lean_dec_ref(v_recur_346_);
lean_dec(v___x_341_);
return v_acc_344_;
}
v___jp_347_:
{
if (lean_obj_tag(v_acc_344_) == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_out_349_);
v___x_351_ = lean_apply_4(v_recur_346_, v_it_348_, v___x_350_, lean_box(0), lean_box(0));
return v___x_351_;
}
else
{
lean_object* v_val_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_363_; 
v_val_352_ = lean_ctor_get(v_acc_344_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_acc_344_);
if (v_isSharedCheck_363_ == 0)
{
v___x_354_ = v_acc_344_;
v_isShared_355_ = v_isSharedCheck_363_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_val_352_);
lean_dec(v_acc_344_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_363_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_356_ = lean_string_utf8_extract_fast(v___x_337_, v___x_338_, v___x_339_);
v___x_357_ = lean_string_append(v_val_352_, v___x_356_);
lean_dec_ref(v___x_356_);
v___x_358_ = lean_string_append(v___x_357_, v_out_349_);
lean_dec_ref(v_out_349_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_358_);
v___x_360_ = v___x_354_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_362_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; 
v___x_361_ = lean_apply_4(v_recur_346_, v_it_348_, v___x_360_, lean_box(0), lean_box(0));
return v___x_361_;
}
}
}
}
v___jp_364_:
{
if (v___y_369_ == 0)
{
lean_object* v___x_370_; 
v___x_370_ = lean_string_utf8_set(v___y_368_, v___y_366_, v___y_367_);
v_it_348_ = v___y_365_;
v_out_349_ = v___x_370_;
goto v___jp_347_;
}
else
{
uint32_t v___x_371_; uint32_t v___x_372_; lean_object* v___x_373_; 
v___x_371_ = 4294967264;
v___x_372_ = lean_uint32_add(v___y_367_, v___x_371_);
v___x_373_ = lean_string_utf8_set(v___y_368_, v___y_366_, v___x_372_);
v_it_348_ = v___y_365_;
v_out_349_ = v___x_373_;
goto v___jp_347_;
}
}
v___jp_374_:
{
lean_object* v___x_378_; lean_object* v___x_379_; uint32_t v___x_380_; uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_378_ = lean_string_utf8_extract_fast(v_name_340_, v_startInclusive_376_, v_endExclusive_377_);
lean_dec(v_endExclusive_377_);
lean_dec(v_startInclusive_376_);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_string_utf8_get(v___x_378_, v___x_379_);
v___x_381_ = 97;
v___x_382_ = lean_uint32_dec_le(v___x_381_, v___x_380_);
if (v___x_382_ == 0)
{
v___y_365_ = v_it_375_;
v___y_366_ = v___x_379_;
v___y_367_ = v___x_380_;
v___y_368_ = v___x_378_;
v___y_369_ = v___x_382_;
goto v___jp_364_;
}
else
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 122;
v___x_384_ = lean_uint32_dec_le(v___x_380_, v___x_383_);
v___y_365_ = v_it_375_;
v___y_366_ = v___x_379_;
v___y_367_ = v___x_380_;
v___y_368_ = v___x_378_;
v___y_369_ = v___x_384_;
goto v___jp_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_instToString___lam__0___boxed(lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v___x_412_, lean_object* v_name_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v_it_416_, lean_object* v_acc_417_, lean_object* v_hP_418_, lean_object* v_recur_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_Http_Header_Name_instToString___lam__0(v___x_410_, v___x_411_, v___x_412_, v_name_413_, v___x_414_, v___x_415_, v_it_416_, v_acc_417_, v_hP_418_, v_recur_419_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v_name_413_);
lean_dec(v___x_412_);
lean_dec(v___x_411_);
lean_dec_ref(v___x_410_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Name_instToString___lam__1(lean_object* v_name_421_){
_start:
{
lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_it_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___f_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___f_422_ = ((lean_object*)(l_Std_Http_Header_Name_toCanonical___closed__0));
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_string_utf8_byte_size(v_name_421_);
lean_inc_ref(v_name_421_);
v___x_425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_425_, 0, v_name_421_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
lean_ctor_set(v___x_425_, 2, v___x_424_);
lean_inc_ref(v___x_425_);
v_it_426_ = l_String_Slice_splitToSubslice___redArg(v___x_425_, v___f_422_);
v___x_427_ = ((lean_object*)(l_Std_Http_Header_Name_toCanonical___closed__1));
v___x_428_ = lean_obj_once(&l_Std_Http_Header_Name_toCanonical___closed__2, &l_Std_Http_Header_Name_toCanonical___closed__2_once, _init_l_Std_Http_Header_Name_toCanonical___closed__2);
v___f_429_ = lean_alloc_closure((void*)(l_Std_Http_Header_Name_instToString___lam__0___boxed), 10, 6);
lean_closure_set(v___f_429_, 0, v___x_427_);
lean_closure_set(v___f_429_, 1, v___x_423_);
lean_closure_set(v___f_429_, 2, v___x_428_);
lean_closure_set(v___f_429_, 3, v_name_421_);
lean_closure_set(v___f_429_, 4, v___x_424_);
lean_closure_set(v___f_429_, 5, v___x_425_);
v___x_430_ = lean_box(0);
v___x_431_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_429_, v_it_426_, v___x_430_, lean_box(0));
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_Std_Http_Header_Name_toCanonical___closed__3));
return v___x_432_;
}
else
{
lean_object* v_val_433_; 
v_val_433_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v___x_431_, 1);
return v_val_433_;
}
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iter(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Headers_Name(uint8_t builtin) {
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
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Headers_Name(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Http_Header_Name_isValidHeaderValue___autoParam = _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam();
lean_mark_persistent(l_Std_Http_Header_Name_isValidHeaderValue___autoParam);
l_Std_Http_Header_Name_isLowerCase___autoParam = _init_l_Std_Http_Header_Name_isLowerCase___autoParam();
lean_mark_persistent(l_Std_Http_Header_Name_isLowerCase___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Std_Http_Internal(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Headers_Name(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Headers_Name(builtin);
}
#ifdef __cplusplus
}
#endif
