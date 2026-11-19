// Lean compiler output
// Module: Std.Http.Data.Headers.Value
// Imports: public import Init.Data.ToString public import Std.Http.Internal public import Init.Data.String.Search import Init.Data.String.Lemmas.Pattern.TakeDrop.Pred import Init.Data.String.Lemmas.Search
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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_Value_ofString_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_Value_ofString_x3f_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_instEncodeV11___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_Value_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Value_instEncodeV11___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Value_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_Header_Value_instEncodeV11___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Value_instEncodeV11 = (const lean_object*)&l_Std_Http_Header_Value_instEncodeV11___closed__0_value;
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
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqValue_beq(lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = lean_string_dec_eq(v_x_78_, v_x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqValue_beq___boxed(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Std_Http_Header_instBEqValue_beq(v_x_81_, v_x_82_);
lean_dec_ref(v_x_82_);
lean_dec_ref(v_x_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instDecidableEqValue_decEq(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = lean_string_dec_eq(v_x_87_, v_x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instDecidableEqValue_decEq___boxed(lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Std_Http_Header_instDecidableEqValue_decEq(v_x_90_, v_x_91_);
lean_dec_ref(v_x_91_);
lean_dec_ref(v_x_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instDecidableEqValue(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = lean_string_dec_eq(v_x_94_, v_x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instDecidableEqValue___boxed(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Std_Http_Header_instDecidableEqValue(v_x_97_, v_x_98_);
lean_dec_ref(v_x_98_);
lean_dec_ref(v_x_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprValue_repr_spec__0(lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_nat_to_int(v_a_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(9u);
v___x_117_ = lean_nat_to_int(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__0));
v___x_129_ = lean_string_length(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_Std_Http_Header_instReprValue_repr___redArg___closed__15, &l_Std_Http_Header_instReprValue_repr___redArg___closed__15_once, _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__15);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprValue_repr___redArg(lean_object* v_x_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_137_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__5));
v___x_138_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__6));
v___x_139_ = lean_obj_once(&l_Std_Http_Header_instReprValue_repr___redArg___closed__7, &l_Std_Http_Header_instReprValue_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__7);
v___x_140_ = l_String_quote(v_x_136_);
v___x_141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
v___x_142_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_139_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = 0;
v___x_144_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*1, v___x_143_);
v___x_145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_138_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__9));
v___x_147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_box(1);
v___x_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__11));
v___x_151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_137_);
v___x_153_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__13));
v___x_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_obj_once(&l_Std_Http_Header_instReprValue_repr___redArg___closed__16, &l_Std_Http_Header_instReprValue_repr___redArg___closed__16_once, _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__16);
v___x_156_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__17));
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_154_);
v___x_158_ = ((lean_object*)(l_Std_Http_Header_instReprValue_repr___redArg___closed__18));
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_155_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*1, v___x_143_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprValue_repr(lean_object* v_x_162_, lean_object* v_prec_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_Http_Header_instReprValue_repr___redArg(v_x_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprValue_repr___boxed(lean_object* v_x_165_, lean_object* v_prec_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Http_Header_instReprValue_repr(v_x_165_, v_prec_166_);
lean_dec(v_prec_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instHashableValue___lam__0(lean_object* v_self_170_){
_start:
{
lean_inc_ref(v_self_170_);
return v_self_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instHashableValue___lam__0___boxed(lean_object* v_self_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_Http_Header_instHashableValue___lam__0(v_self_171_);
lean_dec_ref(v_self_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_Value_ofString_x3f_spec__0(lean_object* v_s_181_, lean_object* v_pos_182_){
_start:
{
lean_object* v_str_183_; lean_object* v_startInclusive_184_; lean_object* v_endExclusive_185_; lean_object* v___x_186_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v_decide_197_; 
v_str_183_ = lean_ctor_get(v_s_181_, 0);
v_startInclusive_184_ = lean_ctor_get(v_s_181_, 1);
v_endExclusive_185_ = lean_ctor_get(v_s_181_, 2);
v___x_186_ = lean_nat_add(v_startInclusive_184_, v_pos_182_);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_nat_sub(v_endExclusive_185_, v___x_186_);
v_decide_197_ = lean_nat_dec_eq(v___x_195_, v___x_196_);
lean_dec(v___x_196_);
if (v_decide_197_ == 0)
{
uint32_t v___x_198_; uint32_t v___x_206_; uint8_t v___x_207_; 
v___x_198_ = lean_string_utf8_get_fast(v_str_183_, v___x_186_);
v___x_206_ = 33;
v___x_207_ = lean_uint32_dec_le(v___x_206_, v___x_198_);
if (v___x_207_ == 0)
{
goto v___jp_199_;
}
else
{
uint32_t v___x_208_; uint8_t v___x_209_; 
v___x_208_ = 126;
v___x_209_ = lean_uint32_dec_le(v___x_198_, v___x_208_);
if (v___x_209_ == 0)
{
goto v___jp_199_;
}
else
{
goto v___jp_187_;
}
}
v___jp_199_:
{
uint32_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = 128;
v___x_201_ = lean_uint32_dec_le(v___x_200_, v___x_198_);
if (v___x_201_ == 0)
{
uint32_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = 32;
v___x_203_ = lean_uint32_dec_eq(v___x_198_, v___x_202_);
if (v___x_203_ == 0)
{
uint32_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = 9;
v___x_205_ = lean_uint32_dec_eq(v___x_198_, v___x_204_);
if (v___x_205_ == 0)
{
lean_dec(v___x_186_);
return v_pos_182_;
}
else
{
goto v___jp_187_;
}
}
else
{
goto v___jp_187_;
}
}
else
{
goto v___jp_187_;
}
}
}
else
{
lean_dec(v___x_186_);
return v_pos_182_;
}
v___jp_187_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_188_ = lean_string_utf8_next_fast(v_str_183_, v___x_186_);
v___x_189_ = lean_nat_sub(v___x_188_, v___x_186_);
lean_dec(v___x_186_);
v___x_190_ = lean_nat_add(v_pos_182_, v___x_189_);
lean_dec(v___x_189_);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_add(v_pos_182_, v___x_191_);
v___x_193_ = lean_nat_dec_le(v___x_192_, v___x_190_);
lean_dec(v___x_192_);
if (v___x_193_ == 0)
{
lean_dec(v___x_190_);
return v_pos_182_;
}
else
{
lean_dec(v_pos_182_);
v_pos_182_ = v___x_190_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_Value_ofString_x3f_spec__0___boxed(lean_object* v_s_210_, lean_object* v_pos_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_Value_ofString_x3f_spec__0(v_s_210_, v_pos_211_);
lean_dec_ref(v_s_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_ofString_x3f(lean_object* v_s_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_val_218_; uint32_t v___y_220_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v_decide_258_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_string_utf8_byte_size(v_s_213_);
v___x_216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_216_, 0, v_s_213_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___x_215_);
v___x_217_ = l_String_Slice_trimAscii(v___x_216_);
v_val_218_ = l_String_Slice_toString(v___x_217_);
lean_dec_ref(v___x_217_);
v___x_255_ = lean_string_utf8_byte_size(v_val_218_);
lean_inc_ref(v_val_218_);
v___x_256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_256_, 0, v_val_218_);
lean_ctor_set(v___x_256_, 1, v___x_214_);
lean_ctor_set(v___x_256_, 2, v___x_255_);
v___x_257_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_Value_ofString_x3f_spec__0(v___x_256_, v___x_214_);
v_decide_258_ = lean_nat_dec_eq(v___x_257_, v___x_255_);
lean_dec(v___x_257_);
if (v_decide_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec_ref_known(v___x_256_, 3);
lean_dec_ref(v_val_218_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
else
{
lean_object* v___x_260_; 
v___x_260_ = l_String_Slice_Pos_get_x3f(v___x_256_, v___x_214_);
lean_dec_ref_known(v___x_256_, 3);
if (lean_obj_tag(v___x_260_) == 0)
{
goto v___jp_225_;
}
else
{
lean_object* v_val_261_; uint32_t v___x_267_; uint32_t v___x_268_; uint8_t v___x_269_; 
v_val_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_267_ = 33;
v___x_268_ = lean_unbox_uint32(v_val_261_);
v___x_269_ = lean_uint32_dec_le(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
goto v___jp_262_;
}
else
{
uint32_t v___x_270_; uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_270_ = 126;
v___x_271_ = lean_unbox_uint32(v_val_261_);
v___x_272_ = lean_uint32_dec_le(v___x_271_, v___x_270_);
if (v___x_272_ == 0)
{
goto v___jp_262_;
}
else
{
lean_dec(v_val_261_);
goto v___jp_225_;
}
}
v___jp_262_:
{
uint32_t v___x_263_; uint32_t v___x_264_; uint8_t v___x_265_; 
v___x_263_ = 128;
v___x_264_ = lean_unbox_uint32(v_val_261_);
lean_dec(v_val_261_);
v___x_265_ = lean_uint32_dec_le(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
lean_dec_ref(v_val_218_);
v___x_266_ = lean_box(0);
return v___x_266_;
}
else
{
goto v___jp_225_;
}
}
}
}
v___jp_219_:
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 128;
v___x_222_ = lean_uint32_dec_le(v___x_221_, v___y_220_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_dec_ref(v_val_218_);
v___x_223_ = lean_box(0);
return v___x_223_;
}
else
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v_val_218_);
return v___x_224_;
}
}
v___jp_225_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_string_utf8_byte_size(v_val_218_);
lean_inc_ref(v_val_218_);
v___x_227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_227_, 0, v_val_218_);
lean_ctor_set(v___x_227_, 1, v___x_214_);
lean_ctor_set(v___x_227_, 2, v___x_226_);
v___x_228_ = l_String_Slice_Pos_prev_x3f(v___x_227_, v___x_226_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; 
lean_dec_ref_known(v___x_227_, 3);
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v_val_218_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_254_; 
v_val_230_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_254_ == 0)
{
v___x_232_ = v___x_228_;
v_isShared_233_ = v_isSharedCheck_254_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_val_230_);
lean_dec(v___x_228_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_254_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; 
v___x_234_ = l_String_Slice_Pos_get_x3f(v___x_227_, v_val_230_);
lean_dec(v_val_230_);
lean_dec_ref_known(v___x_227_, 3);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_236_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v_val_218_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_val_218_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
else
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_253_; 
lean_del_object(v___x_232_);
v_val_238_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_253_ == 0)
{
v___x_240_ = v___x_234_;
v_isShared_241_ = v_isSharedCheck_253_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v___x_234_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_253_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
uint32_t v___x_242_; uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_242_ = 33;
v___x_243_ = lean_unbox_uint32(v_val_238_);
v___x_244_ = lean_uint32_dec_le(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
uint32_t v___x_245_; 
lean_del_object(v___x_240_);
v___x_245_ = lean_unbox_uint32(v_val_238_);
lean_dec(v_val_238_);
v___y_220_ = v___x_245_;
goto v___jp_219_;
}
else
{
uint32_t v___x_246_; uint32_t v___x_247_; uint8_t v___x_248_; 
v___x_246_ = 126;
v___x_247_ = lean_unbox_uint32(v_val_238_);
v___x_248_ = lean_uint32_dec_le(v___x_247_, v___x_246_);
if (v___x_248_ == 0)
{
uint32_t v___x_249_; 
lean_del_object(v___x_240_);
v___x_249_ = lean_unbox_uint32(v_val_238_);
lean_dec(v_val_238_);
v___y_220_ = v___x_249_;
goto v___jp_219_;
}
else
{
lean_object* v___x_251_; 
lean_dec(v_val_238_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v_val_218_);
v___x_251_ = v___x_240_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_val_218_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Header_Value_ofString_x21_spec__0(lean_object* v_msg_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Std_Http_Header_instInhabitedValue___closed__0));
v___x_275_ = lean_panic_fn_borrowed(v___x_274_, v_msg_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object* v_s_279_){
_start:
{
lean_object* v___x_280_; 
lean_inc_ref(v_s_279_);
v___x_280_ = l_Std_Http_Header_Value_ofString_x3f(v_s_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_281_ = ((lean_object*)(l_Std_Http_Header_Value_ofString_x21___closed__0));
v___x_282_ = ((lean_object*)(l_Std_Http_Header_Value_ofString_x21___closed__1));
v___x_283_ = lean_unsigned_to_nat(95u);
v___x_284_ = lean_unsigned_to_nat(12u);
v___x_285_ = ((lean_object*)(l_Std_Http_Header_Value_ofString_x21___closed__2));
v___x_286_ = l_String_quote(v_s_279_);
v___x_287_ = lean_string_append(v___x_285_, v___x_286_);
lean_dec_ref(v___x_286_);
v___x_288_ = l_mkPanicMessageWithDecl(v___x_281_, v___x_282_, v___x_283_, v___x_284_, v___x_287_);
lean_dec_ref(v___x_287_);
v___x_289_ = l_panic___at___00Std_Http_Header_Value_ofString_x21_spec__0(v___x_288_);
return v___x_289_;
}
else
{
lean_object* v_val_290_; 
lean_dec_ref(v_s_279_);
v_val_290_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_290_);
lean_dec_ref_known(v___x_280_, 1);
return v_val_290_;
}
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Std_Http_Header_Value_is_spec__0(lean_object* v_s_291_, lean_object* v_p_292_){
_start:
{
lean_object* v___y_294_; lean_object* v___y_295_; uint32_t v___y_299_; lean_object* v___x_311_; uint8_t v_decide_312_; 
v___x_311_ = lean_string_utf8_byte_size(v_s_291_);
v_decide_312_ = lean_nat_dec_eq(v_p_292_, v___x_311_);
if (v_decide_312_ == 0)
{
uint32_t v___x_313_; uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_313_ = lean_string_utf8_get_fast(v_s_291_, v_p_292_);
v___x_314_ = 65;
v___x_315_ = lean_uint32_dec_le(v___x_314_, v___x_313_);
if (v___x_315_ == 0)
{
v___y_299_ = v___x_313_;
goto v___jp_298_;
}
else
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 90;
v___x_317_ = lean_uint32_dec_le(v___x_313_, v___x_316_);
if (v___x_317_ == 0)
{
v___y_299_ = v___x_313_;
goto v___jp_298_;
}
else
{
uint32_t v___x_318_; uint32_t v___x_319_; 
v___x_318_ = 32;
v___x_319_ = lean_uint32_add(v___x_313_, v___x_318_);
v___y_299_ = v___x_319_;
goto v___jp_298_;
}
}
}
else
{
lean_dec(v_p_292_);
return v_s_291_;
}
v___jp_293_:
{
lean_object* v___x_296_; 
v___x_296_ = lean_nat_add(v_p_292_, v___y_295_);
lean_dec(v_p_292_);
v_s_291_ = v___y_294_;
v_p_292_ = v___x_296_;
goto _start;
}
v___jp_298_:
{
lean_object* v___x_300_; uint32_t v___x_301_; uint8_t v___x_302_; 
lean_inc(v_p_292_);
v___x_300_ = lean_string_utf8_set(v_s_291_, v_p_292_, v___y_299_);
v___x_301_ = 127;
v___x_302_ = lean_uint32_dec_le(v___y_299_, v___x_301_);
if (v___x_302_ == 0)
{
uint32_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = 2047;
v___x_304_ = lean_uint32_dec_le(v___y_299_, v___x_303_);
if (v___x_304_ == 0)
{
uint32_t v___x_305_; uint8_t v___x_306_; 
v___x_305_ = 65535;
v___x_306_ = lean_uint32_dec_le(v___y_299_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(4u);
v___y_294_ = v___x_300_;
v___y_295_ = v___x_307_;
goto v___jp_293_;
}
else
{
lean_object* v___x_308_; 
v___x_308_ = lean_unsigned_to_nat(3u);
v___y_294_ = v___x_300_;
v___y_295_ = v___x_308_;
goto v___jp_293_;
}
}
else
{
lean_object* v___x_309_; 
v___x_309_ = lean_unsigned_to_nat(2u);
v___y_294_ = v___x_300_;
v___y_295_ = v___x_309_;
goto v___jp_293_;
}
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_unsigned_to_nat(1u);
v___y_294_ = v___x_300_;
v___y_295_ = v___x_310_;
goto v___jp_293_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Value_is(lean_object* v_s_320_, lean_object* v_h_321_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = l_String_mapAux___at___00Std_Http_Header_Value_is_spec__0(v_s_320_, v___x_322_);
v___x_324_ = l_String_mapAux___at___00Std_Http_Header_Value_is_spec__0(v_h_321_, v___x_322_);
v___x_325_ = lean_string_dec_eq(v___x_323_, v___x_324_);
lean_dec_ref(v___x_324_);
lean_dec_ref(v___x_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_is___boxed(lean_object* v_s_326_, lean_object* v_h_327_){
_start:
{
uint8_t v_res_328_; lean_object* v_r_329_; 
v_res_328_ = l_Std_Http_Header_Value_is(v_s_326_, v_h_327_);
v_r_329_ = lean_box(v_res_328_);
return v_r_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_instToString___lam__0(lean_object* v_v_330_){
_start:
{
lean_inc_ref(v_v_330_);
return v_v_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_instToString___lam__0___boxed(lean_object* v_v_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Http_Header_Value_instToString___lam__0(v_v_331_);
lean_dec_ref(v_v_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Value_instEncodeV11___lam__0(lean_object* v_out_335_, lean_object* v_v_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; 
v___x_337_ = lean_string_to_utf8(v_v_336_);
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_byte_array_size(v_out_335_);
v___x_340_ = lean_byte_array_size(v___x_337_);
v___x_341_ = 0;
v___x_342_ = lean_byte_array_copy_slice(v___x_337_, v___x_338_, v_out_335_, v___x_339_, v___x_340_, v___x_341_);
lean_dec_ref(v___x_337_);
return v___x_342_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Pred(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Search(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Search(builtin);
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
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Pred(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Search(uint8_t builtin);
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
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Search(builtin);
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
