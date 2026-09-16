// Lean compiler output
// Module: Init.Data.List.Basic
// Imports: public import Init.Data.List.Notation public import Init.Data.Zero public import Init.Grind.Tactics public import Init.SimpLemmas import Init.Data.Nat.Basic
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_length___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_set_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_set_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instBEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEqv___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEqv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableLex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableLex___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLT(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLE(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_lex___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_List_lex___auto__1___closed__0 = (const lean_object*)&l_List_lex___auto__1___closed__0_value;
static const lean_string_object l_List_lex___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_List_lex___auto__1___closed__1 = (const lean_object*)&l_List_lex___auto__1___closed__1_value;
static const lean_string_object l_List_lex___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_List_lex___auto__1___closed__2 = (const lean_object*)&l_List_lex___auto__1___closed__2_value;
static const lean_string_object l_List_lex___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_List_lex___auto__1___closed__3 = (const lean_object*)&l_List_lex___auto__1___closed__3_value;
static const lean_ctor_object l_List_lex___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_lex___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__4_value_aux_0),((lean_object*)&l_List_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_lex___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__4_value_aux_1),((lean_object*)&l_List_lex___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_lex___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__4_value_aux_2),((lean_object*)&l_List_lex___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_List_lex___auto__1___closed__4 = (const lean_object*)&l_List_lex___auto__1___closed__4_value;
static const lean_array_object l_List_lex___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_lex___auto__1___closed__5 = (const lean_object*)&l_List_lex___auto__1___closed__5_value;
static const lean_string_object l_List_lex___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_List_lex___auto__1___closed__6 = (const lean_object*)&l_List_lex___auto__1___closed__6_value;
static const lean_ctor_object l_List_lex___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_lex___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__7_value_aux_0),((lean_object*)&l_List_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_lex___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__7_value_aux_1),((lean_object*)&l_List_lex___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_lex___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__7_value_aux_2),((lean_object*)&l_List_lex___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_List_lex___auto__1___closed__7 = (const lean_object*)&l_List_lex___auto__1___closed__7_value;
static const lean_string_object l_List_lex___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_lex___auto__1___closed__8 = (const lean_object*)&l_List_lex___auto__1___closed__8_value;
static const lean_ctor_object l_List_lex___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_lex___auto__1___closed__9 = (const lean_object*)&l_List_lex___auto__1___closed__9_value;
static const lean_string_object l_List_lex___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_List_lex___auto__1___closed__10 = (const lean_object*)&l_List_lex___auto__1___closed__10_value;
static const lean_ctor_object l_List_lex___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_lex___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__11_value_aux_0),((lean_object*)&l_List_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_lex___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__11_value_aux_1),((lean_object*)&l_List_lex___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_lex___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__11_value_aux_2),((lean_object*)&l_List_lex___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_List_lex___auto__1___closed__11 = (const lean_object*)&l_List_lex___auto__1___closed__11_value;
static lean_once_cell_t l_List_lex___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__12;
static lean_once_cell_t l_List_lex___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__13;
static const lean_string_object l_List_lex___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_List_lex___auto__1___closed__14 = (const lean_object*)&l_List_lex___auto__1___closed__14_value;
static const lean_string_object l_List_lex___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_List_lex___auto__1___closed__15 = (const lean_object*)&l_List_lex___auto__1___closed__15_value;
static const lean_ctor_object l_List_lex___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_lex___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__16_value_aux_0),((lean_object*)&l_List_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_lex___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__16_value_aux_1),((lean_object*)&l_List_lex___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_lex___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__16_value_aux_2),((lean_object*)&l_List_lex___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_List_lex___auto__1___closed__16 = (const lean_object*)&l_List_lex___auto__1___closed__16_value;
static const lean_string_object l_List_lex___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_List_lex___auto__1___closed__17 = (const lean_object*)&l_List_lex___auto__1___closed__17_value;
static const lean_ctor_object l_List_lex___auto__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_lex___auto__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__18_value_aux_0),((lean_object*)&l_List_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_lex___auto__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__18_value_aux_1),((lean_object*)&l_List_lex___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_lex___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__18_value_aux_2),((lean_object*)&l_List_lex___auto__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_List_lex___auto__1___closed__18 = (const lean_object*)&l_List_lex___auto__1___closed__18_value;
static const lean_string_object l_List_lex___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_List_lex___auto__1___closed__19 = (const lean_object*)&l_List_lex___auto__1___closed__19_value;
static lean_once_cell_t l_List_lex___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__20;
static lean_once_cell_t l_List_lex___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__21;
static const lean_string_object l_List_lex___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_List_lex___auto__1___closed__22 = (const lean_object*)&l_List_lex___auto__1___closed__22_value;
static const lean_ctor_object l_List_lex___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_List_lex___auto__1___closed__23 = (const lean_object*)&l_List_lex___auto__1___closed__23_value;
static const lean_string_object l_List_lex___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_List_lex___auto__1___closed__24 = (const lean_object*)&l_List_lex___auto__1___closed__24_value;
static lean_once_cell_t l_List_lex___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__25;
static lean_once_cell_t l_List_lex___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__26;
static lean_once_cell_t l_List_lex___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__27;
static lean_once_cell_t l_List_lex___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__28;
static lean_once_cell_t l_List_lex___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__29;
static lean_once_cell_t l_List_lex___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__30;
static lean_once_cell_t l_List_lex___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__31;
static lean_once_cell_t l_List_lex___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__32;
static const lean_string_object l_List_lex___auto__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l_List_lex___auto__1___closed__33 = (const lean_object*)&l_List_lex___auto__1___closed__33_value;
static const lean_ctor_object l_List_lex___auto__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l_List_lex___auto__1___closed__34 = (const lean_object*)&l_List_lex___auto__1___closed__34_value;
static const lean_string_object l_List_lex___auto__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l_List_lex___auto__1___closed__35 = (const lean_object*)&l_List_lex___auto__1___closed__35_value;
static const lean_ctor_object l_List_lex___auto__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_lex___auto__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__36_value_aux_0),((lean_object*)&l_List_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_lex___auto__1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__36_value_aux_1),((lean_object*)&l_List_lex___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_lex___auto__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__36_value_aux_2),((lean_object*)&l_List_lex___auto__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l_List_lex___auto__1___closed__36 = (const lean_object*)&l_List_lex___auto__1___closed__36_value;
static const lean_string_object l_List_lex___auto__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l_List_lex___auto__1___closed__37 = (const lean_object*)&l_List_lex___auto__1___closed__37_value;
static lean_once_cell_t l_List_lex___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__38;
static lean_once_cell_t l_List_lex___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__39;
static lean_once_cell_t l_List_lex___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__40;
static lean_once_cell_t l_List_lex___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__41;
static lean_once_cell_t l_List_lex___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__42;
static const lean_string_object l_List_lex___auto__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_List_lex___auto__1___closed__43 = (const lean_object*)&l_List_lex___auto__1___closed__43_value;
static lean_once_cell_t l_List_lex___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__44;
static lean_once_cell_t l_List_lex___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__45;
static lean_once_cell_t l_List_lex___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__46;
static lean_once_cell_t l_List_lex___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__47;
static lean_once_cell_t l_List_lex___auto__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__48;
static const lean_string_object l_List_lex___auto__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_List_lex___auto__1___closed__49 = (const lean_object*)&l_List_lex___auto__1___closed__49_value;
static lean_once_cell_t l_List_lex___auto__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__50;
static lean_once_cell_t l_List_lex___auto__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__51;
static lean_once_cell_t l_List_lex___auto__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__52;
static lean_once_cell_t l_List_lex___auto__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__53;
static lean_once_cell_t l_List_lex___auto__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__54;
static lean_once_cell_t l_List_lex___auto__1___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__55;
static lean_once_cell_t l_List_lex___auto__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__56;
static lean_once_cell_t l_List_lex___auto__1___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__57;
static lean_once_cell_t l_List_lex___auto__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__58;
static lean_once_cell_t l_List_lex___auto__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__59;
static lean_once_cell_t l_List_lex___auto__1___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__60;
LEAN_EXPORT lean_object* l_List_lex___auto__1;
LEAN_EXPORT uint8_t l_List_lex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lex___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_lex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_getLast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_getLast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_getLast_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLast_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLastD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLastD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLastD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLastD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_head___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_head___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_head(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_head___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_head_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_head_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_head_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_head_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_headD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_headD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_headD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_headD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tail___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_tail___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_tail(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tail___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_tail_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tail_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tailD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tailD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tailD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tailD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_reverseAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_appendTR, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_List_instAppend___closed__0 = (const lean_object*)&l_List_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_List_instAppend(lean_object*);
LEAN_EXPORT lean_object* l_List_singleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_singleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicate___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_leftpad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_leftpad___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_leftpad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_leftpad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rightpad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rightpad___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rightpad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rightpad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object*);
LEAN_EXPORT uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_contains(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instMembership(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableBEx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableBEx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableBEx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableBEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableBAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableBAll___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableBAll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableBAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_take___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_take___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_take(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_take___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_drop___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_drop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_drop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_extract___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_extract(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_extract___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_takeWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_takeWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dropWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_partition___redArg___closed__0 = (const lean_object*)&l_List_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_partition___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dropLast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_dropLast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_term___x3c_x2b___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_List_term___x3c_x2b___00__closed__0 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__0_value;
static const lean_string_object l_List_term___x3c_x2b___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_<+_"};
static const lean_object* l_List_term___x3c_x2b___00__closed__1 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__1_value;
static const lean_ctor_object l_List_term___x3c_x2b___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List_term___x3c_x2b___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b___00__closed__2_value_aux_0),((lean_object*)&l_List_term___x3c_x2b___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 196, 185, 53, 62, 139, 215, 69)}};
static const lean_object* l_List_term___x3c_x2b___00__closed__2 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__2_value;
static const lean_string_object l_List_term___x3c_x2b___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_List_term___x3c_x2b___00__closed__3 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__3_value;
static const lean_ctor_object l_List_term___x3c_x2b___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_List_term___x3c_x2b___00__closed__4 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__4_value;
static const lean_string_object l_List_term___x3c_x2b___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " <+ "};
static const lean_object* l_List_term___x3c_x2b___00__closed__5 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__5_value;
static const lean_ctor_object l_List_term___x3c_x2b___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b___00__closed__5_value)}};
static const lean_object* l_List_term___x3c_x2b___00__closed__6 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__6_value;
static const lean_string_object l_List_term___x3c_x2b___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_List_term___x3c_x2b___00__closed__7 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__7_value;
static const lean_ctor_object l_List_term___x3c_x2b___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_List_term___x3c_x2b___00__closed__8 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__8_value;
static const lean_ctor_object l_List_term___x3c_x2b___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b___00__closed__8_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_List_term___x3c_x2b___00__closed__9 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__9_value;
static const lean_ctor_object l_List_term___x3c_x2b___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b___00__closed__4_value),((lean_object*)&l_List_term___x3c_x2b___00__closed__6_value),((lean_object*)&l_List_term___x3c_x2b___00__closed__9_value)}};
static const lean_object* l_List_term___x3c_x2b___00__closed__10 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__10_value;
static const lean_ctor_object l_List_term___x3c_x2b___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b___00__closed__2_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__10_value)}};
static const lean_object* l_List_term___x3c_x2b___00__closed__11 = (const lean_object*)&l_List_term___x3c_x2b___00__closed__11_value;
LEAN_EXPORT const lean_object* l_List_term___x3c_x2b__ = (const lean_object*)&l_List_term___x3c_x2b___00__closed__11_value;
static const lean_string_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_0),((lean_object*)&l_List_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_1),((lean_object*)&l_List_lex___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value;
static const lean_string_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Sublist"};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value;
static lean_once_cell_t l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 57, 174, 210, 111, 90, 29, 55)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 22, 78, 3, 46, 110, 14, 182)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8_value)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6_value),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9_value)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10_value;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1_value;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isSublist___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSublist___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isSublist(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSublist___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_term___x3c_x2b_x3a___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_<+:_"};
static const lean_object* l_List_term___x3c_x2b_x3a___00__closed__0 = (const lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__0_value;
static const lean_ctor_object l_List_term___x3c_x2b_x3a___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List_term___x3c_x2b_x3a___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__1_value_aux_0),((lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 46, 199, 175, 86, 17, 90, 157)}};
static const lean_object* l_List_term___x3c_x2b_x3a___00__closed__1 = (const lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__1_value;
static const lean_string_object l_List_term___x3c_x2b_x3a___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " <+: "};
static const lean_object* l_List_term___x3c_x2b_x3a___00__closed__2 = (const lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__2_value;
static const lean_ctor_object l_List_term___x3c_x2b_x3a___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__2_value)}};
static const lean_object* l_List_term___x3c_x2b_x3a___00__closed__3 = (const lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__3_value;
static const lean_ctor_object l_List_term___x3c_x2b_x3a___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b___00__closed__4_value),((lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__3_value),((lean_object*)&l_List_term___x3c_x2b___00__closed__9_value)}};
static const lean_object* l_List_term___x3c_x2b_x3a___00__closed__4 = (const lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__4_value;
static const lean_ctor_object l_List_term___x3c_x2b_x3a___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__4_value)}};
static const lean_object* l_List_term___x3c_x2b_x3a___00__closed__5 = (const lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__5_value;
LEAN_EXPORT const lean_object* l_List_term___x3c_x2b_x3a__ = (const lean_object*)&l_List_term___x3c_x2b_x3a___00__closed__5_value;
static const lean_string_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "IsPrefix"};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value;
static lean_once_cell_t l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 111, 237, 222, 126, 19, 59, 60)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 46, 95, 235, 1, 49, 30, 153)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5_value;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isPrefixOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isPrefixOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isSuffixOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSuffixOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isSuffixOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSuffixOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_term___x3c_x3a_x2b___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_<:+_"};
static const lean_object* l_List_term___x3c_x3a_x2b___00__closed__0 = (const lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__0_value;
static const lean_ctor_object l_List_term___x3c_x3a_x2b___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List_term___x3c_x3a_x2b___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__1_value_aux_0),((lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 113, 2, 132, 68, 188, 186, 46)}};
static const lean_object* l_List_term___x3c_x3a_x2b___00__closed__1 = (const lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__1_value;
static const lean_string_object l_List_term___x3c_x3a_x2b___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " <:+ "};
static const lean_object* l_List_term___x3c_x3a_x2b___00__closed__2 = (const lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__2_value;
static const lean_ctor_object l_List_term___x3c_x3a_x2b___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__2_value)}};
static const lean_object* l_List_term___x3c_x3a_x2b___00__closed__3 = (const lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__3_value;
static const lean_ctor_object l_List_term___x3c_x3a_x2b___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b___00__closed__4_value),((lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__3_value),((lean_object*)&l_List_term___x3c_x2b___00__closed__9_value)}};
static const lean_object* l_List_term___x3c_x3a_x2b___00__closed__4 = (const lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__4_value;
static const lean_ctor_object l_List_term___x3c_x3a_x2b___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__4_value)}};
static const lean_object* l_List_term___x3c_x3a_x2b___00__closed__5 = (const lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__5_value;
LEAN_EXPORT const lean_object* l_List_term___x3c_x3a_x2b__ = (const lean_object*)&l_List_term___x3c_x3a_x2b___00__closed__5_value;
static const lean_string_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "IsSuffix"};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value;
static lean_once_cell_t l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 165, 175, 201, 24, 12, 223, 31)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 140, 134, 30, 20, 233, 184, 173)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5_value;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_term___x3c_x3a_x2b_x3a___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_<:+:_"};
static const lean_object* l_List_term___x3c_x3a_x2b_x3a___00__closed__0 = (const lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__0_value;
static const lean_ctor_object l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value_aux_0),((lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 100, 205, 176, 23, 167, 63, 78)}};
static const lean_object* l_List_term___x3c_x3a_x2b_x3a___00__closed__1 = (const lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value;
static const lean_string_object l_List_term___x3c_x3a_x2b_x3a___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " <:+: "};
static const lean_object* l_List_term___x3c_x3a_x2b_x3a___00__closed__2 = (const lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__2_value;
static const lean_ctor_object l_List_term___x3c_x3a_x2b_x3a___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__2_value)}};
static const lean_object* l_List_term___x3c_x3a_x2b_x3a___00__closed__3 = (const lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__3_value;
static const lean_ctor_object l_List_term___x3c_x3a_x2b_x3a___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b___00__closed__4_value),((lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__3_value),((lean_object*)&l_List_term___x3c_x2b___00__closed__9_value)}};
static const lean_object* l_List_term___x3c_x3a_x2b_x3a___00__closed__4 = (const lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__4_value;
static const lean_ctor_object l_List_term___x3c_x3a_x2b_x3a___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__4_value)}};
static const lean_object* l_List_term___x3c_x3a_x2b_x3a___00__closed__5 = (const lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__5_value;
LEAN_EXPORT const lean_object* l_List_term___x3c_x3a_x2b_x3a__ = (const lean_object*)&l_List_term___x3c_x3a_x2b_x3a___00__closed__5_value;
static const lean_string_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IsInfix"};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value;
static lean_once_cell_t l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 240, 110, 175, 10, 19, 61, 151)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 172, 213, 72, 247, 99, 170, 125)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5_value;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isInfixOf__internal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isInfixOf__internal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitAt_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeft___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRight___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRight___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidablePairwise___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidablePairwise(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_nodupDecidable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_nodupDecidable___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyHead___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyHead(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modify___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modify(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modify___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdx___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseP___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findRev_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_idxOf___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_idxOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_idxOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_idxOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_idxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_idxOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_count___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_count(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_term___x7e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_~_"};
static const lean_object* l_List_term___x7e___00__closed__0 = (const lean_object*)&l_List_term___x7e___00__closed__0_value;
static const lean_ctor_object l_List_term___x7e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List_term___x7e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_term___x7e___00__closed__1_value_aux_0),((lean_object*)&l_List_term___x7e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 66, 91, 28, 235, 133, 125, 244)}};
static const lean_object* l_List_term___x7e___00__closed__1 = (const lean_object*)&l_List_term___x7e___00__closed__1_value;
static const lean_string_object l_List_term___x7e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " ~ "};
static const lean_object* l_List_term___x7e___00__closed__2 = (const lean_object*)&l_List_term___x7e___00__closed__2_value;
static const lean_ctor_object l_List_term___x7e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_term___x7e___00__closed__2_value)}};
static const lean_object* l_List_term___x7e___00__closed__3 = (const lean_object*)&l_List_term___x7e___00__closed__3_value;
static const lean_ctor_object l_List_term___x7e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_List_term___x3c_x2b___00__closed__4_value),((lean_object*)&l_List_term___x7e___00__closed__3_value),((lean_object*)&l_List_term___x3c_x2b___00__closed__9_value)}};
static const lean_object* l_List_term___x7e___00__closed__4 = (const lean_object*)&l_List_term___x7e___00__closed__4_value;
static const lean_ctor_object l_List_term___x7e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_List_term___x7e___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_List_term___x7e___00__closed__4_value)}};
static const lean_object* l_List_term___x7e___00__closed__5 = (const lean_object*)&l_List_term___x7e___00__closed__5_value;
LEAN_EXPORT const lean_object* l_List_term___x7e__ = (const lean_object*)&l_List_term___x7e___00__closed__5_value;
static const lean_string_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Perm"};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value;
static lean_once_cell_t l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 39, 207, 243, 25, 131, 84, 93)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_term___x3c_x2b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 187, 193, 253, 117, 51, 247, 91)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6_value)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7_value;
static const lean_ctor_object l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4_value),((lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7_value)}};
static const lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8 = (const lean_object*)&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8_value;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isPerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPerm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isPerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00List_or_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00List_or_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_or(lean_object*);
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00List_and_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00List_and_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_and(lean_object*);
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_zipWith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zip(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_unzip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_prod___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_prod(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_prod___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_min(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intersperse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intersperse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDupsBy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDupsBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_eraseDups___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseRepsBy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseRepsBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseReps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_removeAll___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_leftpadTR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_set_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_h__1_4_, lean_object* v_h__2_5_, lean_object* v_h__3_6_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_7_; 
lean_dec(v_h__2_5_);
lean_dec(v_h__1_4_);
v___x_7_ = lean_apply_2(v_h__3_6_, v_x_2_, v_x_3_);
return v___x_7_;
}
else
{
lean_object* v_head_8_; lean_object* v_tail_9_; lean_object* v_zero_10_; uint8_t v_isZero_11_; 
lean_dec(v_h__3_6_);
v_head_8_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_head_8_);
v_tail_9_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_tail_9_);
lean_dec_ref_known(v_x_1_, 2);
v_zero_10_ = lean_unsigned_to_nat(0u);
v_isZero_11_ = lean_nat_dec_eq(v_x_2_, v_zero_10_);
if (v_isZero_11_ == 1)
{
lean_object* v___x_12_; 
lean_dec(v_h__2_5_);
lean_dec(v_x_2_);
v___x_12_ = lean_apply_3(v_h__1_4_, v_head_8_, v_tail_9_, v_x_3_);
return v___x_12_;
}
else
{
lean_object* v_one_13_; lean_object* v_n_14_; lean_object* v___x_15_; 
lean_dec(v_h__1_4_);
v_one_13_ = lean_unsigned_to_nat(1u);
v_n_14_ = lean_nat_sub(v_x_2_, v_one_13_);
lean_dec(v_x_2_);
v___x_15_ = lean_apply_4(v_h__2_5_, v_head_8_, v_tail_9_, v_n_14_, v_x_3_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_set_match__1_splitter(lean_object* v_00_u03b1_16_, lean_object* v_motive_17_, lean_object* v_x_18_, lean_object* v_x_19_, lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_, lean_object* v_h__3_23_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v___x_24_; 
lean_dec(v_h__2_22_);
lean_dec(v_h__1_21_);
v___x_24_ = lean_apply_2(v_h__3_23_, v_x_19_, v_x_20_);
return v___x_24_;
}
else
{
lean_object* v_head_25_; lean_object* v_tail_26_; lean_object* v_zero_27_; uint8_t v_isZero_28_; 
lean_dec(v_h__3_23_);
v_head_25_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_head_25_);
v_tail_26_ = lean_ctor_get(v_x_18_, 1);
lean_inc(v_tail_26_);
lean_dec_ref_known(v_x_18_, 2);
v_zero_27_ = lean_unsigned_to_nat(0u);
v_isZero_28_ = lean_nat_dec_eq(v_x_19_, v_zero_27_);
if (v_isZero_28_ == 1)
{
lean_object* v___x_29_; 
lean_dec(v_h__2_22_);
lean_dec(v_x_19_);
v___x_29_ = lean_apply_3(v_h__1_21_, v_head_25_, v_tail_26_, v_x_20_);
return v___x_29_;
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_21_);
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_19_, v_one_30_);
lean_dec(v_x_19_);
v___x_32_ = lean_apply_4(v_h__2_22_, v_head_25_, v_tail_26_, v_n_31_, v_x_20_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter___redArg(lean_object* v_x_33_, lean_object* v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v___x_37_; 
lean_dec(v_h__2_36_);
v___x_37_ = lean_apply_1(v_h__1_35_, v_x_34_);
return v___x_37_;
}
else
{
lean_object* v_head_38_; lean_object* v_tail_39_; lean_object* v___x_40_; 
lean_dec(v_h__1_35_);
v_head_38_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_head_38_);
v_tail_39_ = lean_ctor_get(v_x_33_, 1);
lean_inc(v_tail_39_);
lean_dec_ref_known(v_x_33_, 2);
v___x_40_ = lean_apply_3(v_h__2_36_, v_head_38_, v_tail_39_, v_x_34_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter(lean_object* v_00_u03b1_41_, lean_object* v_motive_42_, lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v___x_47_; 
lean_dec(v_h__2_46_);
v___x_47_ = lean_apply_1(v_h__1_45_, v_x_44_);
return v___x_47_;
}
else
{
lean_object* v_head_48_; lean_object* v_tail_49_; lean_object* v___x_50_; 
lean_dec(v_h__1_45_);
v_head_48_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_head_48_);
v_tail_49_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_tail_49_);
lean_dec_ref_known(v_x_43_, 2);
v___x_50_ = lean_apply_3(v_h__2_46_, v_head_48_, v_tail_49_, v_x_44_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_List_instBEq___redArg(lean_object* v_inst_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_52_, 0, lean_box(0));
lean_closure_set(v___x_52_, 1, v_inst_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_List_instBEq(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_55_, 0, lean_box(0));
lean_closure_set(v___x_55_, 1, v_inst_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___redArg(lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_, lean_object* v_h__3_60_, lean_object* v_h__4_61_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
lean_dec(v_h__4_61_);
lean_dec(v_h__2_59_);
if (lean_obj_tag(v_x_57_) == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__3_60_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__1_58_, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v_head_64_; lean_object* v_tail_65_; lean_object* v___x_66_; 
lean_dec(v_h__1_58_);
v_head_64_ = lean_ctor_get(v_x_57_, 0);
lean_inc(v_head_64_);
v_tail_65_ = lean_ctor_get(v_x_57_, 1);
lean_inc(v_tail_65_);
lean_dec_ref_known(v_x_57_, 2);
v___x_66_ = lean_apply_2(v_h__3_60_, v_head_64_, v_tail_65_);
return v___x_66_;
}
}
else
{
lean_dec(v_h__3_60_);
lean_dec(v_h__1_58_);
if (lean_obj_tag(v_x_57_) == 0)
{
lean_object* v_head_67_; lean_object* v_tail_68_; lean_object* v___x_69_; 
lean_dec(v_h__4_61_);
v_head_67_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_head_67_);
v_tail_68_ = lean_ctor_get(v_x_56_, 1);
lean_inc(v_tail_68_);
lean_dec_ref_known(v_x_56_, 2);
v___x_69_ = lean_apply_2(v_h__2_59_, v_head_67_, v_tail_68_);
return v___x_69_;
}
else
{
lean_object* v_head_70_; lean_object* v_tail_71_; lean_object* v_head_72_; lean_object* v_tail_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_59_);
v_head_70_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_head_70_);
v_tail_71_ = lean_ctor_get(v_x_56_, 1);
lean_inc(v_tail_71_);
lean_dec_ref_known(v_x_56_, 2);
v_head_72_ = lean_ctor_get(v_x_57_, 0);
lean_inc(v_head_72_);
v_tail_73_ = lean_ctor_get(v_x_57_, 1);
lean_inc(v_tail_73_);
lean_dec_ref_known(v_x_57_, 2);
v___x_74_ = lean_apply_4(v_h__4_61_, v_head_70_, v_tail_71_, v_head_72_, v_tail_73_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter(lean_object* v_00_u03b1_75_, lean_object* v_motive_76_, lean_object* v_x_77_, lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_, lean_object* v_h__3_81_, lean_object* v_h__4_82_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_dec(v_h__4_82_);
lean_dec(v_h__2_80_);
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_h__3_81_);
v___x_83_ = lean_box(0);
v___x_84_ = lean_apply_1(v_h__1_79_, v___x_83_);
return v___x_84_;
}
else
{
lean_object* v_head_85_; lean_object* v_tail_86_; lean_object* v___x_87_; 
lean_dec(v_h__1_79_);
v_head_85_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_head_85_);
v_tail_86_ = lean_ctor_get(v_x_78_, 1);
lean_inc(v_tail_86_);
lean_dec_ref_known(v_x_78_, 2);
v___x_87_ = lean_apply_2(v_h__3_81_, v_head_85_, v_tail_86_);
return v___x_87_;
}
}
else
{
lean_dec(v_h__3_81_);
lean_dec(v_h__1_79_);
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v_head_88_; lean_object* v_tail_89_; lean_object* v___x_90_; 
lean_dec(v_h__4_82_);
v_head_88_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_head_88_);
v_tail_89_ = lean_ctor_get(v_x_77_, 1);
lean_inc(v_tail_89_);
lean_dec_ref_known(v_x_77_, 2);
v___x_90_ = lean_apply_2(v_h__2_80_, v_head_88_, v_tail_89_);
return v___x_90_;
}
else
{
lean_object* v_head_91_; lean_object* v_tail_92_; lean_object* v_head_93_; lean_object* v_tail_94_; lean_object* v___x_95_; 
lean_dec(v_h__2_80_);
v_head_91_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_head_91_);
v_tail_92_ = lean_ctor_get(v_x_77_, 1);
lean_inc(v_tail_92_);
lean_dec_ref_known(v_x_77_, 2);
v_head_93_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_head_93_);
v_tail_94_ = lean_ctor_get(v_x_78_, 1);
lean_inc(v_tail_94_);
lean_dec_ref_known(v_x_78_, 2);
v___x_95_ = lean_apply_4(v_h__4_82_, v_head_91_, v_tail_92_, v_head_93_, v_tail_94_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_isEqv___redArg(lean_object* v_x_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_dec_ref(v_x_98_);
if (lean_obj_tag(v_x_97_) == 0)
{
uint8_t v___x_99_; 
v___x_99_ = 1;
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
lean_dec_ref_known(v_x_97_, 2);
v___x_100_ = 0;
return v___x_100_;
}
}
else
{
if (lean_obj_tag(v_x_97_) == 0)
{
uint8_t v___x_101_; 
lean_dec_ref_known(v_x_96_, 2);
lean_dec_ref(v_x_98_);
v___x_101_ = 0;
return v___x_101_;
}
else
{
lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v_head_104_; lean_object* v_tail_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_head_102_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_head_102_);
v_tail_103_ = lean_ctor_get(v_x_96_, 1);
lean_inc(v_tail_103_);
lean_dec_ref_known(v_x_96_, 2);
v_head_104_ = lean_ctor_get(v_x_97_, 0);
lean_inc(v_head_104_);
v_tail_105_ = lean_ctor_get(v_x_97_, 1);
lean_inc(v_tail_105_);
lean_dec_ref_known(v_x_97_, 2);
lean_inc_ref(v_x_98_);
v___x_106_ = lean_apply_2(v_x_98_, v_head_102_, v_head_104_);
v___x_107_ = lean_unbox(v___x_106_);
if (v___x_107_ == 0)
{
uint8_t v___x_108_; 
lean_dec(v_tail_105_);
lean_dec(v_tail_103_);
lean_dec_ref(v_x_98_);
v___x_108_ = lean_unbox(v___x_106_);
return v___x_108_;
}
else
{
v_x_96_ = v_tail_103_;
v_x_97_ = v_tail_105_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___redArg___boxed(lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_List_isEqv___redArg(v_x_110_, v_x_111_, v_x_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv(lean_object* v_00_u03b1_115_, lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = l_List_isEqv___redArg(v_x_116_, v_x_117_, v_x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_List_isEqv___boxed(lean_object* v_00_u03b1_120_, lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_x_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_List_isEqv(v_00_u03b1_120_, v_x_121_, v_x_122_, v_x_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLex___redArg(lean_object* v_inst_126_, lean_object* v_h_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_dec_ref(v_h_127_);
lean_dec_ref(v_inst_126_);
if (lean_obj_tag(v_x_129_) == 0)
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
lean_dec_ref_known(v_x_129_, 2);
v___x_131_ = 1;
return v___x_131_;
}
}
else
{
if (lean_obj_tag(v_x_129_) == 0)
{
uint8_t v___x_132_; 
lean_dec_ref_known(v_x_128_, 2);
lean_dec_ref(v_h_127_);
lean_dec_ref(v_inst_126_);
v___x_132_ = 0;
return v___x_132_;
}
else
{
lean_object* v_head_133_; lean_object* v_tail_134_; lean_object* v_head_135_; lean_object* v_tail_136_; lean_object* v___x_137_; lean_object* v_decide_138_; uint8_t v___x_139_; 
v_head_133_ = lean_ctor_get(v_x_128_, 0);
lean_inc_n(v_head_133_, 2);
v_tail_134_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_tail_134_);
lean_dec_ref_known(v_x_128_, 2);
v_head_135_ = lean_ctor_get(v_x_129_, 0);
lean_inc_n(v_head_135_, 2);
v_tail_136_ = lean_ctor_get(v_x_129_, 1);
lean_inc(v_tail_136_);
lean_dec_ref_known(v_x_129_, 2);
lean_inc_ref(v_inst_126_);
v___x_137_ = lean_apply_2(v_inst_126_, v_head_133_, v_head_135_);
lean_inc_ref(v_h_127_);
v_decide_138_ = lean_apply_2(v_h_127_, v_head_133_, v_head_135_);
v___x_139_ = lean_unbox(v_decide_138_);
if (v___x_139_ == 0)
{
uint8_t v___x_140_; 
v___x_140_ = lean_unbox(v___x_137_);
if (v___x_140_ == 0)
{
uint8_t v___x_141_; 
lean_dec(v_tail_136_);
lean_dec(v_tail_134_);
lean_dec_ref(v_h_127_);
lean_dec_ref(v_inst_126_);
v___x_141_ = lean_unbox(v___x_137_);
return v___x_141_;
}
else
{
uint8_t v_decide_142_; 
v_decide_142_ = l_List_decidableLex___redArg(v_inst_126_, v_h_127_, v_tail_134_, v_tail_136_);
if (v_decide_142_ == 0)
{
return v_decide_142_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = lean_unbox(v___x_137_);
return v___x_143_;
}
}
}
else
{
uint8_t v___x_144_; 
lean_dec(v_tail_136_);
lean_dec(v_tail_134_);
lean_dec_ref(v_h_127_);
lean_dec_ref(v_inst_126_);
v___x_144_ = lean_unbox(v_decide_138_);
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableLex___redArg___boxed(lean_object* v_inst_145_, lean_object* v_h_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_List_decidableLex___redArg(v_inst_145_, v_h_146_, v_x_147_, v_x_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLex(lean_object* v_00_u03b1_151_, lean_object* v_inst_152_, lean_object* v_r_153_, lean_object* v_h_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = l_List_decidableLex___redArg(v_inst_152_, v_h_154_, v_x_155_, v_x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLex___boxed(lean_object* v_00_u03b1_158_, lean_object* v_inst_159_, lean_object* v_r_160_, lean_object* v_h_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_List_decidableLex(v_00_u03b1_158_, v_inst_159_, v_r_160_, v_h_161_, v_x_162_, v_x_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_List_instLT(lean_object* v_00_u03b1_166_, lean_object* v_inst_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLT___redArg(lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_l_u2081_171_, lean_object* v_l_u2082_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = l_List_decidableLex___redArg(v_inst_169_, v_inst_170_, v_l_u2081_171_, v_l_u2082_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLT___redArg___boxed(lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_l_u2081_176_, lean_object* v_l_u2082_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_List_decidableLT___redArg(v_inst_174_, v_inst_175_, v_l_u2081_176_, v_l_u2082_177_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLT(lean_object* v_00_u03b1_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_l_u2081_184_, lean_object* v_l_u2082_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_List_decidableLex___redArg(v_inst_181_, v_inst_183_, v_l_u2081_184_, v_l_u2082_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLT___boxed(lean_object* v_00_u03b1_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_l_u2081_191_, lean_object* v_l_u2082_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_List_decidableLT(v_00_u03b1_187_, v_inst_188_, v_inst_189_, v_inst_190_, v_l_u2081_191_, v_l_u2082_192_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_List_instLE(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_box(0);
return v___x_197_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLE___redArg(lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_l_u2081_200_, lean_object* v_l_u2082_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = l_List_decidableLex___redArg(v_inst_198_, v_inst_199_, v_l_u2082_201_, v_l_u2081_200_);
if (v___x_202_ == 0)
{
uint8_t v___x_203_; 
v___x_203_ = 1;
return v___x_203_;
}
else
{
uint8_t v___x_204_; 
v___x_204_ = 0;
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_List_decidableLE___redArg___boxed(lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_l_u2081_207_, lean_object* v_l_u2082_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_List_decidableLE___redArg(v_inst_205_, v_inst_206_, v_l_u2081_207_, v_l_u2082_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLE(lean_object* v_00_u03b1_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_l_u2081_215_, lean_object* v_l_u2082_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = l_List_decidableLE___redArg(v_inst_212_, v_inst_214_, v_l_u2081_215_, v_l_u2082_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLE___boxed(lean_object* v_00_u03b1_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_l_u2081_222_, lean_object* v_l_u2082_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_List_decidableLE(v_00_u03b1_218_, v_inst_219_, v_inst_220_, v_inst_221_, v_l_u2081_222_, v_l_u2082_223_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__12(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(l_List_lex___auto__1___closed__10));
v___x_253_ = l_Lean_mkAtom(v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_obj_once(&l_List_lex___auto__1___closed__12, &l_List_lex___auto__1___closed__12_once, _init_l_List_lex___auto__1___closed__12);
v___x_255_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_256_ = lean_array_push(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l_List_lex___auto__1___closed__19));
v___x_272_ = l_Lean_mkAtom(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__21(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_obj_once(&l_List_lex___auto__1___closed__20, &l_List_lex___auto__1___closed__20_once, _init_l_List_lex___auto__1___closed__20);
v___x_274_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_275_ = lean_array_push(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__25(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_List_lex___auto__1___closed__24));
v___x_281_ = lean_string_utf8_byte_size(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_282_ = lean_obj_once(&l_List_lex___auto__1___closed__25, &l_List_lex___auto__1___closed__25_once, _init_l_List_lex___auto__1___closed__25);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = ((lean_object*)(l_List_lex___auto__1___closed__24));
v___x_285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
lean_ctor_set(v___x_285_, 2, v___x_282_);
return v___x_285_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_286_ = lean_box(0);
v___x_287_ = lean_box(0);
v___x_288_ = lean_obj_once(&l_List_lex___auto__1___closed__26, &l_List_lex___auto__1___closed__26_once, _init_l_List_lex___auto__1___closed__26);
v___x_289_ = lean_box(2);
v___x_290_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_288_);
lean_ctor_set(v___x_290_, 2, v___x_287_);
lean_ctor_set(v___x_290_, 3, v___x_286_);
return v___x_290_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_List_lex___auto__1___closed__27, &l_List_lex___auto__1___closed__27_once, _init_l_List_lex___auto__1___closed__27);
v___x_292_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_293_ = lean_array_push(v___x_292_, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = lean_obj_once(&l_List_lex___auto__1___closed__28, &l_List_lex___auto__1___closed__28_once, _init_l_List_lex___auto__1___closed__28);
v___x_295_ = ((lean_object*)(l_List_lex___auto__1___closed__23));
v___x_296_ = lean_box(2);
v___x_297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
lean_ctor_set(v___x_297_, 2, v___x_294_);
return v___x_297_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_299_ = lean_obj_once(&l_List_lex___auto__1___closed__21, &l_List_lex___auto__1___closed__21_once, _init_l_List_lex___auto__1___closed__21);
v___x_300_ = lean_array_push(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = lean_obj_once(&l_List_lex___auto__1___closed__30, &l_List_lex___auto__1___closed__30_once, _init_l_List_lex___auto__1___closed__30);
v___x_302_ = ((lean_object*)(l_List_lex___auto__1___closed__18));
v___x_303_ = lean_box(2);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_ctor_set(v___x_304_, 2, v___x_301_);
return v___x_304_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_obj_once(&l_List_lex___auto__1___closed__31, &l_List_lex___auto__1___closed__31_once, _init_l_List_lex___auto__1___closed__31);
v___x_306_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_307_ = lean_array_push(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_List_lex___auto__1___closed__37));
v___x_319_ = l_Lean_mkAtom(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_obj_once(&l_List_lex___auto__1___closed__38, &l_List_lex___auto__1___closed__38_once, _init_l_List_lex___auto__1___closed__38);
v___x_321_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_322_ = lean_array_push(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_324_ = lean_obj_once(&l_List_lex___auto__1___closed__39, &l_List_lex___auto__1___closed__39_once, _init_l_List_lex___auto__1___closed__39);
v___x_325_ = lean_array_push(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_326_ = lean_obj_once(&l_List_lex___auto__1___closed__40, &l_List_lex___auto__1___closed__40_once, _init_l_List_lex___auto__1___closed__40);
v___x_327_ = ((lean_object*)(l_List_lex___auto__1___closed__36));
v___x_328_ = lean_box(2);
v___x_329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
lean_ctor_set(v___x_329_, 2, v___x_326_);
return v___x_329_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_331_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_332_ = lean_array_push(v___x_331_, v___x_330_);
return v___x_332_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l_List_lex___auto__1___closed__43));
v___x_335_ = l_Lean_mkAtom(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_obj_once(&l_List_lex___auto__1___closed__44, &l_List_lex___auto__1___closed__44_once, _init_l_List_lex___auto__1___closed__44);
v___x_337_ = lean_obj_once(&l_List_lex___auto__1___closed__42, &l_List_lex___auto__1___closed__42_once, _init_l_List_lex___auto__1___closed__42);
v___x_338_ = lean_array_push(v___x_337_, v___x_336_);
return v___x_338_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_340_ = lean_obj_once(&l_List_lex___auto__1___closed__45, &l_List_lex___auto__1___closed__45_once, _init_l_List_lex___auto__1___closed__45);
v___x_341_ = lean_array_push(v___x_340_, v___x_339_);
return v___x_341_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_342_ = lean_obj_once(&l_List_lex___auto__1___closed__46, &l_List_lex___auto__1___closed__46_once, _init_l_List_lex___auto__1___closed__46);
v___x_343_ = ((lean_object*)(l_List_lex___auto__1___closed__34));
v___x_344_ = lean_box(2);
v___x_345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
lean_ctor_set(v___x_345_, 2, v___x_342_);
return v___x_345_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__48(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_obj_once(&l_List_lex___auto__1___closed__47, &l_List_lex___auto__1___closed__47_once, _init_l_List_lex___auto__1___closed__47);
v___x_347_ = lean_obj_once(&l_List_lex___auto__1___closed__32, &l_List_lex___auto__1___closed__32_once, _init_l_List_lex___auto__1___closed__32);
v___x_348_ = lean_array_push(v___x_347_, v___x_346_);
return v___x_348_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__50(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_List_lex___auto__1___closed__49));
v___x_351_ = l_Lean_mkAtom(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__51(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&l_List_lex___auto__1___closed__50, &l_List_lex___auto__1___closed__50_once, _init_l_List_lex___auto__1___closed__50);
v___x_353_ = lean_obj_once(&l_List_lex___auto__1___closed__48, &l_List_lex___auto__1___closed__48_once, _init_l_List_lex___auto__1___closed__48);
v___x_354_ = lean_array_push(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__52(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_obj_once(&l_List_lex___auto__1___closed__51, &l_List_lex___auto__1___closed__51_once, _init_l_List_lex___auto__1___closed__51);
v___x_356_ = ((lean_object*)(l_List_lex___auto__1___closed__16));
v___x_357_ = lean_box(2);
v___x_358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
lean_ctor_set(v___x_358_, 2, v___x_355_);
return v___x_358_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__53(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_List_lex___auto__1___closed__52, &l_List_lex___auto__1___closed__52_once, _init_l_List_lex___auto__1___closed__52);
v___x_360_ = lean_obj_once(&l_List_lex___auto__1___closed__13, &l_List_lex___auto__1___closed__13_once, _init_l_List_lex___auto__1___closed__13);
v___x_361_ = lean_array_push(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__54(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = lean_obj_once(&l_List_lex___auto__1___closed__53, &l_List_lex___auto__1___closed__53_once, _init_l_List_lex___auto__1___closed__53);
v___x_363_ = ((lean_object*)(l_List_lex___auto__1___closed__11));
v___x_364_ = lean_box(2);
v___x_365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_362_);
return v___x_365_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__55(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_obj_once(&l_List_lex___auto__1___closed__54, &l_List_lex___auto__1___closed__54_once, _init_l_List_lex___auto__1___closed__54);
v___x_367_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_368_ = lean_array_push(v___x_367_, v___x_366_);
return v___x_368_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__56(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_369_ = lean_obj_once(&l_List_lex___auto__1___closed__55, &l_List_lex___auto__1___closed__55_once, _init_l_List_lex___auto__1___closed__55);
v___x_370_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_371_ = lean_box(2);
v___x_372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
lean_ctor_set(v___x_372_, 2, v___x_369_);
return v___x_372_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__57(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_List_lex___auto__1___closed__56, &l_List_lex___auto__1___closed__56_once, _init_l_List_lex___auto__1___closed__56);
v___x_374_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_375_ = lean_array_push(v___x_374_, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__58(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_376_ = lean_obj_once(&l_List_lex___auto__1___closed__57, &l_List_lex___auto__1___closed__57_once, _init_l_List_lex___auto__1___closed__57);
v___x_377_ = ((lean_object*)(l_List_lex___auto__1___closed__7));
v___x_378_ = lean_box(2);
v___x_379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
lean_ctor_set(v___x_379_, 2, v___x_376_);
return v___x_379_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__59(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_obj_once(&l_List_lex___auto__1___closed__58, &l_List_lex___auto__1___closed__58_once, _init_l_List_lex___auto__1___closed__58);
v___x_381_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_382_ = lean_array_push(v___x_381_, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__60(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_383_ = lean_obj_once(&l_List_lex___auto__1___closed__59, &l_List_lex___auto__1___closed__59_once, _init_l_List_lex___auto__1___closed__59);
v___x_384_ = ((lean_object*)(l_List_lex___auto__1___closed__4));
v___x_385_ = lean_box(2);
v___x_386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_384_);
lean_ctor_set(v___x_386_, 2, v___x_383_);
return v___x_386_;
}
}
static lean_object* _init_l_List_lex___auto__1(void){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_obj_once(&l_List_lex___auto__1___closed__60, &l_List_lex___auto__1___closed__60_once, _init_l_List_lex___auto__1___closed__60);
return v___x_387_;
}
}
LEAN_EXPORT uint8_t l_List_lex___redArg(lean_object* v_inst_388_, lean_object* v_l_u2081_389_, lean_object* v_l_u2082_390_, lean_object* v_lt_391_){
_start:
{
if (lean_obj_tag(v_l_u2081_389_) == 0)
{
lean_dec_ref(v_lt_391_);
lean_dec_ref(v_inst_388_);
if (lean_obj_tag(v_l_u2082_390_) == 0)
{
uint8_t v___x_392_; 
v___x_392_ = 0;
return v___x_392_;
}
else
{
uint8_t v___x_393_; 
lean_dec_ref_known(v_l_u2082_390_, 2);
v___x_393_ = 1;
return v___x_393_;
}
}
else
{
if (lean_obj_tag(v_l_u2082_390_) == 0)
{
uint8_t v___x_394_; 
lean_dec_ref_known(v_l_u2081_389_, 2);
lean_dec_ref(v_lt_391_);
lean_dec_ref(v_inst_388_);
v___x_394_ = 0;
return v___x_394_;
}
else
{
lean_object* v_head_395_; lean_object* v_tail_396_; lean_object* v_head_397_; lean_object* v_tail_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_head_395_ = lean_ctor_get(v_l_u2081_389_, 0);
lean_inc_n(v_head_395_, 2);
v_tail_396_ = lean_ctor_get(v_l_u2081_389_, 1);
lean_inc(v_tail_396_);
lean_dec_ref_known(v_l_u2081_389_, 2);
v_head_397_ = lean_ctor_get(v_l_u2082_390_, 0);
lean_inc_n(v_head_397_, 2);
v_tail_398_ = lean_ctor_get(v_l_u2082_390_, 1);
lean_inc(v_tail_398_);
lean_dec_ref_known(v_l_u2082_390_, 2);
lean_inc_ref(v_lt_391_);
v___x_399_ = lean_apply_2(v_lt_391_, v_head_395_, v_head_397_);
v___x_400_ = lean_unbox(v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; uint8_t v___x_402_; 
lean_inc_ref(v_inst_388_);
v___x_401_ = lean_apply_2(v_inst_388_, v_head_395_, v_head_397_);
v___x_402_ = lean_unbox(v___x_401_);
if (v___x_402_ == 0)
{
uint8_t v___x_403_; 
lean_dec(v_tail_398_);
lean_dec(v_tail_396_);
lean_dec_ref(v_lt_391_);
lean_dec_ref(v_inst_388_);
v___x_403_ = lean_unbox(v___x_401_);
return v___x_403_;
}
else
{
v_l_u2081_389_ = v_tail_396_;
v_l_u2082_390_ = v_tail_398_;
goto _start;
}
}
else
{
uint8_t v___x_405_; 
lean_dec(v_tail_398_);
lean_dec(v_head_397_);
lean_dec(v_tail_396_);
lean_dec(v_head_395_);
lean_dec_ref(v_lt_391_);
lean_dec_ref(v_inst_388_);
v___x_405_ = lean_unbox(v___x_399_);
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_lex___redArg___boxed(lean_object* v_inst_406_, lean_object* v_l_u2081_407_, lean_object* v_l_u2082_408_, lean_object* v_lt_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_List_lex___redArg(v_inst_406_, v_l_u2081_407_, v_l_u2082_408_, v_lt_409_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l_List_lex(lean_object* v_00_u03b1_412_, lean_object* v_inst_413_, lean_object* v_l_u2081_414_, lean_object* v_l_u2082_415_, lean_object* v_lt_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = l_List_lex___redArg(v_inst_413_, v_l_u2081_414_, v_l_u2082_415_, v_lt_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_List_lex___boxed(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_, lean_object* v_l_u2081_420_, lean_object* v_l_u2082_421_, lean_object* v_lt_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_List_lex(v_00_u03b1_418_, v_inst_419_, v_l_u2081_420_, v_l_u2082_421_, v_lt_422_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg(lean_object* v_x_425_){
_start:
{
lean_object* v_tail_426_; 
v_tail_426_ = lean_ctor_get(v_x_425_, 1);
if (lean_obj_tag(v_tail_426_) == 0)
{
lean_object* v_head_427_; 
v_head_427_ = lean_ctor_get(v_x_425_, 0);
lean_inc(v_head_427_);
return v_head_427_;
}
else
{
v_x_425_ = v_tail_426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg___boxed(lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_List_getLast___redArg(v_x_429_);
lean_dec(v_x_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_List_getLast(lean_object* v_00_u03b1_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_List_getLast___redArg(v_x_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___boxed(lean_object* v_00_u03b1_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_List_getLast(v_00_u03b1_435_, v_x_436_, v_x_437_);
lean_dec(v_x_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg(lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_box(0);
return v___x_440_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = l_List_getLast___redArg(v_x_439_);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg___boxed(lean_object* v_x_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_List_getLast_x3f___redArg(v_x_443_);
lean_dec(v_x_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f(lean_object* v_00_u03b1_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_List_getLast_x3f___redArg(v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___boxed(lean_object* v_00_u03b1_448_, lean_object* v_x_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_List_getLast_x3f(v_00_u03b1_448_, v_x_449_);
lean_dec(v_x_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg(lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_inc(v_x_452_);
return v_x_452_;
}
else
{
lean_object* v___x_453_; 
v___x_453_ = l_List_getLast___redArg(v_x_451_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg___boxed(lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_List_getLastD___redArg(v_x_454_, v_x_455_);
lean_dec(v_x_455_);
lean_dec(v_x_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD(lean_object* v_00_u03b1_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_List_getLastD___redArg(v_x_458_, v_x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___boxed(lean_object* v_00_u03b1_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_List_getLastD(v_00_u03b1_461_, v_x_462_, v_x_463_);
lean_dec(v_x_463_);
lean_dec(v_x_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg(lean_object* v_x_465_){
_start:
{
lean_object* v_head_466_; 
v_head_466_ = lean_ctor_get(v_x_465_, 0);
lean_inc(v_head_466_);
return v_head_466_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg___boxed(lean_object* v_x_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_List_head___redArg(v_x_467_);
lean_dec(v_x_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_List_head(lean_object* v_00_u03b1_469_, lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v_head_472_; 
v_head_472_ = lean_ctor_get(v_x_470_, 0);
lean_inc(v_head_472_);
return v_head_472_;
}
}
LEAN_EXPORT lean_object* l_List_head___boxed(lean_object* v_00_u03b1_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_List_head(v_00_u03b1_473_, v_x_474_, v_x_475_);
lean_dec(v_x_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg(lean_object* v_x_477_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_box(0);
return v___x_478_;
}
else
{
lean_object* v_head_479_; lean_object* v___x_480_; 
v_head_479_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_head_479_);
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v_head_479_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg___boxed(lean_object* v_x_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_List_head_x3f___redArg(v_x_481_);
lean_dec(v_x_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f(lean_object* v_00_u03b1_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_List_head_x3f___redArg(v_x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___boxed(lean_object* v_00_u03b1_486_, lean_object* v_x_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_List_head_x3f(v_00_u03b1_486_, v_x_487_);
lean_dec(v_x_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg(lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
lean_inc(v_x_490_);
return v_x_490_;
}
else
{
lean_object* v_head_491_; 
v_head_491_ = lean_ctor_get(v_x_489_, 0);
lean_inc(v_head_491_);
return v_head_491_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg___boxed(lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_List_headD___redArg(v_x_492_, v_x_493_);
lean_dec(v_x_493_);
lean_dec(v_x_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_List_headD(lean_object* v_00_u03b1_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_inc(v_x_497_);
return v_x_497_;
}
else
{
lean_object* v_head_498_; 
v_head_498_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_head_498_);
return v_head_498_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___boxed(lean_object* v_00_u03b1_499_, lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_List_headD(v_00_u03b1_499_, v_x_500_, v_x_501_);
lean_dec(v_x_501_);
lean_dec(v_x_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg(lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
return v_x_503_;
}
else
{
lean_object* v_tail_504_; 
v_tail_504_ = lean_ctor_get(v_x_503_, 1);
lean_inc(v_tail_504_);
return v_tail_504_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg___boxed(lean_object* v_x_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_List_tail___redArg(v_x_505_);
lean_dec(v_x_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_List_tail(lean_object* v_00_u03b1_507_, lean_object* v_x_508_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
return v_x_508_;
}
else
{
lean_object* v_tail_509_; 
v_tail_509_ = lean_ctor_get(v_x_508_, 1);
lean_inc(v_tail_509_);
return v_tail_509_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___boxed(lean_object* v_00_u03b1_510_, lean_object* v_x_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_List_tail(v_00_u03b1_510_, v_x_511_);
lean_dec(v_x_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg(lean_object* v_x_513_){
_start:
{
if (lean_obj_tag(v_x_513_) == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_box(0);
return v___x_514_;
}
else
{
lean_object* v_tail_515_; lean_object* v___x_516_; 
v_tail_515_ = lean_ctor_get(v_x_513_, 1);
lean_inc(v_tail_515_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v_tail_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg___boxed(lean_object* v_x_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_List_tail_x3f___redArg(v_x_517_);
lean_dec(v_x_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f(lean_object* v_00_u03b1_519_, lean_object* v_x_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_List_tail_x3f___redArg(v_x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___boxed(lean_object* v_00_u03b1_522_, lean_object* v_x_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_List_tail_x3f(v_00_u03b1_522_, v_x_523_);
lean_dec(v_x_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg(lean_object* v_l_525_, lean_object* v_fallback_526_){
_start:
{
if (lean_obj_tag(v_l_525_) == 0)
{
lean_inc(v_fallback_526_);
return v_fallback_526_;
}
else
{
lean_object* v_tail_527_; 
v_tail_527_ = lean_ctor_get(v_l_525_, 1);
lean_inc(v_tail_527_);
return v_tail_527_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg___boxed(lean_object* v_l_528_, lean_object* v_fallback_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_List_tailD___redArg(v_l_528_, v_fallback_529_);
lean_dec(v_fallback_529_);
lean_dec(v_l_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_List_tailD(lean_object* v_00_u03b1_531_, lean_object* v_l_532_, lean_object* v_fallback_533_){
_start:
{
if (lean_obj_tag(v_l_532_) == 0)
{
lean_inc(v_fallback_533_);
return v_fallback_533_;
}
else
{
lean_object* v_tail_534_; 
v_tail_534_ = lean_ctor_get(v_l_532_, 1);
lean_inc(v_tail_534_);
return v_tail_534_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___boxed(lean_object* v_00_u03b1_535_, lean_object* v_l_536_, lean_object* v_fallback_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_List_tailD(v_00_u03b1_535_, v_l_536_, v_fallback_537_);
lean_dec(v_fallback_537_);
lean_dec(v_l_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_List_filter___redArg(lean_object* v_p_539_, lean_object* v_x_540_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_dec_ref(v_p_539_);
return v_x_540_;
}
else
{
lean_object* v_head_541_; lean_object* v_tail_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_553_; 
v_head_541_ = lean_ctor_get(v_x_540_, 0);
v_tail_542_ = lean_ctor_get(v_x_540_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_553_ == 0)
{
v___x_544_ = v_x_540_;
v_isShared_545_ = v_isSharedCheck_553_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_tail_542_);
lean_inc(v_head_541_);
lean_dec(v_x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_553_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; uint8_t v___x_547_; 
lean_inc_ref(v_p_539_);
lean_inc(v_head_541_);
v___x_546_ = lean_apply_1(v_p_539_, v_head_541_);
v___x_547_ = lean_unbox(v___x_546_);
if (v___x_547_ == 0)
{
lean_del_object(v___x_544_);
lean_dec(v_head_541_);
v_x_540_ = v_tail_542_;
goto _start;
}
else
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = l_List_filter___redArg(v_p_539_, v_tail_542_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_549_);
v___x_551_ = v___x_544_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_head_541_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filter(lean_object* v_00_u03b1_554_, lean_object* v_p_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_List_filter___redArg(v_p_555_, v_x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg(lean_object* v_f_558_, lean_object* v_init_559_, lean_object* v_x_560_){
_start:
{
if (lean_obj_tag(v_x_560_) == 0)
{
lean_dec(v_f_558_);
lean_inc(v_init_559_);
return v_init_559_;
}
else
{
lean_object* v_head_561_; lean_object* v_tail_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_head_561_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_head_561_);
v_tail_562_ = lean_ctor_get(v_x_560_, 1);
lean_inc(v_tail_562_);
lean_dec_ref_known(v_x_560_, 2);
lean_inc(v_f_558_);
v___x_563_ = l_List_foldr___redArg(v_f_558_, v_init_559_, v_tail_562_);
v___x_564_ = lean_apply_2(v_f_558_, v_head_561_, v___x_563_);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg___boxed(lean_object* v_f_565_, lean_object* v_init_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_List_foldr___redArg(v_f_565_, v_init_566_, v_x_567_);
lean_dec(v_init_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_List_foldr(lean_object* v_00_u03b1_569_, lean_object* v_00_u03b2_570_, lean_object* v_f_571_, lean_object* v_init_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_List_foldr___redArg(v_f_571_, v_init_572_, v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___boxed(lean_object* v_00_u03b1_575_, lean_object* v_00_u03b2_576_, lean_object* v_f_577_, lean_object* v_init_578_, lean_object* v_x_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_List_foldr(v_00_u03b1_575_, v_00_u03b2_576_, v_f_577_, v_init_578_, v_x_579_);
lean_dec(v_init_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_List_reverseAux___redArg(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
return v_x_582_;
}
else
{
lean_object* v_head_583_; lean_object* v_tail_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_head_583_ = lean_ctor_get(v_x_581_, 0);
v_tail_584_ = lean_ctor_get(v_x_581_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v_x_581_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_tail_584_);
lean_inc(v_head_583_);
lean_dec(v_x_581_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_x_582_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_head_583_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_x_582_);
v___x_589_ = v_reuseFailAlloc_591_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
v_x_581_ = v_tail_584_;
v_x_582_ = v___x_589_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object* v_00_u03b1_593_, lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_List_reverseAux___redArg(v_x_594_, v_x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_List_reverse___redArg(lean_object* v_as_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_box(0);
v___x_599_ = l_List_reverseAux___redArg(v_as_597_, v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_List_reverse(lean_object* v_00_u03b1_600_, lean_object* v_as_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_List_reverse___redArg(v_as_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
_start:
{
if (lean_obj_tag(v_x_603_) == 0)
{
lean_object* v___x_607_; 
lean_dec(v_h__2_606_);
v___x_607_ = lean_apply_1(v_h__1_605_, v_x_604_);
return v___x_607_;
}
else
{
lean_object* v_head_608_; lean_object* v_tail_609_; lean_object* v___x_610_; 
lean_dec(v_h__1_605_);
v_head_608_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_head_608_);
v_tail_609_ = lean_ctor_get(v_x_603_, 1);
lean_inc(v_tail_609_);
lean_dec_ref_known(v_x_603_, 2);
v___x_610_ = lean_apply_3(v_h__2_606_, v_head_608_, v_tail_609_, v_x_604_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_611_, lean_object* v_motive_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v___x_617_; 
lean_dec(v_h__2_616_);
v___x_617_ = lean_apply_1(v_h__1_615_, v_x_614_);
return v___x_617_;
}
else
{
lean_object* v_head_618_; lean_object* v_tail_619_; lean_object* v___x_620_; 
lean_dec(v_h__1_615_);
v_head_618_ = lean_ctor_get(v_x_613_, 0);
lean_inc(v_head_618_);
v_tail_619_ = lean_ctor_get(v_x_613_, 1);
lean_inc(v_tail_619_);
lean_dec_ref_known(v_x_613_, 2);
v___x_620_ = lean_apply_3(v_h__2_616_, v_head_618_, v_tail_619_, v_x_614_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_List_appendTR___redArg(lean_object* v_as_621_, lean_object* v_bs_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = l_List_reverse___redArg(v_as_621_);
v___x_624_ = l_List_reverseAux___redArg(v___x_623_, v_bs_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR(lean_object* v_00_u03b1_625_, lean_object* v_as_626_, lean_object* v_bs_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_List_appendTR___redArg(v_as_626_, v_bs_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter___redArg(lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_h__1_631_, lean_object* v_h__2_632_){
_start:
{
if (lean_obj_tag(v_x_629_) == 0)
{
lean_object* v___x_633_; 
lean_dec(v_h__2_632_);
v___x_633_ = lean_apply_1(v_h__1_631_, v_x_630_);
return v___x_633_;
}
else
{
lean_object* v_head_634_; lean_object* v_tail_635_; lean_object* v___x_636_; 
lean_dec(v_h__1_631_);
v_head_634_ = lean_ctor_get(v_x_629_, 0);
lean_inc(v_head_634_);
v_tail_635_ = lean_ctor_get(v_x_629_, 1);
lean_inc(v_tail_635_);
lean_dec_ref_known(v_x_629_, 2);
v___x_636_ = lean_apply_3(v_h__2_632_, v_head_634_, v_tail_635_, v_x_630_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter(lean_object* v_00_u03b1_637_, lean_object* v_motive_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_h__1_641_, lean_object* v_h__2_642_){
_start:
{
if (lean_obj_tag(v_x_639_) == 0)
{
lean_object* v___x_643_; 
lean_dec(v_h__2_642_);
v___x_643_ = lean_apply_1(v_h__1_641_, v_x_640_);
return v___x_643_;
}
else
{
lean_object* v_head_644_; lean_object* v_tail_645_; lean_object* v___x_646_; 
lean_dec(v_h__1_641_);
v_head_644_ = lean_ctor_get(v_x_639_, 0);
lean_inc(v_head_644_);
v_tail_645_ = lean_ctor_get(v_x_639_, 1);
lean_inc(v_tail_645_);
lean_dec_ref_known(v_x_639_, 2);
v___x_646_ = lean_apply_3(v_h__2_642_, v_head_644_, v_tail_645_, v_x_640_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_List_instAppend(lean_object* v_00_u03b1_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = ((lean_object*)(l_List_instAppend___closed__0));
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_List_singleton___redArg(lean_object* v_a_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_box(0);
v___x_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_652_, 0, v_a_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_List_singleton(lean_object* v_00_u03b1_653_, lean_object* v_a_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_box(0);
v___x_656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_656_, 0, v_a_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg(lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
lean_object* v_zero_659_; uint8_t v_isZero_660_; 
v_zero_659_ = lean_unsigned_to_nat(0u);
v_isZero_660_ = lean_nat_dec_eq(v_x_657_, v_zero_659_);
if (v_isZero_660_ == 1)
{
lean_object* v___x_661_; 
lean_dec(v_x_658_);
v___x_661_ = lean_box(0);
return v___x_661_;
}
else
{
lean_object* v_one_662_; lean_object* v_n_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_one_662_ = lean_unsigned_to_nat(1u);
v_n_663_ = lean_nat_sub(v_x_657_, v_one_662_);
lean_inc(v_x_658_);
v___x_664_ = l_List_replicate___redArg(v_n_663_, v_x_658_);
lean_dec(v_n_663_);
v___x_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_665_, 0, v_x_658_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg___boxed(lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_List_replicate___redArg(v_x_666_, v_x_667_);
lean_dec(v_x_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_List_replicate(lean_object* v_00_u03b1_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_List_replicate___redArg(v_x_670_, v_x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___boxed(lean_object* v_00_u03b1_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_List_replicate(v_00_u03b1_673_, v_x_674_, v_x_675_);
lean_dec(v_x_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg(lean_object* v_n_677_, lean_object* v_a_678_, lean_object* v_l_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_680_ = l_List_length___redArg(v_l_679_);
v___x_681_ = lean_nat_sub(v_n_677_, v___x_680_);
lean_dec(v___x_680_);
v___x_682_ = l_List_replicate___redArg(v___x_681_, v_a_678_);
lean_dec(v___x_681_);
v___x_683_ = l_List_appendTR___redArg(v___x_682_, v_l_679_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg___boxed(lean_object* v_n_684_, lean_object* v_a_685_, lean_object* v_l_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_List_leftpad___redArg(v_n_684_, v_a_685_, v_l_686_);
lean_dec(v_n_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad(lean_object* v_00_u03b1_688_, lean_object* v_n_689_, lean_object* v_a_690_, lean_object* v_l_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_List_leftpad___redArg(v_n_689_, v_a_690_, v_l_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___boxed(lean_object* v_00_u03b1_693_, lean_object* v_n_694_, lean_object* v_a_695_, lean_object* v_l_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_List_leftpad(v_00_u03b1_693_, v_n_694_, v_a_695_, v_l_696_);
lean_dec(v_n_694_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg(lean_object* v_n_698_, lean_object* v_a_699_, lean_object* v_l_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_701_ = l_List_length___redArg(v_l_700_);
v___x_702_ = lean_nat_sub(v_n_698_, v___x_701_);
lean_dec(v___x_701_);
v___x_703_ = l_List_replicate___redArg(v___x_702_, v_a_699_);
lean_dec(v___x_702_);
v___x_704_ = l_List_appendTR___redArg(v_l_700_, v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg___boxed(lean_object* v_n_705_, lean_object* v_a_706_, lean_object* v_l_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_List_rightpad___redArg(v_n_705_, v_a_706_, v_l_707_);
lean_dec(v_n_705_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad(lean_object* v_00_u03b1_709_, lean_object* v_n_710_, lean_object* v_a_711_, lean_object* v_l_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_List_rightpad___redArg(v_n_710_, v_a_711_, v_l_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___boxed(lean_object* v_00_u03b1_714_, lean_object* v_n_715_, lean_object* v_a_716_, lean_object* v_l_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_List_rightpad(v_00_u03b1_714_, v_n_715_, v_a_716_, v_l_717_);
lean_dec(v_n_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object* v_00_u03b1_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_box(0);
return v___x_720_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty___redArg(lean_object* v_x_721_){
_start:
{
if (lean_obj_tag(v_x_721_) == 0)
{
uint8_t v___x_722_; 
v___x_722_ = 1;
return v___x_722_;
}
else
{
uint8_t v___x_723_; 
v___x_723_ = 0;
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___redArg___boxed(lean_object* v_x_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l_List_isEmpty___redArg(v_x_724_);
lean_dec(v_x_724_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty(lean_object* v_00_u03b1_727_, lean_object* v_x_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = l_List_isEmpty___redArg(v_x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___boxed(lean_object* v_00_u03b1_730_, lean_object* v_x_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l_List_isEmpty(v_00_u03b1_730_, v_x_731_);
lean_dec(v_x_731_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT uint8_t l_List_elem___redArg(lean_object* v_inst_734_, lean_object* v_a_735_, lean_object* v_x_736_){
_start:
{
if (lean_obj_tag(v_x_736_) == 0)
{
uint8_t v___x_737_; 
lean_dec(v_a_735_);
lean_dec_ref(v_inst_734_);
v___x_737_ = 0;
return v___x_737_;
}
else
{
lean_object* v_head_738_; lean_object* v_tail_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_head_738_ = lean_ctor_get(v_x_736_, 0);
lean_inc(v_head_738_);
v_tail_739_ = lean_ctor_get(v_x_736_, 1);
lean_inc(v_tail_739_);
lean_dec_ref_known(v_x_736_, 2);
lean_inc_ref(v_inst_734_);
lean_inc(v_a_735_);
v___x_740_ = lean_apply_2(v_inst_734_, v_a_735_, v_head_738_);
v___x_741_ = lean_unbox(v___x_740_);
if (v___x_741_ == 0)
{
v_x_736_ = v_tail_739_;
goto _start;
}
else
{
uint8_t v___x_743_; 
lean_dec(v_tail_739_);
lean_dec(v_a_735_);
lean_dec_ref(v_inst_734_);
v___x_743_ = lean_unbox(v___x_740_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___redArg___boxed(lean_object* v_inst_744_, lean_object* v_a_745_, lean_object* v_x_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_List_elem___redArg(v_inst_744_, v_a_745_, v_x_746_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT uint8_t l_List_elem(lean_object* v_00_u03b1_749_, lean_object* v_inst_750_, lean_object* v_a_751_, lean_object* v_x_752_){
_start:
{
uint8_t v___x_753_; 
v___x_753_ = l_List_elem___redArg(v_inst_750_, v_a_751_, v_x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_List_elem___boxed(lean_object* v_00_u03b1_754_, lean_object* v_inst_755_, lean_object* v_a_756_, lean_object* v_x_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l_List_elem(v_00_u03b1_754_, v_inst_755_, v_a_756_, v_x_757_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT uint8_t l_List_contains___redArg(lean_object* v_inst_760_, lean_object* v_as_761_, lean_object* v_a_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = l_List_elem___redArg(v_inst_760_, v_a_762_, v_as_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_List_contains___redArg___boxed(lean_object* v_inst_764_, lean_object* v_as_765_, lean_object* v_a_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_List_contains___redArg(v_inst_764_, v_as_765_, v_a_766_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT uint8_t l_List_contains(lean_object* v_00_u03b1_769_, lean_object* v_inst_770_, lean_object* v_as_771_, lean_object* v_a_772_){
_start:
{
uint8_t v___x_773_; 
v___x_773_ = l_List_elem___redArg(v_inst_770_, v_a_772_, v_as_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_List_contains___boxed(lean_object* v_00_u03b1_774_, lean_object* v_inst_775_, lean_object* v_as_776_, lean_object* v_a_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l_List_contains(v_00_u03b1_774_, v_inst_775_, v_as_776_, v_a_777_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership(lean_object* v_00_u03b1_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_box(0);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_782_, lean_object* v_h__1_783_, lean_object* v_h__2_784_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec(v_h__2_784_);
v___x_785_ = lean_box(0);
v___x_786_ = lean_apply_1(v_h__1_783_, v___x_785_);
return v___x_786_;
}
else
{
lean_object* v_head_787_; lean_object* v_tail_788_; lean_object* v___x_789_; 
lean_dec(v_h__1_783_);
v_head_787_ = lean_ctor_get(v_x_782_, 0);
lean_inc(v_head_787_);
v_tail_788_ = lean_ctor_get(v_x_782_, 1);
lean_inc(v_tail_788_);
lean_dec_ref_known(v_x_782_, 2);
v___x_789_ = lean_apply_2(v_h__2_784_, v_head_787_, v_tail_788_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_790_, lean_object* v_motive_791_, lean_object* v_x_792_, lean_object* v_h__1_793_, lean_object* v_h__2_794_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec(v_h__2_794_);
v___x_795_ = lean_box(0);
v___x_796_ = lean_apply_1(v_h__1_793_, v___x_795_);
return v___x_796_;
}
else
{
lean_object* v_head_797_; lean_object* v_tail_798_; lean_object* v___x_799_; 
lean_dec(v_h__1_793_);
v_head_797_ = lean_ctor_get(v_x_792_, 0);
lean_inc(v_head_797_);
v_tail_798_ = lean_ctor_get(v_x_792_, 1);
lean_inc(v_tail_798_);
lean_dec_ref_known(v_x_792_, 2);
v___x_799_ = lean_apply_2(v_h__2_794_, v_head_797_, v_tail_798_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(uint8_t v_x_800_, lean_object* v_h__1_801_, lean_object* v_h__2_802_){
_start:
{
if (v_x_800_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v_h__1_801_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_apply_1(v_h__2_802_, v___x_803_);
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v_h__2_802_);
v___x_805_ = lean_box(0);
v___x_806_ = lean_apply_1(v_h__1_801_, v___x_805_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_807_, lean_object* v_h__1_808_, lean_object* v_h__2_809_){
_start:
{
uint8_t v_x_24__boxed_810_; lean_object* v_res_811_; 
v_x_24__boxed_810_ = lean_unbox(v_x_807_);
v_res_811_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_810_, v_h__1_808_, v_h__2_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object* v_motive_812_, uint8_t v_x_813_, lean_object* v_h__1_814_, lean_object* v_h__2_815_){
_start:
{
if (v_x_813_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec(v_h__1_814_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_apply_1(v_h__2_815_, v___x_816_);
return v___x_817_;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec(v_h__2_815_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_apply_1(v_h__1_814_, v___x_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_820_, lean_object* v_x_821_, lean_object* v_h__1_822_, lean_object* v_h__2_823_){
_start:
{
uint8_t v_x_35__boxed_824_; lean_object* v_res_825_; 
v_x_35__boxed_824_ = lean_unbox(v_x_821_);
v_res_825_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(v_motive_820_, v_x_35__boxed_824_, v_h__1_822_, v_h__2_823_);
return v_res_825_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_826_, lean_object* v_a_827_, lean_object* v_as_828_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = l_List_elem___redArg(v_inst_826_, v_a_827_, v_as_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_830_, lean_object* v_a_831_, lean_object* v_as_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_List_instDecidableMemOfLawfulBEq___redArg(v_inst_830_, v_a_831_, v_as_832_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_a_838_, lean_object* v_as_839_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = l_List_elem___redArg(v_inst_836_, v_a_838_, v_as_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_a_844_, lean_object* v_as_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_List_instDecidableMemOfLawfulBEq(v_00_u03b1_841_, v_inst_842_, v_inst_843_, v_a_844_, v_as_845_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx___redArg(lean_object* v_inst_848_, lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
uint8_t v___x_850_; 
lean_dec_ref(v_inst_848_);
v___x_850_ = 0;
return v___x_850_;
}
else
{
lean_object* v_head_851_; lean_object* v_tail_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_head_851_ = lean_ctor_get(v_x_849_, 0);
lean_inc(v_head_851_);
v_tail_852_ = lean_ctor_get(v_x_849_, 1);
lean_inc(v_tail_852_);
lean_dec_ref_known(v_x_849_, 2);
lean_inc_ref(v_inst_848_);
v___x_853_ = lean_apply_1(v_inst_848_, v_head_851_);
v___x_854_ = lean_unbox(v___x_853_);
if (v___x_854_ == 0)
{
uint8_t v_decide_855_; 
v_decide_855_ = l_List_decidableBEx___redArg(v_inst_848_, v_tail_852_);
if (v_decide_855_ == 0)
{
uint8_t v___x_856_; 
v___x_856_ = lean_unbox(v___x_853_);
return v___x_856_;
}
else
{
return v_decide_855_;
}
}
else
{
uint8_t v___x_857_; 
lean_dec(v_tail_852_);
lean_dec_ref(v_inst_848_);
v___x_857_ = lean_unbox(v___x_853_);
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___redArg___boxed(lean_object* v_inst_858_, lean_object* v_x_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_List_decidableBEx___redArg(v_inst_858_, v_x_859_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx(lean_object* v_00_u03b1_862_, lean_object* v_p_863_, lean_object* v_inst_864_, lean_object* v_x_865_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = l_List_decidableBEx___redArg(v_inst_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___boxed(lean_object* v_00_u03b1_867_, lean_object* v_p_868_, lean_object* v_inst_869_, lean_object* v_x_870_){
_start:
{
uint8_t v_res_871_; lean_object* v_r_872_; 
v_res_871_ = l_List_decidableBEx(v_00_u03b1_867_, v_p_868_, v_inst_869_, v_x_870_);
v_r_872_ = lean_box(v_res_871_);
return v_r_872_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll___redArg(lean_object* v_inst_873_, lean_object* v_x_874_){
_start:
{
if (lean_obj_tag(v_x_874_) == 0)
{
uint8_t v___x_875_; 
lean_dec_ref(v_inst_873_);
v___x_875_ = 1;
return v___x_875_;
}
else
{
lean_object* v_head_876_; lean_object* v_tail_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v_head_876_ = lean_ctor_get(v_x_874_, 0);
lean_inc(v_head_876_);
v_tail_877_ = lean_ctor_get(v_x_874_, 1);
lean_inc(v_tail_877_);
lean_dec_ref_known(v_x_874_, 2);
lean_inc_ref(v_inst_873_);
v___x_878_ = lean_apply_1(v_inst_873_, v_head_876_);
v___x_879_ = lean_unbox(v___x_878_);
if (v___x_879_ == 0)
{
uint8_t v___x_880_; 
lean_dec(v_tail_877_);
lean_dec_ref(v_inst_873_);
v___x_880_ = lean_unbox(v___x_878_);
return v___x_880_;
}
else
{
uint8_t v_decide_881_; 
v_decide_881_ = l_List_decidableBAll___redArg(v_inst_873_, v_tail_877_);
if (v_decide_881_ == 0)
{
return v_decide_881_;
}
else
{
uint8_t v___x_882_; 
v___x_882_ = lean_unbox(v___x_878_);
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___redArg___boxed(lean_object* v_inst_883_, lean_object* v_x_884_){
_start:
{
uint8_t v_res_885_; lean_object* v_r_886_; 
v_res_885_ = l_List_decidableBAll___redArg(v_inst_883_, v_x_884_);
v_r_886_ = lean_box(v_res_885_);
return v_r_886_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll(lean_object* v_00_u03b1_887_, lean_object* v_p_888_, lean_object* v_inst_889_, lean_object* v_x_890_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = l_List_decidableBAll___redArg(v_inst_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___boxed(lean_object* v_00_u03b1_892_, lean_object* v_p_893_, lean_object* v_inst_894_, lean_object* v_x_895_){
_start:
{
uint8_t v_res_896_; lean_object* v_r_897_; 
v_res_896_ = l_List_decidableBAll(v_00_u03b1_892_, v_p_893_, v_inst_894_, v_x_895_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT lean_object* l_List_take___redArg(lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
lean_object* v_zero_900_; uint8_t v_isZero_901_; 
v_zero_900_ = lean_unsigned_to_nat(0u);
v_isZero_901_ = lean_nat_dec_eq(v_x_898_, v_zero_900_);
if (v_isZero_901_ == 1)
{
lean_object* v___x_902_; 
lean_dec(v_x_899_);
v___x_902_ = lean_box(0);
return v___x_902_;
}
else
{
if (lean_obj_tag(v_x_899_) == 0)
{
return v_x_899_;
}
else
{
lean_object* v_head_903_; lean_object* v_tail_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_914_; 
v_head_903_ = lean_ctor_get(v_x_899_, 0);
v_tail_904_ = lean_ctor_get(v_x_899_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_899_);
if (v_isSharedCheck_914_ == 0)
{
v___x_906_ = v_x_899_;
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_tail_904_);
lean_inc(v_head_903_);
lean_dec(v_x_899_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_one_908_; lean_object* v_n_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v_one_908_ = lean_unsigned_to_nat(1u);
v_n_909_ = lean_nat_sub(v_x_898_, v_one_908_);
v___x_910_ = l_List_take___redArg(v_n_909_, v_tail_904_);
lean_dec(v_n_909_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v___x_910_);
v___x_912_ = v___x_906_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_head_903_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_take___redArg___boxed(lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_List_take___redArg(v_x_915_, v_x_916_);
lean_dec(v_x_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_List_take(lean_object* v_00_u03b1_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_List_take___redArg(v_x_919_, v_x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_List_take___boxed(lean_object* v_00_u03b1_922_, lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_List_take(v_00_u03b1_922_, v_x_923_, v_x_924_);
lean_dec(v_x_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg(lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v_zero_928_; uint8_t v_isZero_929_; 
v_zero_928_ = lean_unsigned_to_nat(0u);
v_isZero_929_ = lean_nat_dec_eq(v_x_926_, v_zero_928_);
if (v_isZero_929_ == 1)
{
lean_dec(v_x_926_);
lean_inc(v_x_927_);
return v_x_927_;
}
else
{
if (lean_obj_tag(v_x_927_) == 0)
{
lean_dec(v_x_926_);
return v_x_927_;
}
else
{
lean_object* v_tail_930_; lean_object* v_one_931_; lean_object* v_n_932_; 
v_tail_930_ = lean_ctor_get(v_x_927_, 1);
v_one_931_ = lean_unsigned_to_nat(1u);
v_n_932_ = lean_nat_sub(v_x_926_, v_one_931_);
lean_dec(v_x_926_);
v_x_926_ = v_n_932_;
v_x_927_ = v_tail_930_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg___boxed(lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_List_drop___redArg(v_x_934_, v_x_935_);
lean_dec(v_x_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_List_drop(lean_object* v_00_u03b1_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_List_drop___redArg(v_x_938_, v_x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_List_drop___boxed(lean_object* v_00_u03b1_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_List_drop(v_00_u03b1_941_, v_x_942_, v_x_943_);
lean_dec(v_x_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg(lean_object* v_l_945_, lean_object* v_start_946_, lean_object* v_stop_947_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_nat_sub(v_stop_947_, v_start_946_);
v___x_949_ = l_List_drop___redArg(v_start_946_, v_l_945_);
v___x_950_ = l_List_take___redArg(v___x_948_, v___x_949_);
lean_dec(v___x_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg___boxed(lean_object* v_l_951_, lean_object* v_start_952_, lean_object* v_stop_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_List_extract___redArg(v_l_951_, v_start_952_, v_stop_953_);
lean_dec(v_stop_953_);
lean_dec(v_l_951_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_List_extract(lean_object* v_00_u03b1_955_, lean_object* v_l_956_, lean_object* v_start_957_, lean_object* v_stop_958_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_nat_sub(v_stop_958_, v_start_957_);
v___x_960_ = l_List_drop___redArg(v_start_957_, v_l_956_);
v___x_961_ = l_List_take___redArg(v___x_959_, v___x_960_);
lean_dec(v___x_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_List_extract___boxed(lean_object* v_00_u03b1_962_, lean_object* v_l_963_, lean_object* v_start_964_, lean_object* v_stop_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_List_extract(v_00_u03b1_962_, v_l_963_, v_start_964_, v_stop_965_);
lean_dec(v_stop_965_);
lean_dec(v_l_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhile___redArg(lean_object* v_p_967_, lean_object* v_x_968_){
_start:
{
if (lean_obj_tag(v_x_968_) == 0)
{
lean_dec_ref(v_p_967_);
return v_x_968_;
}
else
{
lean_object* v_head_969_; lean_object* v_tail_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_981_; 
v_head_969_ = lean_ctor_get(v_x_968_, 0);
v_tail_970_ = lean_ctor_get(v_x_968_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_981_ == 0)
{
v___x_972_ = v_x_968_;
v_isShared_973_ = v_isSharedCheck_981_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_tail_970_);
lean_inc(v_head_969_);
lean_dec(v_x_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_981_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; uint8_t v___x_975_; 
lean_inc_ref(v_p_967_);
lean_inc(v_head_969_);
v___x_974_ = lean_apply_1(v_p_967_, v_head_969_);
v___x_975_ = lean_unbox(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
lean_del_object(v___x_972_);
lean_dec(v_tail_970_);
lean_dec(v_head_969_);
lean_dec_ref(v_p_967_);
v___x_976_ = lean_box(0);
return v___x_976_;
}
else
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = l_List_takeWhile___redArg(v_p_967_, v_tail_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v___x_977_);
v___x_979_ = v___x_972_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_head_969_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_takeWhile(lean_object* v_00_u03b1_982_, lean_object* v_p_983_, lean_object* v_x_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_List_takeWhile___redArg(v_p_983_, v_x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___redArg(lean_object* v_p_986_, lean_object* v_x_987_){
_start:
{
if (lean_obj_tag(v_x_987_) == 0)
{
lean_dec_ref(v_p_986_);
return v_x_987_;
}
else
{
lean_object* v_head_988_; lean_object* v_tail_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_head_988_ = lean_ctor_get(v_x_987_, 0);
v_tail_989_ = lean_ctor_get(v_x_987_, 1);
lean_inc_ref(v_p_986_);
lean_inc(v_head_988_);
v___x_990_ = lean_apply_1(v_p_986_, v_head_988_);
v___x_991_ = lean_unbox(v___x_990_);
if (v___x_991_ == 0)
{
lean_dec_ref(v_p_986_);
return v_x_987_;
}
else
{
lean_inc(v_tail_989_);
lean_dec_ref_known(v_x_987_, 2);
v_x_987_ = v_tail_989_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object* v_00_u03b1_993_, lean_object* v_p_994_, lean_object* v_x_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_List_dropWhile___redArg(v_p_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___redArg(lean_object* v_p_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
if (lean_obj_tag(v_a_998_) == 0)
{
lean_object* v_fst_1000_; lean_object* v_snd_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_p_997_);
v_fst_1000_ = lean_ctor_get(v_a_999_, 0);
v_snd_1001_ = lean_ctor_get(v_a_999_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_a_999_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1003_ = v_a_999_;
v_isShared_1004_ = v_isSharedCheck_1010_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_snd_1001_);
lean_inc(v_fst_1000_);
lean_dec(v_a_999_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1010_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1005_ = l_List_reverse___redArg(v_fst_1000_);
v___x_1006_ = l_List_reverse___redArg(v_snd_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___x_1006_);
lean_ctor_set(v___x_1003_, 0, v___x_1005_);
v___x_1008_ = v___x_1003_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v_head_1011_; lean_object* v_tail_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1038_; 
v_head_1011_ = lean_ctor_get(v_a_998_, 0);
v_tail_1012_ = lean_ctor_get(v_a_998_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_a_998_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1014_ = v_a_998_;
v_isShared_1015_ = v_isSharedCheck_1038_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_tail_1012_);
lean_inc(v_head_1011_);
lean_dec(v_a_998_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1038_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_fst_1016_; lean_object* v_snd_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1037_; 
v_fst_1016_ = lean_ctor_get(v_a_999_, 0);
v_snd_1017_ = lean_ctor_get(v_a_999_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_a_999_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1019_ = v_a_999_;
v_isShared_1020_ = v_isSharedCheck_1037_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_snd_1017_);
lean_inc(v_fst_1016_);
lean_dec(v_a_999_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1037_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
lean_inc_ref(v_p_997_);
lean_inc(v_head_1011_);
v___x_1021_ = lean_apply_1(v_p_997_, v_head_1011_);
v___x_1022_ = lean_unbox(v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1024_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v_snd_1017_);
v___x_1024_ = v___x_1014_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_head_1011_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_snd_1017_);
v___x_1024_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v___x_1024_);
v___x_1026_ = v___x_1019_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_fst_1016_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
v_a_998_ = v_tail_1012_;
v_a_999_ = v___x_1026_;
goto _start;
}
}
}
else
{
lean_object* v___x_1031_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v_fst_1016_);
v___x_1031_ = v___x_1014_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_head_1011_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_fst_1016_);
v___x_1031_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1033_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1031_);
v___x_1033_ = v___x_1019_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_snd_1017_);
v___x_1033_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
v_a_998_ = v_tail_1012_;
v_a_999_ = v___x_1033_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object* v_00_u03b1_1039_, lean_object* v_p_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_List_partition_loop___redArg(v_p_1040_, v_a_1041_, v_a_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_List_partition___redArg(lean_object* v_p_1046_, lean_object* v_as_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1049_ = l_List_partition_loop___redArg(v_p_1046_, v_as_1047_, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_List_partition(lean_object* v_00_u03b1_1050_, lean_object* v_p_1051_, lean_object* v_as_1052_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1054_ = l_List_partition_loop___redArg(v_p_1051_, v_as_1052_, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_List_dropLast___redArg(lean_object* v_x_1055_){
_start:
{
if (lean_obj_tag(v_x_1055_) == 0)
{
return v_x_1055_;
}
else
{
lean_object* v_tail_1056_; 
v_tail_1056_ = lean_ctor_get(v_x_1055_, 1);
lean_inc(v_tail_1056_);
if (lean_obj_tag(v_tail_1056_) == 0)
{
lean_dec_ref_known(v_x_1055_, 2);
return v_tail_1056_;
}
else
{
lean_object* v_head_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1065_; 
v_head_1057_ = lean_ctor_get(v_x_1055_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_x_1055_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v_x_1055_, 1);
lean_dec(v_unused_1066_);
v___x_1059_ = v_x_1055_;
v_isShared_1060_ = v_isSharedCheck_1065_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_head_1057_);
lean_dec(v_x_1055_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1065_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = l_List_dropLast___redArg(v_tail_1056_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_head_1057_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropLast(lean_object* v_00_u03b1_1067_, lean_object* v_x_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_List_dropLast___redArg(v_x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_1070_, lean_object* v_h__1_1071_, lean_object* v_h__2_1072_, lean_object* v_h__3_1073_){
_start:
{
if (lean_obj_tag(v_x_1070_) == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec(v_h__3_1073_);
lean_dec(v_h__2_1072_);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_apply_1(v_h__1_1071_, v___x_1074_);
return v___x_1075_;
}
else
{
lean_object* v_tail_1076_; 
lean_dec(v_h__1_1071_);
v_tail_1076_ = lean_ctor_get(v_x_1070_, 1);
if (lean_obj_tag(v_tail_1076_) == 0)
{
lean_object* v_head_1077_; lean_object* v___x_1078_; 
lean_dec(v_h__3_1073_);
v_head_1077_ = lean_ctor_get(v_x_1070_, 0);
lean_inc(v_head_1077_);
lean_dec_ref_known(v_x_1070_, 2);
v___x_1078_ = lean_apply_1(v_h__2_1072_, v_head_1077_);
return v___x_1078_;
}
else
{
lean_object* v_head_1079_; lean_object* v___x_1080_; 
lean_inc_ref(v_tail_1076_);
lean_dec(v_h__2_1072_);
v_head_1079_ = lean_ctor_get(v_x_1070_, 0);
lean_inc(v_head_1079_);
lean_dec_ref_known(v_x_1070_, 2);
v___x_1080_ = lean_apply_3(v_h__3_1073_, v_head_1079_, v_tail_1076_, lean_box(0));
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_1081_, lean_object* v_motive_1082_, lean_object* v_x_1083_, lean_object* v_h__1_1084_, lean_object* v_h__2_1085_, lean_object* v_h__3_1086_){
_start:
{
if (lean_obj_tag(v_x_1083_) == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec(v_h__3_1086_);
lean_dec(v_h__2_1085_);
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_apply_1(v_h__1_1084_, v___x_1087_);
return v___x_1088_;
}
else
{
lean_object* v_tail_1089_; 
lean_dec(v_h__1_1084_);
v_tail_1089_ = lean_ctor_get(v_x_1083_, 1);
if (lean_obj_tag(v_tail_1089_) == 0)
{
lean_object* v_head_1090_; lean_object* v___x_1091_; 
lean_dec(v_h__3_1086_);
v_head_1090_ = lean_ctor_get(v_x_1083_, 0);
lean_inc(v_head_1090_);
lean_dec_ref_known(v_x_1083_, 2);
v___x_1091_ = lean_apply_1(v_h__2_1085_, v_head_1090_);
return v___x_1091_;
}
else
{
lean_object* v_head_1092_; lean_object* v___x_1093_; 
lean_inc_ref(v_tail_1089_);
lean_dec(v_h__2_1085_);
v_head_1092_ = lean_ctor_get(v_x_1083_, 0);
lean_inc(v_head_1092_);
lean_dec_ref_known(v_x_1083_, 2);
v___x_1093_ = lean_apply_3(v_h__3_1086_, v_head_1092_, v_tail_1089_, lean_box(0));
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object* v_00_u03b1_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_box(0);
return v___x_1095_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(lean_object* v___f_1096_, lean_object* v_x_1097_, lean_object* v_a_1098_){
_start:
{
uint8_t v___x_1099_; 
v___x_1099_ = l_List_elem___redArg(v___f_1096_, v_a_1098_, v_x_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(lean_object* v___f_1100_, lean_object* v_x_1101_, lean_object* v_a_1102_){
_start:
{
uint8_t v_res_1103_; lean_object* v_r_1104_; 
v_res_1103_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(v___f_1100_, v_x_1101_, v_a_1102_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg(lean_object* v_inst_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v___f_1108_; lean_object* v___f_1109_; uint8_t v___x_1110_; 
v___f_1108_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1108_, 0, v_inst_1105_);
v___f_1109_ = lean_alloc_closure((void*)(l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1109_, 0, v___f_1108_);
lean_closure_set(v___f_1109_, 1, v_x_1107_);
v___x_1110_ = l_List_decidableBAll___redArg(v___f_1109_, v_x_1106_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(lean_object* v_inst_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1111_, v_x_1112_, v_x_1113_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq(lean_object* v_00_u03b1_1116_, lean_object* v_inst_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
uint8_t v___x_1120_; 
v___x_1120_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1117_, v_x_1118_, v_x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___boxed(lean_object* v_00_u03b1_1121_, lean_object* v_inst_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_res_1125_ = l_List_instDecidableRelSubsetOfDecidableEq(v_00_u03b1_1121_, v_inst_1122_, v_x_1123_, v_x_1124_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2));
v___x_1161_ = l_String_toRawSubstring_x27(v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object* v_x_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
lean_inc(v_x_1181_);
v___x_1185_ = l_Lean_Syntax_isOfKind(v_x_1181_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec(v_x_1181_);
v___x_1186_ = lean_box(1);
v___x_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v_a_1183_);
return v___x_1187_;
}
else
{
lean_object* v_quotContext_1188_; lean_object* v_currMacroScope_1189_; lean_object* v_ref_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_quotContext_1188_ = lean_ctor_get(v_a_1182_, 1);
v_currMacroScope_1189_ = lean_ctor_get(v_a_1182_, 2);
v_ref_1190_ = lean_ctor_get(v_a_1182_, 5);
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = l_Lean_Syntax_getArg(v_x_1181_, v___x_1191_);
v___x_1193_ = lean_unsigned_to_nat(2u);
v___x_1194_ = l_Lean_Syntax_getArg(v_x_1181_, v___x_1193_);
lean_dec(v_x_1181_);
v___x_1195_ = 0;
v___x_1196_ = l_Lean_SourceInfo_fromRef(v_ref_1190_, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1198_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
v___x_1199_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4));
lean_inc(v_currMacroScope_1189_);
lean_inc(v_quotContext_1188_);
v___x_1200_ = l_Lean_addMacroScope(v_quotContext_1188_, v___x_1199_, v_currMacroScope_1189_);
v___x_1201_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10));
lean_inc_n(v___x_1196_, 2);
v___x_1202_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1196_);
lean_ctor_set(v___x_1202_, 1, v___x_1198_);
lean_ctor_set(v___x_1202_, 2, v___x_1200_);
lean_ctor_set(v___x_1202_, 3, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1204_ = l_Lean_Syntax_node2(v___x_1196_, v___x_1203_, v___x_1192_, v___x_1194_);
v___x_1205_ = l_Lean_Syntax_node2(v___x_1196_, v___x_1197_, v___x_1202_, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v_a_1183_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___boxed(lean_object* v_x_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(v_x_1207_, v_a_1208_, v_a_1209_);
lean_dec_ref(v_a_1208_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object* v_x_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1214_);
v___x_1218_ = l_Lean_Syntax_isOfKind(v_x_1214_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec(v_x_1214_);
v___x_1219_ = lean_box(0);
v___x_1220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v_a_1216_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = l_Lean_Syntax_getArg(v_x_1214_, v___x_1221_);
v___x_1223_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1222_);
v___x_1224_ = l_Lean_Syntax_isOfKind(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec(v___x_1222_);
lean_dec(v_x_1214_);
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_a_1216_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1227_ = lean_unsigned_to_nat(1u);
v___x_1228_ = l_Lean_Syntax_getArg(v_x_1214_, v___x_1227_);
lean_dec(v_x_1214_);
v___x_1229_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1228_);
v___x_1230_ = l_Lean_Syntax_matchesNull(v___x_1228_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec(v___x_1228_);
lean_dec(v___x_1222_);
v___x_1231_ = lean_box(0);
v___x_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v_a_1216_);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_ref_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1233_ = l_Lean_Syntax_getArg(v___x_1228_, v___x_1221_);
v___x_1234_ = l_Lean_Syntax_getArg(v___x_1228_, v___x_1227_);
lean_dec(v___x_1228_);
v_ref_1235_ = l_Lean_replaceRef(v___x_1222_, v_a_1215_);
lean_dec(v___x_1222_);
v___x_1236_ = 0;
v___x_1237_ = l_Lean_SourceInfo_fromRef(v_ref_1235_, v___x_1236_);
lean_dec(v_ref_1235_);
v___x_1238_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
v___x_1239_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__5));
lean_inc(v___x_1237_);
v___x_1240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1237_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = l_Lean_Syntax_node3(v___x_1237_, v___x_1238_, v___x_1233_, v___x_1240_, v___x_1234_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_a_1216_);
return v___x_1242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object* v_x_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(v_x_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist___redArg(lean_object* v_inst_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
if (lean_obj_tag(v_x_1248_) == 0)
{
uint8_t v___x_1250_; 
lean_dec(v_x_1249_);
lean_dec_ref(v_inst_1247_);
v___x_1250_ = 1;
return v___x_1250_;
}
else
{
if (lean_obj_tag(v_x_1249_) == 0)
{
uint8_t v___x_1251_; 
lean_dec_ref_known(v_x_1248_, 2);
lean_dec_ref(v_inst_1247_);
v___x_1251_ = 0;
return v___x_1251_;
}
else
{
lean_object* v_head_1252_; lean_object* v_tail_1253_; lean_object* v_head_1254_; lean_object* v_tail_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_head_1252_ = lean_ctor_get(v_x_1248_, 0);
v_tail_1253_ = lean_ctor_get(v_x_1248_, 1);
v_head_1254_ = lean_ctor_get(v_x_1249_, 0);
lean_inc(v_head_1254_);
v_tail_1255_ = lean_ctor_get(v_x_1249_, 1);
lean_inc(v_tail_1255_);
lean_dec_ref_known(v_x_1249_, 2);
lean_inc_ref(v_inst_1247_);
lean_inc(v_head_1252_);
v___x_1256_ = lean_apply_2(v_inst_1247_, v_head_1252_, v_head_1254_);
v___x_1257_ = lean_unbox(v___x_1256_);
if (v___x_1257_ == 0)
{
v_x_1249_ = v_tail_1255_;
goto _start;
}
else
{
lean_inc(v_tail_1253_);
lean_dec_ref_known(v_x_1248_, 2);
v_x_1248_ = v_tail_1253_;
v_x_1249_ = v_tail_1255_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSublist___redArg___boxed(lean_object* v_inst_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
uint8_t v_res_1263_; lean_object* v_r_1264_; 
v_res_1263_ = l_List_isSublist___redArg(v_inst_1260_, v_x_1261_, v_x_1262_);
v_r_1264_ = lean_box(v_res_1263_);
return v_r_1264_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist(lean_object* v_00_u03b1_1265_, lean_object* v_inst_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
uint8_t v___x_1269_; 
v___x_1269_ = l_List_isSublist___redArg(v_inst_1266_, v_x_1267_, v_x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_List_isSublist___boxed(lean_object* v_00_u03b1_1270_, lean_object* v_inst_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l_List_isSublist(v_00_u03b1_1270_, v_inst_1271_, v_x_1272_, v_x_1273_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0));
v___x_1294_ = l_String_toRawSubstring_x27(v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object* v_x_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
lean_inc(v_x_1306_);
v___x_1310_ = l_Lean_Syntax_isOfKind(v_x_1306_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec(v_x_1306_);
v___x_1311_ = lean_box(1);
v___x_1312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v_a_1308_);
return v___x_1312_;
}
else
{
lean_object* v_quotContext_1313_; lean_object* v_currMacroScope_1314_; lean_object* v_ref_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_quotContext_1313_ = lean_ctor_get(v_a_1307_, 1);
v_currMacroScope_1314_ = lean_ctor_get(v_a_1307_, 2);
v_ref_1315_ = lean_ctor_get(v_a_1307_, 5);
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = l_Lean_Syntax_getArg(v_x_1306_, v___x_1316_);
v___x_1318_ = lean_unsigned_to_nat(2u);
v___x_1319_ = l_Lean_Syntax_getArg(v_x_1306_, v___x_1318_);
lean_dec(v_x_1306_);
v___x_1320_ = 0;
v___x_1321_ = l_Lean_SourceInfo_fromRef(v_ref_1315_, v___x_1320_);
v___x_1322_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1323_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
v___x_1324_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1314_);
lean_inc(v_quotContext_1313_);
v___x_1325_ = l_Lean_addMacroScope(v_quotContext_1313_, v___x_1324_, v_currMacroScope_1314_);
v___x_1326_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1321_, 2);
v___x_1327_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1321_);
lean_ctor_set(v___x_1327_, 1, v___x_1323_);
lean_ctor_set(v___x_1327_, 2, v___x_1325_);
lean_ctor_set(v___x_1327_, 3, v___x_1326_);
v___x_1328_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1329_ = l_Lean_Syntax_node2(v___x_1321_, v___x_1328_, v___x_1317_, v___x_1319_);
v___x_1330_ = l_Lean_Syntax_node2(v___x_1321_, v___x_1322_, v___x_1327_, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v_a_1308_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___boxed(lean_object* v_x_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(v_x_1332_, v_a_1333_, v_a_1334_);
lean_dec_ref(v_a_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object* v_x_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1336_);
v___x_1340_ = l_Lean_Syntax_isOfKind(v_x_1336_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec(v_x_1336_);
v___x_1341_ = lean_box(0);
v___x_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v_a_1338_);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = l_Lean_Syntax_getArg(v_x_1336_, v___x_1343_);
v___x_1345_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1344_);
v___x_1346_ = l_Lean_Syntax_isOfKind(v___x_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec(v___x_1344_);
lean_dec(v_x_1336_);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v_a_1338_);
return v___x_1348_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1349_ = lean_unsigned_to_nat(1u);
v___x_1350_ = l_Lean_Syntax_getArg(v_x_1336_, v___x_1349_);
lean_dec(v_x_1336_);
v___x_1351_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1350_);
v___x_1352_ = l_Lean_Syntax_matchesNull(v___x_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec(v___x_1350_);
lean_dec(v___x_1344_);
v___x_1353_ = lean_box(0);
v___x_1354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v_a_1338_);
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_ref_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1355_ = l_Lean_Syntax_getArg(v___x_1350_, v___x_1343_);
v___x_1356_ = l_Lean_Syntax_getArg(v___x_1350_, v___x_1349_);
lean_dec(v___x_1350_);
v_ref_1357_ = l_Lean_replaceRef(v___x_1344_, v_a_1337_);
lean_dec(v___x_1344_);
v___x_1358_ = 0;
v___x_1359_ = l_Lean_SourceInfo_fromRef(v_ref_1357_, v___x_1358_);
lean_dec(v_ref_1357_);
v___x_1360_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
v___x_1361_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__2));
lean_inc(v___x_1359_);
v___x_1362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1359_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = l_Lean_Syntax_node3(v___x_1359_, v___x_1360_, v___x_1355_, v___x_1362_, v___x_1356_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v_a_1338_);
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object* v_x_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(v_x_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1366_);
return v_res_1368_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf___redArg(lean_object* v_inst_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
if (lean_obj_tag(v_x_1370_) == 0)
{
uint8_t v___x_1372_; 
lean_dec(v_x_1371_);
lean_dec_ref(v_inst_1369_);
v___x_1372_ = 1;
return v___x_1372_;
}
else
{
if (lean_obj_tag(v_x_1371_) == 0)
{
uint8_t v___x_1373_; 
lean_dec_ref_known(v_x_1370_, 2);
lean_dec_ref(v_inst_1369_);
v___x_1373_ = 0;
return v___x_1373_;
}
else
{
lean_object* v_head_1374_; lean_object* v_tail_1375_; lean_object* v_head_1376_; lean_object* v_tail_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_head_1374_ = lean_ctor_get(v_x_1370_, 0);
lean_inc(v_head_1374_);
v_tail_1375_ = lean_ctor_get(v_x_1370_, 1);
lean_inc(v_tail_1375_);
lean_dec_ref_known(v_x_1370_, 2);
v_head_1376_ = lean_ctor_get(v_x_1371_, 0);
lean_inc(v_head_1376_);
v_tail_1377_ = lean_ctor_get(v_x_1371_, 1);
lean_inc(v_tail_1377_);
lean_dec_ref_known(v_x_1371_, 2);
lean_inc_ref(v_inst_1369_);
v___x_1378_ = lean_apply_2(v_inst_1369_, v_head_1374_, v_head_1376_);
v___x_1379_ = lean_unbox(v___x_1378_);
if (v___x_1379_ == 0)
{
uint8_t v___x_1380_; 
lean_dec(v_tail_1377_);
lean_dec(v_tail_1375_);
lean_dec_ref(v_inst_1369_);
v___x_1380_ = lean_unbox(v___x_1378_);
return v___x_1380_;
}
else
{
v_x_1370_ = v_tail_1375_;
v_x_1371_ = v_tail_1377_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___redArg___boxed(lean_object* v_inst_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_){
_start:
{
uint8_t v_res_1385_; lean_object* v_r_1386_; 
v_res_1385_ = l_List_isPrefixOf___redArg(v_inst_1382_, v_x_1383_, v_x_1384_);
v_r_1386_ = lean_box(v_res_1385_);
return v_r_1386_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf(lean_object* v_00_u03b1_1387_, lean_object* v_inst_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
uint8_t v___x_1391_; 
v___x_1391_ = l_List_isPrefixOf___redArg(v_inst_1388_, v_x_1389_, v_x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___boxed(lean_object* v_00_u03b1_1392_, lean_object* v_inst_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
uint8_t v_res_1396_; lean_object* v_r_1397_; 
v_res_1396_ = l_List_isPrefixOf(v_00_u03b1_1392_, v_inst_1393_, v_x_1394_, v_x_1395_);
v_r_1397_ = lean_box(v_res_1396_);
return v_r_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v_h__1_1400_, lean_object* v_h__2_1401_, lean_object* v_h__3_1402_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v___x_1403_; 
lean_dec(v_h__3_1402_);
lean_dec(v_h__2_1401_);
v___x_1403_ = lean_apply_1(v_h__1_1400_, v_x_1399_);
return v___x_1403_;
}
else
{
lean_dec(v_h__1_1400_);
if (lean_obj_tag(v_x_1399_) == 0)
{
lean_object* v___x_1404_; 
lean_dec(v_h__3_1402_);
v___x_1404_ = lean_apply_2(v_h__2_1401_, v_x_1398_, lean_box(0));
return v___x_1404_;
}
else
{
lean_object* v_head_1405_; lean_object* v_tail_1406_; lean_object* v_head_1407_; lean_object* v_tail_1408_; lean_object* v___x_1409_; 
lean_dec(v_h__2_1401_);
v_head_1405_ = lean_ctor_get(v_x_1398_, 0);
lean_inc(v_head_1405_);
v_tail_1406_ = lean_ctor_get(v_x_1398_, 1);
lean_inc(v_tail_1406_);
lean_dec_ref_known(v_x_1398_, 2);
v_head_1407_ = lean_ctor_get(v_x_1399_, 0);
lean_inc(v_head_1407_);
v_tail_1408_ = lean_ctor_get(v_x_1399_, 1);
lean_inc(v_tail_1408_);
lean_dec_ref_known(v_x_1399_, 2);
v___x_1409_ = lean_apply_4(v_h__3_1402_, v_head_1405_, v_tail_1406_, v_head_1407_, v_tail_1408_);
return v___x_1409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object* v_00_u03b1_1410_, lean_object* v_motive_1411_, lean_object* v_x_1412_, lean_object* v_x_1413_, lean_object* v_h__1_1414_, lean_object* v_h__2_1415_, lean_object* v_h__3_1416_){
_start:
{
if (lean_obj_tag(v_x_1412_) == 0)
{
lean_object* v___x_1417_; 
lean_dec(v_h__3_1416_);
lean_dec(v_h__2_1415_);
v___x_1417_ = lean_apply_1(v_h__1_1414_, v_x_1413_);
return v___x_1417_;
}
else
{
lean_dec(v_h__1_1414_);
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v___x_1418_; 
lean_dec(v_h__3_1416_);
v___x_1418_ = lean_apply_2(v_h__2_1415_, v_x_1412_, lean_box(0));
return v___x_1418_;
}
else
{
lean_object* v_head_1419_; lean_object* v_tail_1420_; lean_object* v_head_1421_; lean_object* v_tail_1422_; lean_object* v___x_1423_; 
lean_dec(v_h__2_1415_);
v_head_1419_ = lean_ctor_get(v_x_1412_, 0);
lean_inc(v_head_1419_);
v_tail_1420_ = lean_ctor_get(v_x_1412_, 1);
lean_inc(v_tail_1420_);
lean_dec_ref_known(v_x_1412_, 2);
v_head_1421_ = lean_ctor_get(v_x_1413_, 0);
lean_inc(v_head_1421_);
v_tail_1422_ = lean_ctor_get(v_x_1413_, 1);
lean_inc(v_tail_1422_);
lean_dec_ref_known(v_x_1413_, 2);
v___x_1423_ = lean_apply_4(v_h__3_1416_, v_head_1419_, v_tail_1420_, v_head_1421_, v_tail_1422_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___redArg(lean_object* v_inst_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
if (lean_obj_tag(v_x_1425_) == 0)
{
lean_object* v___x_1427_; 
lean_dec_ref(v_inst_1424_);
v___x_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_x_1426_);
return v___x_1427_;
}
else
{
if (lean_obj_tag(v_x_1426_) == 0)
{
lean_object* v___x_1428_; 
lean_dec_ref_known(v_x_1425_, 2);
lean_dec_ref(v_inst_1424_);
v___x_1428_ = lean_box(0);
return v___x_1428_;
}
else
{
lean_object* v_head_1429_; lean_object* v_tail_1430_; lean_object* v_head_1431_; lean_object* v_tail_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_head_1429_ = lean_ctor_get(v_x_1425_, 0);
lean_inc(v_head_1429_);
v_tail_1430_ = lean_ctor_get(v_x_1425_, 1);
lean_inc(v_tail_1430_);
lean_dec_ref_known(v_x_1425_, 2);
v_head_1431_ = lean_ctor_get(v_x_1426_, 0);
lean_inc(v_head_1431_);
v_tail_1432_ = lean_ctor_get(v_x_1426_, 1);
lean_inc(v_tail_1432_);
lean_dec_ref_known(v_x_1426_, 2);
lean_inc_ref(v_inst_1424_);
v___x_1433_ = lean_apply_2(v_inst_1424_, v_head_1429_, v_head_1431_);
v___x_1434_ = lean_unbox(v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
lean_dec(v_tail_1432_);
lean_dec(v_tail_1430_);
lean_dec_ref(v_inst_1424_);
v___x_1435_ = lean_box(0);
return v___x_1435_;
}
else
{
v_x_1425_ = v_tail_1430_;
v_x_1426_ = v_tail_1432_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object* v_00_u03b1_1437_, lean_object* v_inst_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_List_isPrefixOf_x3f___redArg(v_inst_1438_, v_x_1439_, v_x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf___redArg(lean_object* v_inst_1442_, lean_object* v_l_u2081_1443_, lean_object* v_l_u2082_1444_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = l_List_reverse___redArg(v_l_u2081_1443_);
v___x_1446_ = l_List_reverse___redArg(v_l_u2082_1444_);
v___x_1447_ = l_List_isPrefixOf___redArg(v_inst_1442_, v___x_1445_, v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___redArg___boxed(lean_object* v_inst_1448_, lean_object* v_l_u2081_1449_, lean_object* v_l_u2082_1450_){
_start:
{
uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_res_1451_ = l_List_isSuffixOf___redArg(v_inst_1448_, v_l_u2081_1449_, v_l_u2082_1450_);
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf(lean_object* v_00_u03b1_1453_, lean_object* v_inst_1454_, lean_object* v_l_u2081_1455_, lean_object* v_l_u2082_1456_){
_start:
{
uint8_t v___x_1457_; 
v___x_1457_ = l_List_isSuffixOf___redArg(v_inst_1454_, v_l_u2081_1455_, v_l_u2082_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___boxed(lean_object* v_00_u03b1_1458_, lean_object* v_inst_1459_, lean_object* v_l_u2081_1460_, lean_object* v_l_u2082_1461_){
_start:
{
uint8_t v_res_1462_; lean_object* v_r_1463_; 
v_res_1462_ = l_List_isSuffixOf(v_00_u03b1_1458_, v_inst_1459_, v_l_u2081_1460_, v_l_u2082_1461_);
v_r_1463_ = lean_box(v_res_1462_);
return v_r_1463_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___redArg(lean_object* v_inst_1464_, lean_object* v_l_u2081_1465_, lean_object* v_l_u2082_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = l_List_reverse___redArg(v_l_u2081_1465_);
v___x_1468_ = l_List_reverse___redArg(v_l_u2082_1466_);
v___x_1469_ = l_List_isPrefixOf_x3f___redArg(v_inst_1464_, v___x_1467_, v___x_1468_);
if (lean_obj_tag(v___x_1469_) == 0)
{
return v___x_1469_;
}
else
{
lean_object* v_val_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1478_; 
v_val_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_val_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = l_List_reverse___redArg(v_val_1470_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1474_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object* v_00_u03b1_1479_, lean_object* v_inst_1480_, lean_object* v_l_u2081_1481_, lean_object* v_l_u2082_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_List_isSuffixOf_x3f___redArg(v_inst_1480_, v_l_u2081_1481_, v_l_u2082_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0));
v___x_1502_ = l_String_toRawSubstring_x27(v___x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object* v_x_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
lean_inc(v_x_1514_);
v___x_1518_ = l_Lean_Syntax_isOfKind(v_x_1514_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec(v_x_1514_);
v___x_1519_ = lean_box(1);
v___x_1520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v_a_1516_);
return v___x_1520_;
}
else
{
lean_object* v_quotContext_1521_; lean_object* v_currMacroScope_1522_; lean_object* v_ref_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_quotContext_1521_ = lean_ctor_get(v_a_1515_, 1);
v_currMacroScope_1522_ = lean_ctor_get(v_a_1515_, 2);
v_ref_1523_ = lean_ctor_get(v_a_1515_, 5);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = l_Lean_Syntax_getArg(v_x_1514_, v___x_1524_);
v___x_1526_ = lean_unsigned_to_nat(2u);
v___x_1527_ = l_Lean_Syntax_getArg(v_x_1514_, v___x_1526_);
lean_dec(v_x_1514_);
v___x_1528_ = 0;
v___x_1529_ = l_Lean_SourceInfo_fromRef(v_ref_1523_, v___x_1528_);
v___x_1530_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1531_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
v___x_1532_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2));
lean_inc(v_currMacroScope_1522_);
lean_inc(v_quotContext_1521_);
v___x_1533_ = l_Lean_addMacroScope(v_quotContext_1521_, v___x_1532_, v_currMacroScope_1522_);
v___x_1534_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5));
lean_inc_n(v___x_1529_, 2);
v___x_1535_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1529_);
lean_ctor_set(v___x_1535_, 1, v___x_1531_);
lean_ctor_set(v___x_1535_, 2, v___x_1533_);
lean_ctor_set(v___x_1535_, 3, v___x_1534_);
v___x_1536_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1537_ = l_Lean_Syntax_node2(v___x_1529_, v___x_1536_, v___x_1525_, v___x_1527_);
v___x_1538_ = l_Lean_Syntax_node2(v___x_1529_, v___x_1530_, v___x_1535_, v___x_1537_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v_a_1516_);
return v___x_1539_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___boxed(lean_object* v_x_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(v_x_1540_, v_a_1541_, v_a_1542_);
lean_dec_ref(v_a_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object* v_x_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1547_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1544_);
v___x_1548_ = l_Lean_Syntax_isOfKind(v_x_1544_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec(v_x_1544_);
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v_a_1546_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = l_Lean_Syntax_getArg(v_x_1544_, v___x_1551_);
v___x_1553_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1552_);
v___x_1554_ = l_Lean_Syntax_isOfKind(v___x_1552_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec(v___x_1552_);
lean_dec(v_x_1544_);
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v_a_1546_);
return v___x_1556_;
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = l_Lean_Syntax_getArg(v_x_1544_, v___x_1557_);
lean_dec(v_x_1544_);
v___x_1559_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1558_);
v___x_1560_ = l_Lean_Syntax_matchesNull(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec(v___x_1558_);
lean_dec(v___x_1552_);
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v_a_1546_);
return v___x_1562_;
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_ref_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1563_ = l_Lean_Syntax_getArg(v___x_1558_, v___x_1551_);
v___x_1564_ = l_Lean_Syntax_getArg(v___x_1558_, v___x_1557_);
lean_dec(v___x_1558_);
v_ref_1565_ = l_Lean_replaceRef(v___x_1552_, v_a_1545_);
lean_dec(v___x_1552_);
v___x_1566_ = 0;
v___x_1567_ = l_Lean_SourceInfo_fromRef(v_ref_1565_, v___x_1566_);
lean_dec(v_ref_1565_);
v___x_1568_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
v___x_1569_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__2));
lean_inc(v___x_1567_);
v___x_1570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1567_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = l_Lean_Syntax_node3(v___x_1567_, v___x_1568_, v___x_1563_, v___x_1570_, v___x_1564_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_a_1546_);
return v___x_1572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object* v_x_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(v_x_1573_, v_a_1574_, v_a_1575_);
lean_dec(v_a_1574_);
return v_res_1576_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0));
v___x_1595_ = l_String_toRawSubstring_x27(v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object* v_x_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
lean_inc(v_x_1607_);
v___x_1611_ = l_Lean_Syntax_isOfKind(v_x_1607_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec(v_x_1607_);
v___x_1612_ = lean_box(1);
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v_a_1609_);
return v___x_1613_;
}
else
{
lean_object* v_quotContext_1614_; lean_object* v_currMacroScope_1615_; lean_object* v_ref_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_quotContext_1614_ = lean_ctor_get(v_a_1608_, 1);
v_currMacroScope_1615_ = lean_ctor_get(v_a_1608_, 2);
v_ref_1616_ = lean_ctor_get(v_a_1608_, 5);
v___x_1617_ = lean_unsigned_to_nat(0u);
v___x_1618_ = l_Lean_Syntax_getArg(v_x_1607_, v___x_1617_);
v___x_1619_ = lean_unsigned_to_nat(2u);
v___x_1620_ = l_Lean_Syntax_getArg(v_x_1607_, v___x_1619_);
lean_dec(v_x_1607_);
v___x_1621_ = 0;
v___x_1622_ = l_Lean_SourceInfo_fromRef(v_ref_1616_, v___x_1621_);
v___x_1623_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1624_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
v___x_1625_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1615_);
lean_inc(v_quotContext_1614_);
v___x_1626_ = l_Lean_addMacroScope(v_quotContext_1614_, v___x_1625_, v_currMacroScope_1615_);
v___x_1627_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1622_, 2);
v___x_1628_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1622_);
lean_ctor_set(v___x_1628_, 1, v___x_1624_);
lean_ctor_set(v___x_1628_, 2, v___x_1626_);
lean_ctor_set(v___x_1628_, 3, v___x_1627_);
v___x_1629_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1630_ = l_Lean_Syntax_node2(v___x_1622_, v___x_1629_, v___x_1618_, v___x_1620_);
v___x_1631_ = l_Lean_Syntax_node2(v___x_1622_, v___x_1623_, v___x_1628_, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v_a_1609_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___boxed(lean_object* v_x_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(v_x_1633_, v_a_1634_, v_a_1635_);
lean_dec_ref(v_a_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object* v_x_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1637_);
v___x_1641_ = l_Lean_Syntax_isOfKind(v_x_1637_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec(v_x_1637_);
v___x_1642_ = lean_box(0);
v___x_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_a_1639_);
return v___x_1643_;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = l_Lean_Syntax_getArg(v_x_1637_, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1645_);
v___x_1647_ = l_Lean_Syntax_isOfKind(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec(v___x_1645_);
lean_dec(v_x_1637_);
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v_a_1639_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = l_Lean_Syntax_getArg(v_x_1637_, v___x_1650_);
lean_dec(v_x_1637_);
v___x_1652_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1651_);
v___x_1653_ = l_Lean_Syntax_matchesNull(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec(v___x_1651_);
lean_dec(v___x_1645_);
v___x_1654_ = lean_box(0);
v___x_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v_a_1639_);
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v_ref_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1656_ = l_Lean_Syntax_getArg(v___x_1651_, v___x_1644_);
v___x_1657_ = l_Lean_Syntax_getArg(v___x_1651_, v___x_1650_);
lean_dec(v___x_1651_);
v_ref_1658_ = l_Lean_replaceRef(v___x_1645_, v_a_1638_);
lean_dec(v___x_1645_);
v___x_1659_ = 0;
v___x_1660_ = l_Lean_SourceInfo_fromRef(v_ref_1658_, v___x_1659_);
lean_dec(v_ref_1658_);
v___x_1661_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
v___x_1662_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__2));
lean_inc(v___x_1660_);
v___x_1663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1660_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_Syntax_node3(v___x_1660_, v___x_1661_, v___x_1656_, v___x_1663_, v___x_1657_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v_a_1639_);
return v___x_1665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object* v_x_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(v_x_1666_, v_a_1667_, v_a_1668_);
lean_dec(v_a_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal___redArg(lean_object* v_inst_1670_, lean_object* v_l_u2081_1671_, lean_object* v_l_u2082_1672_){
_start:
{
uint8_t v___x_1673_; 
lean_inc(v_l_u2082_1672_);
lean_inc(v_l_u2081_1671_);
lean_inc_ref(v_inst_1670_);
v___x_1673_ = l_List_isPrefixOf___redArg(v_inst_1670_, v_l_u2081_1671_, v_l_u2082_1672_);
if (v___x_1673_ == 0)
{
if (lean_obj_tag(v_l_u2082_1672_) == 0)
{
lean_dec(v_l_u2081_1671_);
lean_dec_ref(v_inst_1670_);
return v___x_1673_;
}
else
{
lean_object* v_tail_1674_; 
v_tail_1674_ = lean_ctor_get(v_l_u2082_1672_, 1);
lean_inc(v_tail_1674_);
lean_dec_ref_known(v_l_u2082_1672_, 2);
v_l_u2082_1672_ = v_tail_1674_;
goto _start;
}
}
else
{
lean_dec(v_l_u2082_1672_);
lean_dec(v_l_u2081_1671_);
lean_dec_ref(v_inst_1670_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___redArg___boxed(lean_object* v_inst_1676_, lean_object* v_l_u2081_1677_, lean_object* v_l_u2082_1678_){
_start:
{
uint8_t v_res_1679_; lean_object* v_r_1680_; 
v_res_1679_ = l_List_isInfixOf__internal___redArg(v_inst_1676_, v_l_u2081_1677_, v_l_u2082_1678_);
v_r_1680_ = lean_box(v_res_1679_);
return v_r_1680_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal(lean_object* v_00_u03b1_1681_, lean_object* v_inst_1682_, lean_object* v_l_u2081_1683_, lean_object* v_l_u2082_1684_){
_start:
{
uint8_t v___x_1685_; 
v___x_1685_ = l_List_isInfixOf__internal___redArg(v_inst_1682_, v_l_u2081_1683_, v_l_u2082_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___boxed(lean_object* v_00_u03b1_1686_, lean_object* v_inst_1687_, lean_object* v_l_u2081_1688_, lean_object* v_l_u2082_1689_){
_start:
{
uint8_t v_res_1690_; lean_object* v_r_1691_; 
v_res_1690_ = l_List_isInfixOf__internal(v_00_u03b1_1686_, v_inst_1687_, v_l_u2081_1688_, v_l_u2082_1689_);
v_r_1691_ = lean_box(v_res_1690_);
return v_r_1691_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go___redArg(lean_object* v_l_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
if (lean_obj_tag(v_a_1693_) == 0)
{
lean_object* v___x_1696_; 
lean_dec(v_a_1695_);
lean_dec(v_a_1694_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_l_1692_);
lean_ctor_set(v___x_1696_, 1, v_a_1693_);
return v___x_1696_;
}
else
{
lean_object* v_head_1697_; lean_object* v_tail_1698_; lean_object* v_zero_1699_; uint8_t v_isZero_1700_; 
v_head_1697_ = lean_ctor_get(v_a_1693_, 0);
v_tail_1698_ = lean_ctor_get(v_a_1693_, 1);
v_zero_1699_ = lean_unsigned_to_nat(0u);
v_isZero_1700_ = lean_nat_dec_eq(v_a_1694_, v_zero_1699_);
if (v_isZero_1700_ == 1)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec(v_a_1694_);
lean_dec(v_l_1692_);
v___x_1701_ = l_List_reverse___redArg(v_a_1695_);
v___x_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v_a_1693_);
return v___x_1702_;
}
else
{
lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1712_; 
lean_inc(v_tail_1698_);
lean_inc(v_head_1697_);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_a_1693_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; lean_object* v_unused_1714_; 
v_unused_1713_ = lean_ctor_get(v_a_1693_, 1);
lean_dec(v_unused_1713_);
v_unused_1714_ = lean_ctor_get(v_a_1693_, 0);
lean_dec(v_unused_1714_);
v___x_1704_ = v_a_1693_;
v_isShared_1705_ = v_isSharedCheck_1712_;
goto v_resetjp_1703_;
}
else
{
lean_dec(v_a_1693_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1712_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v_one_1706_; lean_object* v_n_1707_; lean_object* v___x_1709_; 
v_one_1706_ = lean_unsigned_to_nat(1u);
v_n_1707_ = lean_nat_sub(v_a_1694_, v_one_1706_);
lean_dec(v_a_1694_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v_a_1695_);
v___x_1709_ = v___x_1704_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_head_1697_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_a_1695_);
v___x_1709_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
v_a_1693_ = v_tail_1698_;
v_a_1694_ = v_n_1707_;
v_a_1695_ = v___x_1709_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object* v_00_u03b1_1715_, lean_object* v_l_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_List_splitAt_go___redArg(v_l_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt___redArg(lean_object* v_n_1721_, lean_object* v_l_1722_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_box(0);
lean_inc(v_l_1722_);
v___x_1724_ = l_List_splitAt_go___redArg(v_l_1722_, v_l_1722_, v_n_1721_, v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt(lean_object* v_00_u03b1_1725_, lean_object* v_n_1726_, lean_object* v_l_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_List_splitAt___redArg(v_n_1726_, v_l_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg(lean_object* v_xs_1729_, lean_object* v_i_1730_){
_start:
{
lean_object* v_len_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_len_1731_ = l_List_length___redArg(v_xs_1729_);
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_dec_le(v_len_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v_i_1734_; lean_object* v_ys_1735_; lean_object* v_zs_1736_; lean_object* v___x_1737_; 
v_i_1734_ = lean_nat_mod(v_i_1730_, v_len_1731_);
lean_dec(v_len_1731_);
lean_inc(v_xs_1729_);
v_ys_1735_ = l_List_take___redArg(v_i_1734_, v_xs_1729_);
v_zs_1736_ = l_List_drop___redArg(v_i_1734_, v_xs_1729_);
lean_dec(v_xs_1729_);
v___x_1737_ = l_List_appendTR___redArg(v_zs_1736_, v_ys_1735_);
return v___x_1737_;
}
else
{
lean_dec(v_len_1731_);
return v_xs_1729_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg___boxed(lean_object* v_xs_1738_, lean_object* v_i_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_List_rotateLeft___redArg(v_xs_1738_, v_i_1739_);
lean_dec(v_i_1739_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft(lean_object* v_00_u03b1_1741_, lean_object* v_xs_1742_, lean_object* v_i_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_List_rotateLeft___redArg(v_xs_1742_, v_i_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_xs_1746_, lean_object* v_i_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_List_rotateLeft(v_00_u03b1_1745_, v_xs_1746_, v_i_1747_);
lean_dec(v_i_1747_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg(lean_object* v_xs_1749_, lean_object* v_i_1750_){
_start:
{
lean_object* v_len_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v_len_1751_ = l_List_length___redArg(v_xs_1749_);
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_dec_le(v_len_1751_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v_i_1755_; lean_object* v_ys_1756_; lean_object* v_zs_1757_; lean_object* v___x_1758_; 
v___x_1754_ = lean_nat_mod(v_i_1750_, v_len_1751_);
v_i_1755_ = lean_nat_sub(v_len_1751_, v___x_1754_);
lean_dec(v___x_1754_);
lean_dec(v_len_1751_);
lean_inc(v_xs_1749_);
v_ys_1756_ = l_List_take___redArg(v_i_1755_, v_xs_1749_);
v_zs_1757_ = l_List_drop___redArg(v_i_1755_, v_xs_1749_);
lean_dec(v_xs_1749_);
v___x_1758_ = l_List_appendTR___redArg(v_zs_1757_, v_ys_1756_);
return v___x_1758_;
}
else
{
lean_dec(v_len_1751_);
return v_xs_1749_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg___boxed(lean_object* v_xs_1759_, lean_object* v_i_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_List_rotateRight___redArg(v_xs_1759_, v_i_1760_);
lean_dec(v_i_1760_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight(lean_object* v_00_u03b1_1762_, lean_object* v_xs_1763_, lean_object* v_i_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_List_rotateRight___redArg(v_xs_1763_, v_i_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___boxed(lean_object* v_00_u03b1_1766_, lean_object* v_xs_1767_, lean_object* v_i_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_List_rotateRight(v_00_u03b1_1766_, v_xs_1767_, v_i_1768_);
lean_dec(v_i_1768_);
return v_res_1769_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise___redArg(lean_object* v_inst_1770_, lean_object* v_x_1771_){
_start:
{
if (lean_obj_tag(v_x_1771_) == 0)
{
uint8_t v___x_1772_; 
lean_dec_ref(v_inst_1770_);
v___x_1772_ = 1;
return v___x_1772_;
}
else
{
lean_object* v_head_1773_; lean_object* v_tail_1774_; uint8_t v_decide_1775_; 
v_head_1773_ = lean_ctor_get(v_x_1771_, 0);
lean_inc(v_head_1773_);
v_tail_1774_ = lean_ctor_get(v_x_1771_, 1);
lean_inc_n(v_tail_1774_, 2);
lean_dec_ref_known(v_x_1771_, 2);
lean_inc_ref(v_inst_1770_);
v_decide_1775_ = l_List_instDecidablePairwise___redArg(v_inst_1770_, v_tail_1774_);
if (v_decide_1775_ == 0)
{
lean_dec(v_tail_1774_);
lean_dec(v_head_1773_);
lean_dec_ref(v_inst_1770_);
return v_decide_1775_;
}
else
{
lean_object* v___x_1776_; uint8_t v_decide_1777_; 
v___x_1776_ = lean_apply_1(v_inst_1770_, v_head_1773_);
v_decide_1777_ = l_List_decidableBAll___redArg(v___x_1776_, v_tail_1774_);
return v_decide_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___redArg___boxed(lean_object* v_inst_1778_, lean_object* v_x_1779_){
_start:
{
uint8_t v_res_1780_; lean_object* v_r_1781_; 
v_res_1780_ = l_List_instDecidablePairwise___redArg(v_inst_1778_, v_x_1779_);
v_r_1781_ = lean_box(v_res_1780_);
return v_r_1781_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise(lean_object* v_00_u03b1_1782_, lean_object* v_R_1783_, lean_object* v_inst_1784_, lean_object* v_x_1785_){
_start:
{
uint8_t v___x_1786_; 
v___x_1786_ = l_List_instDecidablePairwise___redArg(v_inst_1784_, v_x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___boxed(lean_object* v_00_u03b1_1787_, lean_object* v_R_1788_, lean_object* v_inst_1789_, lean_object* v_x_1790_){
_start:
{
uint8_t v_res_1791_; lean_object* v_r_1792_; 
v_res_1791_ = l_List_instDecidablePairwise(v_00_u03b1_1787_, v_R_1788_, v_inst_1789_, v_x_1790_);
v_r_1792_ = lean_box(v_res_1791_);
return v_r_1792_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg___lam__0(lean_object* v_inst_1793_, lean_object* v_a_1794_, lean_object* v_b_1795_){
_start:
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = lean_apply_2(v_inst_1793_, v_a_1794_, v_b_1795_);
v___x_1797_ = lean_unbox(v___x_1796_);
if (v___x_1797_ == 0)
{
uint8_t v___x_1798_; 
v___x_1798_ = 1;
return v___x_1798_;
}
else
{
uint8_t v___x_1799_; 
v___x_1799_ = 0;
return v___x_1799_;
}
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___lam__0___boxed(lean_object* v_inst_1800_, lean_object* v_a_1801_, lean_object* v_b_1802_){
_start:
{
uint8_t v_res_1803_; lean_object* v_r_1804_; 
v_res_1803_ = l_List_nodupDecidable___redArg___lam__0(v_inst_1800_, v_a_1801_, v_b_1802_);
v_r_1804_ = lean_box(v_res_1803_);
return v_r_1804_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg(lean_object* v_inst_1805_, lean_object* v_l_1806_){
_start:
{
lean_object* v___f_1807_; uint8_t v___x_1808_; 
v___f_1807_ = lean_alloc_closure((void*)(l_List_nodupDecidable___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1807_, 0, v_inst_1805_);
v___x_1808_ = l_List_instDecidablePairwise___redArg(v___f_1807_, v_l_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___boxed(lean_object* v_inst_1809_, lean_object* v_l_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l_List_nodupDecidable___redArg(v_inst_1809_, v_l_1810_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable(lean_object* v_00_u03b1_1813_, lean_object* v_inst_1814_, lean_object* v_l_1815_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = l_List_nodupDecidable___redArg(v_inst_1814_, v_l_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___boxed(lean_object* v_00_u03b1_1817_, lean_object* v_inst_1818_, lean_object* v_l_1819_){
_start:
{
uint8_t v_res_1820_; lean_object* v_r_1821_; 
v_res_1820_ = l_List_nodupDecidable(v_00_u03b1_1817_, v_inst_1818_, v_l_1819_);
v_r_1821_ = lean_box(v_res_1820_);
return v_r_1821_;
}
}
LEAN_EXPORT lean_object* l_List_replace___redArg(lean_object* v_inst_1822_, lean_object* v_x_1823_, lean_object* v_x_1824_, lean_object* v_x_1825_){
_start:
{
if (lean_obj_tag(v_x_1823_) == 0)
{
lean_dec(v_x_1825_);
lean_dec(v_x_1824_);
lean_dec_ref(v_inst_1822_);
return v_x_1823_;
}
else
{
lean_object* v_head_1826_; lean_object* v_tail_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1840_; 
v_head_1826_ = lean_ctor_get(v_x_1823_, 0);
v_tail_1827_ = lean_ctor_get(v_x_1823_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_x_1823_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1829_ = v_x_1823_;
v_isShared_1830_ = v_isSharedCheck_1840_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_tail_1827_);
lean_inc(v_head_1826_);
lean_dec(v_x_1823_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1840_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
lean_inc_ref(v_inst_1822_);
lean_inc(v_head_1826_);
lean_inc(v_x_1824_);
v___x_1831_ = lean_apply_2(v_inst_1822_, v_x_1824_, v_head_1826_);
v___x_1832_ = lean_unbox(v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = l_List_replace___redArg(v_inst_1822_, v_tail_1827_, v_x_1824_, v_x_1825_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v___x_1833_);
v___x_1835_ = v___x_1829_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_head_1826_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
else
{
lean_object* v___x_1838_; 
lean_dec(v_head_1826_);
lean_dec(v_x_1824_);
lean_dec_ref(v_inst_1822_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v_x_1825_);
v___x_1838_ = v___x_1829_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_x_1825_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_tail_1827_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_replace(lean_object* v_00_u03b1_1841_, lean_object* v_inst_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_List_replace___redArg(v_inst_1842_, v_x_1843_, v_x_1844_, v_x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg(lean_object* v_f_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_zero_1850_; uint8_t v_isZero_1851_; 
v_zero_1850_ = lean_unsigned_to_nat(0u);
v_isZero_1851_ = lean_nat_dec_eq(v_a_1848_, v_zero_1850_);
if (v_isZero_1851_ == 1)
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_apply_1(v_f_1847_, v_a_1849_);
return v___x_1852_;
}
else
{
if (lean_obj_tag(v_a_1849_) == 0)
{
lean_dec_ref(v_f_1847_);
return v_a_1849_;
}
else
{
lean_object* v_head_1853_; lean_object* v_tail_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1864_; 
v_head_1853_ = lean_ctor_get(v_a_1849_, 0);
v_tail_1854_ = lean_ctor_get(v_a_1849_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_a_1849_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1856_ = v_a_1849_;
v_isShared_1857_ = v_isSharedCheck_1864_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_tail_1854_);
lean_inc(v_head_1853_);
lean_dec(v_a_1849_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1864_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v_one_1858_; lean_object* v_n_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v_one_1858_ = lean_unsigned_to_nat(1u);
v_n_1859_ = lean_nat_sub(v_a_1848_, v_one_1858_);
v___x_1860_ = l_List_modifyTailIdx_go___redArg(v_f_1847_, v_n_1859_, v_tail_1854_);
lean_dec(v_n_1859_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 1, v___x_1860_);
v___x_1862_ = v___x_1856_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_head_1853_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg___boxed(lean_object* v_f_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_List_modifyTailIdx_go___redArg(v_f_1865_, v_a_1866_, v_a_1867_);
lean_dec(v_a_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go(lean_object* v_00_u03b1_1869_, lean_object* v_f_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_List_modifyTailIdx_go___redArg(v_f_1870_, v_a_1871_, v_a_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___boxed(lean_object* v_00_u03b1_1874_, lean_object* v_f_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_List_modifyTailIdx_go(v_00_u03b1_1874_, v_f_1875_, v_a_1876_, v_a_1877_);
lean_dec(v_a_1876_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg(lean_object* v_l_1879_, lean_object* v_i_1880_, lean_object* v_f_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_List_modifyTailIdx_go___redArg(v_f_1881_, v_i_1880_, v_l_1879_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg___boxed(lean_object* v_l_1883_, lean_object* v_i_1884_, lean_object* v_f_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_List_modifyTailIdx___redArg(v_l_1883_, v_i_1884_, v_f_1885_);
lean_dec(v_i_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx(lean_object* v_00_u03b1_1887_, lean_object* v_l_1888_, lean_object* v_i_1889_, lean_object* v_f_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_List_modifyTailIdx_go___redArg(v_f_1890_, v_i_1889_, v_l_1888_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_l_1893_, lean_object* v_i_1894_, lean_object* v_f_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_List_modifyTailIdx(v_00_u03b1_1892_, v_l_1893_, v_i_1894_, v_f_1895_);
lean_dec(v_i_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_List_modifyHead___redArg(lean_object* v_f_1897_, lean_object* v_x_1898_){
_start:
{
if (lean_obj_tag(v_x_1898_) == 0)
{
lean_dec(v_f_1897_);
return v_x_1898_;
}
else
{
lean_object* v_head_1899_; lean_object* v_tail_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1908_; 
v_head_1899_ = lean_ctor_get(v_x_1898_, 0);
v_tail_1900_ = lean_ctor_get(v_x_1898_, 1);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_x_1898_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1902_ = v_x_1898_;
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_tail_1900_);
lean_inc(v_head_1899_);
lean_dec(v_x_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = lean_apply_1(v_f_1897_, v_head_1899_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_tail_1900_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyHead(lean_object* v_00_u03b1_1909_, lean_object* v_f_1910_, lean_object* v_x_1911_){
_start:
{
if (lean_obj_tag(v_x_1911_) == 0)
{
lean_dec(v_f_1910_);
return v_x_1911_;
}
else
{
lean_object* v_head_1912_; lean_object* v_tail_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1921_; 
v_head_1912_ = lean_ctor_get(v_x_1911_, 0);
v_tail_1913_ = lean_ctor_get(v_x_1911_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_x_1911_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1915_ = v_x_1911_;
v_isShared_1916_ = v_isSharedCheck_1921_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_tail_1913_);
lean_inc(v_head_1912_);
lean_dec(v_x_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1921_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1917_ = lean_apply_1(v_f_1910_, v_head_1912_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1917_);
v___x_1919_ = v___x_1915_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_tail_1913_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg(lean_object* v_l_1922_, lean_object* v_i_1923_, lean_object* v_f_1924_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1925_, 0, lean_box(0));
lean_closure_set(v___x_1925_, 1, v_f_1924_);
v___x_1926_ = l_List_modifyTailIdx_go___redArg(v___x_1925_, v_i_1923_, v_l_1922_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg___boxed(lean_object* v_l_1927_, lean_object* v_i_1928_, lean_object* v_f_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_List_modify___redArg(v_l_1927_, v_i_1928_, v_f_1929_);
lean_dec(v_i_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_List_modify(lean_object* v_00_u03b1_1931_, lean_object* v_l_1932_, lean_object* v_i_1933_, lean_object* v_f_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1935_, 0, lean_box(0));
lean_closure_set(v___x_1935_, 1, v_f_1934_);
v___x_1936_ = l_List_modifyTailIdx_go___redArg(v___x_1935_, v_i_1933_, v_l_1932_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_List_modify___boxed(lean_object* v_00_u03b1_1937_, lean_object* v_l_1938_, lean_object* v_i_1939_, lean_object* v_f_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_List_modify(v_00_u03b1_1937_, v_l_1938_, v_i_1939_, v_f_1940_);
lean_dec(v_i_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object* v_inst_1942_, lean_object* v_a_1943_, lean_object* v_l_1944_){
_start:
{
uint8_t v___x_1945_; 
lean_inc(v_l_1944_);
lean_inc(v_a_1943_);
v___x_1945_ = l_List_elem___redArg(v_inst_1942_, v_a_1943_, v_l_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1946_, 0, v_a_1943_);
lean_ctor_set(v___x_1946_, 1, v_l_1944_);
return v___x_1946_;
}
else
{
lean_dec(v_a_1943_);
return v_l_1944_;
}
}
}
LEAN_EXPORT lean_object* l_List_insert(lean_object* v_00_u03b1_1947_, lean_object* v_inst_1948_, lean_object* v_a_1949_, lean_object* v_l_1950_){
_start:
{
uint8_t v___x_1951_; 
lean_inc(v_l_1950_);
lean_inc(v_a_1949_);
v___x_1951_ = l_List_elem___redArg(v_inst_1948_, v_a_1949_, v_l_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_a_1949_);
lean_ctor_set(v___x_1952_, 1, v_l_1950_);
return v___x_1952_;
}
else
{
lean_dec(v_a_1949_);
return v_l_1950_;
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_zero_1956_; uint8_t v_isZero_1957_; 
v_zero_1956_ = lean_unsigned_to_nat(0u);
v_isZero_1957_ = lean_nat_dec_eq(v_a_1954_, v_zero_1956_);
if (v_isZero_1957_ == 1)
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_a_1953_);
lean_ctor_set(v___x_1958_, 1, v_a_1955_);
return v___x_1958_;
}
else
{
if (lean_obj_tag(v_a_1955_) == 0)
{
lean_dec(v_a_1953_);
return v_a_1955_;
}
else
{
lean_object* v_head_1959_; lean_object* v_tail_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1970_; 
v_head_1959_ = lean_ctor_get(v_a_1955_, 0);
v_tail_1960_ = lean_ctor_get(v_a_1955_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_a_1955_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1962_ = v_a_1955_;
v_isShared_1963_ = v_isSharedCheck_1970_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_tail_1960_);
lean_inc(v_head_1959_);
lean_dec(v_a_1955_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1970_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_one_1964_; lean_object* v_n_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v_one_1964_ = lean_unsigned_to_nat(1u);
v_n_1965_ = lean_nat_sub(v_a_1954_, v_one_1964_);
v___x_1966_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1953_, v_n_1965_, v_tail_1960_);
lean_dec(v_n_1965_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v___x_1966_);
v___x_1968_ = v___x_1962_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_head_1959_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg___boxed(lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1971_, v_a_1972_, v_a_1973_);
lean_dec(v_a_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg(lean_object* v_xs_1975_, lean_object* v_i_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1977_, v_i_1976_, v_xs_1975_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___boxed(lean_object* v_xs_1979_, lean_object* v_i_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_List_insertIdx___redArg(v_xs_1979_, v_i_1980_, v_a_1981_);
lean_dec(v_i_1980_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx(lean_object* v_00_u03b1_1983_, lean_object* v_xs_1984_, lean_object* v_i_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1986_, v_i_1985_, v_xs_1984_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___boxed(lean_object* v_00_u03b1_1988_, lean_object* v_xs_1989_, lean_object* v_i_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_List_insertIdx(v_00_u03b1_1988_, v_xs_1989_, v_i_1990_, v_a_1991_);
lean_dec(v_i_1990_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(lean_object* v_00_u03b1_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(v_00_u03b1_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec(v_a_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_List_erase___redArg(lean_object* v_inst_2003_, lean_object* v_x_2004_, lean_object* v_x_2005_){
_start:
{
if (lean_obj_tag(v_x_2004_) == 0)
{
lean_dec(v_x_2005_);
lean_dec_ref(v_inst_2003_);
return v_x_2004_;
}
else
{
lean_object* v_head_2006_; lean_object* v_tail_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2017_; 
v_head_2006_ = lean_ctor_get(v_x_2004_, 0);
v_tail_2007_ = lean_ctor_get(v_x_2004_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_x_2004_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2009_ = v_x_2004_;
v_isShared_2010_ = v_isSharedCheck_2017_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_tail_2007_);
lean_inc(v_head_2006_);
lean_dec(v_x_2004_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2017_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
lean_inc_ref(v_inst_2003_);
lean_inc(v_x_2005_);
lean_inc(v_head_2006_);
v___x_2011_ = lean_apply_2(v_inst_2003_, v_head_2006_, v_x_2005_);
v___x_2012_ = lean_unbox(v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2013_ = l_List_erase___redArg(v_inst_2003_, v_tail_2007_, v_x_2005_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v___x_2013_);
v___x_2015_ = v___x_2009_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_head_2006_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
else
{
lean_del_object(v___x_2009_);
lean_dec(v_head_2006_);
lean_dec(v_x_2005_);
lean_dec_ref(v_inst_2003_);
return v_tail_2007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_erase(lean_object* v_00_u03b1_2018_, lean_object* v_inst_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_List_erase___redArg(v_inst_2019_, v_x_2020_, v_x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(lean_object* v_x_2023_, lean_object* v_x_2024_, lean_object* v_h__1_2025_, lean_object* v_h__2_2026_){
_start:
{
if (lean_obj_tag(v_x_2023_) == 0)
{
lean_object* v___x_2027_; 
lean_dec(v_h__2_2026_);
v___x_2027_ = lean_apply_1(v_h__1_2025_, v_x_2024_);
return v___x_2027_;
}
else
{
lean_object* v_head_2028_; lean_object* v_tail_2029_; lean_object* v___x_2030_; 
lean_dec(v_h__1_2025_);
v_head_2028_ = lean_ctor_get(v_x_2023_, 0);
lean_inc(v_head_2028_);
v_tail_2029_ = lean_ctor_get(v_x_2023_, 1);
lean_inc(v_tail_2029_);
lean_dec_ref_known(v_x_2023_, 2);
v___x_2030_ = lean_apply_3(v_h__2_2026_, v_head_2028_, v_tail_2029_, v_x_2024_);
return v___x_2030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object* v_00_u03b1_2031_, lean_object* v_motive_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_h__1_2035_, lean_object* v_h__2_2036_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
lean_object* v___x_2037_; 
lean_dec(v_h__2_2036_);
v___x_2037_ = lean_apply_1(v_h__1_2035_, v_x_2034_);
return v___x_2037_;
}
else
{
lean_object* v_head_2038_; lean_object* v_tail_2039_; lean_object* v___x_2040_; 
lean_dec(v_h__1_2035_);
v_head_2038_ = lean_ctor_get(v_x_2033_, 0);
lean_inc(v_head_2038_);
v_tail_2039_ = lean_ctor_get(v_x_2033_, 1);
lean_inc(v_tail_2039_);
lean_dec_ref_known(v_x_2033_, 2);
v___x_2040_ = lean_apply_3(v_h__2_2036_, v_head_2038_, v_tail_2039_, v_x_2034_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP___redArg(lean_object* v_p_2041_, lean_object* v_x_2042_){
_start:
{
if (lean_obj_tag(v_x_2042_) == 0)
{
lean_dec_ref(v_p_2041_);
return v_x_2042_;
}
else
{
lean_object* v_head_2043_; lean_object* v_tail_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2054_; 
v_head_2043_ = lean_ctor_get(v_x_2042_, 0);
v_tail_2044_ = lean_ctor_get(v_x_2042_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_x_2042_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2046_ = v_x_2042_;
v_isShared_2047_ = v_isSharedCheck_2054_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_tail_2044_);
lean_inc(v_head_2043_);
lean_dec(v_x_2042_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2054_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; uint8_t v___x_2049_; 
lean_inc_ref(v_p_2041_);
lean_inc(v_head_2043_);
v___x_2048_ = lean_apply_1(v_p_2041_, v_head_2043_);
v___x_2049_ = lean_unbox(v___x_2048_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2050_ = l_List_eraseP___redArg(v_p_2041_, v_tail_2044_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v___x_2050_);
v___x_2052_ = v___x_2046_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_head_2043_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
else
{
lean_del_object(v___x_2046_);
lean_dec(v_head_2043_);
lean_dec_ref(v_p_2041_);
return v_tail_2044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP(lean_object* v_00_u03b1_2055_, lean_object* v_p_2056_, lean_object* v_x_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_List_eraseP___redArg(v_p_2056_, v_x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg(lean_object* v_x_2059_, lean_object* v_x_2060_){
_start:
{
if (lean_obj_tag(v_x_2059_) == 0)
{
return v_x_2059_;
}
else
{
lean_object* v_head_2061_; lean_object* v_tail_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2074_; 
v_head_2061_ = lean_ctor_get(v_x_2059_, 0);
v_tail_2062_ = lean_ctor_get(v_x_2059_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_x_2059_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2064_ = v_x_2059_;
v_isShared_2065_ = v_isSharedCheck_2074_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_tail_2062_);
lean_inc(v_head_2061_);
lean_dec(v_x_2059_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2074_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_zero_2066_; uint8_t v_isZero_2067_; 
v_zero_2066_ = lean_unsigned_to_nat(0u);
v_isZero_2067_ = lean_nat_dec_eq(v_x_2060_, v_zero_2066_);
if (v_isZero_2067_ == 1)
{
lean_del_object(v___x_2064_);
lean_dec(v_head_2061_);
return v_tail_2062_;
}
else
{
lean_object* v_one_2068_; lean_object* v_n_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v_one_2068_ = lean_unsigned_to_nat(1u);
v_n_2069_ = lean_nat_sub(v_x_2060_, v_one_2068_);
v___x_2070_ = l_List_eraseIdx___redArg(v_tail_2062_, v_n_2069_);
lean_dec(v_n_2069_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v___x_2070_);
v___x_2072_ = v___x_2064_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_head_2061_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg___boxed(lean_object* v_x_2075_, lean_object* v_x_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_List_eraseIdx___redArg(v_x_2075_, v_x_2076_);
lean_dec(v_x_2076_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object* v_00_u03b1_2078_, lean_object* v_x_2079_, lean_object* v_x_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_List_eraseIdx___redArg(v_x_2079_, v_x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___boxed(lean_object* v_00_u03b1_2082_, lean_object* v_x_2083_, lean_object* v_x_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_List_eraseIdx(v_00_u03b1_2082_, v_x_2083_, v_x_2084_);
lean_dec(v_x_2084_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object* v_p_2086_, lean_object* v_x_2087_){
_start:
{
if (lean_obj_tag(v_x_2087_) == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref(v_p_2086_);
v___x_2088_ = lean_box(0);
return v___x_2088_;
}
else
{
lean_object* v_head_2089_; lean_object* v_tail_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v_head_2089_ = lean_ctor_get(v_x_2087_, 0);
lean_inc_n(v_head_2089_, 2);
v_tail_2090_ = lean_ctor_get(v_x_2087_, 1);
lean_inc(v_tail_2090_);
lean_dec_ref_known(v_x_2087_, 2);
lean_inc_ref(v_p_2086_);
v___x_2091_ = lean_apply_1(v_p_2086_, v_head_2089_);
v___x_2092_ = lean_unbox(v___x_2091_);
if (v___x_2092_ == 0)
{
lean_dec(v_head_2089_);
v_x_2087_ = v_tail_2090_;
goto _start;
}
else
{
lean_object* v___x_2094_; 
lean_dec(v_tail_2090_);
lean_dec_ref(v_p_2086_);
v___x_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2094_, 0, v_head_2089_);
return v___x_2094_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object* v_00_u03b1_2095_, lean_object* v_p_2096_, lean_object* v_x_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_List_find_x3f___redArg(v_p_2096_, v_x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object* v_f_2099_, lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 0)
{
lean_object* v___x_2101_; 
lean_dec_ref(v_f_2099_);
v___x_2101_ = lean_box(0);
return v___x_2101_;
}
else
{
lean_object* v_head_2102_; lean_object* v_tail_2103_; lean_object* v___x_2104_; 
v_head_2102_ = lean_ctor_get(v_x_2100_, 0);
lean_inc(v_head_2102_);
v_tail_2103_ = lean_ctor_get(v_x_2100_, 1);
lean_inc(v_tail_2103_);
lean_dec_ref_known(v_x_2100_, 2);
lean_inc_ref(v_f_2099_);
v___x_2104_ = lean_apply_1(v_f_2099_, v_head_2102_);
if (lean_obj_tag(v___x_2104_) == 0)
{
v_x_2100_ = v_tail_2103_;
goto _start;
}
else
{
lean_dec(v_tail_2103_);
lean_dec_ref(v_f_2099_);
return v___x_2104_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object* v_00_u03b1_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_f_2108_, lean_object* v_x_2109_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_List_findSome_x3f___redArg(v_f_2108_, v_x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f___redArg(lean_object* v_p_2111_, lean_object* v_x_2112_){
_start:
{
if (lean_obj_tag(v_x_2112_) == 0)
{
lean_object* v___x_2113_; 
lean_dec_ref(v_p_2111_);
v___x_2113_ = lean_box(0);
return v___x_2113_;
}
else
{
lean_object* v_head_2114_; lean_object* v_tail_2115_; lean_object* v___x_2116_; 
v_head_2114_ = lean_ctor_get(v_x_2112_, 0);
lean_inc(v_head_2114_);
v_tail_2115_ = lean_ctor_get(v_x_2112_, 1);
lean_inc(v_tail_2115_);
lean_dec_ref_known(v_x_2112_, 2);
lean_inc_ref(v_p_2111_);
v___x_2116_ = l_List_findRev_x3f___redArg(v_p_2111_, v_tail_2115_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
lean_inc(v_head_2114_);
v___x_2117_ = lean_apply_1(v_p_2111_, v_head_2114_);
v___x_2118_ = lean_unbox(v___x_2117_);
if (v___x_2118_ == 0)
{
lean_dec(v_head_2114_);
return v___x_2116_;
}
else
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v_head_2114_);
return v___x_2119_;
}
}
else
{
lean_dec(v_head_2114_);
lean_dec_ref(v_p_2111_);
return v___x_2116_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f(lean_object* v_00_u03b1_2120_, lean_object* v_p_2121_, lean_object* v_x_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_List_findRev_x3f___redArg(v_p_2121_, v_x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f___redArg(lean_object* v_f_2124_, lean_object* v_x_2125_){
_start:
{
if (lean_obj_tag(v_x_2125_) == 0)
{
lean_object* v___x_2126_; 
lean_dec_ref(v_f_2124_);
v___x_2126_ = lean_box(0);
return v___x_2126_;
}
else
{
lean_object* v_head_2127_; lean_object* v_tail_2128_; lean_object* v___x_2129_; 
v_head_2127_ = lean_ctor_get(v_x_2125_, 0);
lean_inc(v_head_2127_);
v_tail_2128_ = lean_ctor_get(v_x_2125_, 1);
lean_inc(v_tail_2128_);
lean_dec_ref_known(v_x_2125_, 2);
lean_inc_ref(v_f_2124_);
v___x_2129_ = l_List_findSomeRev_x3f___redArg(v_f_2124_, v_tail_2128_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_apply_1(v_f_2124_, v_head_2127_);
return v___x_2130_;
}
else
{
lean_dec(v_head_2127_);
lean_dec_ref(v_f_2124_);
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f(lean_object* v_00_u03b1_2131_, lean_object* v_00_u03b2_2132_, lean_object* v_f_2133_, lean_object* v_x_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_List_findSomeRev_x3f___redArg(v_f_2133_, v_x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___redArg(lean_object* v_p_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
if (lean_obj_tag(v_a_2137_) == 0)
{
lean_dec_ref(v_p_2136_);
return v_a_2138_;
}
else
{
lean_object* v_head_2139_; lean_object* v_tail_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_head_2139_ = lean_ctor_get(v_a_2137_, 0);
lean_inc(v_head_2139_);
v_tail_2140_ = lean_ctor_get(v_a_2137_, 1);
lean_inc(v_tail_2140_);
lean_dec_ref_known(v_a_2137_, 2);
lean_inc_ref(v_p_2136_);
v___x_2141_ = lean_apply_1(v_p_2136_, v_head_2139_);
v___x_2142_ = lean_unbox(v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_unsigned_to_nat(1u);
v___x_2144_ = lean_nat_add(v_a_2138_, v___x_2143_);
lean_dec(v_a_2138_);
v_a_2137_ = v_tail_2140_;
v_a_2138_ = v___x_2144_;
goto _start;
}
else
{
lean_dec(v_tail_2140_);
lean_dec_ref(v_p_2136_);
return v_a_2138_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object* v_00_u03b1_2146_, lean_object* v_p_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_List_findIdx_go___redArg(v_p_2147_, v_a_2148_, v_a_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx___redArg(lean_object* v_p_2151_, lean_object* v_l_2152_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_unsigned_to_nat(0u);
v___x_2154_ = l_List_findIdx_go___redArg(v_p_2151_, v_l_2152_, v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx(lean_object* v_00_u03b1_2155_, lean_object* v_p_2156_, lean_object* v_l_2157_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_unsigned_to_nat(0u);
v___x_2159_ = l_List_findIdx_go___redArg(v_p_2156_, v_l_2157_, v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT uint8_t l_List_idxOf___redArg___lam__0(lean_object* v_inst_2160_, lean_object* v_a_2161_, lean_object* v_x_2162_){
_start:
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = lean_apply_2(v_inst_2160_, v_x_2162_, v_a_2161_);
v___x_2164_ = lean_unbox(v___x_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg___lam__0___boxed(lean_object* v_inst_2165_, lean_object* v_a_2166_, lean_object* v_x_2167_){
_start:
{
uint8_t v_res_2168_; lean_object* v_r_2169_; 
v_res_2168_ = l_List_idxOf___redArg___lam__0(v_inst_2165_, v_a_2166_, v_x_2167_);
v_r_2169_ = lean_box(v_res_2168_);
return v_r_2169_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg(lean_object* v_inst_2170_, lean_object* v_a_2171_, lean_object* v_l_2172_){
_start:
{
lean_object* v___f_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___f_2173_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2173_, 0, v_inst_2170_);
lean_closure_set(v___f_2173_, 1, v_a_2171_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = l_List_findIdx_go___redArg(v___f_2173_, v_l_2172_, v___x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf(lean_object* v_00_u03b1_2176_, lean_object* v_inst_2177_, lean_object* v_a_2178_, lean_object* v_l_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_List_idxOf___redArg(v_inst_2177_, v_a_2178_, v_l_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___redArg(lean_object* v_p_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
if (lean_obj_tag(v_a_2182_) == 0)
{
lean_object* v___x_2184_; 
lean_dec(v_a_2183_);
lean_dec_ref(v_p_2181_);
v___x_2184_ = lean_box(0);
return v___x_2184_;
}
else
{
lean_object* v_head_2185_; lean_object* v_tail_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v_head_2185_ = lean_ctor_get(v_a_2182_, 0);
lean_inc(v_head_2185_);
v_tail_2186_ = lean_ctor_get(v_a_2182_, 1);
lean_inc(v_tail_2186_);
lean_dec_ref_known(v_a_2182_, 2);
lean_inc_ref(v_p_2181_);
v___x_2187_ = lean_apply_1(v_p_2181_, v_head_2185_);
v___x_2188_ = lean_unbox(v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_unsigned_to_nat(1u);
v___x_2190_ = lean_nat_add(v_a_2183_, v___x_2189_);
lean_dec(v_a_2183_);
v_a_2182_ = v_tail_2186_;
v_a_2183_ = v___x_2190_;
goto _start;
}
else
{
lean_object* v___x_2192_; 
lean_dec(v_tail_2186_);
lean_dec_ref(v_p_2181_);
v___x_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2192_, 0, v_a_2183_);
return v___x_2192_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go(lean_object* v_00_u03b1_2193_, lean_object* v_p_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_List_findIdx_x3f_go___redArg(v_p_2194_, v_a_2195_, v_a_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f___redArg(lean_object* v_p_2198_, lean_object* v_l_2199_){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = l_List_findIdx_x3f_go___redArg(v_p_2198_, v_l_2199_, v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object* v_00_u03b1_2202_, lean_object* v_p_2203_, lean_object* v_l_2204_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = l_List_findIdx_x3f_go___redArg(v_p_2203_, v_l_2204_, v___x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f___redArg(lean_object* v_inst_2207_, lean_object* v_a_2208_, lean_object* v_l_2209_){
_start:
{
lean_object* v___f_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___f_2210_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2210_, 0, v_inst_2207_);
lean_closure_set(v___f_2210_, 1, v_a_2208_);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = l_List_findIdx_x3f_go___redArg(v___f_2210_, v_l_2209_, v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f(lean_object* v_00_u03b1_2213_, lean_object* v_inst_2214_, lean_object* v_a_2215_, lean_object* v_l_2216_){
_start:
{
lean_object* v___f_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___f_2217_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2217_, 0, v_inst_2214_);
lean_closure_set(v___f_2217_, 1, v_a_2215_);
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = l_List_findIdx_x3f_go___redArg(v___f_2217_, v_l_2216_, v___x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___redArg(lean_object* v_p_2220_, lean_object* v_l_x27_2221_, lean_object* v_i_2222_){
_start:
{
if (lean_obj_tag(v_l_x27_2221_) == 0)
{
lean_object* v___x_2223_; 
lean_dec(v_i_2222_);
lean_dec_ref(v_p_2220_);
v___x_2223_ = lean_box(0);
return v___x_2223_;
}
else
{
lean_object* v_head_2224_; lean_object* v_tail_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v_head_2224_ = lean_ctor_get(v_l_x27_2221_, 0);
lean_inc(v_head_2224_);
v_tail_2225_ = lean_ctor_get(v_l_x27_2221_, 1);
lean_inc(v_tail_2225_);
lean_dec_ref_known(v_l_x27_2221_, 2);
lean_inc_ref(v_p_2220_);
v___x_2226_ = lean_apply_1(v_p_2220_, v_head_2224_);
v___x_2227_ = lean_unbox(v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_unsigned_to_nat(1u);
v___x_2229_ = lean_nat_add(v_i_2222_, v___x_2228_);
lean_dec(v_i_2222_);
v_l_x27_2221_ = v_tail_2225_;
v_i_2222_ = v___x_2229_;
goto _start;
}
else
{
lean_object* v___x_2231_; 
lean_dec(v_tail_2225_);
lean_dec_ref(v_p_2220_);
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_i_2222_);
return v___x_2231_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go(lean_object* v_00_u03b1_2232_, lean_object* v_p_2233_, lean_object* v_l_2234_, lean_object* v_l_x27_2235_, lean_object* v_i_2236_, lean_object* v_h_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_List_findFinIdx_x3f_go___redArg(v_p_2233_, v_l_x27_2235_, v_i_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___boxed(lean_object* v_00_u03b1_2239_, lean_object* v_p_2240_, lean_object* v_l_2241_, lean_object* v_l_x27_2242_, lean_object* v_i_2243_, lean_object* v_h_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_List_findFinIdx_x3f_go(v_00_u03b1_2239_, v_p_2240_, v_l_2241_, v_l_x27_2242_, v_i_2243_, v_h_2244_);
lean_dec(v_l_2241_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f___redArg(lean_object* v_p_2246_, lean_object* v_l_2247_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = l_List_findFinIdx_x3f_go___redArg(v_p_2246_, v_l_2247_, v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f(lean_object* v_00_u03b1_2250_, lean_object* v_p_2251_, lean_object* v_l_2252_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = l_List_findFinIdx_x3f_go___redArg(v_p_2251_, v_l_2252_, v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f___redArg(lean_object* v_inst_2255_, lean_object* v_a_2256_, lean_object* v_l_2257_){
_start:
{
lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___f_2258_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2258_, 0, v_inst_2255_);
lean_closure_set(v___f_2258_, 1, v_a_2256_);
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = l_List_findFinIdx_x3f_go___redArg(v___f_2258_, v_l_2257_, v___x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f(lean_object* v_00_u03b1_2261_, lean_object* v_inst_2262_, lean_object* v_a_2263_, lean_object* v_l_2264_){
_start:
{
lean_object* v___f_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___f_2265_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2265_, 0, v_inst_2262_);
lean_closure_set(v___f_2265_, 1, v_a_2263_);
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = l_List_findFinIdx_x3f_go___redArg(v___f_2265_, v_l_2264_, v___x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___redArg(lean_object* v_p_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
if (lean_obj_tag(v_a_2269_) == 0)
{
lean_dec_ref(v_p_2268_);
return v_a_2270_;
}
else
{
lean_object* v_head_2271_; lean_object* v_tail_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_head_2271_ = lean_ctor_get(v_a_2269_, 0);
lean_inc(v_head_2271_);
v_tail_2272_ = lean_ctor_get(v_a_2269_, 1);
lean_inc(v_tail_2272_);
lean_dec_ref_known(v_a_2269_, 2);
lean_inc_ref(v_p_2268_);
v___x_2273_ = lean_apply_1(v_p_2268_, v_head_2271_);
v___x_2274_ = lean_unbox(v___x_2273_);
if (v___x_2274_ == 0)
{
v_a_2269_ = v_tail_2272_;
goto _start;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_unsigned_to_nat(1u);
v___x_2277_ = lean_nat_add(v_a_2270_, v___x_2276_);
lean_dec(v_a_2270_);
v_a_2269_ = v_tail_2272_;
v_a_2270_ = v___x_2277_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go(lean_object* v_00_u03b1_2279_, lean_object* v_p_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_List_countP_go___redArg(v_p_2280_, v_a_2281_, v_a_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_List_countP___redArg(lean_object* v_p_2284_, lean_object* v_l_2285_){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_unsigned_to_nat(0u);
v___x_2287_ = l_List_countP_go___redArg(v_p_2284_, v_l_2285_, v___x_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_List_countP(lean_object* v_00_u03b1_2288_, lean_object* v_p_2289_, lean_object* v_l_2290_){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = l_List_countP_go___redArg(v_p_2289_, v_l_2290_, v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_List_count___redArg(lean_object* v_inst_2293_, lean_object* v_a_2294_, lean_object* v_l_2295_){
_start:
{
lean_object* v___f_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___f_2296_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2296_, 0, v_inst_2293_);
lean_closure_set(v___f_2296_, 1, v_a_2294_);
v___x_2297_ = lean_unsigned_to_nat(0u);
v___x_2298_ = l_List_countP_go___redArg(v___f_2296_, v_l_2295_, v___x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_List_count(lean_object* v_00_u03b1_2299_, lean_object* v_inst_2300_, lean_object* v_a_2301_, lean_object* v_l_2302_){
_start:
{
lean_object* v___f_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___f_2303_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2303_, 0, v_inst_2300_);
lean_closure_set(v___f_2303_, 1, v_a_2301_);
v___x_2304_ = lean_unsigned_to_nat(0u);
v___x_2305_ = l_List_countP_go___redArg(v___f_2303_, v_l_2302_, v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___redArg(lean_object* v_inst_2306_, lean_object* v_x_2307_, lean_object* v_x_2308_){
_start:
{
if (lean_obj_tag(v_x_2308_) == 0)
{
lean_object* v___x_2309_; 
lean_dec(v_x_2307_);
lean_dec_ref(v_inst_2306_);
v___x_2309_ = lean_box(0);
return v___x_2309_;
}
else
{
lean_object* v_head_2310_; lean_object* v_tail_2311_; lean_object* v_fst_2312_; lean_object* v_snd_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v_head_2310_ = lean_ctor_get(v_x_2308_, 0);
lean_inc(v_head_2310_);
v_tail_2311_ = lean_ctor_get(v_x_2308_, 1);
lean_inc(v_tail_2311_);
lean_dec_ref_known(v_x_2308_, 2);
v_fst_2312_ = lean_ctor_get(v_head_2310_, 0);
lean_inc(v_fst_2312_);
v_snd_2313_ = lean_ctor_get(v_head_2310_, 1);
lean_inc(v_snd_2313_);
lean_dec(v_head_2310_);
lean_inc_ref(v_inst_2306_);
lean_inc(v_x_2307_);
v___x_2314_ = lean_apply_2(v_inst_2306_, v_x_2307_, v_fst_2312_);
v___x_2315_ = lean_unbox(v___x_2314_);
if (v___x_2315_ == 0)
{
lean_dec(v_snd_2313_);
v_x_2308_ = v_tail_2311_;
goto _start;
}
else
{
lean_object* v___x_2317_; 
lean_dec(v_tail_2311_);
lean_dec(v_x_2307_);
lean_dec_ref(v_inst_2306_);
v___x_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2317_, 0, v_snd_2313_);
return v___x_2317_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup(lean_object* v_00_u03b1_2318_, lean_object* v_00_u03b2_2319_, lean_object* v_inst_2320_, lean_object* v_x_2321_, lean_object* v_x_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_List_lookup___redArg(v_inst_2320_, v_x_2321_, v_x_2322_);
return v___x_2323_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0));
v___x_2342_ = l_String_toRawSubstring_x27(v___x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object* v_x_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
lean_inc(v_x_2362_);
v___x_2366_ = l_Lean_Syntax_isOfKind(v_x_2362_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_dec(v_x_2362_);
v___x_2367_ = lean_box(1);
v___x_2368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v_a_2364_);
return v___x_2368_;
}
else
{
lean_object* v_quotContext_2369_; lean_object* v_currMacroScope_2370_; lean_object* v_ref_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_quotContext_2369_ = lean_ctor_get(v_a_2363_, 1);
v_currMacroScope_2370_ = lean_ctor_get(v_a_2363_, 2);
v_ref_2371_ = lean_ctor_get(v_a_2363_, 5);
v___x_2372_ = lean_unsigned_to_nat(0u);
v___x_2373_ = l_Lean_Syntax_getArg(v_x_2362_, v___x_2372_);
v___x_2374_ = lean_unsigned_to_nat(2u);
v___x_2375_ = l_Lean_Syntax_getArg(v_x_2362_, v___x_2374_);
lean_dec(v_x_2362_);
v___x_2376_ = 0;
v___x_2377_ = l_Lean_SourceInfo_fromRef(v_ref_2371_, v___x_2376_);
v___x_2378_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_2379_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
v___x_2380_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2));
lean_inc(v_currMacroScope_2370_);
lean_inc(v_quotContext_2369_);
v___x_2381_ = l_Lean_addMacroScope(v_quotContext_2369_, v___x_2380_, v_currMacroScope_2370_);
v___x_2382_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8));
lean_inc_n(v___x_2377_, 2);
v___x_2383_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2377_);
lean_ctor_set(v___x_2383_, 1, v___x_2379_);
lean_ctor_set(v___x_2383_, 2, v___x_2381_);
lean_ctor_set(v___x_2383_, 3, v___x_2382_);
v___x_2384_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_2385_ = l_Lean_Syntax_node2(v___x_2377_, v___x_2384_, v___x_2373_, v___x_2375_);
v___x_2386_ = l_Lean_Syntax_node2(v___x_2377_, v___x_2378_, v___x_2383_, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v_a_2364_);
return v___x_2387_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___boxed(lean_object* v_x_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(v_x_2388_, v_a_2389_, v_a_2390_);
lean_dec_ref(v_a_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object* v_x_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_2392_);
v___x_2396_ = l_Lean_Syntax_isOfKind(v_x_2392_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec(v_x_2392_);
v___x_2397_ = lean_box(0);
v___x_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
lean_ctor_set(v___x_2398_, 1, v_a_2394_);
return v___x_2398_;
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2400_ = l_Lean_Syntax_getArg(v_x_2392_, v___x_2399_);
v___x_2401_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_2400_);
v___x_2402_ = l_Lean_Syntax_isOfKind(v___x_2400_, v___x_2401_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
lean_dec(v___x_2400_);
lean_dec(v_x_2392_);
v___x_2403_ = lean_box(0);
v___x_2404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v_a_2394_);
return v___x_2404_;
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = l_Lean_Syntax_getArg(v_x_2392_, v___x_2405_);
lean_dec(v_x_2392_);
v___x_2407_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2406_);
v___x_2408_ = l_Lean_Syntax_matchesNull(v___x_2406_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec(v___x_2406_);
lean_dec(v___x_2400_);
v___x_2409_ = lean_box(0);
v___x_2410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
lean_ctor_set(v___x_2410_, 1, v_a_2394_);
return v___x_2410_;
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v_ref_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2411_ = l_Lean_Syntax_getArg(v___x_2406_, v___x_2399_);
v___x_2412_ = l_Lean_Syntax_getArg(v___x_2406_, v___x_2405_);
lean_dec(v___x_2406_);
v_ref_2413_ = l_Lean_replaceRef(v___x_2400_, v_a_2393_);
lean_dec(v___x_2400_);
v___x_2414_ = 0;
v___x_2415_ = l_Lean_SourceInfo_fromRef(v_ref_2413_, v___x_2414_);
lean_dec(v_ref_2413_);
v___x_2416_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
v___x_2417_ = ((lean_object*)(l_List_term___x7e___00__closed__2));
lean_inc(v___x_2415_);
v___x_2418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2415_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_node3(v___x_2415_, v___x_2416_, v___x_2411_, v___x_2418_, v___x_2412_);
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v_a_2394_);
return v___x_2420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object* v_x_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(v_x_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2422_);
return v_res_2424_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm___redArg(lean_object* v_inst_2425_, lean_object* v_x_2426_, lean_object* v_x_2427_){
_start:
{
if (lean_obj_tag(v_x_2426_) == 0)
{
uint8_t v___x_2428_; 
lean_dec_ref(v_inst_2425_);
v___x_2428_ = l_List_isEmpty___redArg(v_x_2427_);
lean_dec(v_x_2427_);
return v___x_2428_;
}
else
{
lean_object* v_head_2429_; lean_object* v_tail_2430_; uint8_t v___x_2431_; 
v_head_2429_ = lean_ctor_get(v_x_2426_, 0);
lean_inc_n(v_head_2429_, 2);
v_tail_2430_ = lean_ctor_get(v_x_2426_, 1);
lean_inc(v_tail_2430_);
lean_dec_ref_known(v_x_2426_, 2);
lean_inc(v_x_2427_);
lean_inc_ref(v_inst_2425_);
v___x_2431_ = l_List_elem___redArg(v_inst_2425_, v_head_2429_, v_x_2427_);
if (v___x_2431_ == 0)
{
lean_dec(v_tail_2430_);
lean_dec(v_head_2429_);
lean_dec(v_x_2427_);
lean_dec_ref(v_inst_2425_);
return v___x_2431_;
}
else
{
lean_object* v___x_2432_; 
lean_inc_ref(v_inst_2425_);
v___x_2432_ = l_List_erase___redArg(v_inst_2425_, v_x_2427_, v_head_2429_);
v_x_2426_ = v_tail_2430_;
v_x_2427_ = v___x_2432_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPerm___redArg___boxed(lean_object* v_inst_2434_, lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
uint8_t v_res_2437_; lean_object* v_r_2438_; 
v_res_2437_ = l_List_isPerm___redArg(v_inst_2434_, v_x_2435_, v_x_2436_);
v_r_2438_ = lean_box(v_res_2437_);
return v_r_2438_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm(lean_object* v_00_u03b1_2439_, lean_object* v_inst_2440_, lean_object* v_x_2441_, lean_object* v_x_2442_){
_start:
{
uint8_t v___x_2443_; 
v___x_2443_ = l_List_isPerm___redArg(v_inst_2440_, v_x_2441_, v_x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_List_isPerm___boxed(lean_object* v_00_u03b1_2444_, lean_object* v_inst_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
uint8_t v_res_2448_; lean_object* v_r_2449_; 
v_res_2448_ = l_List_isPerm(v_00_u03b1_2444_, v_inst_2445_, v_x_2446_, v_x_2447_);
v_r_2449_ = lean_box(v_res_2448_);
return v_r_2449_;
}
}
LEAN_EXPORT uint8_t l_List_any___redArg(lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
if (lean_obj_tag(v_x_2450_) == 0)
{
uint8_t v___x_2452_; 
lean_dec_ref(v_x_2451_);
v___x_2452_ = 0;
return v___x_2452_;
}
else
{
lean_object* v_head_2453_; lean_object* v_tail_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v_head_2453_ = lean_ctor_get(v_x_2450_, 0);
lean_inc(v_head_2453_);
v_tail_2454_ = lean_ctor_get(v_x_2450_, 1);
lean_inc(v_tail_2454_);
lean_dec_ref_known(v_x_2450_, 2);
lean_inc_ref(v_x_2451_);
v___x_2455_ = lean_apply_1(v_x_2451_, v_head_2453_);
v___x_2456_ = lean_unbox(v___x_2455_);
if (v___x_2456_ == 0)
{
v_x_2450_ = v_tail_2454_;
goto _start;
}
else
{
uint8_t v___x_2458_; 
lean_dec(v_tail_2454_);
lean_dec_ref(v_x_2451_);
v___x_2458_ = lean_unbox(v___x_2455_);
return v___x_2458_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___redArg___boxed(lean_object* v_x_2459_, lean_object* v_x_2460_){
_start:
{
uint8_t v_res_2461_; lean_object* v_r_2462_; 
v_res_2461_ = l_List_any___redArg(v_x_2459_, v_x_2460_);
v_r_2462_ = lean_box(v_res_2461_);
return v_r_2462_;
}
}
LEAN_EXPORT uint8_t l_List_any(lean_object* v_00_u03b1_2463_, lean_object* v_x_2464_, lean_object* v_x_2465_){
_start:
{
uint8_t v___x_2466_; 
v___x_2466_ = l_List_any___redArg(v_x_2464_, v_x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_List_any___boxed(lean_object* v_00_u03b1_2467_, lean_object* v_x_2468_, lean_object* v_x_2469_){
_start:
{
uint8_t v_res_2470_; lean_object* v_r_2471_; 
v_res_2470_ = l_List_any(v_00_u03b1_2467_, v_x_2468_, v_x_2469_);
v_r_2471_ = lean_box(v_res_2470_);
return v_r_2471_;
}
}
LEAN_EXPORT uint8_t l_List_all___redArg(lean_object* v_x_2472_, lean_object* v_x_2473_){
_start:
{
if (lean_obj_tag(v_x_2472_) == 0)
{
uint8_t v___x_2474_; 
lean_dec_ref(v_x_2473_);
v___x_2474_ = 1;
return v___x_2474_;
}
else
{
lean_object* v_head_2475_; lean_object* v_tail_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; 
v_head_2475_ = lean_ctor_get(v_x_2472_, 0);
lean_inc(v_head_2475_);
v_tail_2476_ = lean_ctor_get(v_x_2472_, 1);
lean_inc(v_tail_2476_);
lean_dec_ref_known(v_x_2472_, 2);
lean_inc_ref(v_x_2473_);
v___x_2477_ = lean_apply_1(v_x_2473_, v_head_2475_);
v___x_2478_ = lean_unbox(v___x_2477_);
if (v___x_2478_ == 0)
{
uint8_t v___x_2479_; 
lean_dec(v_tail_2476_);
lean_dec_ref(v_x_2473_);
v___x_2479_ = lean_unbox(v___x_2477_);
return v___x_2479_;
}
else
{
v_x_2472_ = v_tail_2476_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___redArg___boxed(lean_object* v_x_2481_, lean_object* v_x_2482_){
_start:
{
uint8_t v_res_2483_; lean_object* v_r_2484_; 
v_res_2483_ = l_List_all___redArg(v_x_2481_, v_x_2482_);
v_r_2484_ = lean_box(v_res_2483_);
return v_r_2484_;
}
}
LEAN_EXPORT uint8_t l_List_all(lean_object* v_00_u03b1_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_){
_start:
{
uint8_t v___x_2488_; 
v___x_2488_ = l_List_all___redArg(v_x_2486_, v_x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_List_all___boxed(lean_object* v_00_u03b1_2489_, lean_object* v_x_2490_, lean_object* v_x_2491_){
_start:
{
uint8_t v_res_2492_; lean_object* v_r_2493_; 
v_res_2492_ = l_List_all(v_00_u03b1_2489_, v_x_2490_, v_x_2491_);
v_r_2493_ = lean_box(v_res_2492_);
return v_r_2493_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_or_spec__0(lean_object* v_x_2494_){
_start:
{
if (lean_obj_tag(v_x_2494_) == 0)
{
uint8_t v___x_2495_; 
v___x_2495_ = 0;
return v___x_2495_;
}
else
{
lean_object* v_head_2496_; uint8_t v___x_2497_; 
v_head_2496_ = lean_ctor_get(v_x_2494_, 0);
v___x_2497_ = lean_unbox(v_head_2496_);
if (v___x_2497_ == 0)
{
lean_object* v_tail_2498_; 
v_tail_2498_ = lean_ctor_get(v_x_2494_, 1);
v_x_2494_ = v_tail_2498_;
goto _start;
}
else
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_unbox(v_head_2496_);
return v___x_2500_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_or_spec__0___boxed(lean_object* v_x_2501_){
_start:
{
uint8_t v_res_2502_; lean_object* v_r_2503_; 
v_res_2502_ = l_List_any___at___00List_or_spec__0(v_x_2501_);
lean_dec(v_x_2501_);
v_r_2503_ = lean_box(v_res_2502_);
return v_r_2503_;
}
}
LEAN_EXPORT uint8_t l_List_or(lean_object* v_bs_2504_){
_start:
{
uint8_t v___x_2505_; 
v___x_2505_ = l_List_any___at___00List_or_spec__0(v_bs_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object* v_bs_2506_){
_start:
{
uint8_t v_res_2507_; lean_object* v_r_2508_; 
v_res_2507_ = l_List_or(v_bs_2506_);
lean_dec(v_bs_2506_);
v_r_2508_ = lean_box(v_res_2507_);
return v_r_2508_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00List_and_spec__0(lean_object* v_x_2509_){
_start:
{
if (lean_obj_tag(v_x_2509_) == 0)
{
uint8_t v___x_2510_; 
v___x_2510_ = 1;
return v___x_2510_;
}
else
{
lean_object* v_head_2511_; uint8_t v___x_2512_; 
v_head_2511_ = lean_ctor_get(v_x_2509_, 0);
v___x_2512_ = lean_unbox(v_head_2511_);
if (v___x_2512_ == 0)
{
uint8_t v___x_2513_; 
v___x_2513_ = lean_unbox(v_head_2511_);
return v___x_2513_;
}
else
{
lean_object* v_tail_2514_; 
v_tail_2514_ = lean_ctor_get(v_x_2509_, 1);
v_x_2509_ = v_tail_2514_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00List_and_spec__0___boxed(lean_object* v_x_2516_){
_start:
{
uint8_t v_res_2517_; lean_object* v_r_2518_; 
v_res_2517_ = l_List_all___at___00List_and_spec__0(v_x_2516_);
lean_dec(v_x_2516_);
v_r_2518_ = lean_box(v_res_2517_);
return v_r_2518_;
}
}
LEAN_EXPORT uint8_t l_List_and(lean_object* v_bs_2519_){
_start:
{
uint8_t v___x_2520_; 
v___x_2520_ = l_List_all___at___00List_and_spec__0(v_bs_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object* v_bs_2521_){
_start:
{
uint8_t v_res_2522_; lean_object* v_r_2523_; 
v_res_2522_ = l_List_and(v_bs_2521_);
lean_dec(v_bs_2521_);
v_r_2523_ = lean_box(v_res_2522_);
return v_r_2523_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___redArg(lean_object* v_f_2524_, lean_object* v_x_2525_, lean_object* v_x_2526_){
_start:
{
if (lean_obj_tag(v_x_2525_) == 0)
{
lean_object* v___x_2527_; 
lean_dec(v_x_2526_);
lean_dec(v_f_2524_);
v___x_2527_ = lean_box(0);
return v___x_2527_;
}
else
{
if (lean_obj_tag(v_x_2526_) == 0)
{
lean_object* v___x_2528_; 
lean_dec_ref_known(v_x_2525_, 2);
lean_dec(v_f_2524_);
v___x_2528_ = lean_box(0);
return v___x_2528_;
}
else
{
lean_object* v_head_2529_; lean_object* v_tail_2530_; lean_object* v_head_2531_; lean_object* v_tail_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2541_; 
v_head_2529_ = lean_ctor_get(v_x_2525_, 0);
lean_inc(v_head_2529_);
v_tail_2530_ = lean_ctor_get(v_x_2525_, 1);
lean_inc(v_tail_2530_);
lean_dec_ref_known(v_x_2525_, 2);
v_head_2531_ = lean_ctor_get(v_x_2526_, 0);
v_tail_2532_ = lean_ctor_get(v_x_2526_, 1);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_x_2526_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2534_ = v_x_2526_;
v_isShared_2535_ = v_isSharedCheck_2541_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_tail_2532_);
lean_inc(v_head_2531_);
lean_dec(v_x_2526_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2541_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
lean_inc(v_f_2524_);
v___x_2536_ = lean_apply_2(v_f_2524_, v_head_2529_, v_head_2531_);
v___x_2537_ = l_List_zipWith___redArg(v_f_2524_, v_tail_2530_, v_tail_2532_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v___x_2537_);
lean_ctor_set(v___x_2534_, 0, v___x_2536_);
v___x_2539_ = v___x_2534_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith(lean_object* v_00_u03b1_2542_, lean_object* v_00_u03b2_2543_, lean_object* v_00_u03b3_2544_, lean_object* v_f_2545_, lean_object* v_x_2546_, lean_object* v_x_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_List_zipWith___redArg(v_f_2545_, v_x_2546_, v_x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object* v_x_2549_, lean_object* v_x_2550_, lean_object* v_h__1_2551_, lean_object* v_h__2_2552_){
_start:
{
if (lean_obj_tag(v_x_2549_) == 0)
{
lean_object* v___x_2553_; 
lean_dec(v_h__1_2551_);
v___x_2553_ = lean_apply_3(v_h__2_2552_, v_x_2549_, v_x_2550_, lean_box(0));
return v___x_2553_;
}
else
{
if (lean_obj_tag(v_x_2550_) == 0)
{
lean_object* v___x_2554_; 
lean_dec(v_h__1_2551_);
v___x_2554_ = lean_apply_3(v_h__2_2552_, v_x_2549_, v_x_2550_, lean_box(0));
return v___x_2554_;
}
else
{
lean_object* v_head_2555_; lean_object* v_tail_2556_; lean_object* v_head_2557_; lean_object* v_tail_2558_; lean_object* v___x_2559_; 
lean_dec(v_h__2_2552_);
v_head_2555_ = lean_ctor_get(v_x_2549_, 0);
lean_inc(v_head_2555_);
v_tail_2556_ = lean_ctor_get(v_x_2549_, 1);
lean_inc(v_tail_2556_);
lean_dec_ref_known(v_x_2549_, 2);
v_head_2557_ = lean_ctor_get(v_x_2550_, 0);
lean_inc(v_head_2557_);
v_tail_2558_ = lean_ctor_get(v_x_2550_, 1);
lean_inc(v_tail_2558_);
lean_dec_ref_known(v_x_2550_, 2);
v___x_2559_ = lean_apply_4(v_h__1_2551_, v_head_2555_, v_tail_2556_, v_head_2557_, v_tail_2558_);
return v___x_2559_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object* v_00_u03b1_2560_, lean_object* v_00_u03b2_2561_, lean_object* v_motive_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_, lean_object* v_h__1_2565_, lean_object* v_h__2_2566_){
_start:
{
if (lean_obj_tag(v_x_2563_) == 0)
{
lean_object* v___x_2567_; 
lean_dec(v_h__1_2565_);
v___x_2567_ = lean_apply_3(v_h__2_2566_, v_x_2563_, v_x_2564_, lean_box(0));
return v___x_2567_;
}
else
{
if (lean_obj_tag(v_x_2564_) == 0)
{
lean_object* v___x_2568_; 
lean_dec(v_h__1_2565_);
v___x_2568_ = lean_apply_3(v_h__2_2566_, v_x_2563_, v_x_2564_, lean_box(0));
return v___x_2568_;
}
else
{
lean_object* v_head_2569_; lean_object* v_tail_2570_; lean_object* v_head_2571_; lean_object* v_tail_2572_; lean_object* v___x_2573_; 
lean_dec(v_h__2_2566_);
v_head_2569_ = lean_ctor_get(v_x_2563_, 0);
lean_inc(v_head_2569_);
v_tail_2570_ = lean_ctor_get(v_x_2563_, 1);
lean_inc(v_tail_2570_);
lean_dec_ref_known(v_x_2563_, 2);
v_head_2571_ = lean_ctor_get(v_x_2564_, 0);
lean_inc(v_head_2571_);
v_tail_2572_ = lean_ctor_get(v_x_2564_, 1);
lean_inc(v_tail_2572_);
lean_dec_ref_known(v_x_2564_, 2);
v___x_2573_ = lean_apply_4(v_h__1_2565_, v_head_2569_, v_tail_2570_, v_head_2571_, v_tail_2572_);
return v___x_2573_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object* v_x_2574_, lean_object* v_x_2575_){
_start:
{
if (lean_obj_tag(v_x_2574_) == 0)
{
lean_object* v___x_2576_; 
lean_dec(v_x_2575_);
v___x_2576_ = lean_box(0);
return v___x_2576_;
}
else
{
if (lean_obj_tag(v_x_2575_) == 0)
{
lean_object* v___x_2577_; 
lean_dec_ref_known(v_x_2574_, 2);
v___x_2577_ = lean_box(0);
return v___x_2577_;
}
else
{
lean_object* v_head_2578_; lean_object* v_tail_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2596_; 
v_head_2578_ = lean_ctor_get(v_x_2574_, 0);
v_tail_2579_ = lean_ctor_get(v_x_2574_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_x_2574_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2581_ = v_x_2574_;
v_isShared_2582_ = v_isSharedCheck_2596_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_tail_2579_);
lean_inc(v_head_2578_);
lean_dec(v_x_2574_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2596_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v_head_2583_; lean_object* v_tail_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2595_; 
v_head_2583_ = lean_ctor_get(v_x_2575_, 0);
v_tail_2584_ = lean_ctor_get(v_x_2575_, 1);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_x_2575_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2586_ = v_x_2575_;
v_isShared_2587_ = v_isSharedCheck_2595_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_tail_2584_);
lean_inc(v_head_2583_);
lean_dec(v_x_2575_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2595_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 0);
lean_ctor_set(v___x_2581_, 1, v_head_2583_);
v___x_2589_ = v___x_2581_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_head_2578_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_head_2583_);
v___x_2589_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2590_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_tail_2579_, v_tail_2584_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 1, v___x_2590_);
lean_ctor_set(v___x_2586_, 0, v___x_2589_);
v___x_2592_ = v___x_2586_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zip___redArg(lean_object* v_xs_2597_, lean_object* v_ys_2598_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2597_, v_ys_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_List_zip(lean_object* v_00_u03b1_2600_, lean_object* v_00_u03b2_2601_, lean_object* v_xs_2602_, lean_object* v_ys_2603_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2602_, v_ys_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object* v_00_u03b1_2605_, lean_object* v_00_u03b2_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_x_2607_, v_x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__0(lean_object* v_f_2610_, lean_object* v_b_2611_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_box(0);
v___x_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2613_, 0, v_b_2611_);
v___x_2614_ = lean_apply_2(v_f_2610_, v___x_2612_, v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__1(lean_object* v_f_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v_a_2616_);
v___x_2618_ = lean_box(0);
v___x_2619_ = lean_apply_2(v_f_2615_, v___x_2617_, v___x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object* v_f_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_){
_start:
{
if (lean_obj_tag(v_x_2621_) == 0)
{
lean_object* v___f_2623_; lean_object* v___x_2624_; 
v___f_2623_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2623_, 0, v_f_2620_);
v___x_2624_ = l_List_map___redArg(v___f_2623_, v_x_2622_);
return v___x_2624_;
}
else
{
if (lean_obj_tag(v_x_2622_) == 0)
{
lean_object* v___f_2625_; lean_object* v___x_2626_; 
v___f_2625_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2625_, 0, v_f_2620_);
v___x_2626_ = l_List_map___redArg(v___f_2625_, v_x_2621_);
return v___x_2626_;
}
else
{
lean_object* v_head_2627_; lean_object* v_tail_2628_; lean_object* v_head_2629_; lean_object* v_tail_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2641_; 
v_head_2627_ = lean_ctor_get(v_x_2621_, 0);
lean_inc(v_head_2627_);
v_tail_2628_ = lean_ctor_get(v_x_2621_, 1);
lean_inc(v_tail_2628_);
lean_dec_ref_known(v_x_2621_, 2);
v_head_2629_ = lean_ctor_get(v_x_2622_, 0);
v_tail_2630_ = lean_ctor_get(v_x_2622_, 1);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_x_2622_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2632_ = v_x_2622_;
v_isShared_2633_ = v_isSharedCheck_2641_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_tail_2630_);
lean_inc(v_head_2629_);
lean_dec(v_x_2622_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2641_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_head_2627_);
v___x_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2635_, 0, v_head_2629_);
lean_inc(v_f_2620_);
v___x_2636_ = lean_apply_2(v_f_2620_, v___x_2634_, v___x_2635_);
v___x_2637_ = l_List_zipWithAll___redArg(v_f_2620_, v_tail_2628_, v_tail_2630_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 1, v___x_2637_);
lean_ctor_set(v___x_2632_, 0, v___x_2636_);
v___x_2639_ = v___x_2632_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object* v_00_u03b1_2642_, lean_object* v_00_u03b2_2643_, lean_object* v_00_u03b3_2644_, lean_object* v_f_2645_, lean_object* v_x_2646_, lean_object* v_x_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_List_zipWithAll___redArg(v_f_2645_, v_x_2646_, v_x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_List_unzip___redArg(lean_object* v_x_2649_){
_start:
{
if (lean_obj_tag(v_x_2649_) == 0)
{
lean_object* v___x_2650_; 
v___x_2650_ = ((lean_object*)(l_List_partition___redArg___closed__0));
return v___x_2650_;
}
else
{
lean_object* v_head_2651_; lean_object* v_tail_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2678_; 
v_head_2651_ = lean_ctor_get(v_x_2649_, 0);
v_tail_2652_ = lean_ctor_get(v_x_2649_, 1);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_x_2649_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2654_ = v_x_2649_;
v_isShared_2655_ = v_isSharedCheck_2678_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_tail_2652_);
lean_inc(v_head_2651_);
lean_dec(v_x_2649_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2678_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v_fst_2656_; lean_object* v_snd_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2677_; 
v_fst_2656_ = lean_ctor_get(v_head_2651_, 0);
v_snd_2657_ = lean_ctor_get(v_head_2651_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_head_2651_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2659_ = v_head_2651_;
v_isShared_2660_ = v_isSharedCheck_2677_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_snd_2657_);
lean_inc(v_fst_2656_);
lean_dec(v_head_2651_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2677_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v_fst_2662_; lean_object* v_snd_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2676_; 
v___x_2661_ = l_List_unzip___redArg(v_tail_2652_);
v_fst_2662_ = lean_ctor_get(v___x_2661_, 0);
v_snd_2663_ = lean_ctor_get(v___x_2661_, 1);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2665_ = v___x_2661_;
v_isShared_2666_ = v_isSharedCheck_2676_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_snd_2663_);
lean_inc(v_fst_2662_);
lean_dec(v___x_2661_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2676_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 1, v_fst_2662_);
lean_ctor_set(v___x_2654_, 0, v_fst_2656_);
v___x_2668_ = v___x_2654_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_fst_2656_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_fst_2662_);
v___x_2668_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2670_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set_tag(v___x_2659_, 1);
lean_ctor_set(v___x_2659_, 1, v_snd_2663_);
lean_ctor_set(v___x_2659_, 0, v_snd_2657_);
v___x_2670_ = v___x_2659_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_snd_2657_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_snd_2663_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 1, v___x_2670_);
lean_ctor_set(v___x_2665_, 0, v___x_2668_);
v___x_2672_ = v___x_2665_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_unzip(lean_object* v_00_u03b1_2679_, lean_object* v_00_u03b2_2680_, lean_object* v_x_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_List_unzip___redArg(v_x_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___lam__0(lean_object* v_inst_2683_, lean_object* v_x1_2684_, lean_object* v_x2_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = lean_apply_2(v_inst_2683_, v_x1_2684_, v_x2_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg(lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_l_2689_){
_start:
{
lean_object* v___f_2690_; lean_object* v___x_2691_; 
v___f_2690_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2690_, 0, v_inst_2687_);
v___x_2691_ = l_List_foldr___redArg(v___f_2690_, v_inst_2688_, v_l_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___boxed(lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_l_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_List_sum___redArg(v_inst_2692_, v_inst_2693_, v_l_2694_);
lean_dec(v_inst_2693_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_List_sum(lean_object* v_00_u03b1_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_l_2699_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_List_sum___redArg(v_inst_2697_, v_inst_2698_, v_l_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_List_sum___boxed(lean_object* v_00_u03b1_2701_, lean_object* v_inst_2702_, lean_object* v_inst_2703_, lean_object* v_l_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_List_sum(v_00_u03b1_2701_, v_inst_2702_, v_inst_2703_, v_l_2704_);
lean_dec(v_inst_2703_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg(lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_l_2708_){
_start:
{
lean_object* v___f_2709_; lean_object* v___x_2710_; 
v___f_2709_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2709_, 0, v_inst_2706_);
v___x_2710_ = l_List_foldr___redArg(v___f_2709_, v_inst_2707_, v_l_2708_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg___boxed(lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_l_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_List_prod___redArg(v_inst_2711_, v_inst_2712_, v_l_2713_);
lean_dec(v_inst_2712_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_List_prod(lean_object* v_00_u03b1_2715_, lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_l_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_List_prod___redArg(v_inst_2716_, v_inst_2717_, v_l_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_List_prod___boxed(lean_object* v_00_u03b1_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_l_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_List_prod(v_00_u03b1_2720_, v_inst_2721_, v_inst_2722_, v_l_2723_);
lean_dec(v_inst_2722_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_List_range_loop(lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_zero_2727_; uint8_t v_isZero_2728_; 
v_zero_2727_ = lean_unsigned_to_nat(0u);
v_isZero_2728_ = lean_nat_dec_eq(v_a_2725_, v_zero_2727_);
if (v_isZero_2728_ == 1)
{
lean_dec(v_a_2725_);
return v_a_2726_;
}
else
{
lean_object* v_one_2729_; lean_object* v_n_2730_; lean_object* v___x_2731_; 
v_one_2729_ = lean_unsigned_to_nat(1u);
v_n_2730_ = lean_nat_sub(v_a_2725_, v_one_2729_);
lean_dec(v_a_2725_);
lean_inc(v_n_2730_);
v___x_2731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2731_, 0, v_n_2730_);
lean_ctor_set(v___x_2731_, 1, v_a_2726_);
v_a_2725_ = v_n_2730_;
v_a_2726_ = v___x_2731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range(lean_object* v_n_2733_){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_box(0);
v___x_2735_ = l_List_range_loop(v_n_2733_, v___x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27(lean_object* v_x_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_){
_start:
{
lean_object* v_zero_2739_; uint8_t v_isZero_2740_; 
v_zero_2739_ = lean_unsigned_to_nat(0u);
v_isZero_2740_ = lean_nat_dec_eq(v_x_2737_, v_zero_2739_);
if (v_isZero_2740_ == 1)
{
lean_object* v___x_2741_; 
lean_dec(v_x_2736_);
v___x_2741_ = lean_box(0);
return v___x_2741_;
}
else
{
lean_object* v_one_2742_; lean_object* v_n_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_one_2742_ = lean_unsigned_to_nat(1u);
v_n_2743_ = lean_nat_sub(v_x_2737_, v_one_2742_);
v___x_2744_ = lean_nat_add(v_x_2736_, v_x_2738_);
v___x_2745_ = l_List_range_x27(v___x_2744_, v_n_2743_, v_x_2738_);
lean_dec(v_n_2743_);
v___x_2746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2746_, 0, v_x_2736_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object* v_x_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_List_range_x27(v_x_2747_, v_x_2748_, v_x_2749_);
lean_dec(v_x_2749_);
lean_dec(v_x_2748_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdx___redArg(lean_object* v_x_2751_, lean_object* v_x_2752_){
_start:
{
if (lean_obj_tag(v_x_2751_) == 0)
{
lean_object* v___x_2753_; 
lean_dec(v_x_2752_);
v___x_2753_ = lean_box(0);
return v___x_2753_;
}
else
{
lean_object* v_head_2754_; lean_object* v_tail_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2766_; 
v_head_2754_ = lean_ctor_get(v_x_2751_, 0);
v_tail_2755_ = lean_ctor_get(v_x_2751_, 1);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_x_2751_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2757_ = v_x_2751_;
v_isShared_2758_ = v_isSharedCheck_2766_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_tail_2755_);
lean_inc(v_head_2754_);
lean_dec(v_x_2751_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2766_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
lean_inc(v_x_2752_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_head_2754_);
lean_ctor_set(v___x_2759_, 1, v_x_2752_);
v___x_2760_ = lean_unsigned_to_nat(1u);
v___x_2761_ = lean_nat_add(v_x_2752_, v___x_2760_);
lean_dec(v_x_2752_);
v___x_2762_ = l_List_zipIdx___redArg(v_tail_2755_, v___x_2761_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2762_);
lean_ctor_set(v___x_2757_, 0, v___x_2759_);
v___x_2764_ = v___x_2757_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2759_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdx(lean_object* v_00_u03b1_2767_, lean_object* v_x_2768_, lean_object* v_x_2769_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_List_zipIdx___redArg(v_x_2768_, v_x_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object* v_inst_2771_, lean_object* v_x_2772_){
_start:
{
if (lean_obj_tag(v_x_2772_) == 0)
{
lean_object* v___x_2773_; 
lean_dec(v_inst_2771_);
v___x_2773_ = lean_box(0);
return v___x_2773_;
}
else
{
lean_object* v_head_2774_; lean_object* v_tail_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v_head_2774_ = lean_ctor_get(v_x_2772_, 0);
lean_inc(v_head_2774_);
v_tail_2775_ = lean_ctor_get(v_x_2772_, 1);
lean_inc(v_tail_2775_);
lean_dec_ref_known(v_x_2772_, 2);
v___x_2776_ = l_List_foldl___redArg(v_inst_2771_, v_head_2774_, v_tail_2775_);
v___x_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
return v___x_2777_;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object* v_00_u03b1_2778_, lean_object* v_inst_2779_, lean_object* v_x_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_List_min_x3f___redArg(v_inst_2779_, v_x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object* v_inst_2782_, lean_object* v_x_2783_){
_start:
{
lean_object* v_head_2784_; lean_object* v_tail_2785_; lean_object* v___x_2786_; 
v_head_2784_ = lean_ctor_get(v_x_2783_, 0);
lean_inc(v_head_2784_);
v_tail_2785_ = lean_ctor_get(v_x_2783_, 1);
lean_inc(v_tail_2785_);
lean_dec(v_x_2783_);
v___x_2786_ = l_List_foldl___redArg(v_inst_2782_, v_head_2784_, v_tail_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_List_min(lean_object* v_00_u03b1_2787_, lean_object* v_inst_2788_, lean_object* v_x_2789_, lean_object* v_x_2790_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_List_min___redArg(v_inst_2788_, v_x_2789_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object* v_inst_2792_, lean_object* v_x_2793_){
_start:
{
if (lean_obj_tag(v_x_2793_) == 0)
{
lean_object* v___x_2794_; 
lean_dec(v_inst_2792_);
v___x_2794_ = lean_box(0);
return v___x_2794_;
}
else
{
lean_object* v_head_2795_; lean_object* v_tail_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_head_2795_ = lean_ctor_get(v_x_2793_, 0);
lean_inc(v_head_2795_);
v_tail_2796_ = lean_ctor_get(v_x_2793_, 1);
lean_inc(v_tail_2796_);
lean_dec_ref_known(v_x_2793_, 2);
v___x_2797_ = l_List_foldl___redArg(v_inst_2792_, v_head_2795_, v_tail_2796_);
v___x_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
return v___x_2798_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object* v_00_u03b1_2799_, lean_object* v_inst_2800_, lean_object* v_x_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_List_max_x3f___redArg(v_inst_2800_, v_x_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object* v_inst_2803_, lean_object* v_x_2804_){
_start:
{
lean_object* v_head_2805_; lean_object* v_tail_2806_; lean_object* v___x_2807_; 
v_head_2805_ = lean_ctor_get(v_x_2804_, 0);
lean_inc(v_head_2805_);
v_tail_2806_ = lean_ctor_get(v_x_2804_, 1);
lean_inc(v_tail_2806_);
lean_dec(v_x_2804_);
v___x_2807_ = l_List_foldl___redArg(v_inst_2803_, v_head_2805_, v_tail_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_List_max(lean_object* v_00_u03b1_2808_, lean_object* v_inst_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_List_max___redArg(v_inst_2809_, v_x_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_List_intersperse___redArg(lean_object* v_sep_2813_, lean_object* v_x_2814_){
_start:
{
if (lean_obj_tag(v_x_2814_) == 0)
{
lean_dec(v_sep_2813_);
return v_x_2814_;
}
else
{
lean_object* v_tail_2815_; 
v_tail_2815_ = lean_ctor_get(v_x_2814_, 1);
if (lean_obj_tag(v_tail_2815_) == 0)
{
lean_dec(v_sep_2813_);
return v_x_2814_;
}
else
{
lean_object* v_head_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2825_; 
lean_inc_ref(v_tail_2815_);
v_head_2816_ = lean_ctor_get(v_x_2814_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_x_2814_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v_x_2814_, 1);
lean_dec(v_unused_2826_);
v___x_2818_ = v_x_2814_;
v_isShared_2819_ = v_isSharedCheck_2825_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_head_2816_);
lean_dec(v_x_2814_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2825_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
lean_inc(v_sep_2813_);
v___x_2820_ = l_List_intersperse___redArg(v_sep_2813_, v_tail_2815_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 1, v___x_2820_);
lean_ctor_set(v___x_2818_, 0, v_sep_2813_);
v___x_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_sep_2813_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2823_; 
v___x_2823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2823_, 0, v_head_2816_);
lean_ctor_set(v___x_2823_, 1, v___x_2822_);
return v___x_2823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperse(lean_object* v_00_u03b1_2827_, lean_object* v_sep_2828_, lean_object* v_x_2829_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_List_intersperse___redArg(v_sep_2828_, v_x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(lean_object* v___x_2831_, lean_object* v_x_2832_){
_start:
{
if (lean_obj_tag(v_x_2832_) == 0)
{
uint8_t v___x_2833_; 
lean_dec_ref(v___x_2831_);
v___x_2833_ = 0;
return v___x_2833_;
}
else
{
lean_object* v_head_2834_; lean_object* v_tail_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v_head_2834_ = lean_ctor_get(v_x_2832_, 0);
lean_inc(v_head_2834_);
v_tail_2835_ = lean_ctor_get(v_x_2832_, 1);
lean_inc(v_tail_2835_);
lean_dec_ref_known(v_x_2832_, 2);
lean_inc_ref(v___x_2831_);
v___x_2836_ = lean_apply_1(v___x_2831_, v_head_2834_);
v___x_2837_ = lean_unbox(v___x_2836_);
if (v___x_2837_ == 0)
{
v_x_2832_ = v_tail_2835_;
goto _start;
}
else
{
uint8_t v___x_2839_; 
lean_dec(v_tail_2835_);
lean_dec_ref(v___x_2831_);
v___x_2839_ = lean_unbox(v___x_2836_);
return v___x_2839_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg___boxed(lean_object* v___x_2840_, lean_object* v_x_2841_){
_start:
{
uint8_t v_res_2842_; lean_object* v_r_2843_; 
v_res_2842_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2840_, v_x_2841_);
v_r_2843_ = lean_box(v_res_2842_);
return v_r_2843_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object* v_r_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
if (lean_obj_tag(v_a_2845_) == 0)
{
lean_object* v___x_2847_; 
lean_dec_ref(v_r_2844_);
v___x_2847_ = l_List_reverse___redArg(v_a_2846_);
return v___x_2847_;
}
else
{
lean_object* v_head_2848_; lean_object* v_tail_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2860_; 
v_head_2848_ = lean_ctor_get(v_a_2845_, 0);
v_tail_2849_ = lean_ctor_get(v_a_2845_, 1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_a_2845_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2851_ = v_a_2845_;
v_isShared_2852_ = v_isSharedCheck_2860_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_tail_2849_);
lean_inc(v_head_2848_);
lean_dec(v_a_2845_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2860_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; uint8_t v___x_2854_; 
lean_inc_ref(v_r_2844_);
lean_inc(v_head_2848_);
v___x_2853_ = lean_apply_1(v_r_2844_, v_head_2848_);
lean_inc(v_a_2846_);
v___x_2854_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2853_, v_a_2846_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2856_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_a_2846_);
v___x_2856_ = v___x_2851_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_head_2848_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_a_2846_);
v___x_2856_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
v_a_2845_ = v_tail_2849_;
v_a_2846_ = v___x_2856_;
goto _start;
}
}
else
{
lean_del_object(v___x_2851_);
lean_dec(v_head_2848_);
v_a_2845_ = v_tail_2849_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object* v_00_u03b1_2861_, lean_object* v_r_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_List_eraseDupsBy_loop___redArg(v_r_2862_, v_a_2863_, v_a_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0(lean_object* v_00_u03b1_2866_, lean_object* v___x_2867_, lean_object* v_x_2868_){
_start:
{
uint8_t v___x_2869_; 
v___x_2869_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2867_, v_x_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___boxed(lean_object* v_00_u03b1_2870_, lean_object* v___x_2871_, lean_object* v_x_2872_){
_start:
{
uint8_t v_res_2873_; lean_object* v_r_2874_; 
v_res_2873_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0(v_00_u03b1_2870_, v___x_2871_, v_x_2872_);
v_r_2874_ = lean_box(v_res_2873_);
return v_r_2874_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy___redArg(lean_object* v_r_2875_, lean_object* v_as_2876_){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = lean_box(0);
v___x_2878_ = l_List_eraseDupsBy_loop___redArg(v_r_2875_, v_as_2876_, v___x_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy(lean_object* v_00_u03b1_2879_, lean_object* v_r_2880_, lean_object* v_as_2881_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_List_eraseDupsBy___redArg(v_r_2880_, v_as_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT uint8_t l_List_eraseDups___redArg___lam__0(lean_object* v_inst_2883_, lean_object* v_x1_2884_, lean_object* v_x2_2885_){
_start:
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = lean_apply_2(v_inst_2883_, v_x1_2884_, v_x2_2885_);
v___x_2887_ = lean_unbox(v___x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg___lam__0___boxed(lean_object* v_inst_2888_, lean_object* v_x1_2889_, lean_object* v_x2_2890_){
_start:
{
uint8_t v_res_2891_; lean_object* v_r_2892_; 
v_res_2891_ = l_List_eraseDups___redArg___lam__0(v_inst_2888_, v_x1_2889_, v_x2_2890_);
v_r_2892_ = lean_box(v_res_2891_);
return v_r_2892_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg(lean_object* v_inst_2893_, lean_object* v_as_2894_){
_start:
{
lean_object* v___f_2895_; lean_object* v___x_2896_; 
v___f_2895_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2895_, 0, v_inst_2893_);
v___x_2896_ = l_List_eraseDupsBy___redArg(v___f_2895_, v_as_2894_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object* v_00_u03b1_2897_, lean_object* v_inst_2898_, lean_object* v_as_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_List_eraseDups___redArg(v_inst_2898_, v_as_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop___redArg(lean_object* v_r_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
if (lean_obj_tag(v_a_2903_) == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
lean_dec_ref(v_r_2901_);
v___x_2905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2905_, 0, v_a_2902_);
lean_ctor_set(v___x_2905_, 1, v_a_2904_);
v___x_2906_ = l_List_reverse___redArg(v___x_2905_);
return v___x_2906_;
}
else
{
lean_object* v_head_2907_; lean_object* v_tail_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2919_; 
v_head_2907_ = lean_ctor_get(v_a_2903_, 0);
v_tail_2908_ = lean_ctor_get(v_a_2903_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_a_2903_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2910_ = v_a_2903_;
v_isShared_2911_ = v_isSharedCheck_2919_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_tail_2908_);
lean_inc(v_head_2907_);
lean_dec(v_a_2903_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2919_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; uint8_t v___x_2913_; 
lean_inc_ref(v_r_2901_);
lean_inc(v_head_2907_);
lean_inc(v_a_2902_);
v___x_2912_ = lean_apply_2(v_r_2901_, v_a_2902_, v_head_2907_);
v___x_2913_ = lean_unbox(v___x_2912_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2915_; 
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 1, v_a_2904_);
lean_ctor_set(v___x_2910_, 0, v_a_2902_);
v___x_2915_ = v___x_2910_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2902_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_a_2904_);
v___x_2915_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
v_a_2902_ = v_head_2907_;
v_a_2903_ = v_tail_2908_;
v_a_2904_ = v___x_2915_;
goto _start;
}
}
else
{
lean_del_object(v___x_2910_);
lean_dec(v_head_2907_);
v_a_2903_ = v_tail_2908_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop(lean_object* v_00_u03b1_2920_, lean_object* v_r_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_List_eraseRepsBy_loop___redArg(v_r_2921_, v_a_2922_, v_a_2923_, v_a_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy___redArg(lean_object* v_r_2926_, lean_object* v_x_2927_){
_start:
{
if (lean_obj_tag(v_x_2927_) == 0)
{
lean_dec_ref(v_r_2926_);
return v_x_2927_;
}
else
{
lean_object* v_head_2928_; lean_object* v_tail_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v_head_2928_ = lean_ctor_get(v_x_2927_, 0);
lean_inc(v_head_2928_);
v_tail_2929_ = lean_ctor_get(v_x_2927_, 1);
lean_inc(v_tail_2929_);
lean_dec_ref_known(v_x_2927_, 2);
v___x_2930_ = lean_box(0);
v___x_2931_ = l_List_eraseRepsBy_loop___redArg(v_r_2926_, v_head_2928_, v_tail_2929_, v___x_2930_);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy(lean_object* v_00_u03b1_2932_, lean_object* v_r_2933_, lean_object* v_x_2934_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_List_eraseRepsBy___redArg(v_r_2933_, v_x_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___redArg(lean_object* v_inst_2936_, lean_object* v_as_2937_){
_start:
{
lean_object* v___f_2938_; lean_object* v___x_2939_; 
v___f_2938_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2938_, 0, v_inst_2936_);
v___x_2939_ = l_List_eraseRepsBy___redArg(v___f_2938_, v_as_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object* v_00_u03b1_2940_, lean_object* v_inst_2941_, lean_object* v_as_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_List_eraseReps___redArg(v_inst_2941_, v_as_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___redArg(lean_object* v_p_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
if (lean_obj_tag(v_a_2945_) == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_dec_ref(v_p_2944_);
v___x_2947_ = l_List_reverse___redArg(v_a_2946_);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v_a_2945_);
return v___x_2948_;
}
else
{
lean_object* v_head_2949_; lean_object* v_tail_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v_head_2949_ = lean_ctor_get(v_a_2945_, 0);
v_tail_2950_ = lean_ctor_get(v_a_2945_, 1);
lean_inc_ref(v_p_2944_);
lean_inc(v_head_2949_);
v___x_2951_ = lean_apply_1(v_p_2944_, v_head_2949_);
v___x_2952_ = lean_unbox(v___x_2951_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec_ref(v_p_2944_);
v___x_2953_ = l_List_reverse___redArg(v_a_2946_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set(v___x_2954_, 1, v_a_2945_);
return v___x_2954_;
}
else
{
lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2962_; 
lean_inc(v_tail_2950_);
lean_inc(v_head_2949_);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_a_2945_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; lean_object* v_unused_2964_; 
v_unused_2963_ = lean_ctor_get(v_a_2945_, 1);
lean_dec(v_unused_2963_);
v_unused_2964_ = lean_ctor_get(v_a_2945_, 0);
lean_dec(v_unused_2964_);
v___x_2956_ = v_a_2945_;
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
else
{
lean_dec(v_a_2945_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v_a_2946_);
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_head_2949_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_a_2946_);
v___x_2959_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
v_a_2945_ = v_tail_2950_;
v_a_2946_ = v___x_2959_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop(lean_object* v_00_u03b1_2965_, lean_object* v_p_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_List_span_loop___redArg(v_p_2966_, v_a_2967_, v_a_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_List_span___redArg(lean_object* v_p_2970_, lean_object* v_as_2971_){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_box(0);
v___x_2973_ = l_List_span_loop___redArg(v_p_2970_, v_as_2971_, v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_List_span(lean_object* v_00_u03b1_2974_, lean_object* v_p_2975_, lean_object* v_as_2976_){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_box(0);
v___x_2978_ = l_List_span_loop___redArg(v_p_2975_, v_as_2976_, v___x_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___redArg(lean_object* v_R_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
if (lean_obj_tag(v_a_2980_) == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec_ref(v_R_2979_);
v___x_2984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2984_, 0, v_a_2981_);
lean_ctor_set(v___x_2984_, 1, v_a_2982_);
v___x_2985_ = l_List_reverse___redArg(v___x_2984_);
v___x_2986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
lean_ctor_set(v___x_2986_, 1, v_a_2983_);
v___x_2987_ = l_List_reverse___redArg(v___x_2986_);
return v___x_2987_;
}
else
{
lean_object* v_head_2988_; lean_object* v_tail_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3006_; 
v_head_2988_ = lean_ctor_get(v_a_2980_, 0);
v_tail_2989_ = lean_ctor_get(v_a_2980_, 1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_a_2980_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2991_ = v_a_2980_;
v_isShared_2992_ = v_isSharedCheck_3006_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_tail_2989_);
lean_inc(v_head_2988_);
lean_dec(v_a_2980_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3006_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; uint8_t v___x_2994_; 
lean_inc_ref(v_R_2979_);
lean_inc(v_head_2988_);
lean_inc(v_a_2981_);
v___x_2993_ = lean_apply_2(v_R_2979_, v_a_2981_, v_head_2988_);
v___x_2994_ = lean_unbox(v___x_2993_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2995_ = lean_box(0);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v_a_2982_);
lean_ctor_set(v___x_2991_, 0, v_a_2981_);
v___x_2997_ = v___x_2991_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2981_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_a_2982_);
v___x_2997_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = l_List_reverse___redArg(v___x_2997_);
v___x_2999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
lean_ctor_set(v___x_2999_, 1, v_a_2983_);
v_a_2980_ = v_tail_2989_;
v_a_2981_ = v_head_2988_;
v_a_2982_ = v___x_2995_;
v_a_2983_ = v___x_2999_;
goto _start;
}
}
else
{
lean_object* v___x_3003_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v_a_2982_);
lean_ctor_set(v___x_2991_, 0, v_a_2981_);
v___x_3003_ = v___x_2991_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2981_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_a_2982_);
v___x_3003_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
v_a_2980_ = v_tail_2989_;
v_a_2981_ = v_head_2988_;
v_a_2982_ = v___x_3003_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop(lean_object* v_00_u03b1_3007_, lean_object* v_R_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_List_splitBy_loop___redArg(v_R_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___redArg(lean_object* v_R_3014_, lean_object* v_x_3015_){
_start:
{
if (lean_obj_tag(v_x_3015_) == 0)
{
lean_object* v___x_3016_; 
lean_dec_ref(v_R_3014_);
v___x_3016_ = lean_box(0);
return v___x_3016_;
}
else
{
lean_object* v_head_3017_; lean_object* v_tail_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_head_3017_ = lean_ctor_get(v_x_3015_, 0);
lean_inc(v_head_3017_);
v_tail_3018_ = lean_ctor_get(v_x_3015_, 1);
lean_inc(v_tail_3018_);
lean_dec_ref_known(v_x_3015_, 2);
v___x_3019_ = lean_box(0);
v___x_3020_ = l_List_splitBy_loop___redArg(v_R_3014_, v_tail_3018_, v_head_3017_, v___x_3019_, v___x_3019_);
return v___x_3020_;
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy(lean_object* v_00_u03b1_3021_, lean_object* v_R_3022_, lean_object* v_x_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_List_splitBy___redArg(v_R_3022_, v_x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___redArg___lam__0(lean_object* v_inst_3025_, lean_object* v_ys_3026_, lean_object* v_x_3027_){
_start:
{
uint8_t v___x_3028_; 
v___x_3028_ = l_List_elem___redArg(v_inst_3025_, v_x_3027_, v_ys_3026_);
if (v___x_3028_ == 0)
{
uint8_t v___x_3029_; 
v___x_3029_ = 1;
return v___x_3029_;
}
else
{
uint8_t v___x_3030_; 
v___x_3030_ = 0;
return v___x_3030_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg___lam__0___boxed(lean_object* v_inst_3031_, lean_object* v_ys_3032_, lean_object* v_x_3033_){
_start:
{
uint8_t v_res_3034_; lean_object* v_r_3035_; 
v_res_3034_ = l_List_removeAll___redArg___lam__0(v_inst_3031_, v_ys_3032_, v_x_3033_);
v_r_3035_ = lean_box(v_res_3034_);
return v_r_3035_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg(lean_object* v_inst_3036_, lean_object* v_xs_3037_, lean_object* v_ys_3038_){
_start:
{
lean_object* v___f_3039_; lean_object* v___x_3040_; 
v___f_3039_ = lean_alloc_closure((void*)(l_List_removeAll___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3039_, 0, v_inst_3036_);
lean_closure_set(v___f_3039_, 1, v_ys_3038_);
v___x_3040_ = l_List_filter___redArg(v___f_3039_, v_xs_3037_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll(lean_object* v_00_u03b1_3041_, lean_object* v_inst_3042_, lean_object* v_xs_3043_, lean_object* v_ys_3044_){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = l_List_removeAll___redArg(v_inst_3042_, v_xs_3043_, v_ys_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_3046_, lean_object* v_h__1_3047_, lean_object* v_h__2_3048_){
_start:
{
if (lean_obj_tag(v_ys_3046_) == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec(v_h__2_3048_);
v___x_3049_ = lean_box(0);
v___x_3050_ = lean_apply_1(v_h__1_3047_, v___x_3049_);
return v___x_3050_;
}
else
{
lean_object* v_head_3051_; lean_object* v_tail_3052_; lean_object* v___x_3053_; 
lean_dec(v_h__1_3047_);
v_head_3051_ = lean_ctor_get(v_ys_3046_, 0);
lean_inc(v_head_3051_);
v_tail_3052_ = lean_ctor_get(v_ys_3046_, 1);
lean_inc(v_tail_3052_);
lean_dec_ref_known(v_ys_3046_, 2);
v___x_3053_ = lean_apply_2(v_h__2_3048_, v_head_3051_, v_tail_3052_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_3054_, lean_object* v_motive_3055_, lean_object* v_ys_3056_, lean_object* v_h__1_3057_, lean_object* v_h__2_3058_){
_start:
{
if (lean_obj_tag(v_ys_3056_) == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
lean_dec(v_h__2_3058_);
v___x_3059_ = lean_box(0);
v___x_3060_ = lean_apply_1(v_h__1_3057_, v___x_3059_);
return v___x_3060_;
}
else
{
lean_object* v_head_3061_; lean_object* v_tail_3062_; lean_object* v___x_3063_; 
lean_dec(v_h__1_3057_);
v_head_3061_ = lean_ctor_get(v_ys_3056_, 0);
lean_inc(v_head_3061_);
v_tail_3062_ = lean_ctor_get(v_ys_3056_, 1);
lean_inc(v_tail_3062_);
lean_dec_ref_known(v_ys_3056_, 2);
v___x_3063_ = lean_apply_2(v_h__2_3058_, v_head_3061_, v_tail_3062_);
return v___x_3063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(lean_object* v_x_3064_, lean_object* v_x_3065_, lean_object* v_h__1_3066_, lean_object* v_h__2_3067_){
_start:
{
if (lean_obj_tag(v_x_3064_) == 0)
{
lean_object* v___x_3068_; 
lean_dec(v_h__2_3067_);
v___x_3068_ = lean_apply_1(v_h__1_3066_, v_x_3065_);
return v___x_3068_;
}
else
{
lean_object* v_head_3069_; lean_object* v_tail_3070_; lean_object* v___x_3071_; 
lean_dec(v_h__1_3066_);
v_head_3069_ = lean_ctor_get(v_x_3064_, 0);
lean_inc(v_head_3069_);
v_tail_3070_ = lean_ctor_get(v_x_3064_, 1);
lean_inc(v_tail_3070_);
lean_dec_ref_known(v_x_3064_, 2);
v___x_3071_ = lean_apply_3(v_h__2_3067_, v_head_3069_, v_tail_3070_, v_x_3065_);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(lean_object* v_00_u03b1_3072_, lean_object* v_motive_3073_, lean_object* v_x_3074_, lean_object* v_x_3075_, lean_object* v_h__1_3076_, lean_object* v_h__2_3077_){
_start:
{
if (lean_obj_tag(v_x_3074_) == 0)
{
lean_object* v___x_3078_; 
lean_dec(v_h__2_3077_);
v___x_3078_ = lean_apply_1(v_h__1_3076_, v_x_3075_);
return v___x_3078_;
}
else
{
lean_object* v_head_3079_; lean_object* v_tail_3080_; lean_object* v___x_3081_; 
lean_dec(v_h__1_3076_);
v_head_3079_ = lean_ctor_get(v_x_3074_, 0);
lean_inc(v_head_3079_);
v_tail_3080_ = lean_ctor_get(v_x_3074_, 1);
lean_inc(v_tail_3080_);
lean_dec_ref_known(v_x_3074_, 2);
v___x_3081_ = lean_apply_3(v_h__2_3077_, v_head_3079_, v_tail_3080_, v_x_3075_);
return v___x_3081_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object* v_f_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
if (lean_obj_tag(v_a_3083_) == 0)
{
lean_object* v___x_3085_; 
lean_dec(v_f_3082_);
v___x_3085_ = l_List_reverse___redArg(v_a_3084_);
return v___x_3085_;
}
else
{
lean_object* v_head_3086_; lean_object* v_tail_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3096_; 
v_head_3086_ = lean_ctor_get(v_a_3083_, 0);
v_tail_3087_ = lean_ctor_get(v_a_3083_, 1);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_a_3083_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3089_ = v_a_3083_;
v_isShared_3090_ = v_isSharedCheck_3096_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_tail_3087_);
lean_inc(v_head_3086_);
lean_dec(v_a_3083_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3096_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3093_; 
lean_inc(v_f_3082_);
v___x_3091_ = lean_apply_1(v_f_3082_, v_head_3086_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 1, v_a_3084_);
lean_ctor_set(v___x_3089_, 0, v___x_3091_);
v___x_3093_ = v___x_3089_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_a_3084_);
v___x_3093_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
v_a_3083_ = v_tail_3087_;
v_a_3084_ = v___x_3093_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object* v_00_u03b1_3097_, lean_object* v_00_u03b2_3098_, lean_object* v_f_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_List_mapTR_loop___redArg(v_f_3099_, v_a_3100_, v_a_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object* v_f_3103_, lean_object* v_as_3104_){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = lean_box(0);
v___x_3106_ = l_List_mapTR_loop___redArg(v_f_3103_, v_as_3104_, v___x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR(lean_object* v_00_u03b1_3107_, lean_object* v_00_u03b2_3108_, lean_object* v_f_3109_, lean_object* v_as_3110_){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = lean_box(0);
v___x_3112_ = l_List_mapTR_loop___redArg(v_f_3109_, v_as_3110_, v___x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(lean_object* v_x_3113_, lean_object* v_x_3114_, lean_object* v_h__1_3115_, lean_object* v_h__2_3116_){
_start:
{
if (lean_obj_tag(v_x_3113_) == 0)
{
lean_object* v___x_3117_; 
lean_dec(v_h__2_3116_);
v___x_3117_ = lean_apply_1(v_h__1_3115_, v_x_3114_);
return v___x_3117_;
}
else
{
lean_object* v_head_3118_; lean_object* v_tail_3119_; lean_object* v___x_3120_; 
lean_dec(v_h__1_3115_);
v_head_3118_ = lean_ctor_get(v_x_3113_, 0);
lean_inc(v_head_3118_);
v_tail_3119_ = lean_ctor_get(v_x_3113_, 1);
lean_inc(v_tail_3119_);
lean_dec_ref_known(v_x_3113_, 2);
v___x_3120_ = lean_apply_3(v_h__2_3116_, v_head_3118_, v_tail_3119_, v_x_3114_);
return v___x_3120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(lean_object* v_00_u03b1_3121_, lean_object* v_00_u03b2_3122_, lean_object* v_motive_3123_, lean_object* v_x_3124_, lean_object* v_x_3125_, lean_object* v_h__1_3126_, lean_object* v_h__2_3127_){
_start:
{
if (lean_obj_tag(v_x_3124_) == 0)
{
lean_object* v___x_3128_; 
lean_dec(v_h__2_3127_);
v___x_3128_ = lean_apply_1(v_h__1_3126_, v_x_3125_);
return v___x_3128_;
}
else
{
lean_object* v_head_3129_; lean_object* v_tail_3130_; lean_object* v___x_3131_; 
lean_dec(v_h__1_3126_);
v_head_3129_ = lean_ctor_get(v_x_3124_, 0);
lean_inc(v_head_3129_);
v_tail_3130_ = lean_ctor_get(v_x_3124_, 1);
lean_inc(v_tail_3130_);
lean_dec_ref_known(v_x_3124_, 2);
v___x_3131_ = lean_apply_3(v_h__2_3127_, v_head_3129_, v_tail_3130_, v_x_3125_);
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object* v_p_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
if (lean_obj_tag(v_a_3133_) == 0)
{
lean_object* v___x_3135_; 
lean_dec_ref(v_p_3132_);
v___x_3135_ = l_List_reverse___redArg(v_a_3134_);
return v___x_3135_;
}
else
{
lean_object* v_head_3136_; lean_object* v_tail_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3148_; 
v_head_3136_ = lean_ctor_get(v_a_3133_, 0);
v_tail_3137_ = lean_ctor_get(v_a_3133_, 1);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_a_3133_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3139_ = v_a_3133_;
v_isShared_3140_ = v_isSharedCheck_3148_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_tail_3137_);
lean_inc(v_head_3136_);
lean_dec(v_a_3133_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3148_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; uint8_t v___x_3142_; 
lean_inc_ref(v_p_3132_);
lean_inc(v_head_3136_);
v___x_3141_ = lean_apply_1(v_p_3132_, v_head_3136_);
v___x_3142_ = lean_unbox(v___x_3141_);
if (v___x_3142_ == 0)
{
lean_del_object(v___x_3139_);
lean_dec(v_head_3136_);
v_a_3133_ = v_tail_3137_;
goto _start;
}
else
{
lean_object* v___x_3145_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 1, v_a_3134_);
v___x_3145_ = v___x_3139_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_head_3136_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_a_3134_);
v___x_3145_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
v_a_3133_ = v_tail_3137_;
v_a_3134_ = v___x_3145_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object* v_00_u03b1_3149_, lean_object* v_p_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l_List_filterTR_loop___redArg(v_p_3150_, v_a_3151_, v_a_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object* v_p_3154_, lean_object* v_as_3155_){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_box(0);
v___x_3157_ = l_List_filterTR_loop___redArg(v_p_3154_, v_as_3155_, v___x_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR(lean_object* v_00_u03b1_3158_, lean_object* v_p_3159_, lean_object* v_as_3160_){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_box(0);
v___x_3162_ = l_List_filterTR_loop___redArg(v_p_3159_, v_as_3160_, v___x_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_){
_start:
{
lean_object* v_zero_3166_; uint8_t v_isZero_3167_; 
v_zero_3166_ = lean_unsigned_to_nat(0u);
v_isZero_3167_ = lean_nat_dec_eq(v_a_3164_, v_zero_3166_);
if (v_isZero_3167_ == 1)
{
lean_dec(v_a_3164_);
lean_dec(v_a_3163_);
return v_a_3165_;
}
else
{
lean_object* v_one_3168_; lean_object* v_n_3169_; lean_object* v___x_3170_; 
v_one_3168_ = lean_unsigned_to_nat(1u);
v_n_3169_ = lean_nat_sub(v_a_3164_, v_one_3168_);
lean_dec(v_a_3164_);
lean_inc(v_a_3163_);
v___x_3170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3170_, 0, v_a_3163_);
lean_ctor_set(v___x_3170_, 1, v_a_3165_);
v_a_3164_ = v_n_3169_;
v_a_3165_ = v___x_3170_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object* v_00_u03b1_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_List_replicateTR_loop___redArg(v_a_3173_, v_a_3174_, v_a_3175_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object* v_n_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_box(0);
v___x_3180_ = l_List_replicateTR_loop___redArg(v_a_3178_, v_n_3177_, v___x_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object* v_00_u03b1_3181_, lean_object* v_n_3182_, lean_object* v_a_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_List_replicateTR___redArg(v_n_3182_, v_a_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(lean_object* v_x_3185_, lean_object* v_x_3186_, lean_object* v_h__1_3187_, lean_object* v_h__2_3188_){
_start:
{
lean_object* v_zero_3189_; uint8_t v_isZero_3190_; 
v_zero_3189_ = lean_unsigned_to_nat(0u);
v_isZero_3190_ = lean_nat_dec_eq(v_x_3185_, v_zero_3189_);
if (v_isZero_3190_ == 1)
{
lean_object* v___x_3191_; 
lean_dec(v_h__2_3188_);
v___x_3191_ = lean_apply_1(v_h__1_3187_, v_x_3186_);
return v___x_3191_;
}
else
{
lean_object* v_one_3192_; lean_object* v_n_3193_; lean_object* v___x_3194_; 
lean_dec(v_h__1_3187_);
v_one_3192_ = lean_unsigned_to_nat(1u);
v_n_3193_ = lean_nat_sub(v_x_3185_, v_one_3192_);
v___x_3194_ = lean_apply_2(v_h__2_3188_, v_n_3193_, v_x_3186_);
return v___x_3194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_3195_, lean_object* v_x_3196_, lean_object* v_h__1_3197_, lean_object* v_h__2_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(v_x_3195_, v_x_3196_, v_h__1_3197_, v_h__2_3198_);
lean_dec(v_x_3195_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(lean_object* v_00_u03b1_3200_, lean_object* v_motive_3201_, lean_object* v_x_3202_, lean_object* v_x_3203_, lean_object* v_h__1_3204_, lean_object* v_h__2_3205_){
_start:
{
lean_object* v_zero_3206_; uint8_t v_isZero_3207_; 
v_zero_3206_ = lean_unsigned_to_nat(0u);
v_isZero_3207_ = lean_nat_dec_eq(v_x_3202_, v_zero_3206_);
if (v_isZero_3207_ == 1)
{
lean_object* v___x_3208_; 
lean_dec(v_h__2_3205_);
v___x_3208_ = lean_apply_1(v_h__1_3204_, v_x_3203_);
return v___x_3208_;
}
else
{
lean_object* v_one_3209_; lean_object* v_n_3210_; lean_object* v___x_3211_; 
lean_dec(v_h__1_3204_);
v_one_3209_ = lean_unsigned_to_nat(1u);
v_n_3210_ = lean_nat_sub(v_x_3202_, v_one_3209_);
v___x_3211_ = lean_apply_2(v_h__2_3205_, v_n_3210_, v_x_3203_);
return v___x_3211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_3212_, lean_object* v_motive_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_, lean_object* v_h__1_3216_, lean_object* v_h__2_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(v_00_u03b1_3212_, v_motive_3213_, v_x_3214_, v_x_3215_, v_h__1_3216_, v_h__2_3217_);
lean_dec(v_x_3214_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(lean_object* v_x_3219_, lean_object* v_x_3220_, lean_object* v_h__1_3221_, lean_object* v_h__2_3222_){
_start:
{
lean_object* v_zero_3223_; uint8_t v_isZero_3224_; 
v_zero_3223_ = lean_unsigned_to_nat(0u);
v_isZero_3224_ = lean_nat_dec_eq(v_x_3219_, v_zero_3223_);
if (v_isZero_3224_ == 1)
{
lean_object* v___x_3225_; 
lean_dec(v_h__2_3222_);
v___x_3225_ = lean_apply_1(v_h__1_3221_, v_x_3220_);
return v___x_3225_;
}
else
{
lean_object* v_one_3226_; lean_object* v_n_3227_; lean_object* v___x_3228_; 
lean_dec(v_h__1_3221_);
v_one_3226_ = lean_unsigned_to_nat(1u);
v_n_3227_ = lean_nat_sub(v_x_3219_, v_one_3226_);
v___x_3228_ = lean_apply_2(v_h__2_3222_, v_n_3227_, v_x_3220_);
return v___x_3228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_3229_, lean_object* v_x_3230_, lean_object* v_h__1_3231_, lean_object* v_h__2_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(v_x_3229_, v_x_3230_, v_h__1_3231_, v_h__2_3232_);
lean_dec(v_x_3229_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(lean_object* v_00_u03b1_3234_, lean_object* v_motive_3235_, lean_object* v_x_3236_, lean_object* v_x_3237_, lean_object* v_h__1_3238_, lean_object* v_h__2_3239_){
_start:
{
lean_object* v_zero_3240_; uint8_t v_isZero_3241_; 
v_zero_3240_ = lean_unsigned_to_nat(0u);
v_isZero_3241_ = lean_nat_dec_eq(v_x_3236_, v_zero_3240_);
if (v_isZero_3241_ == 1)
{
lean_object* v___x_3242_; 
lean_dec(v_h__2_3239_);
v___x_3242_ = lean_apply_1(v_h__1_3238_, v_x_3237_);
return v___x_3242_;
}
else
{
lean_object* v_one_3243_; lean_object* v_n_3244_; lean_object* v___x_3245_; 
lean_dec(v_h__1_3238_);
v_one_3243_ = lean_unsigned_to_nat(1u);
v_n_3244_ = lean_nat_sub(v_x_3236_, v_one_3243_);
v___x_3245_ = lean_apply_2(v_h__2_3239_, v_n_3244_, v_x_3237_);
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___boxed(lean_object* v_00_u03b1_3246_, lean_object* v_motive_3247_, lean_object* v_x_3248_, lean_object* v_x_3249_, lean_object* v_h__1_3250_, lean_object* v_h__2_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(v_00_u03b1_3246_, v_motive_3247_, v_x_3248_, v_x_3249_, v_h__1_3250_, v_h__2_3251_);
lean_dec(v_x_3248_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg(lean_object* v_n_3253_, lean_object* v_a_3254_, lean_object* v_l_3255_){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3256_ = l_List_lengthTR___redArg(v_l_3255_);
v___x_3257_ = lean_nat_sub(v_n_3253_, v___x_3256_);
lean_dec(v___x_3256_);
v___x_3258_ = l_List_replicateTR_loop___redArg(v_a_3254_, v___x_3257_, v_l_3255_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg___boxed(lean_object* v_n_3259_, lean_object* v_a_3260_, lean_object* v_l_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_List_leftpadTR___redArg(v_n_3259_, v_a_3260_, v_l_3261_);
lean_dec(v_n_3259_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object* v_00_u03b1_3263_, lean_object* v_n_3264_, lean_object* v_a_3265_, lean_object* v_l_3266_){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = l_List_lengthTR___redArg(v_l_3266_);
v___x_3268_ = lean_nat_sub(v_n_3264_, v___x_3267_);
lean_dec(v___x_3267_);
v___x_3269_ = l_List_replicateTR_loop___redArg(v_a_3265_, v___x_3268_, v_l_3266_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___boxed(lean_object* v_00_u03b1_3270_, lean_object* v_n_3271_, lean_object* v_a_3272_, lean_object* v_l_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_List_leftpadTR(v_00_u03b1_3270_, v_n_3271_, v_a_3272_, v_l_3273_);
lean_dec(v_n_3271_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg(lean_object* v_init_3275_, lean_object* v_x_3276_){
_start:
{
if (lean_obj_tag(v_x_3276_) == 0)
{
lean_inc_ref(v_init_3275_);
return v_init_3275_;
}
else
{
lean_object* v_head_3277_; lean_object* v_tail_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3304_; 
v_head_3277_ = lean_ctor_get(v_x_3276_, 0);
v_tail_3278_ = lean_ctor_get(v_x_3276_, 1);
v_isSharedCheck_3304_ = !lean_is_exclusive(v_x_3276_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3280_ = v_x_3276_;
v_isShared_3281_ = v_isSharedCheck_3304_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_tail_3278_);
lean_inc(v_head_3277_);
lean_dec(v_x_3276_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3304_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v_fst_3282_; lean_object* v_snd_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3303_; 
v_fst_3282_ = lean_ctor_get(v_head_3277_, 0);
v_snd_3283_ = lean_ctor_get(v_head_3277_, 1);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_head_3277_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3285_ = v_head_3277_;
v_isShared_3286_ = v_isSharedCheck_3303_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_snd_3283_);
lean_inc(v_fst_3282_);
lean_dec(v_head_3277_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3303_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v_fst_3288_; lean_object* v_snd_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3302_; 
v___x_3287_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3275_, v_tail_3278_);
v_fst_3288_ = lean_ctor_get(v___x_3287_, 0);
v_snd_3289_ = lean_ctor_get(v___x_3287_, 1);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3291_ = v___x_3287_;
v_isShared_3292_ = v_isSharedCheck_3302_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_snd_3289_);
lean_inc(v_fst_3288_);
lean_dec(v___x_3287_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3302_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 1, v_fst_3288_);
lean_ctor_set(v___x_3280_, 0, v_fst_3282_);
v___x_3294_ = v___x_3280_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_fst_3282_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_fst_3288_);
v___x_3294_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3296_; 
if (v_isShared_3286_ == 0)
{
lean_ctor_set_tag(v___x_3285_, 1);
lean_ctor_set(v___x_3285_, 1, v_snd_3289_);
lean_ctor_set(v___x_3285_, 0, v_snd_3283_);
v___x_3296_ = v___x_3285_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_snd_3283_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_snd_3289_);
v___x_3296_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3298_; 
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v___x_3296_);
lean_ctor_set(v___x_3291_, 0, v___x_3294_);
v___x_3298_ = v___x_3291_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg___boxed(lean_object* v_init_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3305_, v_x_3306_);
lean_dec_ref(v_init_3305_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object* v_l_3308_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_3310_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v___x_3309_, v_l_3308_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object* v_00_u03b1_3311_, lean_object* v_00_u03b2_3312_, lean_object* v_l_3313_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_List_unzipTR___redArg(v_l_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0(lean_object* v_00_u03b1_3315_, lean_object* v_00_u03b2_3316_, lean_object* v_init_3317_, lean_object* v_x_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3317_, v_x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___boxed(lean_object* v_00_u03b1_3320_, lean_object* v_00_u03b2_3321_, lean_object* v_init_3322_, lean_object* v_x_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_List_foldr___at___00List_unzipTR_spec__0(v_00_u03b1_3320_, v_00_u03b2_3321_, v_init_3322_, v_x_3323_);
lean_dec_ref(v_init_3322_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object* v_step_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v_zero_3329_; uint8_t v_isZero_3330_; 
v_zero_3329_ = lean_unsigned_to_nat(0u);
v_isZero_3330_ = lean_nat_dec_eq(v_a_3326_, v_zero_3329_);
if (v_isZero_3330_ == 1)
{
lean_dec(v_a_3327_);
lean_dec(v_a_3326_);
return v_a_3328_;
}
else
{
lean_object* v_one_3331_; lean_object* v_n_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_one_3331_ = lean_unsigned_to_nat(1u);
v_n_3332_ = lean_nat_sub(v_a_3326_, v_one_3331_);
lean_dec(v_a_3326_);
v___x_3333_ = lean_nat_sub(v_a_3327_, v_step_3325_);
lean_dec(v_a_3327_);
lean_inc(v___x_3333_);
v___x_3334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
lean_ctor_set(v___x_3334_, 1, v_a_3328_);
v_a_3326_ = v_n_3332_;
v_a_3327_ = v___x_3333_;
v_a_3328_ = v___x_3334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object* v_step_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_List_range_x27TR_go(v_step_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
lean_dec(v_step_3336_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object* v_s_3341_, lean_object* v_n_3342_, lean_object* v_step_3343_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3344_ = lean_nat_mul(v_step_3343_, v_n_3342_);
v___x_3345_ = lean_nat_add(v_s_3341_, v___x_3344_);
lean_dec(v___x_3344_);
v___x_3346_ = lean_box(0);
v___x_3347_ = l_List_range_x27TR_go(v_step_3343_, v_n_3342_, v___x_3345_, v___x_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object* v_s_3348_, lean_object* v_n_3349_, lean_object* v_step_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_List_range_x27TR(v_s_3348_, v_n_3349_, v_step_3350_);
lean_dec(v_step_3350_);
lean_dec(v_s_3348_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(lean_object* v_x_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_, lean_object* v_h__1_3355_, lean_object* v_h__2_3356_){
_start:
{
lean_object* v_zero_3357_; uint8_t v_isZero_3358_; 
v_zero_3357_ = lean_unsigned_to_nat(0u);
v_isZero_3358_ = lean_nat_dec_eq(v_x_3352_, v_zero_3357_);
if (v_isZero_3358_ == 1)
{
lean_object* v___x_3359_; 
lean_dec(v_h__2_3356_);
v___x_3359_ = lean_apply_2(v_h__1_3355_, v_x_3353_, v_x_3354_);
return v___x_3359_;
}
else
{
lean_object* v_one_3360_; lean_object* v_n_3361_; lean_object* v___x_3362_; 
lean_dec(v_h__1_3355_);
v_one_3360_ = lean_unsigned_to_nat(1u);
v_n_3361_ = lean_nat_sub(v_x_3352_, v_one_3360_);
v___x_3362_ = lean_apply_3(v_h__2_3356_, v_n_3361_, v_x_3353_, v_x_3354_);
return v___x_3362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(lean_object* v_x_3363_, lean_object* v_x_3364_, lean_object* v_x_3365_, lean_object* v_h__1_3366_, lean_object* v_h__2_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(v_x_3363_, v_x_3364_, v_x_3365_, v_h__1_3366_, v_h__2_3367_);
lean_dec(v_x_3363_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object* v_motive_3369_, lean_object* v_x_3370_, lean_object* v_x_3371_, lean_object* v_x_3372_, lean_object* v_h__1_3373_, lean_object* v_h__2_3374_){
_start:
{
lean_object* v_zero_3375_; uint8_t v_isZero_3376_; 
v_zero_3375_ = lean_unsigned_to_nat(0u);
v_isZero_3376_ = lean_nat_dec_eq(v_x_3370_, v_zero_3375_);
if (v_isZero_3376_ == 1)
{
lean_object* v___x_3377_; 
lean_dec(v_h__2_3374_);
v___x_3377_ = lean_apply_2(v_h__1_3373_, v_x_3371_, v_x_3372_);
return v___x_3377_;
}
else
{
lean_object* v_one_3378_; lean_object* v_n_3379_; lean_object* v___x_3380_; 
lean_dec(v_h__1_3373_);
v_one_3378_ = lean_unsigned_to_nat(1u);
v_n_3379_ = lean_nat_sub(v_x_3370_, v_one_3378_);
v___x_3380_ = lean_apply_3(v_h__2_3374_, v_n_3379_, v_x_3371_, v_x_3372_);
return v___x_3380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(lean_object* v_motive_3381_, lean_object* v_x_3382_, lean_object* v_x_3383_, lean_object* v_x_3384_, lean_object* v_h__1_3385_, lean_object* v_h__2_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(v_motive_3381_, v_x_3382_, v_x_3383_, v_x_3384_, v_h__1_3385_, v_h__2_3386_);
lean_dec(v_x_3382_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg(lean_object* v_sep_3388_, lean_object* v_init_3389_, lean_object* v_x_3390_){
_start:
{
if (lean_obj_tag(v_x_3390_) == 0)
{
lean_dec(v_sep_3388_);
lean_inc(v_init_3389_);
return v_init_3389_;
}
else
{
lean_object* v_head_3391_; lean_object* v_tail_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3401_; 
v_head_3391_ = lean_ctor_get(v_x_3390_, 0);
v_tail_3392_ = lean_ctor_get(v_x_3390_, 1);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_x_3390_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3394_ = v_x_3390_;
v_isShared_3395_ = v_isSharedCheck_3401_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_tail_3392_);
lean_inc(v_head_3391_);
lean_dec(v_x_3390_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3401_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3396_; lean_object* v___x_3398_; 
lean_inc(v_sep_3388_);
v___x_3396_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3388_, v_init_3389_, v_tail_3392_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 1, v___x_3396_);
v___x_3398_ = v___x_3394_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_head_3391_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3399_, 0, v_sep_3388_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
return v___x_3399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(lean_object* v_sep_3402_, lean_object* v_init_3403_, lean_object* v_x_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3402_, v_init_3403_, v_x_3404_);
lean_dec(v_init_3403_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object* v_sep_3406_, lean_object* v_x_3407_){
_start:
{
if (lean_obj_tag(v_x_3407_) == 0)
{
lean_dec(v_sep_3406_);
return v_x_3407_;
}
else
{
lean_object* v_tail_3408_; 
v_tail_3408_ = lean_ctor_get(v_x_3407_, 1);
lean_inc(v_tail_3408_);
if (lean_obj_tag(v_tail_3408_) == 0)
{
lean_dec(v_sep_3406_);
return v_x_3407_;
}
else
{
lean_object* v_head_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3428_; 
v_head_3409_ = lean_ctor_get(v_x_3407_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_x_3407_);
if (v_isSharedCheck_3428_ == 0)
{
lean_object* v_unused_3429_; 
v_unused_3429_ = lean_ctor_get(v_x_3407_, 1);
lean_dec(v_unused_3429_);
v___x_3411_ = v_x_3407_;
v_isShared_3412_ = v_isSharedCheck_3428_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_head_3409_);
lean_dec(v_x_3407_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3428_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v_head_3413_; lean_object* v_tail_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3427_; 
v_head_3413_ = lean_ctor_get(v_tail_3408_, 0);
v_tail_3414_ = lean_ctor_get(v_tail_3408_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_tail_3408_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3416_ = v_tail_3408_;
v_isShared_3417_ = v_isSharedCheck_3427_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_tail_3414_);
lean_inc(v_head_3413_);
lean_dec(v_tail_3408_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3427_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3421_; 
v___x_3418_ = lean_box(0);
lean_inc(v_sep_3406_);
v___x_3419_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3406_, v___x_3418_, v_tail_3414_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 1, v___x_3419_);
v___x_3421_ = v___x_3416_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_head_3413_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3423_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 1, v___x_3421_);
lean_ctor_set(v___x_3411_, 0, v_sep_3406_);
v___x_3423_ = v___x_3411_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_sep_3406_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3424_, 0, v_head_3409_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
return v___x_3424_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object* v_00_u03b1_3430_, lean_object* v_sep_3431_, lean_object* v_x_3432_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_List_intersperseTR___redArg(v_sep_3431_, v_x_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0(lean_object* v_00_u03b1_3434_, lean_object* v_sep_3435_, lean_object* v_init_3436_, lean_object* v_x_3437_){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3435_, v_init_3436_, v_x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___boxed(lean_object* v_00_u03b1_3439_, lean_object* v_sep_3440_, lean_object* v_init_3441_, lean_object* v_x_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_List_foldr___at___00List_intersperseTR_spec__0(v_00_u03b1_3439_, v_sep_3440_, v_init_3441_, v_x_3442_);
lean_dec(v_init_3441_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(lean_object* v_x_3444_, lean_object* v_h__1_3445_, lean_object* v_h__2_3446_, lean_object* v_h__3_3447_){
_start:
{
if (lean_obj_tag(v_x_3444_) == 0)
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
lean_dec(v_h__3_3447_);
lean_dec(v_h__2_3446_);
v___x_3448_ = lean_box(0);
v___x_3449_ = lean_apply_1(v_h__1_3445_, v___x_3448_);
return v___x_3449_;
}
else
{
lean_object* v_tail_3450_; 
lean_dec(v_h__1_3445_);
v_tail_3450_ = lean_ctor_get(v_x_3444_, 1);
if (lean_obj_tag(v_tail_3450_) == 0)
{
lean_object* v_head_3451_; lean_object* v___x_3452_; 
lean_dec(v_h__3_3447_);
v_head_3451_ = lean_ctor_get(v_x_3444_, 0);
lean_inc(v_head_3451_);
lean_dec_ref_known(v_x_3444_, 2);
v___x_3452_ = lean_apply_1(v_h__2_3446_, v_head_3451_);
return v___x_3452_;
}
else
{
lean_object* v_head_3453_; lean_object* v_head_3454_; lean_object* v_tail_3455_; lean_object* v___x_3456_; 
lean_inc_ref(v_tail_3450_);
lean_dec(v_h__2_3446_);
v_head_3453_ = lean_ctor_get(v_x_3444_, 0);
lean_inc(v_head_3453_);
lean_dec_ref_known(v_x_3444_, 2);
v_head_3454_ = lean_ctor_get(v_tail_3450_, 0);
lean_inc(v_head_3454_);
v_tail_3455_ = lean_ctor_get(v_tail_3450_, 1);
lean_inc(v_tail_3455_);
lean_dec_ref_known(v_tail_3450_, 2);
v___x_3456_ = lean_apply_3(v_h__3_3447_, v_head_3453_, v_head_3454_, v_tail_3455_);
return v___x_3456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object* v_00_u03b1_3457_, lean_object* v_motive_3458_, lean_object* v_x_3459_, lean_object* v_h__1_3460_, lean_object* v_h__2_3461_, lean_object* v_h__3_3462_){
_start:
{
if (lean_obj_tag(v_x_3459_) == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_dec(v_h__3_3462_);
lean_dec(v_h__2_3461_);
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_apply_1(v_h__1_3460_, v___x_3463_);
return v___x_3464_;
}
else
{
lean_object* v_tail_3465_; 
lean_dec(v_h__1_3460_);
v_tail_3465_ = lean_ctor_get(v_x_3459_, 1);
if (lean_obj_tag(v_tail_3465_) == 0)
{
lean_object* v_head_3466_; lean_object* v___x_3467_; 
lean_dec(v_h__3_3462_);
v_head_3466_ = lean_ctor_get(v_x_3459_, 0);
lean_inc(v_head_3466_);
lean_dec_ref_known(v_x_3459_, 2);
v___x_3467_ = lean_apply_1(v_h__2_3461_, v_head_3466_);
return v___x_3467_;
}
else
{
lean_object* v_head_3468_; lean_object* v_head_3469_; lean_object* v_tail_3470_; lean_object* v___x_3471_; 
lean_inc_ref(v_tail_3465_);
lean_dec(v_h__2_3461_);
v_head_3468_ = lean_ctor_get(v_x_3459_, 0);
lean_inc(v_head_3468_);
lean_dec_ref_known(v_x_3459_, 2);
v_head_3469_ = lean_ctor_get(v_tail_3465_, 0);
lean_inc(v_head_3469_);
v_tail_3470_ = lean_ctor_get(v_tail_3465_, 1);
lean_inc(v_tail_3470_);
lean_dec_ref_known(v_tail_3465_, 2);
v___x_3471_ = lean_apply_3(v_h__3_3462_, v_head_3468_, v_head_3469_, v_tail_3470_);
return v___x_3471_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_List_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Zero(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Zero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_List_lex___auto__1 = _init_l_List_lex___auto__1();
lean_mark_persistent(l_List_lex___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Notation(uint8_t builtin);
lean_object* initialize_Init_Data_Zero(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Zero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
