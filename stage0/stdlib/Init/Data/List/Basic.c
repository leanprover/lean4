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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_set_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_set_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instBEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_x_1_);
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
lean_dec_ref(v_x_18_);
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
lean_dec_ref(v_x_33_);
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
lean_dec_ref(v_x_43_);
v___x_50_ = lean_apply_3(v_h__2_46_, v_head_48_, v_tail_49_, v_x_44_);
return v___x_50_;
}
}
}
LEAN_EXPORT uint8_t l_List_beq___redArg(lean_object* v_inst_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_52_) == 0)
{
lean_dec_ref(v_inst_51_);
if (lean_obj_tag(v_x_53_) == 0)
{
uint8_t v___x_54_; 
v___x_54_ = 1;
return v___x_54_;
}
else
{
uint8_t v___x_55_; 
lean_dec_ref(v_x_53_);
v___x_55_ = 0;
return v___x_55_;
}
}
else
{
if (lean_obj_tag(v_x_53_) == 0)
{
uint8_t v___x_56_; 
lean_dec_ref(v_x_52_);
lean_dec_ref(v_inst_51_);
v___x_56_ = 0;
return v___x_56_;
}
else
{
lean_object* v_head_57_; lean_object* v_tail_58_; lean_object* v_head_59_; lean_object* v_tail_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_head_57_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_head_57_);
v_tail_58_ = lean_ctor_get(v_x_52_, 1);
lean_inc(v_tail_58_);
lean_dec_ref(v_x_52_);
v_head_59_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_head_59_);
v_tail_60_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_tail_60_);
lean_dec_ref(v_x_53_);
lean_inc_ref(v_inst_51_);
v___x_61_ = lean_apply_2(v_inst_51_, v_head_57_, v_head_59_);
v___x_62_ = lean_unbox(v___x_61_);
if (v___x_62_ == 0)
{
uint8_t v___x_63_; 
lean_dec(v_tail_60_);
lean_dec(v_tail_58_);
lean_dec_ref(v_inst_51_);
v___x_63_ = lean_unbox(v___x_61_);
return v___x_63_;
}
else
{
v_x_52_ = v_tail_58_;
v_x_53_ = v_tail_60_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___redArg___boxed(lean_object* v_inst_65_, lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_List_beq___redArg(v_inst_65_, v_x_66_, v_x_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_List_beq(lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = l_List_beq___redArg(v_inst_71_, v_x_72_, v_x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_List_beq___boxed(lean_object* v_00_u03b1_75_, lean_object* v_inst_76_, lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_List_beq(v_00_u03b1_75_, v_inst_76_, v_x_77_, v_x_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_List_instBEq___redArg(lean_object* v_inst_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_82_, 0, lean_box(0));
lean_closure_set(v___x_82_, 1, v_inst_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_List_instBEq(lean_object* v_00_u03b1_83_, lean_object* v_inst_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_85_, 0, lean_box(0));
lean_closure_set(v___x_85_, 1, v_inst_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___redArg(lean_object* v_x_86_, lean_object* v_x_87_, lean_object* v_h__1_88_, lean_object* v_h__2_89_, lean_object* v_h__3_90_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_dec(v_h__2_89_);
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_h__3_90_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_h__1_88_, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v___x_93_; 
lean_dec(v_h__1_88_);
v___x_93_ = lean_apply_4(v_h__3_90_, v_x_86_, v_x_87_, lean_box(0), lean_box(0));
return v___x_93_;
}
}
else
{
lean_dec(v_h__1_88_);
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_94_; 
lean_dec(v_h__2_89_);
v___x_94_ = lean_apply_4(v_h__3_90_, v_x_86_, v_x_87_, lean_box(0), lean_box(0));
return v___x_94_;
}
else
{
lean_object* v_head_95_; lean_object* v_tail_96_; lean_object* v_head_97_; lean_object* v_tail_98_; lean_object* v___x_99_; 
lean_dec(v_h__3_90_);
v_head_95_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_head_95_);
v_tail_96_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_tail_96_);
lean_dec_ref(v_x_86_);
v_head_97_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_head_97_);
v_tail_98_ = lean_ctor_get(v_x_87_, 1);
lean_inc(v_tail_98_);
lean_dec_ref(v_x_87_);
v___x_99_ = lean_apply_4(v_h__2_89_, v_head_95_, v_tail_96_, v_head_97_, v_tail_98_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter(lean_object* v_00_u03b1_100_, lean_object* v_motive_101_, lean_object* v_x_102_, lean_object* v_x_103_, lean_object* v_h__1_104_, lean_object* v_h__2_105_, lean_object* v_h__3_106_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_dec(v_h__2_105_);
if (lean_obj_tag(v_x_103_) == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v_h__3_106_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_apply_1(v_h__1_104_, v___x_107_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; 
lean_dec(v_h__1_104_);
v___x_109_ = lean_apply_4(v_h__3_106_, v_x_102_, v_x_103_, lean_box(0), lean_box(0));
return v___x_109_;
}
}
else
{
lean_dec(v_h__1_104_);
if (lean_obj_tag(v_x_103_) == 0)
{
lean_object* v___x_110_; 
lean_dec(v_h__2_105_);
v___x_110_ = lean_apply_4(v_h__3_106_, v_x_102_, v_x_103_, lean_box(0), lean_box(0));
return v___x_110_;
}
else
{
lean_object* v_head_111_; lean_object* v_tail_112_; lean_object* v_head_113_; lean_object* v_tail_114_; lean_object* v___x_115_; 
lean_dec(v_h__3_106_);
v_head_111_ = lean_ctor_get(v_x_102_, 0);
lean_inc(v_head_111_);
v_tail_112_ = lean_ctor_get(v_x_102_, 1);
lean_inc(v_tail_112_);
lean_dec_ref(v_x_102_);
v_head_113_ = lean_ctor_get(v_x_103_, 0);
lean_inc(v_head_113_);
v_tail_114_ = lean_ctor_get(v_x_103_, 1);
lean_inc(v_tail_114_);
lean_dec_ref(v_x_103_);
v___x_115_ = lean_apply_4(v_h__2_105_, v_head_111_, v_tail_112_, v_head_113_, v_tail_114_);
return v___x_115_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_isEqv___redArg(lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_dec_ref(v_x_118_);
if (lean_obj_tag(v_x_117_) == 0)
{
uint8_t v___x_119_; 
v___x_119_ = 1;
return v___x_119_;
}
else
{
uint8_t v___x_120_; 
lean_dec_ref(v_x_117_);
v___x_120_ = 0;
return v___x_120_;
}
}
else
{
if (lean_obj_tag(v_x_117_) == 0)
{
uint8_t v___x_121_; 
lean_dec_ref(v_x_116_);
lean_dec_ref(v_x_118_);
v___x_121_ = 0;
return v___x_121_;
}
else
{
lean_object* v_head_122_; lean_object* v_tail_123_; lean_object* v_head_124_; lean_object* v_tail_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_head_122_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_head_122_);
v_tail_123_ = lean_ctor_get(v_x_116_, 1);
lean_inc(v_tail_123_);
lean_dec_ref(v_x_116_);
v_head_124_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_head_124_);
v_tail_125_ = lean_ctor_get(v_x_117_, 1);
lean_inc(v_tail_125_);
lean_dec_ref(v_x_117_);
lean_inc_ref(v_x_118_);
v___x_126_ = lean_apply_2(v_x_118_, v_head_122_, v_head_124_);
v___x_127_ = lean_unbox(v___x_126_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
lean_dec(v_tail_125_);
lean_dec(v_tail_123_);
lean_dec_ref(v_x_118_);
v___x_128_ = lean_unbox(v___x_126_);
return v___x_128_;
}
else
{
v_x_116_ = v_tail_123_;
v_x_117_ = v_tail_125_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___redArg___boxed(lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_List_isEqv___redArg(v_x_130_, v_x_131_, v_x_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv(lean_object* v_00_u03b1_135_, lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = l_List_isEqv___redArg(v_x_136_, v_x_137_, v_x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_List_isEqv___boxed(lean_object* v_00_u03b1_140_, lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_List_isEqv(v_00_u03b1_140_, v_x_141_, v_x_142_, v_x_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLex___redArg(lean_object* v_inst_146_, lean_object* v_h_147_, lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_dec_ref(v_h_147_);
lean_dec_ref(v_inst_146_);
if (lean_obj_tag(v_x_149_) == 0)
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
lean_dec_ref(v_x_149_);
v___x_151_ = 1;
return v___x_151_;
}
}
else
{
lean_object* v_head_152_; lean_object* v_tail_153_; uint8_t v___x_154_; 
v_head_152_ = lean_ctor_get(v_x_148_, 0);
lean_inc(v_head_152_);
v_tail_153_ = lean_ctor_get(v_x_148_, 1);
lean_inc(v_tail_153_);
lean_dec_ref(v_x_148_);
v___x_154_ = 0;
if (lean_obj_tag(v_x_149_) == 0)
{
lean_dec(v_tail_153_);
lean_dec(v_head_152_);
lean_dec_ref(v_h_147_);
lean_dec_ref(v_inst_146_);
return v___x_154_;
}
else
{
lean_object* v_head_155_; lean_object* v_tail_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_head_155_ = lean_ctor_get(v_x_149_, 0);
lean_inc_n(v_head_155_, 2);
v_tail_156_ = lean_ctor_get(v_x_149_, 1);
lean_inc(v_tail_156_);
lean_dec_ref(v_x_149_);
lean_inc_ref(v_inst_146_);
lean_inc(v_head_152_);
v___x_157_ = lean_apply_2(v_inst_146_, v_head_152_, v_head_155_);
lean_inc_ref(v_h_147_);
v___x_158_ = lean_apply_2(v_h_147_, v_head_152_, v_head_155_);
v___x_159_ = lean_unbox(v___x_158_);
if (v___x_159_ == 0)
{
uint8_t v___x_160_; 
v___x_160_ = lean_unbox(v___x_157_);
if (v___x_160_ == 0)
{
lean_dec(v_tail_156_);
lean_dec(v_tail_153_);
lean_dec_ref(v_h_147_);
lean_dec_ref(v_inst_146_);
return v___x_154_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = l_List_decidableLex___redArg(v_inst_146_, v_h_147_, v_tail_153_, v_tail_156_);
if (v___x_161_ == 0)
{
return v___x_154_;
}
else
{
return v___x_161_;
}
}
}
else
{
uint8_t v___x_162_; 
lean_dec(v_tail_156_);
lean_dec(v_tail_153_);
lean_dec_ref(v_h_147_);
lean_dec_ref(v_inst_146_);
v___x_162_ = lean_unbox(v___x_158_);
return v___x_162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableLex___redArg___boxed(lean_object* v_inst_163_, lean_object* v_h_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_List_decidableLex___redArg(v_inst_163_, v_h_164_, v_x_165_, v_x_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLex(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_r_171_, lean_object* v_h_172_, lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = l_List_decidableLex___redArg(v_inst_170_, v_h_172_, v_x_173_, v_x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLex___boxed(lean_object* v_00_u03b1_176_, lean_object* v_inst_177_, lean_object* v_r_178_, lean_object* v_h_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_List_decidableLex(v_00_u03b1_176_, v_inst_177_, v_r_178_, v_h_179_, v_x_180_, v_x_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_List_instLT(lean_object* v_00_u03b1_184_, lean_object* v_inst_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLT___redArg(lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_l_u2081_189_, lean_object* v_l_u2082_190_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = l_List_decidableLex___redArg(v_inst_187_, v_inst_188_, v_l_u2081_189_, v_l_u2082_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLT___redArg___boxed(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_l_u2081_194_, lean_object* v_l_u2082_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_List_decidableLT___redArg(v_inst_192_, v_inst_193_, v_l_u2081_194_, v_l_u2082_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLT(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_l_u2081_202_, lean_object* v_l_u2082_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = l_List_decidableLex___redArg(v_inst_199_, v_inst_201_, v_l_u2081_202_, v_l_u2082_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLT___boxed(lean_object* v_00_u03b1_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_l_u2081_209_, lean_object* v_l_u2082_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_List_decidableLT(v_00_u03b1_205_, v_inst_206_, v_inst_207_, v_inst_208_, v_l_u2081_209_, v_l_u2082_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l_List_instLE(lean_object* v_00_u03b1_213_, lean_object* v_inst_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_box(0);
return v___x_215_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLE___redArg(lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_l_u2081_218_, lean_object* v_l_u2082_219_){
_start:
{
uint8_t v___x_220_; 
v___x_220_ = l_List_decidableLex___redArg(v_inst_216_, v_inst_217_, v_l_u2082_219_, v_l_u2081_218_);
if (v___x_220_ == 0)
{
uint8_t v___x_221_; 
v___x_221_ = 1;
return v___x_221_;
}
else
{
uint8_t v___x_222_; 
v___x_222_ = 0;
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_List_decidableLE___redArg___boxed(lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_l_u2081_225_, lean_object* v_l_u2082_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_List_decidableLE___redArg(v_inst_223_, v_inst_224_, v_l_u2081_225_, v_l_u2082_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLE(lean_object* v_00_u03b1_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_l_u2081_233_, lean_object* v_l_u2082_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = l_List_decidableLE___redArg(v_inst_230_, v_inst_232_, v_l_u2081_233_, v_l_u2082_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLE___boxed(lean_object* v_00_u03b1_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_l_u2081_240_, lean_object* v_l_u2082_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_List_decidableLE(v_00_u03b1_236_, v_inst_237_, v_inst_238_, v_inst_239_, v_l_u2081_240_, v_l_u2082_241_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__12(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l_List_lex___auto__1___closed__10));
v___x_271_ = l_Lean_mkAtom(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_List_lex___auto__1___closed__12, &l_List_lex___auto__1___closed__12_once, _init_l_List_lex___auto__1___closed__12);
v___x_273_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_274_ = lean_array_push(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l_List_lex___auto__1___closed__19));
v___x_290_ = l_Lean_mkAtom(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__21(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_List_lex___auto__1___closed__20, &l_List_lex___auto__1___closed__20_once, _init_l_List_lex___auto__1___closed__20);
v___x_292_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_293_ = lean_array_push(v___x_292_, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__25(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_List_lex___auto__1___closed__24));
v___x_299_ = lean_string_utf8_byte_size(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_300_ = lean_obj_once(&l_List_lex___auto__1___closed__25, &l_List_lex___auto__1___closed__25_once, _init_l_List_lex___auto__1___closed__25);
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = ((lean_object*)(l_List_lex___auto__1___closed__24));
v___x_303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_301_);
lean_ctor_set(v___x_303_, 2, v___x_300_);
return v___x_303_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_304_ = lean_box(0);
v___x_305_ = lean_box(0);
v___x_306_ = lean_obj_once(&l_List_lex___auto__1___closed__26, &l_List_lex___auto__1___closed__26_once, _init_l_List_lex___auto__1___closed__26);
v___x_307_ = lean_box(2);
v___x_308_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
lean_ctor_set(v___x_308_, 2, v___x_305_);
lean_ctor_set(v___x_308_, 3, v___x_304_);
return v___x_308_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l_List_lex___auto__1___closed__27, &l_List_lex___auto__1___closed__27_once, _init_l_List_lex___auto__1___closed__27);
v___x_310_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_311_ = lean_array_push(v___x_310_, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_obj_once(&l_List_lex___auto__1___closed__28, &l_List_lex___auto__1___closed__28_once, _init_l_List_lex___auto__1___closed__28);
v___x_313_ = ((lean_object*)(l_List_lex___auto__1___closed__23));
v___x_314_ = lean_box(2);
v___x_315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
lean_ctor_set(v___x_315_, 2, v___x_312_);
return v___x_315_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_317_ = lean_obj_once(&l_List_lex___auto__1___closed__21, &l_List_lex___auto__1___closed__21_once, _init_l_List_lex___auto__1___closed__21);
v___x_318_ = lean_array_push(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_obj_once(&l_List_lex___auto__1___closed__30, &l_List_lex___auto__1___closed__30_once, _init_l_List_lex___auto__1___closed__30);
v___x_320_ = ((lean_object*)(l_List_lex___auto__1___closed__18));
v___x_321_ = lean_box(2);
v___x_322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
lean_ctor_set(v___x_322_, 2, v___x_319_);
return v___x_322_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_obj_once(&l_List_lex___auto__1___closed__31, &l_List_lex___auto__1___closed__31_once, _init_l_List_lex___auto__1___closed__31);
v___x_324_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_325_ = lean_array_push(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l_List_lex___auto__1___closed__37));
v___x_337_ = l_Lean_mkAtom(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_List_lex___auto__1___closed__38, &l_List_lex___auto__1___closed__38_once, _init_l_List_lex___auto__1___closed__38);
v___x_339_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_340_ = lean_array_push(v___x_339_, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_342_ = lean_obj_once(&l_List_lex___auto__1___closed__39, &l_List_lex___auto__1___closed__39_once, _init_l_List_lex___auto__1___closed__39);
v___x_343_ = lean_array_push(v___x_342_, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_344_ = lean_obj_once(&l_List_lex___auto__1___closed__40, &l_List_lex___auto__1___closed__40_once, _init_l_List_lex___auto__1___closed__40);
v___x_345_ = ((lean_object*)(l_List_lex___auto__1___closed__36));
v___x_346_ = lean_box(2);
v___x_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
lean_ctor_set(v___x_347_, 2, v___x_344_);
return v___x_347_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_349_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_350_ = lean_array_push(v___x_349_, v___x_348_);
return v___x_350_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_List_lex___auto__1___closed__43));
v___x_353_ = l_Lean_mkAtom(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_obj_once(&l_List_lex___auto__1___closed__44, &l_List_lex___auto__1___closed__44_once, _init_l_List_lex___auto__1___closed__44);
v___x_355_ = lean_obj_once(&l_List_lex___auto__1___closed__42, &l_List_lex___auto__1___closed__42_once, _init_l_List_lex___auto__1___closed__42);
v___x_356_ = lean_array_push(v___x_355_, v___x_354_);
return v___x_356_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_358_ = lean_obj_once(&l_List_lex___auto__1___closed__45, &l_List_lex___auto__1___closed__45_once, _init_l_List_lex___auto__1___closed__45);
v___x_359_ = lean_array_push(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = lean_obj_once(&l_List_lex___auto__1___closed__46, &l_List_lex___auto__1___closed__46_once, _init_l_List_lex___auto__1___closed__46);
v___x_361_ = ((lean_object*)(l_List_lex___auto__1___closed__34));
v___x_362_ = lean_box(2);
v___x_363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_360_);
return v___x_363_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__48(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_364_ = lean_obj_once(&l_List_lex___auto__1___closed__47, &l_List_lex___auto__1___closed__47_once, _init_l_List_lex___auto__1___closed__47);
v___x_365_ = lean_obj_once(&l_List_lex___auto__1___closed__32, &l_List_lex___auto__1___closed__32_once, _init_l_List_lex___auto__1___closed__32);
v___x_366_ = lean_array_push(v___x_365_, v___x_364_);
return v___x_366_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__50(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_List_lex___auto__1___closed__49));
v___x_369_ = l_Lean_mkAtom(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__51(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_obj_once(&l_List_lex___auto__1___closed__50, &l_List_lex___auto__1___closed__50_once, _init_l_List_lex___auto__1___closed__50);
v___x_371_ = lean_obj_once(&l_List_lex___auto__1___closed__48, &l_List_lex___auto__1___closed__48_once, _init_l_List_lex___auto__1___closed__48);
v___x_372_ = lean_array_push(v___x_371_, v___x_370_);
return v___x_372_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__52(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = lean_obj_once(&l_List_lex___auto__1___closed__51, &l_List_lex___auto__1___closed__51_once, _init_l_List_lex___auto__1___closed__51);
v___x_374_ = ((lean_object*)(l_List_lex___auto__1___closed__16));
v___x_375_ = lean_box(2);
v___x_376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
lean_ctor_set(v___x_376_, 2, v___x_373_);
return v___x_376_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__53(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l_List_lex___auto__1___closed__52, &l_List_lex___auto__1___closed__52_once, _init_l_List_lex___auto__1___closed__52);
v___x_378_ = lean_obj_once(&l_List_lex___auto__1___closed__13, &l_List_lex___auto__1___closed__13_once, _init_l_List_lex___auto__1___closed__13);
v___x_379_ = lean_array_push(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__54(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_380_ = lean_obj_once(&l_List_lex___auto__1___closed__53, &l_List_lex___auto__1___closed__53_once, _init_l_List_lex___auto__1___closed__53);
v___x_381_ = ((lean_object*)(l_List_lex___auto__1___closed__11));
v___x_382_ = lean_box(2);
v___x_383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_380_);
return v___x_383_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__55(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_obj_once(&l_List_lex___auto__1___closed__54, &l_List_lex___auto__1___closed__54_once, _init_l_List_lex___auto__1___closed__54);
v___x_385_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_386_ = lean_array_push(v___x_385_, v___x_384_);
return v___x_386_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__56(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_obj_once(&l_List_lex___auto__1___closed__55, &l_List_lex___auto__1___closed__55_once, _init_l_List_lex___auto__1___closed__55);
v___x_388_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_389_ = lean_box(2);
v___x_390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
lean_ctor_set(v___x_390_, 2, v___x_387_);
return v___x_390_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__57(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_obj_once(&l_List_lex___auto__1___closed__56, &l_List_lex___auto__1___closed__56_once, _init_l_List_lex___auto__1___closed__56);
v___x_392_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_393_ = lean_array_push(v___x_392_, v___x_391_);
return v___x_393_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__58(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_394_ = lean_obj_once(&l_List_lex___auto__1___closed__57, &l_List_lex___auto__1___closed__57_once, _init_l_List_lex___auto__1___closed__57);
v___x_395_ = ((lean_object*)(l_List_lex___auto__1___closed__7));
v___x_396_ = lean_box(2);
v___x_397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
lean_ctor_set(v___x_397_, 2, v___x_394_);
return v___x_397_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__59(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_obj_once(&l_List_lex___auto__1___closed__58, &l_List_lex___auto__1___closed__58_once, _init_l_List_lex___auto__1___closed__58);
v___x_399_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_400_ = lean_array_push(v___x_399_, v___x_398_);
return v___x_400_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__60(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = lean_obj_once(&l_List_lex___auto__1___closed__59, &l_List_lex___auto__1___closed__59_once, _init_l_List_lex___auto__1___closed__59);
v___x_402_ = ((lean_object*)(l_List_lex___auto__1___closed__4));
v___x_403_ = lean_box(2);
v___x_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_401_);
return v___x_404_;
}
}
static lean_object* _init_l_List_lex___auto__1(void){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_obj_once(&l_List_lex___auto__1___closed__60, &l_List_lex___auto__1___closed__60_once, _init_l_List_lex___auto__1___closed__60);
return v___x_405_;
}
}
LEAN_EXPORT uint8_t l_List_lex___redArg(lean_object* v_inst_406_, lean_object* v_l_u2081_407_, lean_object* v_l_u2082_408_, lean_object* v_lt_409_){
_start:
{
if (lean_obj_tag(v_l_u2081_407_) == 0)
{
lean_dec_ref(v_lt_409_);
lean_dec_ref(v_inst_406_);
if (lean_obj_tag(v_l_u2082_408_) == 0)
{
uint8_t v___x_410_; 
v___x_410_ = 0;
return v___x_410_;
}
else
{
uint8_t v___x_411_; 
lean_dec_ref(v_l_u2082_408_);
v___x_411_ = 1;
return v___x_411_;
}
}
else
{
if (lean_obj_tag(v_l_u2082_408_) == 0)
{
uint8_t v___x_412_; 
lean_dec_ref(v_l_u2081_407_);
lean_dec_ref(v_lt_409_);
lean_dec_ref(v_inst_406_);
v___x_412_ = 0;
return v___x_412_;
}
else
{
lean_object* v_head_413_; lean_object* v_tail_414_; lean_object* v_head_415_; lean_object* v_tail_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_head_413_ = lean_ctor_get(v_l_u2081_407_, 0);
lean_inc_n(v_head_413_, 2);
v_tail_414_ = lean_ctor_get(v_l_u2081_407_, 1);
lean_inc(v_tail_414_);
lean_dec_ref(v_l_u2081_407_);
v_head_415_ = lean_ctor_get(v_l_u2082_408_, 0);
lean_inc_n(v_head_415_, 2);
v_tail_416_ = lean_ctor_get(v_l_u2082_408_, 1);
lean_inc(v_tail_416_);
lean_dec_ref(v_l_u2082_408_);
lean_inc_ref(v_lt_409_);
v___x_417_ = lean_apply_2(v_lt_409_, v_head_413_, v_head_415_);
v___x_418_ = lean_unbox(v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; uint8_t v___x_420_; 
lean_inc_ref(v_inst_406_);
v___x_419_ = lean_apply_2(v_inst_406_, v_head_413_, v_head_415_);
v___x_420_ = lean_unbox(v___x_419_);
if (v___x_420_ == 0)
{
uint8_t v___x_421_; 
lean_dec(v_tail_416_);
lean_dec(v_tail_414_);
lean_dec_ref(v_lt_409_);
lean_dec_ref(v_inst_406_);
v___x_421_ = lean_unbox(v___x_419_);
return v___x_421_;
}
else
{
v_l_u2081_407_ = v_tail_414_;
v_l_u2082_408_ = v_tail_416_;
goto _start;
}
}
else
{
uint8_t v___x_423_; 
lean_dec(v_tail_416_);
lean_dec(v_head_415_);
lean_dec(v_tail_414_);
lean_dec(v_head_413_);
lean_dec_ref(v_lt_409_);
lean_dec_ref(v_inst_406_);
v___x_423_ = lean_unbox(v___x_417_);
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_lex___redArg___boxed(lean_object* v_inst_424_, lean_object* v_l_u2081_425_, lean_object* v_l_u2082_426_, lean_object* v_lt_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_List_lex___redArg(v_inst_424_, v_l_u2081_425_, v_l_u2082_426_, v_lt_427_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT uint8_t l_List_lex(lean_object* v_00_u03b1_430_, lean_object* v_inst_431_, lean_object* v_l_u2081_432_, lean_object* v_l_u2082_433_, lean_object* v_lt_434_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = l_List_lex___redArg(v_inst_431_, v_l_u2081_432_, v_l_u2082_433_, v_lt_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_List_lex___boxed(lean_object* v_00_u03b1_436_, lean_object* v_inst_437_, lean_object* v_l_u2081_438_, lean_object* v_l_u2082_439_, lean_object* v_lt_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_List_lex(v_00_u03b1_436_, v_inst_437_, v_l_u2081_438_, v_l_u2082_439_, v_lt_440_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg(lean_object* v_x_443_){
_start:
{
lean_object* v_tail_444_; 
v_tail_444_ = lean_ctor_get(v_x_443_, 1);
if (lean_obj_tag(v_tail_444_) == 0)
{
lean_object* v_head_445_; 
v_head_445_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_head_445_);
return v_head_445_;
}
else
{
v_x_443_ = v_tail_444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg___boxed(lean_object* v_x_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_List_getLast___redArg(v_x_447_);
lean_dec(v_x_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_List_getLast(lean_object* v_00_u03b1_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_List_getLast___redArg(v_x_450_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___boxed(lean_object* v_00_u03b1_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_List_getLast(v_00_u03b1_453_, v_x_454_, v_x_455_);
lean_dec(v_x_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg(lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
return v___x_458_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = l_List_getLast___redArg(v_x_457_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg___boxed(lean_object* v_x_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_List_getLast_x3f___redArg(v_x_461_);
lean_dec(v_x_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f(lean_object* v_00_u03b1_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_List_getLast_x3f___redArg(v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___boxed(lean_object* v_00_u03b1_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_List_getLast_x3f(v_00_u03b1_466_, v_x_467_);
lean_dec(v_x_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_469_) == 0)
{
lean_inc(v_x_470_);
return v_x_470_;
}
else
{
lean_object* v___x_471_; 
v___x_471_ = l_List_getLast___redArg(v_x_469_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg___boxed(lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_List_getLastD___redArg(v_x_472_, v_x_473_);
lean_dec(v_x_473_);
lean_dec(v_x_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD(lean_object* v_00_u03b1_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_List_getLastD___redArg(v_x_476_, v_x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___boxed(lean_object* v_00_u03b1_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_List_getLastD(v_00_u03b1_479_, v_x_480_, v_x_481_);
lean_dec(v_x_481_);
lean_dec(v_x_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg(lean_object* v_x_483_){
_start:
{
lean_object* v_head_484_; 
v_head_484_ = lean_ctor_get(v_x_483_, 0);
lean_inc(v_head_484_);
return v_head_484_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg___boxed(lean_object* v_x_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_List_head___redArg(v_x_485_);
lean_dec(v_x_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_List_head(lean_object* v_00_u03b1_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_head_490_; 
v_head_490_ = lean_ctor_get(v_x_488_, 0);
lean_inc(v_head_490_);
return v_head_490_;
}
}
LEAN_EXPORT lean_object* l_List_head___boxed(lean_object* v_00_u03b1_491_, lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_List_head(v_00_u03b1_491_, v_x_492_, v_x_493_);
lean_dec(v_x_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg(lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v___x_496_; 
v___x_496_ = lean_box(0);
return v___x_496_;
}
else
{
lean_object* v_head_497_; lean_object* v___x_498_; 
v_head_497_ = lean_ctor_get(v_x_495_, 0);
lean_inc(v_head_497_);
v___x_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_498_, 0, v_head_497_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg___boxed(lean_object* v_x_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_List_head_x3f___redArg(v_x_499_);
lean_dec(v_x_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f(lean_object* v_00_u03b1_501_, lean_object* v_x_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_List_head_x3f___redArg(v_x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___boxed(lean_object* v_00_u03b1_504_, lean_object* v_x_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_List_head_x3f(v_00_u03b1_504_, v_x_505_);
lean_dec(v_x_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg(lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_inc(v_x_508_);
return v_x_508_;
}
else
{
lean_object* v_head_509_; 
v_head_509_ = lean_ctor_get(v_x_507_, 0);
lean_inc(v_head_509_);
return v_head_509_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg___boxed(lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_List_headD___redArg(v_x_510_, v_x_511_);
lean_dec(v_x_511_);
lean_dec(v_x_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_List_headD(lean_object* v_00_u03b1_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_inc(v_x_515_);
return v_x_515_;
}
else
{
lean_object* v_head_516_; 
v_head_516_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_head_516_);
return v_head_516_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___boxed(lean_object* v_00_u03b1_517_, lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_List_headD(v_00_u03b1_517_, v_x_518_, v_x_519_);
lean_dec(v_x_519_);
lean_dec(v_x_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg(lean_object* v_x_521_){
_start:
{
if (lean_obj_tag(v_x_521_) == 0)
{
return v_x_521_;
}
else
{
lean_object* v_tail_522_; 
v_tail_522_ = lean_ctor_get(v_x_521_, 1);
lean_inc(v_tail_522_);
return v_tail_522_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg___boxed(lean_object* v_x_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_List_tail___redArg(v_x_523_);
lean_dec(v_x_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_List_tail(lean_object* v_00_u03b1_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
return v_x_526_;
}
else
{
lean_object* v_tail_527_; 
v_tail_527_ = lean_ctor_get(v_x_526_, 1);
lean_inc(v_tail_527_);
return v_tail_527_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___boxed(lean_object* v_00_u03b1_528_, lean_object* v_x_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_List_tail(v_00_u03b1_528_, v_x_529_);
lean_dec(v_x_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg(lean_object* v_x_531_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v___x_532_; 
v___x_532_ = lean_box(0);
return v___x_532_;
}
else
{
lean_object* v_tail_533_; lean_object* v___x_534_; 
v_tail_533_ = lean_ctor_get(v_x_531_, 1);
lean_inc(v_tail_533_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_tail_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg___boxed(lean_object* v_x_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_List_tail_x3f___redArg(v_x_535_);
lean_dec(v_x_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f(lean_object* v_00_u03b1_537_, lean_object* v_x_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_List_tail_x3f___redArg(v_x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___boxed(lean_object* v_00_u03b1_540_, lean_object* v_x_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_List_tail_x3f(v_00_u03b1_540_, v_x_541_);
lean_dec(v_x_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg(lean_object* v_l_543_, lean_object* v_fallback_544_){
_start:
{
if (lean_obj_tag(v_l_543_) == 0)
{
lean_inc(v_fallback_544_);
return v_fallback_544_;
}
else
{
lean_object* v_tail_545_; 
v_tail_545_ = lean_ctor_get(v_l_543_, 1);
lean_inc(v_tail_545_);
return v_tail_545_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg___boxed(lean_object* v_l_546_, lean_object* v_fallback_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_List_tailD___redArg(v_l_546_, v_fallback_547_);
lean_dec(v_fallback_547_);
lean_dec(v_l_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_List_tailD(lean_object* v_00_u03b1_549_, lean_object* v_l_550_, lean_object* v_fallback_551_){
_start:
{
if (lean_obj_tag(v_l_550_) == 0)
{
lean_inc(v_fallback_551_);
return v_fallback_551_;
}
else
{
lean_object* v_tail_552_; 
v_tail_552_ = lean_ctor_get(v_l_550_, 1);
lean_inc(v_tail_552_);
return v_tail_552_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___boxed(lean_object* v_00_u03b1_553_, lean_object* v_l_554_, lean_object* v_fallback_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_List_tailD(v_00_u03b1_553_, v_l_554_, v_fallback_555_);
lean_dec(v_fallback_555_);
lean_dec(v_l_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_List_filter___redArg(lean_object* v_p_557_, lean_object* v_x_558_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_dec_ref(v_p_557_);
return v_x_558_;
}
else
{
lean_object* v_head_559_; lean_object* v_tail_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_571_; 
v_head_559_ = lean_ctor_get(v_x_558_, 0);
v_tail_560_ = lean_ctor_get(v_x_558_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_571_ == 0)
{
v___x_562_ = v_x_558_;
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_tail_560_);
lean_inc(v_head_559_);
lean_dec(v_x_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; uint8_t v___x_565_; 
lean_inc_ref(v_p_557_);
lean_inc(v_head_559_);
v___x_564_ = lean_apply_1(v_p_557_, v_head_559_);
v___x_565_ = lean_unbox(v___x_564_);
if (v___x_565_ == 0)
{
lean_del_object(v___x_562_);
lean_dec(v_head_559_);
v_x_558_ = v_tail_560_;
goto _start;
}
else
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = l_List_filter___redArg(v_p_557_, v_tail_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_567_);
v___x_569_ = v___x_562_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_head_559_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filter(lean_object* v_00_u03b1_572_, lean_object* v_p_573_, lean_object* v_x_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_List_filter___redArg(v_p_573_, v_x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg(lean_object* v_f_576_, lean_object* v_init_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_dec(v_f_576_);
lean_inc(v_init_577_);
return v_init_577_;
}
else
{
lean_object* v_head_579_; lean_object* v_tail_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_head_579_ = lean_ctor_get(v_x_578_, 0);
lean_inc(v_head_579_);
v_tail_580_ = lean_ctor_get(v_x_578_, 1);
lean_inc(v_tail_580_);
lean_dec_ref(v_x_578_);
lean_inc(v_f_576_);
v___x_581_ = l_List_foldr___redArg(v_f_576_, v_init_577_, v_tail_580_);
v___x_582_ = lean_apply_2(v_f_576_, v_head_579_, v___x_581_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg___boxed(lean_object* v_f_583_, lean_object* v_init_584_, lean_object* v_x_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_List_foldr___redArg(v_f_583_, v_init_584_, v_x_585_);
lean_dec(v_init_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_List_foldr(lean_object* v_00_u03b1_587_, lean_object* v_00_u03b2_588_, lean_object* v_f_589_, lean_object* v_init_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_List_foldr___redArg(v_f_589_, v_init_590_, v_x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___boxed(lean_object* v_00_u03b1_593_, lean_object* v_00_u03b2_594_, lean_object* v_f_595_, lean_object* v_init_596_, lean_object* v_x_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_List_foldr(v_00_u03b1_593_, v_00_u03b2_594_, v_f_595_, v_init_596_, v_x_597_);
lean_dec(v_init_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_List_reverseAux___redArg(lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_599_) == 0)
{
return v_x_600_;
}
else
{
lean_object* v_head_601_; lean_object* v_tail_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
v_head_601_ = lean_ctor_get(v_x_599_, 0);
v_tail_602_ = lean_ctor_get(v_x_599_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_599_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v_x_599_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_tail_602_);
lean_inc(v_head_601_);
lean_dec(v_x_599_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v_x_600_);
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_head_601_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_x_600_);
v___x_607_ = v_reuseFailAlloc_609_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
v_x_599_ = v_tail_602_;
v_x_600_ = v___x_607_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object* v_00_u03b1_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_List_reverseAux___redArg(v_x_612_, v_x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_List_reverse___redArg(lean_object* v_as_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_box(0);
v___x_617_ = l_List_reverseAux___redArg(v_as_615_, v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_List_reverse(lean_object* v_00_u03b1_618_, lean_object* v_as_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_List_reverse___redArg(v_as_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_h__1_623_, lean_object* v_h__2_624_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_object* v___x_625_; 
lean_dec(v_h__2_624_);
v___x_625_ = lean_apply_1(v_h__1_623_, v_x_622_);
return v___x_625_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v___x_628_; 
lean_dec(v_h__1_623_);
v_head_626_ = lean_ctor_get(v_x_621_, 0);
lean_inc(v_head_626_);
v_tail_627_ = lean_ctor_get(v_x_621_, 1);
lean_inc(v_tail_627_);
lean_dec_ref(v_x_621_);
v___x_628_ = lean_apply_3(v_h__2_624_, v_head_626_, v_tail_627_, v_x_622_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_629_, lean_object* v_motive_630_, lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_h__1_633_, lean_object* v_h__2_634_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
lean_object* v___x_635_; 
lean_dec(v_h__2_634_);
v___x_635_ = lean_apply_1(v_h__1_633_, v_x_632_);
return v___x_635_;
}
else
{
lean_object* v_head_636_; lean_object* v_tail_637_; lean_object* v___x_638_; 
lean_dec(v_h__1_633_);
v_head_636_ = lean_ctor_get(v_x_631_, 0);
lean_inc(v_head_636_);
v_tail_637_ = lean_ctor_get(v_x_631_, 1);
lean_inc(v_tail_637_);
lean_dec_ref(v_x_631_);
v___x_638_ = lean_apply_3(v_h__2_634_, v_head_636_, v_tail_637_, v_x_632_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_List_appendTR___redArg(lean_object* v_as_639_, lean_object* v_bs_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = l_List_reverse___redArg(v_as_639_);
v___x_642_ = l_List_reverseAux___redArg(v___x_641_, v_bs_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR(lean_object* v_00_u03b1_643_, lean_object* v_as_644_, lean_object* v_bs_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_List_appendTR___redArg(v_as_644_, v_bs_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter___redArg(lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_h__1_649_, lean_object* v_h__2_650_){
_start:
{
if (lean_obj_tag(v_x_647_) == 0)
{
lean_object* v___x_651_; 
lean_dec(v_h__2_650_);
v___x_651_ = lean_apply_1(v_h__1_649_, v_x_648_);
return v___x_651_;
}
else
{
lean_object* v_head_652_; lean_object* v_tail_653_; lean_object* v___x_654_; 
lean_dec(v_h__1_649_);
v_head_652_ = lean_ctor_get(v_x_647_, 0);
lean_inc(v_head_652_);
v_tail_653_ = lean_ctor_get(v_x_647_, 1);
lean_inc(v_tail_653_);
lean_dec_ref(v_x_647_);
v___x_654_ = lean_apply_3(v_h__2_650_, v_head_652_, v_tail_653_, v_x_648_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter(lean_object* v_00_u03b1_655_, lean_object* v_motive_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_h__1_659_, lean_object* v_h__2_660_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v___x_661_; 
lean_dec(v_h__2_660_);
v___x_661_ = lean_apply_1(v_h__1_659_, v_x_658_);
return v___x_661_;
}
else
{
lean_object* v_head_662_; lean_object* v_tail_663_; lean_object* v___x_664_; 
lean_dec(v_h__1_659_);
v_head_662_ = lean_ctor_get(v_x_657_, 0);
lean_inc(v_head_662_);
v_tail_663_ = lean_ctor_get(v_x_657_, 1);
lean_inc(v_tail_663_);
lean_dec_ref(v_x_657_);
v___x_664_ = lean_apply_3(v_h__2_660_, v_head_662_, v_tail_663_, v_x_658_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_List_instAppend(lean_object* v_00_u03b1_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = ((lean_object*)(l_List_instAppend___closed__0));
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_List_singleton___redArg(lean_object* v_a_668_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_box(0);
v___x_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_670_, 0, v_a_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_List_singleton(lean_object* v_00_u03b1_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_box(0);
v___x_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_674_, 0, v_a_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg(lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v_zero_677_; uint8_t v_isZero_678_; 
v_zero_677_ = lean_unsigned_to_nat(0u);
v_isZero_678_ = lean_nat_dec_eq(v_x_675_, v_zero_677_);
if (v_isZero_678_ == 1)
{
lean_object* v___x_679_; 
lean_dec(v_x_676_);
v___x_679_ = lean_box(0);
return v___x_679_;
}
else
{
lean_object* v_one_680_; lean_object* v_n_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_one_680_ = lean_unsigned_to_nat(1u);
v_n_681_ = lean_nat_sub(v_x_675_, v_one_680_);
lean_inc(v_x_676_);
v___x_682_ = l_List_replicate___redArg(v_n_681_, v_x_676_);
lean_dec(v_n_681_);
v___x_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_683_, 0, v_x_676_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg___boxed(lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_List_replicate___redArg(v_x_684_, v_x_685_);
lean_dec(v_x_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_List_replicate(lean_object* v_00_u03b1_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_List_replicate___redArg(v_x_688_, v_x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___boxed(lean_object* v_00_u03b1_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_List_replicate(v_00_u03b1_691_, v_x_692_, v_x_693_);
lean_dec(v_x_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg(lean_object* v_n_695_, lean_object* v_a_696_, lean_object* v_l_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_698_ = l_List_length___redArg(v_l_697_);
v___x_699_ = lean_nat_sub(v_n_695_, v___x_698_);
lean_dec(v___x_698_);
v___x_700_ = l_List_replicate___redArg(v___x_699_, v_a_696_);
lean_dec(v___x_699_);
v___x_701_ = l_List_appendTR___redArg(v___x_700_, v_l_697_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg___boxed(lean_object* v_n_702_, lean_object* v_a_703_, lean_object* v_l_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_List_leftpad___redArg(v_n_702_, v_a_703_, v_l_704_);
lean_dec(v_n_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad(lean_object* v_00_u03b1_706_, lean_object* v_n_707_, lean_object* v_a_708_, lean_object* v_l_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_List_leftpad___redArg(v_n_707_, v_a_708_, v_l_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___boxed(lean_object* v_00_u03b1_711_, lean_object* v_n_712_, lean_object* v_a_713_, lean_object* v_l_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_List_leftpad(v_00_u03b1_711_, v_n_712_, v_a_713_, v_l_714_);
lean_dec(v_n_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg(lean_object* v_n_716_, lean_object* v_a_717_, lean_object* v_l_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_719_ = l_List_length___redArg(v_l_718_);
v___x_720_ = lean_nat_sub(v_n_716_, v___x_719_);
lean_dec(v___x_719_);
v___x_721_ = l_List_replicate___redArg(v___x_720_, v_a_717_);
lean_dec(v___x_720_);
v___x_722_ = l_List_appendTR___redArg(v_l_718_, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg___boxed(lean_object* v_n_723_, lean_object* v_a_724_, lean_object* v_l_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_List_rightpad___redArg(v_n_723_, v_a_724_, v_l_725_);
lean_dec(v_n_723_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad(lean_object* v_00_u03b1_727_, lean_object* v_n_728_, lean_object* v_a_729_, lean_object* v_l_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_List_rightpad___redArg(v_n_728_, v_a_729_, v_l_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___boxed(lean_object* v_00_u03b1_732_, lean_object* v_n_733_, lean_object* v_a_734_, lean_object* v_l_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_List_rightpad(v_00_u03b1_732_, v_n_733_, v_a_734_, v_l_735_);
lean_dec(v_n_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object* v_00_u03b1_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_box(0);
return v___x_738_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty___redArg(lean_object* v_x_739_){
_start:
{
if (lean_obj_tag(v_x_739_) == 0)
{
uint8_t v___x_740_; 
v___x_740_ = 1;
return v___x_740_;
}
else
{
uint8_t v___x_741_; 
v___x_741_ = 0;
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___redArg___boxed(lean_object* v_x_742_){
_start:
{
uint8_t v_res_743_; lean_object* v_r_744_; 
v_res_743_ = l_List_isEmpty___redArg(v_x_742_);
lean_dec(v_x_742_);
v_r_744_ = lean_box(v_res_743_);
return v_r_744_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty(lean_object* v_00_u03b1_745_, lean_object* v_x_746_){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = l_List_isEmpty___redArg(v_x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___boxed(lean_object* v_00_u03b1_748_, lean_object* v_x_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_List_isEmpty(v_00_u03b1_748_, v_x_749_);
lean_dec(v_x_749_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT uint8_t l_List_elem___redArg(lean_object* v_inst_752_, lean_object* v_a_753_, lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_754_) == 0)
{
uint8_t v___x_755_; 
lean_dec(v_a_753_);
lean_dec_ref(v_inst_752_);
v___x_755_ = 0;
return v___x_755_;
}
else
{
lean_object* v_head_756_; lean_object* v_tail_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_head_756_ = lean_ctor_get(v_x_754_, 0);
lean_inc(v_head_756_);
v_tail_757_ = lean_ctor_get(v_x_754_, 1);
lean_inc(v_tail_757_);
lean_dec_ref(v_x_754_);
lean_inc_ref(v_inst_752_);
lean_inc(v_a_753_);
v___x_758_ = lean_apply_2(v_inst_752_, v_a_753_, v_head_756_);
v___x_759_ = lean_unbox(v___x_758_);
if (v___x_759_ == 0)
{
v_x_754_ = v_tail_757_;
goto _start;
}
else
{
uint8_t v___x_761_; 
lean_dec(v_tail_757_);
lean_dec(v_a_753_);
lean_dec_ref(v_inst_752_);
v___x_761_ = lean_unbox(v___x_758_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___redArg___boxed(lean_object* v_inst_762_, lean_object* v_a_763_, lean_object* v_x_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_List_elem___redArg(v_inst_762_, v_a_763_, v_x_764_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT uint8_t l_List_elem(lean_object* v_00_u03b1_767_, lean_object* v_inst_768_, lean_object* v_a_769_, lean_object* v_x_770_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = l_List_elem___redArg(v_inst_768_, v_a_769_, v_x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_List_elem___boxed(lean_object* v_00_u03b1_772_, lean_object* v_inst_773_, lean_object* v_a_774_, lean_object* v_x_775_){
_start:
{
uint8_t v_res_776_; lean_object* v_r_777_; 
v_res_776_ = l_List_elem(v_00_u03b1_772_, v_inst_773_, v_a_774_, v_x_775_);
v_r_777_ = lean_box(v_res_776_);
return v_r_777_;
}
}
LEAN_EXPORT uint8_t l_List_contains___redArg(lean_object* v_inst_778_, lean_object* v_as_779_, lean_object* v_a_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = l_List_elem___redArg(v_inst_778_, v_a_780_, v_as_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_List_contains___redArg___boxed(lean_object* v_inst_782_, lean_object* v_as_783_, lean_object* v_a_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_List_contains___redArg(v_inst_782_, v_as_783_, v_a_784_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT uint8_t l_List_contains(lean_object* v_00_u03b1_787_, lean_object* v_inst_788_, lean_object* v_as_789_, lean_object* v_a_790_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = l_List_elem___redArg(v_inst_788_, v_a_790_, v_as_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_List_contains___boxed(lean_object* v_00_u03b1_792_, lean_object* v_inst_793_, lean_object* v_as_794_, lean_object* v_a_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_List_contains(v_00_u03b1_792_, v_inst_793_, v_as_794_, v_a_795_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership(lean_object* v_00_u03b1_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = lean_box(0);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_800_, lean_object* v_h__1_801_, lean_object* v_h__2_802_){
_start:
{
if (lean_obj_tag(v_x_800_) == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v_h__2_802_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_apply_1(v_h__1_801_, v___x_803_);
return v___x_804_;
}
else
{
lean_object* v_head_805_; lean_object* v_tail_806_; lean_object* v___x_807_; 
lean_dec(v_h__1_801_);
v_head_805_ = lean_ctor_get(v_x_800_, 0);
lean_inc(v_head_805_);
v_tail_806_ = lean_ctor_get(v_x_800_, 1);
lean_inc(v_tail_806_);
lean_dec_ref(v_x_800_);
v___x_807_ = lean_apply_2(v_h__2_802_, v_head_805_, v_tail_806_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_808_, lean_object* v_motive_809_, lean_object* v_x_810_, lean_object* v_h__1_811_, lean_object* v_h__2_812_){
_start:
{
if (lean_obj_tag(v_x_810_) == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v_h__2_812_);
v___x_813_ = lean_box(0);
v___x_814_ = lean_apply_1(v_h__1_811_, v___x_813_);
return v___x_814_;
}
else
{
lean_object* v_head_815_; lean_object* v_tail_816_; lean_object* v___x_817_; 
lean_dec(v_h__1_811_);
v_head_815_ = lean_ctor_get(v_x_810_, 0);
lean_inc(v_head_815_);
v_tail_816_ = lean_ctor_get(v_x_810_, 1);
lean_inc(v_tail_816_);
lean_dec_ref(v_x_810_);
v___x_817_ = lean_apply_2(v_h__2_812_, v_head_815_, v_tail_816_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(uint8_t v_x_818_, lean_object* v_h__1_819_, lean_object* v_h__2_820_){
_start:
{
if (v_x_818_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v_h__1_819_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_apply_1(v_h__2_820_, v___x_821_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v_h__2_820_);
v___x_823_ = lean_box(0);
v___x_824_ = lean_apply_1(v_h__1_819_, v___x_823_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_825_, lean_object* v_h__1_826_, lean_object* v_h__2_827_){
_start:
{
uint8_t v_x_26__boxed_828_; lean_object* v_res_829_; 
v_x_26__boxed_828_ = lean_unbox(v_x_825_);
v_res_829_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(v_x_26__boxed_828_, v_h__1_826_, v_h__2_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object* v_motive_830_, uint8_t v_x_831_, lean_object* v_h__1_832_, lean_object* v_h__2_833_){
_start:
{
if (v_x_831_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v_h__1_832_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_apply_1(v_h__2_833_, v___x_834_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_h__2_833_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_apply_1(v_h__1_832_, v___x_836_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_838_, lean_object* v_x_839_, lean_object* v_h__1_840_, lean_object* v_h__2_841_){
_start:
{
uint8_t v_x_37__boxed_842_; lean_object* v_res_843_; 
v_x_37__boxed_842_ = lean_unbox(v_x_839_);
v_res_843_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(v_motive_838_, v_x_37__boxed_842_, v_h__1_840_, v_h__2_841_);
return v_res_843_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_844_, lean_object* v_a_845_, lean_object* v_as_846_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = l_List_elem___redArg(v_inst_844_, v_a_845_, v_as_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_848_, lean_object* v_a_849_, lean_object* v_as_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_List_instDecidableMemOfLawfulBEq___redArg(v_inst_848_, v_a_849_, v_as_850_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_a_856_, lean_object* v_as_857_){
_start:
{
uint8_t v___x_858_; 
v___x_858_ = l_List_elem___redArg(v_inst_854_, v_a_856_, v_as_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_a_862_, lean_object* v_as_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_List_instDecidableMemOfLawfulBEq(v_00_u03b1_859_, v_inst_860_, v_inst_861_, v_a_862_, v_as_863_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx___redArg(lean_object* v_inst_866_, lean_object* v_x_867_){
_start:
{
if (lean_obj_tag(v_x_867_) == 0)
{
uint8_t v___x_868_; 
lean_dec_ref(v_inst_866_);
v___x_868_ = 0;
return v___x_868_;
}
else
{
lean_object* v_head_869_; lean_object* v_tail_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_head_869_ = lean_ctor_get(v_x_867_, 0);
lean_inc(v_head_869_);
v_tail_870_ = lean_ctor_get(v_x_867_, 1);
lean_inc(v_tail_870_);
lean_dec_ref(v_x_867_);
lean_inc_ref(v_inst_866_);
v___x_871_ = lean_apply_1(v_inst_866_, v_head_869_);
v___x_872_ = lean_unbox(v___x_871_);
if (v___x_872_ == 0)
{
v_x_867_ = v_tail_870_;
goto _start;
}
else
{
uint8_t v___x_874_; 
lean_dec(v_tail_870_);
lean_dec_ref(v_inst_866_);
v___x_874_ = lean_unbox(v___x_871_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___redArg___boxed(lean_object* v_inst_875_, lean_object* v_x_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l_List_decidableBEx___redArg(v_inst_875_, v_x_876_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx(lean_object* v_00_u03b1_879_, lean_object* v_p_880_, lean_object* v_inst_881_, lean_object* v_x_882_){
_start:
{
uint8_t v___x_883_; 
v___x_883_ = l_List_decidableBEx___redArg(v_inst_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___boxed(lean_object* v_00_u03b1_884_, lean_object* v_p_885_, lean_object* v_inst_886_, lean_object* v_x_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l_List_decidableBEx(v_00_u03b1_884_, v_p_885_, v_inst_886_, v_x_887_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll___redArg(lean_object* v_inst_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
uint8_t v___x_892_; 
lean_dec_ref(v_inst_890_);
v___x_892_ = 1;
return v___x_892_;
}
else
{
lean_object* v_head_893_; lean_object* v_tail_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_head_893_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_head_893_);
v_tail_894_ = lean_ctor_get(v_x_891_, 1);
lean_inc(v_tail_894_);
lean_dec_ref(v_x_891_);
lean_inc_ref(v_inst_890_);
v___x_895_ = lean_apply_1(v_inst_890_, v_head_893_);
v___x_896_ = lean_unbox(v___x_895_);
if (v___x_896_ == 0)
{
uint8_t v___x_897_; 
lean_dec(v_tail_894_);
lean_dec_ref(v_inst_890_);
v___x_897_ = lean_unbox(v___x_895_);
return v___x_897_;
}
else
{
v_x_891_ = v_tail_894_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___redArg___boxed(lean_object* v_inst_899_, lean_object* v_x_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_List_decidableBAll___redArg(v_inst_899_, v_x_900_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll(lean_object* v_00_u03b1_903_, lean_object* v_p_904_, lean_object* v_inst_905_, lean_object* v_x_906_){
_start:
{
uint8_t v___x_907_; 
v___x_907_ = l_List_decidableBAll___redArg(v_inst_905_, v_x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___boxed(lean_object* v_00_u03b1_908_, lean_object* v_p_909_, lean_object* v_inst_910_, lean_object* v_x_911_){
_start:
{
uint8_t v_res_912_; lean_object* v_r_913_; 
v_res_912_ = l_List_decidableBAll(v_00_u03b1_908_, v_p_909_, v_inst_910_, v_x_911_);
v_r_913_ = lean_box(v_res_912_);
return v_r_913_;
}
}
LEAN_EXPORT lean_object* l_List_take___redArg(lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
lean_object* v_zero_916_; uint8_t v_isZero_917_; 
v_zero_916_ = lean_unsigned_to_nat(0u);
v_isZero_917_ = lean_nat_dec_eq(v_x_914_, v_zero_916_);
if (v_isZero_917_ == 1)
{
lean_object* v___x_918_; 
lean_dec(v_x_915_);
v___x_918_ = lean_box(0);
return v___x_918_;
}
else
{
if (lean_obj_tag(v_x_915_) == 0)
{
return v_x_915_;
}
else
{
lean_object* v_head_919_; lean_object* v_tail_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_930_; 
v_head_919_ = lean_ctor_get(v_x_915_, 0);
v_tail_920_ = lean_ctor_get(v_x_915_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_915_);
if (v_isSharedCheck_930_ == 0)
{
v___x_922_ = v_x_915_;
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_tail_920_);
lean_inc(v_head_919_);
lean_dec(v_x_915_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_one_924_; lean_object* v_n_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v_one_924_ = lean_unsigned_to_nat(1u);
v_n_925_ = lean_nat_sub(v_x_914_, v_one_924_);
v___x_926_ = l_List_take___redArg(v_n_925_, v_tail_920_);
lean_dec(v_n_925_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v___x_926_);
v___x_928_ = v___x_922_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_head_919_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_take___redArg___boxed(lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_List_take___redArg(v_x_931_, v_x_932_);
lean_dec(v_x_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_List_take(lean_object* v_00_u03b1_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_List_take___redArg(v_x_935_, v_x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_List_take___boxed(lean_object* v_00_u03b1_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_List_take(v_00_u03b1_938_, v_x_939_, v_x_940_);
lean_dec(v_x_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg(lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
lean_object* v_zero_944_; uint8_t v_isZero_945_; 
v_zero_944_ = lean_unsigned_to_nat(0u);
v_isZero_945_ = lean_nat_dec_eq(v_x_942_, v_zero_944_);
if (v_isZero_945_ == 1)
{
lean_dec(v_x_942_);
lean_inc(v_x_943_);
return v_x_943_;
}
else
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_dec(v_x_942_);
return v_x_943_;
}
else
{
lean_object* v_tail_946_; lean_object* v_one_947_; lean_object* v_n_948_; 
v_tail_946_ = lean_ctor_get(v_x_943_, 1);
v_one_947_ = lean_unsigned_to_nat(1u);
v_n_948_ = lean_nat_sub(v_x_942_, v_one_947_);
lean_dec(v_x_942_);
v_x_942_ = v_n_948_;
v_x_943_ = v_tail_946_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg___boxed(lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_List_drop___redArg(v_x_950_, v_x_951_);
lean_dec(v_x_951_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_List_drop(lean_object* v_00_u03b1_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_List_drop___redArg(v_x_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_List_drop___boxed(lean_object* v_00_u03b1_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_List_drop(v_00_u03b1_957_, v_x_958_, v_x_959_);
lean_dec(v_x_959_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg(lean_object* v_l_961_, lean_object* v_start_962_, lean_object* v_stop_963_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_nat_sub(v_stop_963_, v_start_962_);
v___x_965_ = l_List_drop___redArg(v_start_962_, v_l_961_);
v___x_966_ = l_List_take___redArg(v___x_964_, v___x_965_);
lean_dec(v___x_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg___boxed(lean_object* v_l_967_, lean_object* v_start_968_, lean_object* v_stop_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_List_extract___redArg(v_l_967_, v_start_968_, v_stop_969_);
lean_dec(v_stop_969_);
lean_dec(v_l_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_List_extract(lean_object* v_00_u03b1_971_, lean_object* v_l_972_, lean_object* v_start_973_, lean_object* v_stop_974_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_nat_sub(v_stop_974_, v_start_973_);
v___x_976_ = l_List_drop___redArg(v_start_973_, v_l_972_);
v___x_977_ = l_List_take___redArg(v___x_975_, v___x_976_);
lean_dec(v___x_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_List_extract___boxed(lean_object* v_00_u03b1_978_, lean_object* v_l_979_, lean_object* v_start_980_, lean_object* v_stop_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_List_extract(v_00_u03b1_978_, v_l_979_, v_start_980_, v_stop_981_);
lean_dec(v_stop_981_);
lean_dec(v_l_979_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhile___redArg(lean_object* v_p_983_, lean_object* v_x_984_){
_start:
{
if (lean_obj_tag(v_x_984_) == 0)
{
lean_dec_ref(v_p_983_);
return v_x_984_;
}
else
{
lean_object* v_head_985_; lean_object* v_tail_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_997_; 
v_head_985_ = lean_ctor_get(v_x_984_, 0);
v_tail_986_ = lean_ctor_get(v_x_984_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_x_984_);
if (v_isSharedCheck_997_ == 0)
{
v___x_988_ = v_x_984_;
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_tail_986_);
lean_inc(v_head_985_);
lean_dec(v_x_984_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; uint8_t v___x_991_; 
lean_inc_ref(v_p_983_);
lean_inc(v_head_985_);
v___x_990_ = lean_apply_1(v_p_983_, v_head_985_);
v___x_991_ = lean_unbox(v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_del_object(v___x_988_);
lean_dec(v_tail_986_);
lean_dec(v_head_985_);
lean_dec_ref(v_p_983_);
v___x_992_ = lean_box(0);
return v___x_992_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = l_List_takeWhile___redArg(v_p_983_, v_tail_986_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___x_993_);
v___x_995_ = v___x_988_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_head_985_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_takeWhile(lean_object* v_00_u03b1_998_, lean_object* v_p_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_List_takeWhile___redArg(v_p_999_, v_x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___redArg(lean_object* v_p_1002_, lean_object* v_x_1003_){
_start:
{
if (lean_obj_tag(v_x_1003_) == 0)
{
lean_dec_ref(v_p_1002_);
return v_x_1003_;
}
else
{
lean_object* v_head_1004_; lean_object* v_tail_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_head_1004_ = lean_ctor_get(v_x_1003_, 0);
v_tail_1005_ = lean_ctor_get(v_x_1003_, 1);
lean_inc_ref(v_p_1002_);
lean_inc(v_head_1004_);
v___x_1006_ = lean_apply_1(v_p_1002_, v_head_1004_);
v___x_1007_ = lean_unbox(v___x_1006_);
if (v___x_1007_ == 0)
{
lean_dec_ref(v_p_1002_);
return v_x_1003_;
}
else
{
lean_inc(v_tail_1005_);
lean_dec_ref(v_x_1003_);
v_x_1003_ = v_tail_1005_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object* v_00_u03b1_1009_, lean_object* v_p_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_List_dropWhile___redArg(v_p_1010_, v_x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___redArg(lean_object* v_p_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
if (lean_obj_tag(v_a_1014_) == 0)
{
lean_object* v_fst_1016_; lean_object* v_snd_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v_p_1013_);
v_fst_1016_ = lean_ctor_get(v_a_1015_, 0);
v_snd_1017_ = lean_ctor_get(v_a_1015_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_a_1015_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1019_ = v_a_1015_;
v_isShared_1020_ = v_isSharedCheck_1026_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_snd_1017_);
lean_inc(v_fst_1016_);
lean_dec(v_a_1015_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1026_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1021_ = l_List_reverse___redArg(v_fst_1016_);
v___x_1022_ = l_List_reverse___redArg(v_snd_1017_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v___x_1022_);
lean_ctor_set(v___x_1019_, 0, v___x_1021_);
v___x_1024_ = v___x_1019_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_object* v_head_1027_; lean_object* v_tail_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1054_; 
v_head_1027_ = lean_ctor_get(v_a_1014_, 0);
v_tail_1028_ = lean_ctor_get(v_a_1014_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_a_1014_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1030_ = v_a_1014_;
v_isShared_1031_ = v_isSharedCheck_1054_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_tail_1028_);
lean_inc(v_head_1027_);
lean_dec(v_a_1014_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1054_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_fst_1032_; lean_object* v_snd_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1053_; 
v_fst_1032_ = lean_ctor_get(v_a_1015_, 0);
v_snd_1033_ = lean_ctor_get(v_a_1015_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_a_1015_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1035_ = v_a_1015_;
v_isShared_1036_ = v_isSharedCheck_1053_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_snd_1033_);
lean_inc(v_fst_1032_);
lean_dec(v_a_1015_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1053_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
lean_inc_ref(v_p_1013_);
lean_inc(v_head_1027_);
v___x_1037_ = lean_apply_1(v_p_1013_, v_head_1027_);
v___x_1038_ = lean_unbox(v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1040_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v_snd_1033_);
v___x_1040_ = v___x_1030_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_head_1027_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_snd_1033_);
v___x_1040_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___x_1040_);
v___x_1042_ = v___x_1035_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_fst_1032_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
v_a_1014_ = v_tail_1028_;
v_a_1015_ = v___x_1042_;
goto _start;
}
}
}
else
{
lean_object* v___x_1047_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v_fst_1032_);
v___x_1047_ = v___x_1030_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_head_1027_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_fst_1032_);
v___x_1047_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1047_);
v___x_1049_ = v___x_1035_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_snd_1033_);
v___x_1049_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
v_a_1014_ = v_tail_1028_;
v_a_1015_ = v___x_1049_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object* v_00_u03b1_1055_, lean_object* v_p_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_List_partition_loop___redArg(v_p_1056_, v_a_1057_, v_a_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_List_partition___redArg(lean_object* v_p_1062_, lean_object* v_as_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1065_ = l_List_partition_loop___redArg(v_p_1062_, v_as_1063_, v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_List_partition(lean_object* v_00_u03b1_1066_, lean_object* v_p_1067_, lean_object* v_as_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1070_ = l_List_partition_loop___redArg(v_p_1067_, v_as_1068_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_List_dropLast___redArg(lean_object* v_x_1071_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
return v_x_1071_;
}
else
{
lean_object* v_tail_1072_; 
v_tail_1072_ = lean_ctor_get(v_x_1071_, 1);
lean_inc(v_tail_1072_);
if (lean_obj_tag(v_tail_1072_) == 0)
{
lean_dec_ref(v_x_1071_);
return v_tail_1072_;
}
else
{
lean_object* v_head_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
v_head_1073_ = lean_ctor_get(v_x_1071_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v_x_1071_, 1);
lean_dec(v_unused_1082_);
v___x_1075_ = v_x_1071_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_head_1073_);
lean_dec(v_x_1071_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = l_List_dropLast___redArg(v_tail_1072_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_head_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropLast(lean_object* v_00_u03b1_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_List_dropLast___redArg(v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_1086_, lean_object* v_h__1_1087_, lean_object* v_h__2_1088_, lean_object* v_h__3_1089_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec(v_h__3_1089_);
lean_dec(v_h__2_1088_);
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_apply_1(v_h__1_1087_, v___x_1090_);
return v___x_1091_;
}
else
{
lean_object* v_tail_1092_; 
lean_dec(v_h__1_1087_);
v_tail_1092_ = lean_ctor_get(v_x_1086_, 1);
if (lean_obj_tag(v_tail_1092_) == 0)
{
lean_object* v_head_1093_; lean_object* v___x_1094_; 
lean_dec(v_h__3_1089_);
v_head_1093_ = lean_ctor_get(v_x_1086_, 0);
lean_inc(v_head_1093_);
lean_dec_ref(v_x_1086_);
v___x_1094_ = lean_apply_1(v_h__2_1088_, v_head_1093_);
return v___x_1094_;
}
else
{
lean_object* v_head_1095_; lean_object* v___x_1096_; 
lean_inc_ref(v_tail_1092_);
lean_dec(v_h__2_1088_);
v_head_1095_ = lean_ctor_get(v_x_1086_, 0);
lean_inc(v_head_1095_);
lean_dec_ref(v_x_1086_);
v___x_1096_ = lean_apply_3(v_h__3_1089_, v_head_1095_, v_tail_1092_, lean_box(0));
return v___x_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_1097_, lean_object* v_motive_1098_, lean_object* v_x_1099_, lean_object* v_h__1_1100_, lean_object* v_h__2_1101_, lean_object* v_h__3_1102_){
_start:
{
if (lean_obj_tag(v_x_1099_) == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec(v_h__3_1102_);
lean_dec(v_h__2_1101_);
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_apply_1(v_h__1_1100_, v___x_1103_);
return v___x_1104_;
}
else
{
lean_object* v_tail_1105_; 
lean_dec(v_h__1_1100_);
v_tail_1105_ = lean_ctor_get(v_x_1099_, 1);
if (lean_obj_tag(v_tail_1105_) == 0)
{
lean_object* v_head_1106_; lean_object* v___x_1107_; 
lean_dec(v_h__3_1102_);
v_head_1106_ = lean_ctor_get(v_x_1099_, 0);
lean_inc(v_head_1106_);
lean_dec_ref(v_x_1099_);
v___x_1107_ = lean_apply_1(v_h__2_1101_, v_head_1106_);
return v___x_1107_;
}
else
{
lean_object* v_head_1108_; lean_object* v___x_1109_; 
lean_inc_ref(v_tail_1105_);
lean_dec(v_h__2_1101_);
v_head_1108_ = lean_ctor_get(v_x_1099_, 0);
lean_inc(v_head_1108_);
lean_dec_ref(v_x_1099_);
v___x_1109_ = lean_apply_3(v_h__3_1102_, v_head_1108_, v_tail_1105_, lean_box(0));
return v___x_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object* v_00_u03b1_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_box(0);
return v___x_1111_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(lean_object* v___f_1112_, lean_object* v_x_1113_, lean_object* v_a_1114_){
_start:
{
uint8_t v___x_1115_; 
v___x_1115_ = l_List_elem___redArg(v___f_1112_, v_a_1114_, v_x_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(lean_object* v___f_1116_, lean_object* v_x_1117_, lean_object* v_a_1118_){
_start:
{
uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_res_1119_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(v___f_1116_, v_x_1117_, v_a_1118_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg(lean_object* v_inst_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
lean_object* v___f_1124_; lean_object* v___f_1125_; uint8_t v___x_1126_; 
v___f_1124_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1124_, 0, v_inst_1121_);
v___f_1125_ = lean_alloc_closure((void*)(l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1125_, 0, v___f_1124_);
lean_closure_set(v___f_1125_, 1, v_x_1123_);
v___x_1126_ = l_List_decidableBAll___redArg(v___f_1125_, v_x_1122_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(lean_object* v_inst_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1127_, v_x_1128_, v_x_1129_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq(lean_object* v_00_u03b1_1132_, lean_object* v_inst_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
uint8_t v___x_1136_; 
v___x_1136_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1133_, v_x_1134_, v_x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_inst_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
uint8_t v_res_1141_; lean_object* v_r_1142_; 
v_res_1141_ = l_List_instDecidableRelSubsetOfDecidableEq(v_00_u03b1_1137_, v_inst_1138_, v_x_1139_, v_x_1140_);
v_r_1142_ = lean_box(v_res_1141_);
return v_r_1142_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2));
v___x_1177_ = l_String_toRawSubstring_x27(v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object* v_x_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
lean_inc(v_x_1197_);
v___x_1201_ = l_Lean_Syntax_isOfKind(v_x_1197_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_dec(v_x_1197_);
v___x_1202_ = lean_box(1);
v___x_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v_a_1199_);
return v___x_1203_;
}
else
{
lean_object* v_quotContext_1204_; lean_object* v_currMacroScope_1205_; lean_object* v_ref_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_quotContext_1204_ = lean_ctor_get(v_a_1198_, 1);
v_currMacroScope_1205_ = lean_ctor_get(v_a_1198_, 2);
v_ref_1206_ = lean_ctor_get(v_a_1198_, 5);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = l_Lean_Syntax_getArg(v_x_1197_, v___x_1207_);
v___x_1209_ = lean_unsigned_to_nat(2u);
v___x_1210_ = l_Lean_Syntax_getArg(v_x_1197_, v___x_1209_);
lean_dec(v_x_1197_);
v___x_1211_ = 0;
v___x_1212_ = l_Lean_SourceInfo_fromRef(v_ref_1206_, v___x_1211_);
v___x_1213_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1214_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
v___x_1215_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4));
lean_inc(v_currMacroScope_1205_);
lean_inc(v_quotContext_1204_);
v___x_1216_ = l_Lean_addMacroScope(v_quotContext_1204_, v___x_1215_, v_currMacroScope_1205_);
v___x_1217_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10));
lean_inc_n(v___x_1212_, 2);
v___x_1218_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1212_);
lean_ctor_set(v___x_1218_, 1, v___x_1214_);
lean_ctor_set(v___x_1218_, 2, v___x_1216_);
lean_ctor_set(v___x_1218_, 3, v___x_1217_);
v___x_1219_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1220_ = l_Lean_Syntax_node2(v___x_1212_, v___x_1219_, v___x_1208_, v___x_1210_);
v___x_1221_ = l_Lean_Syntax_node2(v___x_1212_, v___x_1213_, v___x_1218_, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_a_1199_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___boxed(lean_object* v_x_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(v_x_1223_, v_a_1224_, v_a_1225_);
lean_dec_ref(v_a_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object* v_x_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1230_);
v___x_1234_ = l_Lean_Syntax_isOfKind(v_x_1230_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v_x_1230_);
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v_a_1232_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = l_Lean_Syntax_getArg(v_x_1230_, v___x_1237_);
v___x_1239_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1238_);
v___x_1240_ = l_Lean_Syntax_isOfKind(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec(v___x_1238_);
lean_dec(v_x_1230_);
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_a_1232_);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = l_Lean_Syntax_getArg(v_x_1230_, v___x_1243_);
lean_dec(v_x_1230_);
v___x_1245_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1244_);
v___x_1246_ = l_Lean_Syntax_matchesNull(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec(v___x_1244_);
lean_dec(v___x_1238_);
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v_a_1232_);
return v___x_1248_;
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v_ref_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1249_ = l_Lean_Syntax_getArg(v___x_1244_, v___x_1237_);
v___x_1250_ = l_Lean_Syntax_getArg(v___x_1244_, v___x_1243_);
lean_dec(v___x_1244_);
v_ref_1251_ = l_Lean_replaceRef(v___x_1238_, v_a_1231_);
lean_dec(v___x_1238_);
v___x_1252_ = 0;
v___x_1253_ = l_Lean_SourceInfo_fromRef(v_ref_1251_, v___x_1252_);
lean_dec(v_ref_1251_);
v___x_1254_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
v___x_1255_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__5));
lean_inc(v___x_1253_);
v___x_1256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1253_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = l_Lean_Syntax_node3(v___x_1253_, v___x_1254_, v___x_1249_, v___x_1256_, v___x_1250_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_a_1232_);
return v___x_1258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object* v_x_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(v_x_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist___redArg(lean_object* v_inst_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 0)
{
uint8_t v___x_1266_; 
lean_dec(v_x_1265_);
lean_dec_ref(v_inst_1263_);
v___x_1266_ = 1;
return v___x_1266_;
}
else
{
if (lean_obj_tag(v_x_1265_) == 0)
{
uint8_t v___x_1267_; 
lean_dec_ref(v_x_1264_);
lean_dec_ref(v_inst_1263_);
v___x_1267_ = 0;
return v___x_1267_;
}
else
{
lean_object* v_head_1268_; lean_object* v_tail_1269_; lean_object* v_head_1270_; lean_object* v_tail_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_head_1268_ = lean_ctor_get(v_x_1264_, 0);
v_tail_1269_ = lean_ctor_get(v_x_1264_, 1);
v_head_1270_ = lean_ctor_get(v_x_1265_, 0);
lean_inc(v_head_1270_);
v_tail_1271_ = lean_ctor_get(v_x_1265_, 1);
lean_inc(v_tail_1271_);
lean_dec_ref(v_x_1265_);
lean_inc_ref(v_inst_1263_);
lean_inc(v_head_1268_);
v___x_1272_ = lean_apply_2(v_inst_1263_, v_head_1268_, v_head_1270_);
v___x_1273_ = lean_unbox(v___x_1272_);
if (v___x_1273_ == 0)
{
v_x_1265_ = v_tail_1271_;
goto _start;
}
else
{
lean_inc(v_tail_1269_);
lean_dec_ref(v_x_1264_);
v_x_1264_ = v_tail_1269_;
v_x_1265_ = v_tail_1271_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSublist___redArg___boxed(lean_object* v_inst_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_res_1279_ = l_List_isSublist___redArg(v_inst_1276_, v_x_1277_, v_x_1278_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist(lean_object* v_00_u03b1_1281_, lean_object* v_inst_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
uint8_t v___x_1285_; 
v___x_1285_ = l_List_isSublist___redArg(v_inst_1282_, v_x_1283_, v_x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_List_isSublist___boxed(lean_object* v_00_u03b1_1286_, lean_object* v_inst_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
uint8_t v_res_1290_; lean_object* v_r_1291_; 
v_res_1290_ = l_List_isSublist(v_00_u03b1_1286_, v_inst_1287_, v_x_1288_, v_x_1289_);
v_r_1291_ = lean_box(v_res_1290_);
return v_r_1291_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0));
v___x_1310_ = l_String_toRawSubstring_x27(v___x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object* v_x_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
lean_inc(v_x_1322_);
v___x_1326_ = l_Lean_Syntax_isOfKind(v_x_1322_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec(v_x_1322_);
v___x_1327_ = lean_box(1);
v___x_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v_a_1324_);
return v___x_1328_;
}
else
{
lean_object* v_quotContext_1329_; lean_object* v_currMacroScope_1330_; lean_object* v_ref_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_quotContext_1329_ = lean_ctor_get(v_a_1323_, 1);
v_currMacroScope_1330_ = lean_ctor_get(v_a_1323_, 2);
v_ref_1331_ = lean_ctor_get(v_a_1323_, 5);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = l_Lean_Syntax_getArg(v_x_1322_, v___x_1332_);
v___x_1334_ = lean_unsigned_to_nat(2u);
v___x_1335_ = l_Lean_Syntax_getArg(v_x_1322_, v___x_1334_);
lean_dec(v_x_1322_);
v___x_1336_ = 0;
v___x_1337_ = l_Lean_SourceInfo_fromRef(v_ref_1331_, v___x_1336_);
v___x_1338_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1339_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
v___x_1340_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1330_);
lean_inc(v_quotContext_1329_);
v___x_1341_ = l_Lean_addMacroScope(v_quotContext_1329_, v___x_1340_, v_currMacroScope_1330_);
v___x_1342_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1337_, 2);
v___x_1343_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1337_);
lean_ctor_set(v___x_1343_, 1, v___x_1339_);
lean_ctor_set(v___x_1343_, 2, v___x_1341_);
lean_ctor_set(v___x_1343_, 3, v___x_1342_);
v___x_1344_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1345_ = l_Lean_Syntax_node2(v___x_1337_, v___x_1344_, v___x_1333_, v___x_1335_);
v___x_1346_ = l_Lean_Syntax_node2(v___x_1337_, v___x_1338_, v___x_1343_, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v_a_1324_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___boxed(lean_object* v_x_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(v_x_1348_, v_a_1349_, v_a_1350_);
lean_dec_ref(v_a_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object* v_x_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1352_);
v___x_1356_ = l_Lean_Syntax_isOfKind(v_x_1352_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_x_1352_);
v___x_1357_ = lean_box(0);
v___x_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v_a_1354_);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = l_Lean_Syntax_getArg(v_x_1352_, v___x_1359_);
v___x_1361_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1360_);
v___x_1362_ = l_Lean_Syntax_isOfKind(v___x_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec(v___x_1360_);
lean_dec(v_x_1352_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v_a_1354_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = l_Lean_Syntax_getArg(v_x_1352_, v___x_1365_);
lean_dec(v_x_1352_);
v___x_1367_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1366_);
v___x_1368_ = l_Lean_Syntax_matchesNull(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v___x_1366_);
lean_dec(v___x_1360_);
v___x_1369_ = lean_box(0);
v___x_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v_a_1354_);
return v___x_1370_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_ref_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1371_ = l_Lean_Syntax_getArg(v___x_1366_, v___x_1359_);
v___x_1372_ = l_Lean_Syntax_getArg(v___x_1366_, v___x_1365_);
lean_dec(v___x_1366_);
v_ref_1373_ = l_Lean_replaceRef(v___x_1360_, v_a_1353_);
lean_dec(v___x_1360_);
v___x_1374_ = 0;
v___x_1375_ = l_Lean_SourceInfo_fromRef(v_ref_1373_, v___x_1374_);
lean_dec(v_ref_1373_);
v___x_1376_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
v___x_1377_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__2));
lean_inc(v___x_1375_);
v___x_1378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1375_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = l_Lean_Syntax_node3(v___x_1375_, v___x_1376_, v___x_1371_, v___x_1378_, v___x_1372_);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v_a_1354_);
return v___x_1380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object* v_x_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(v_x_1381_, v_a_1382_, v_a_1383_);
lean_dec(v_a_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf___redArg(lean_object* v_inst_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
if (lean_obj_tag(v_x_1386_) == 0)
{
uint8_t v___x_1388_; 
lean_dec(v_x_1387_);
lean_dec_ref(v_inst_1385_);
v___x_1388_ = 1;
return v___x_1388_;
}
else
{
if (lean_obj_tag(v_x_1387_) == 0)
{
uint8_t v___x_1389_; 
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_inst_1385_);
v___x_1389_ = 0;
return v___x_1389_;
}
else
{
lean_object* v_head_1390_; lean_object* v_tail_1391_; lean_object* v_head_1392_; lean_object* v_tail_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_head_1390_ = lean_ctor_get(v_x_1386_, 0);
lean_inc(v_head_1390_);
v_tail_1391_ = lean_ctor_get(v_x_1386_, 1);
lean_inc(v_tail_1391_);
lean_dec_ref(v_x_1386_);
v_head_1392_ = lean_ctor_get(v_x_1387_, 0);
lean_inc(v_head_1392_);
v_tail_1393_ = lean_ctor_get(v_x_1387_, 1);
lean_inc(v_tail_1393_);
lean_dec_ref(v_x_1387_);
lean_inc_ref(v_inst_1385_);
v___x_1394_ = lean_apply_2(v_inst_1385_, v_head_1390_, v_head_1392_);
v___x_1395_ = lean_unbox(v___x_1394_);
if (v___x_1395_ == 0)
{
uint8_t v___x_1396_; 
lean_dec(v_tail_1393_);
lean_dec(v_tail_1391_);
lean_dec_ref(v_inst_1385_);
v___x_1396_ = lean_unbox(v___x_1394_);
return v___x_1396_;
}
else
{
v_x_1386_ = v_tail_1391_;
v_x_1387_ = v_tail_1393_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___redArg___boxed(lean_object* v_inst_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_res_1401_ = l_List_isPrefixOf___redArg(v_inst_1398_, v_x_1399_, v_x_1400_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf(lean_object* v_00_u03b1_1403_, lean_object* v_inst_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
uint8_t v___x_1407_; 
v___x_1407_ = l_List_isPrefixOf___redArg(v_inst_1404_, v_x_1405_, v_x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___boxed(lean_object* v_00_u03b1_1408_, lean_object* v_inst_1409_, lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
uint8_t v_res_1412_; lean_object* v_r_1413_; 
v_res_1412_ = l_List_isPrefixOf(v_00_u03b1_1408_, v_inst_1409_, v_x_1410_, v_x_1411_);
v_r_1413_ = lean_box(v_res_1412_);
return v_r_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_1414_, lean_object* v_x_1415_, lean_object* v_h__1_1416_, lean_object* v_h__2_1417_, lean_object* v_h__3_1418_){
_start:
{
if (lean_obj_tag(v_x_1414_) == 0)
{
lean_object* v___x_1419_; 
lean_dec(v_h__3_1418_);
lean_dec(v_h__2_1417_);
v___x_1419_ = lean_apply_1(v_h__1_1416_, v_x_1415_);
return v___x_1419_;
}
else
{
lean_dec(v_h__1_1416_);
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v___x_1420_; 
lean_dec(v_h__3_1418_);
v___x_1420_ = lean_apply_2(v_h__2_1417_, v_x_1414_, lean_box(0));
return v___x_1420_;
}
else
{
lean_object* v_head_1421_; lean_object* v_tail_1422_; lean_object* v_head_1423_; lean_object* v_tail_1424_; lean_object* v___x_1425_; 
lean_dec(v_h__2_1417_);
v_head_1421_ = lean_ctor_get(v_x_1414_, 0);
lean_inc(v_head_1421_);
v_tail_1422_ = lean_ctor_get(v_x_1414_, 1);
lean_inc(v_tail_1422_);
lean_dec_ref(v_x_1414_);
v_head_1423_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_head_1423_);
v_tail_1424_ = lean_ctor_get(v_x_1415_, 1);
lean_inc(v_tail_1424_);
lean_dec_ref(v_x_1415_);
v___x_1425_ = lean_apply_4(v_h__3_1418_, v_head_1421_, v_tail_1422_, v_head_1423_, v_tail_1424_);
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object* v_00_u03b1_1426_, lean_object* v_motive_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v_h__1_1430_, lean_object* v_h__2_1431_, lean_object* v_h__3_1432_){
_start:
{
if (lean_obj_tag(v_x_1428_) == 0)
{
lean_object* v___x_1433_; 
lean_dec(v_h__3_1432_);
lean_dec(v_h__2_1431_);
v___x_1433_ = lean_apply_1(v_h__1_1430_, v_x_1429_);
return v___x_1433_;
}
else
{
lean_dec(v_h__1_1430_);
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v___x_1434_; 
lean_dec(v_h__3_1432_);
v___x_1434_ = lean_apply_2(v_h__2_1431_, v_x_1428_, lean_box(0));
return v___x_1434_;
}
else
{
lean_object* v_head_1435_; lean_object* v_tail_1436_; lean_object* v_head_1437_; lean_object* v_tail_1438_; lean_object* v___x_1439_; 
lean_dec(v_h__2_1431_);
v_head_1435_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_head_1435_);
v_tail_1436_ = lean_ctor_get(v_x_1428_, 1);
lean_inc(v_tail_1436_);
lean_dec_ref(v_x_1428_);
v_head_1437_ = lean_ctor_get(v_x_1429_, 0);
lean_inc(v_head_1437_);
v_tail_1438_ = lean_ctor_get(v_x_1429_, 1);
lean_inc(v_tail_1438_);
lean_dec_ref(v_x_1429_);
v___x_1439_ = lean_apply_4(v_h__3_1432_, v_head_1435_, v_tail_1436_, v_head_1437_, v_tail_1438_);
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___redArg(lean_object* v_inst_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
if (lean_obj_tag(v_x_1441_) == 0)
{
lean_object* v___x_1443_; 
lean_dec_ref(v_inst_1440_);
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_x_1442_);
return v___x_1443_;
}
else
{
if (lean_obj_tag(v_x_1442_) == 0)
{
lean_object* v___x_1444_; 
lean_dec_ref(v_x_1441_);
lean_dec_ref(v_inst_1440_);
v___x_1444_ = lean_box(0);
return v___x_1444_;
}
else
{
lean_object* v_head_1445_; lean_object* v_tail_1446_; lean_object* v_head_1447_; lean_object* v_tail_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_head_1445_ = lean_ctor_get(v_x_1441_, 0);
lean_inc(v_head_1445_);
v_tail_1446_ = lean_ctor_get(v_x_1441_, 1);
lean_inc(v_tail_1446_);
lean_dec_ref(v_x_1441_);
v_head_1447_ = lean_ctor_get(v_x_1442_, 0);
lean_inc(v_head_1447_);
v_tail_1448_ = lean_ctor_get(v_x_1442_, 1);
lean_inc(v_tail_1448_);
lean_dec_ref(v_x_1442_);
lean_inc_ref(v_inst_1440_);
v___x_1449_ = lean_apply_2(v_inst_1440_, v_head_1445_, v_head_1447_);
v___x_1450_ = lean_unbox(v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; 
lean_dec(v_tail_1448_);
lean_dec(v_tail_1446_);
lean_dec_ref(v_inst_1440_);
v___x_1451_ = lean_box(0);
return v___x_1451_;
}
else
{
v_x_1441_ = v_tail_1446_;
v_x_1442_ = v_tail_1448_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object* v_00_u03b1_1453_, lean_object* v_inst_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_List_isPrefixOf_x3f___redArg(v_inst_1454_, v_x_1455_, v_x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf___redArg(lean_object* v_inst_1458_, lean_object* v_l_u2081_1459_, lean_object* v_l_u2082_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1461_ = l_List_reverse___redArg(v_l_u2081_1459_);
v___x_1462_ = l_List_reverse___redArg(v_l_u2082_1460_);
v___x_1463_ = l_List_isPrefixOf___redArg(v_inst_1458_, v___x_1461_, v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___redArg___boxed(lean_object* v_inst_1464_, lean_object* v_l_u2081_1465_, lean_object* v_l_u2082_1466_){
_start:
{
uint8_t v_res_1467_; lean_object* v_r_1468_; 
v_res_1467_ = l_List_isSuffixOf___redArg(v_inst_1464_, v_l_u2081_1465_, v_l_u2082_1466_);
v_r_1468_ = lean_box(v_res_1467_);
return v_r_1468_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf(lean_object* v_00_u03b1_1469_, lean_object* v_inst_1470_, lean_object* v_l_u2081_1471_, lean_object* v_l_u2082_1472_){
_start:
{
uint8_t v___x_1473_; 
v___x_1473_ = l_List_isSuffixOf___redArg(v_inst_1470_, v_l_u2081_1471_, v_l_u2082_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___boxed(lean_object* v_00_u03b1_1474_, lean_object* v_inst_1475_, lean_object* v_l_u2081_1476_, lean_object* v_l_u2082_1477_){
_start:
{
uint8_t v_res_1478_; lean_object* v_r_1479_; 
v_res_1478_ = l_List_isSuffixOf(v_00_u03b1_1474_, v_inst_1475_, v_l_u2081_1476_, v_l_u2082_1477_);
v_r_1479_ = lean_box(v_res_1478_);
return v_r_1479_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___redArg(lean_object* v_inst_1480_, lean_object* v_l_u2081_1481_, lean_object* v_l_u2082_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = l_List_reverse___redArg(v_l_u2081_1481_);
v___x_1484_ = l_List_reverse___redArg(v_l_u2082_1482_);
v___x_1485_ = l_List_isPrefixOf_x3f___redArg(v_inst_1480_, v___x_1483_, v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
return v___x_1485_;
}
else
{
lean_object* v_val_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1494_; 
v_val_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_val_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = l_List_reverse___redArg(v_val_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object* v_00_u03b1_1495_, lean_object* v_inst_1496_, lean_object* v_l_u2081_1497_, lean_object* v_l_u2082_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_List_isSuffixOf_x3f___redArg(v_inst_1496_, v_l_u2081_1497_, v_l_u2082_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0));
v___x_1518_ = l_String_toRawSubstring_x27(v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object* v_x_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
lean_inc(v_x_1530_);
v___x_1534_ = l_Lean_Syntax_isOfKind(v_x_1530_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_x_1530_);
v___x_1535_ = lean_box(1);
v___x_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v_a_1532_);
return v___x_1536_;
}
else
{
lean_object* v_quotContext_1537_; lean_object* v_currMacroScope_1538_; lean_object* v_ref_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_quotContext_1537_ = lean_ctor_get(v_a_1531_, 1);
v_currMacroScope_1538_ = lean_ctor_get(v_a_1531_, 2);
v_ref_1539_ = lean_ctor_get(v_a_1531_, 5);
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = l_Lean_Syntax_getArg(v_x_1530_, v___x_1540_);
v___x_1542_ = lean_unsigned_to_nat(2u);
v___x_1543_ = l_Lean_Syntax_getArg(v_x_1530_, v___x_1542_);
lean_dec(v_x_1530_);
v___x_1544_ = 0;
v___x_1545_ = l_Lean_SourceInfo_fromRef(v_ref_1539_, v___x_1544_);
v___x_1546_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1547_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
v___x_1548_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2));
lean_inc(v_currMacroScope_1538_);
lean_inc(v_quotContext_1537_);
v___x_1549_ = l_Lean_addMacroScope(v_quotContext_1537_, v___x_1548_, v_currMacroScope_1538_);
v___x_1550_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5));
lean_inc_n(v___x_1545_, 2);
v___x_1551_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1545_);
lean_ctor_set(v___x_1551_, 1, v___x_1547_);
lean_ctor_set(v___x_1551_, 2, v___x_1549_);
lean_ctor_set(v___x_1551_, 3, v___x_1550_);
v___x_1552_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1553_ = l_Lean_Syntax_node2(v___x_1545_, v___x_1552_, v___x_1541_, v___x_1543_);
v___x_1554_ = l_Lean_Syntax_node2(v___x_1545_, v___x_1546_, v___x_1551_, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v_a_1532_);
return v___x_1555_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___boxed(lean_object* v_x_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(v_x_1556_, v_a_1557_, v_a_1558_);
lean_dec_ref(v_a_1557_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object* v_x_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1560_);
v___x_1564_ = l_Lean_Syntax_isOfKind(v_x_1560_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v_x_1560_);
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v_a_1562_);
return v___x_1566_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = l_Lean_Syntax_getArg(v_x_1560_, v___x_1567_);
v___x_1569_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1568_);
v___x_1570_ = l_Lean_Syntax_isOfKind(v___x_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec(v___x_1568_);
lean_dec(v_x_1560_);
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_a_1562_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1573_ = lean_unsigned_to_nat(1u);
v___x_1574_ = l_Lean_Syntax_getArg(v_x_1560_, v___x_1573_);
lean_dec(v_x_1560_);
v___x_1575_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1574_);
v___x_1576_ = l_Lean_Syntax_matchesNull(v___x_1574_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec(v___x_1574_);
lean_dec(v___x_1568_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v_a_1562_);
return v___x_1578_;
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_ref_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1579_ = l_Lean_Syntax_getArg(v___x_1574_, v___x_1567_);
v___x_1580_ = l_Lean_Syntax_getArg(v___x_1574_, v___x_1573_);
lean_dec(v___x_1574_);
v_ref_1581_ = l_Lean_replaceRef(v___x_1568_, v_a_1561_);
lean_dec(v___x_1568_);
v___x_1582_ = 0;
v___x_1583_ = l_Lean_SourceInfo_fromRef(v_ref_1581_, v___x_1582_);
lean_dec(v_ref_1581_);
v___x_1584_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
v___x_1585_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__2));
lean_inc(v___x_1583_);
v___x_1586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1583_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_Syntax_node3(v___x_1583_, v___x_1584_, v___x_1579_, v___x_1586_, v___x_1580_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v_a_1562_);
return v___x_1588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object* v_x_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(v_x_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1590_);
return v_res_1592_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0));
v___x_1611_ = l_String_toRawSubstring_x27(v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object* v_x_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
lean_inc(v_x_1623_);
v___x_1627_ = l_Lean_Syntax_isOfKind(v_x_1623_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_x_1623_);
v___x_1628_ = lean_box(1);
v___x_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v_a_1625_);
return v___x_1629_;
}
else
{
lean_object* v_quotContext_1630_; lean_object* v_currMacroScope_1631_; lean_object* v_ref_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_quotContext_1630_ = lean_ctor_get(v_a_1624_, 1);
v_currMacroScope_1631_ = lean_ctor_get(v_a_1624_, 2);
v_ref_1632_ = lean_ctor_get(v_a_1624_, 5);
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = l_Lean_Syntax_getArg(v_x_1623_, v___x_1633_);
v___x_1635_ = lean_unsigned_to_nat(2u);
v___x_1636_ = l_Lean_Syntax_getArg(v_x_1623_, v___x_1635_);
lean_dec(v_x_1623_);
v___x_1637_ = 0;
v___x_1638_ = l_Lean_SourceInfo_fromRef(v_ref_1632_, v___x_1637_);
v___x_1639_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1640_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
v___x_1641_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1631_);
lean_inc(v_quotContext_1630_);
v___x_1642_ = l_Lean_addMacroScope(v_quotContext_1630_, v___x_1641_, v_currMacroScope_1631_);
v___x_1643_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1638_, 2);
v___x_1644_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1638_);
lean_ctor_set(v___x_1644_, 1, v___x_1640_);
lean_ctor_set(v___x_1644_, 2, v___x_1642_);
lean_ctor_set(v___x_1644_, 3, v___x_1643_);
v___x_1645_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1646_ = l_Lean_Syntax_node2(v___x_1638_, v___x_1645_, v___x_1634_, v___x_1636_);
v___x_1647_ = l_Lean_Syntax_node2(v___x_1638_, v___x_1639_, v___x_1644_, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v_a_1625_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___boxed(lean_object* v_x_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(v_x_1649_, v_a_1650_, v_a_1651_);
lean_dec_ref(v_a_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object* v_x_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1653_);
v___x_1657_ = l_Lean_Syntax_isOfKind(v_x_1653_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec(v_x_1653_);
v___x_1658_ = lean_box(0);
v___x_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v_a_1655_);
return v___x_1659_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = l_Lean_Syntax_getArg(v_x_1653_, v___x_1660_);
v___x_1662_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1661_);
v___x_1663_ = l_Lean_Syntax_isOfKind(v___x_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v___x_1661_);
lean_dec(v_x_1653_);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v_a_1655_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = l_Lean_Syntax_getArg(v_x_1653_, v___x_1666_);
lean_dec(v_x_1653_);
v___x_1668_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1667_);
v___x_1669_ = l_Lean_Syntax_matchesNull(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec(v___x_1667_);
lean_dec(v___x_1661_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v_a_1655_);
return v___x_1671_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v_ref_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1672_ = l_Lean_Syntax_getArg(v___x_1667_, v___x_1660_);
v___x_1673_ = l_Lean_Syntax_getArg(v___x_1667_, v___x_1666_);
lean_dec(v___x_1667_);
v_ref_1674_ = l_Lean_replaceRef(v___x_1661_, v_a_1654_);
lean_dec(v___x_1661_);
v___x_1675_ = 0;
v___x_1676_ = l_Lean_SourceInfo_fromRef(v_ref_1674_, v___x_1675_);
lean_dec(v_ref_1674_);
v___x_1677_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
v___x_1678_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__2));
lean_inc(v___x_1676_);
v___x_1679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1676_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Lean_Syntax_node3(v___x_1676_, v___x_1677_, v___x_1672_, v___x_1679_, v___x_1673_);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v_a_1655_);
return v___x_1681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object* v_x_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(v_x_1682_, v_a_1683_, v_a_1684_);
lean_dec(v_a_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal___redArg(lean_object* v_inst_1686_, lean_object* v_l_u2081_1687_, lean_object* v_l_u2082_1688_){
_start:
{
uint8_t v___x_1689_; 
lean_inc(v_l_u2082_1688_);
lean_inc(v_l_u2081_1687_);
lean_inc_ref(v_inst_1686_);
v___x_1689_ = l_List_isPrefixOf___redArg(v_inst_1686_, v_l_u2081_1687_, v_l_u2082_1688_);
if (v___x_1689_ == 0)
{
if (lean_obj_tag(v_l_u2082_1688_) == 0)
{
lean_dec(v_l_u2081_1687_);
lean_dec_ref(v_inst_1686_);
return v___x_1689_;
}
else
{
lean_object* v_tail_1690_; 
v_tail_1690_ = lean_ctor_get(v_l_u2082_1688_, 1);
lean_inc(v_tail_1690_);
lean_dec_ref(v_l_u2082_1688_);
v_l_u2082_1688_ = v_tail_1690_;
goto _start;
}
}
else
{
lean_dec(v_l_u2082_1688_);
lean_dec(v_l_u2081_1687_);
lean_dec_ref(v_inst_1686_);
return v___x_1689_;
}
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___redArg___boxed(lean_object* v_inst_1692_, lean_object* v_l_u2081_1693_, lean_object* v_l_u2082_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l_List_isInfixOf__internal___redArg(v_inst_1692_, v_l_u2081_1693_, v_l_u2082_1694_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal(lean_object* v_00_u03b1_1697_, lean_object* v_inst_1698_, lean_object* v_l_u2081_1699_, lean_object* v_l_u2082_1700_){
_start:
{
uint8_t v___x_1701_; 
v___x_1701_ = l_List_isInfixOf__internal___redArg(v_inst_1698_, v_l_u2081_1699_, v_l_u2082_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___boxed(lean_object* v_00_u03b1_1702_, lean_object* v_inst_1703_, lean_object* v_l_u2081_1704_, lean_object* v_l_u2082_1705_){
_start:
{
uint8_t v_res_1706_; lean_object* v_r_1707_; 
v_res_1706_ = l_List_isInfixOf__internal(v_00_u03b1_1702_, v_inst_1703_, v_l_u2081_1704_, v_l_u2082_1705_);
v_r_1707_ = lean_box(v_res_1706_);
return v_r_1707_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go___redArg(lean_object* v_l_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
if (lean_obj_tag(v_a_1709_) == 0)
{
lean_object* v___x_1712_; 
lean_dec(v_a_1711_);
lean_dec(v_a_1710_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_l_1708_);
lean_ctor_set(v___x_1712_, 1, v_a_1709_);
return v___x_1712_;
}
else
{
lean_object* v_head_1713_; lean_object* v_tail_1714_; lean_object* v_zero_1715_; uint8_t v_isZero_1716_; 
v_head_1713_ = lean_ctor_get(v_a_1709_, 0);
v_tail_1714_ = lean_ctor_get(v_a_1709_, 1);
v_zero_1715_ = lean_unsigned_to_nat(0u);
v_isZero_1716_ = lean_nat_dec_eq(v_a_1710_, v_zero_1715_);
if (v_isZero_1716_ == 1)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec(v_a_1710_);
lean_dec(v_l_1708_);
v___x_1717_ = l_List_reverse___redArg(v_a_1711_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v_a_1709_);
return v___x_1718_;
}
else
{
lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1728_; 
lean_inc(v_tail_1714_);
lean_inc(v_head_1713_);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_a_1709_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; lean_object* v_unused_1730_; 
v_unused_1729_ = lean_ctor_get(v_a_1709_, 1);
lean_dec(v_unused_1729_);
v_unused_1730_ = lean_ctor_get(v_a_1709_, 0);
lean_dec(v_unused_1730_);
v___x_1720_ = v_a_1709_;
v_isShared_1721_ = v_isSharedCheck_1728_;
goto v_resetjp_1719_;
}
else
{
lean_dec(v_a_1709_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1728_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v_one_1722_; lean_object* v_n_1723_; lean_object* v___x_1725_; 
v_one_1722_ = lean_unsigned_to_nat(1u);
v_n_1723_ = lean_nat_sub(v_a_1710_, v_one_1722_);
lean_dec(v_a_1710_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v_a_1711_);
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_head_1713_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_a_1711_);
v___x_1725_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
v_a_1709_ = v_tail_1714_;
v_a_1710_ = v_n_1723_;
v_a_1711_ = v___x_1725_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object* v_00_u03b1_1731_, lean_object* v_l_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_List_splitAt_go___redArg(v_l_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt___redArg(lean_object* v_n_1737_, lean_object* v_l_1738_){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_box(0);
lean_inc(v_l_1738_);
v___x_1740_ = l_List_splitAt_go___redArg(v_l_1738_, v_l_1738_, v_n_1737_, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt(lean_object* v_00_u03b1_1741_, lean_object* v_n_1742_, lean_object* v_l_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_List_splitAt___redArg(v_n_1742_, v_l_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg(lean_object* v_xs_1745_, lean_object* v_i_1746_){
_start:
{
lean_object* v_len_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_len_1747_ = l_List_length___redArg(v_xs_1745_);
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = lean_nat_dec_le(v_len_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v_i_1750_; lean_object* v_ys_1751_; lean_object* v_zs_1752_; lean_object* v___x_1753_; 
v_i_1750_ = lean_nat_mod(v_i_1746_, v_len_1747_);
lean_dec(v_len_1747_);
lean_inc(v_xs_1745_);
v_ys_1751_ = l_List_take___redArg(v_i_1750_, v_xs_1745_);
v_zs_1752_ = l_List_drop___redArg(v_i_1750_, v_xs_1745_);
lean_dec(v_xs_1745_);
v___x_1753_ = l_List_appendTR___redArg(v_zs_1752_, v_ys_1751_);
return v___x_1753_;
}
else
{
lean_dec(v_len_1747_);
return v_xs_1745_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg___boxed(lean_object* v_xs_1754_, lean_object* v_i_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_List_rotateLeft___redArg(v_xs_1754_, v_i_1755_);
lean_dec(v_i_1755_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft(lean_object* v_00_u03b1_1757_, lean_object* v_xs_1758_, lean_object* v_i_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_List_rotateLeft___redArg(v_xs_1758_, v_i_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_xs_1762_, lean_object* v_i_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_List_rotateLeft(v_00_u03b1_1761_, v_xs_1762_, v_i_1763_);
lean_dec(v_i_1763_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg(lean_object* v_xs_1765_, lean_object* v_i_1766_){
_start:
{
lean_object* v_len_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_len_1767_ = l_List_length___redArg(v_xs_1765_);
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = lean_nat_dec_le(v_len_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v_i_1771_; lean_object* v_ys_1772_; lean_object* v_zs_1773_; lean_object* v___x_1774_; 
v___x_1770_ = lean_nat_mod(v_i_1766_, v_len_1767_);
v_i_1771_ = lean_nat_sub(v_len_1767_, v___x_1770_);
lean_dec(v___x_1770_);
lean_dec(v_len_1767_);
lean_inc(v_xs_1765_);
v_ys_1772_ = l_List_take___redArg(v_i_1771_, v_xs_1765_);
v_zs_1773_ = l_List_drop___redArg(v_i_1771_, v_xs_1765_);
lean_dec(v_xs_1765_);
v___x_1774_ = l_List_appendTR___redArg(v_zs_1773_, v_ys_1772_);
return v___x_1774_;
}
else
{
lean_dec(v_len_1767_);
return v_xs_1765_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg___boxed(lean_object* v_xs_1775_, lean_object* v_i_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_List_rotateRight___redArg(v_xs_1775_, v_i_1776_);
lean_dec(v_i_1776_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight(lean_object* v_00_u03b1_1778_, lean_object* v_xs_1779_, lean_object* v_i_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_List_rotateRight___redArg(v_xs_1779_, v_i_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___boxed(lean_object* v_00_u03b1_1782_, lean_object* v_xs_1783_, lean_object* v_i_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_List_rotateRight(v_00_u03b1_1782_, v_xs_1783_, v_i_1784_);
lean_dec(v_i_1784_);
return v_res_1785_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise___redArg(lean_object* v_inst_1786_, lean_object* v_x_1787_){
_start:
{
if (lean_obj_tag(v_x_1787_) == 0)
{
uint8_t v___x_1788_; 
lean_dec_ref(v_inst_1786_);
v___x_1788_ = 1;
return v___x_1788_;
}
else
{
lean_object* v_head_1789_; lean_object* v_tail_1790_; uint8_t v___x_1791_; 
v_head_1789_ = lean_ctor_get(v_x_1787_, 0);
lean_inc(v_head_1789_);
v_tail_1790_ = lean_ctor_get(v_x_1787_, 1);
lean_inc_n(v_tail_1790_, 2);
lean_dec_ref(v_x_1787_);
lean_inc_ref(v_inst_1786_);
v___x_1791_ = l_List_instDecidablePairwise___redArg(v_inst_1786_, v_tail_1790_);
if (v___x_1791_ == 0)
{
lean_dec(v_tail_1790_);
lean_dec(v_head_1789_);
lean_dec_ref(v_inst_1786_);
return v___x_1791_;
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_apply_1(v_inst_1786_, v_head_1789_);
v___x_1793_ = l_List_decidableBAll___redArg(v___x_1792_, v_tail_1790_);
return v___x_1793_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___redArg___boxed(lean_object* v_inst_1794_, lean_object* v_x_1795_){
_start:
{
uint8_t v_res_1796_; lean_object* v_r_1797_; 
v_res_1796_ = l_List_instDecidablePairwise___redArg(v_inst_1794_, v_x_1795_);
v_r_1797_ = lean_box(v_res_1796_);
return v_r_1797_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise(lean_object* v_00_u03b1_1798_, lean_object* v_R_1799_, lean_object* v_inst_1800_, lean_object* v_x_1801_){
_start:
{
uint8_t v___x_1802_; 
v___x_1802_ = l_List_instDecidablePairwise___redArg(v_inst_1800_, v_x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___boxed(lean_object* v_00_u03b1_1803_, lean_object* v_R_1804_, lean_object* v_inst_1805_, lean_object* v_x_1806_){
_start:
{
uint8_t v_res_1807_; lean_object* v_r_1808_; 
v_res_1807_ = l_List_instDecidablePairwise(v_00_u03b1_1803_, v_R_1804_, v_inst_1805_, v_x_1806_);
v_r_1808_ = lean_box(v_res_1807_);
return v_r_1808_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg___lam__0(lean_object* v_inst_1809_, lean_object* v_a_1810_, lean_object* v_b_1811_){
_start:
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = lean_apply_2(v_inst_1809_, v_a_1810_, v_b_1811_);
v___x_1813_ = lean_unbox(v___x_1812_);
if (v___x_1813_ == 0)
{
uint8_t v___x_1814_; 
v___x_1814_ = 1;
return v___x_1814_;
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = 0;
return v___x_1815_;
}
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___lam__0___boxed(lean_object* v_inst_1816_, lean_object* v_a_1817_, lean_object* v_b_1818_){
_start:
{
uint8_t v_res_1819_; lean_object* v_r_1820_; 
v_res_1819_ = l_List_nodupDecidable___redArg___lam__0(v_inst_1816_, v_a_1817_, v_b_1818_);
v_r_1820_ = lean_box(v_res_1819_);
return v_r_1820_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg(lean_object* v_inst_1821_, lean_object* v_l_1822_){
_start:
{
lean_object* v___f_1823_; uint8_t v___x_1824_; 
v___f_1823_ = lean_alloc_closure((void*)(l_List_nodupDecidable___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1823_, 0, v_inst_1821_);
v___x_1824_ = l_List_instDecidablePairwise___redArg(v___f_1823_, v_l_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___boxed(lean_object* v_inst_1825_, lean_object* v_l_1826_){
_start:
{
uint8_t v_res_1827_; lean_object* v_r_1828_; 
v_res_1827_ = l_List_nodupDecidable___redArg(v_inst_1825_, v_l_1826_);
v_r_1828_ = lean_box(v_res_1827_);
return v_r_1828_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable(lean_object* v_00_u03b1_1829_, lean_object* v_inst_1830_, lean_object* v_l_1831_){
_start:
{
uint8_t v___x_1832_; 
v___x_1832_ = l_List_nodupDecidable___redArg(v_inst_1830_, v_l_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___boxed(lean_object* v_00_u03b1_1833_, lean_object* v_inst_1834_, lean_object* v_l_1835_){
_start:
{
uint8_t v_res_1836_; lean_object* v_r_1837_; 
v_res_1836_ = l_List_nodupDecidable(v_00_u03b1_1833_, v_inst_1834_, v_l_1835_);
v_r_1837_ = lean_box(v_res_1836_);
return v_r_1837_;
}
}
LEAN_EXPORT lean_object* l_List_replace___redArg(lean_object* v_inst_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_){
_start:
{
if (lean_obj_tag(v_x_1839_) == 0)
{
lean_dec(v_x_1841_);
lean_dec(v_x_1840_);
lean_dec_ref(v_inst_1838_);
return v_x_1839_;
}
else
{
lean_object* v_head_1842_; lean_object* v_tail_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1856_; 
v_head_1842_ = lean_ctor_get(v_x_1839_, 0);
v_tail_1843_ = lean_ctor_get(v_x_1839_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_x_1839_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1845_ = v_x_1839_;
v_isShared_1846_ = v_isSharedCheck_1856_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_tail_1843_);
lean_inc(v_head_1842_);
lean_dec(v_x_1839_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1856_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
lean_inc_ref(v_inst_1838_);
lean_inc(v_head_1842_);
lean_inc(v_x_1840_);
v___x_1847_ = lean_apply_2(v_inst_1838_, v_x_1840_, v_head_1842_);
v___x_1848_ = lean_unbox(v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = l_List_replace___redArg(v_inst_1838_, v_tail_1843_, v_x_1840_, v_x_1841_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v___x_1849_);
v___x_1851_ = v___x_1845_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_head_1842_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
else
{
lean_object* v___x_1854_; 
lean_dec(v_head_1842_);
lean_dec(v_x_1840_);
lean_dec_ref(v_inst_1838_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v_x_1841_);
v___x_1854_ = v___x_1845_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_x_1841_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_tail_1843_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_replace(lean_object* v_00_u03b1_1857_, lean_object* v_inst_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_List_replace___redArg(v_inst_1858_, v_x_1859_, v_x_1860_, v_x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg(lean_object* v_f_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v_zero_1866_; uint8_t v_isZero_1867_; 
v_zero_1866_ = lean_unsigned_to_nat(0u);
v_isZero_1867_ = lean_nat_dec_eq(v_a_1864_, v_zero_1866_);
if (v_isZero_1867_ == 1)
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_apply_1(v_f_1863_, v_a_1865_);
return v___x_1868_;
}
else
{
if (lean_obj_tag(v_a_1865_) == 0)
{
lean_dec_ref(v_f_1863_);
return v_a_1865_;
}
else
{
lean_object* v_head_1869_; lean_object* v_tail_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1880_; 
v_head_1869_ = lean_ctor_get(v_a_1865_, 0);
v_tail_1870_ = lean_ctor_get(v_a_1865_, 1);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_a_1865_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1872_ = v_a_1865_;
v_isShared_1873_ = v_isSharedCheck_1880_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_tail_1870_);
lean_inc(v_head_1869_);
lean_dec(v_a_1865_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1880_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_one_1874_; lean_object* v_n_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v_one_1874_ = lean_unsigned_to_nat(1u);
v_n_1875_ = lean_nat_sub(v_a_1864_, v_one_1874_);
v___x_1876_ = l_List_modifyTailIdx_go___redArg(v_f_1863_, v_n_1875_, v_tail_1870_);
lean_dec(v_n_1875_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v___x_1876_);
v___x_1878_ = v___x_1872_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_head_1869_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg___boxed(lean_object* v_f_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_List_modifyTailIdx_go___redArg(v_f_1881_, v_a_1882_, v_a_1883_);
lean_dec(v_a_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go(lean_object* v_00_u03b1_1885_, lean_object* v_f_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_List_modifyTailIdx_go___redArg(v_f_1886_, v_a_1887_, v_a_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___boxed(lean_object* v_00_u03b1_1890_, lean_object* v_f_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_List_modifyTailIdx_go(v_00_u03b1_1890_, v_f_1891_, v_a_1892_, v_a_1893_);
lean_dec(v_a_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg(lean_object* v_l_1895_, lean_object* v_i_1896_, lean_object* v_f_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_List_modifyTailIdx_go___redArg(v_f_1897_, v_i_1896_, v_l_1895_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg___boxed(lean_object* v_l_1899_, lean_object* v_i_1900_, lean_object* v_f_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_List_modifyTailIdx___redArg(v_l_1899_, v_i_1900_, v_f_1901_);
lean_dec(v_i_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx(lean_object* v_00_u03b1_1903_, lean_object* v_l_1904_, lean_object* v_i_1905_, lean_object* v_f_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_List_modifyTailIdx_go___redArg(v_f_1906_, v_i_1905_, v_l_1904_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___boxed(lean_object* v_00_u03b1_1908_, lean_object* v_l_1909_, lean_object* v_i_1910_, lean_object* v_f_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_List_modifyTailIdx(v_00_u03b1_1908_, v_l_1909_, v_i_1910_, v_f_1911_);
lean_dec(v_i_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_List_modifyHead___redArg(lean_object* v_f_1913_, lean_object* v_x_1914_){
_start:
{
if (lean_obj_tag(v_x_1914_) == 0)
{
lean_dec(v_f_1913_);
return v_x_1914_;
}
else
{
lean_object* v_head_1915_; lean_object* v_tail_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1924_; 
v_head_1915_ = lean_ctor_get(v_x_1914_, 0);
v_tail_1916_ = lean_ctor_get(v_x_1914_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_x_1914_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1918_ = v_x_1914_;
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_tail_1916_);
lean_inc(v_head_1915_);
lean_dec(v_x_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1920_ = lean_apply_1(v_f_1913_, v_head_1915_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1920_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_tail_1916_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyHead(lean_object* v_00_u03b1_1925_, lean_object* v_f_1926_, lean_object* v_x_1927_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_dec(v_f_1926_);
return v_x_1927_;
}
else
{
lean_object* v_head_1928_; lean_object* v_tail_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1937_; 
v_head_1928_ = lean_ctor_get(v_x_1927_, 0);
v_tail_1929_ = lean_ctor_get(v_x_1927_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1931_ = v_x_1927_;
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_tail_1929_);
lean_inc(v_head_1928_);
lean_dec(v_x_1927_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = lean_apply_1(v_f_1926_, v_head_1928_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1933_);
v___x_1935_ = v___x_1931_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_tail_1929_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg(lean_object* v_l_1938_, lean_object* v_i_1939_, lean_object* v_f_1940_){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1941_, 0, lean_box(0));
lean_closure_set(v___x_1941_, 1, v_f_1940_);
v___x_1942_ = l_List_modifyTailIdx_go___redArg(v___x_1941_, v_i_1939_, v_l_1938_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg___boxed(lean_object* v_l_1943_, lean_object* v_i_1944_, lean_object* v_f_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_List_modify___redArg(v_l_1943_, v_i_1944_, v_f_1945_);
lean_dec(v_i_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_List_modify(lean_object* v_00_u03b1_1947_, lean_object* v_l_1948_, lean_object* v_i_1949_, lean_object* v_f_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1951_, 0, lean_box(0));
lean_closure_set(v___x_1951_, 1, v_f_1950_);
v___x_1952_ = l_List_modifyTailIdx_go___redArg(v___x_1951_, v_i_1949_, v_l_1948_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_List_modify___boxed(lean_object* v_00_u03b1_1953_, lean_object* v_l_1954_, lean_object* v_i_1955_, lean_object* v_f_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_List_modify(v_00_u03b1_1953_, v_l_1954_, v_i_1955_, v_f_1956_);
lean_dec(v_i_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object* v_inst_1958_, lean_object* v_a_1959_, lean_object* v_l_1960_){
_start:
{
uint8_t v___x_1961_; 
lean_inc(v_l_1960_);
lean_inc(v_a_1959_);
v___x_1961_ = l_List_elem___redArg(v_inst_1958_, v_a_1959_, v_l_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
v___x_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_a_1959_);
lean_ctor_set(v___x_1962_, 1, v_l_1960_);
return v___x_1962_;
}
else
{
lean_dec(v_a_1959_);
return v_l_1960_;
}
}
}
LEAN_EXPORT lean_object* l_List_insert(lean_object* v_00_u03b1_1963_, lean_object* v_inst_1964_, lean_object* v_a_1965_, lean_object* v_l_1966_){
_start:
{
uint8_t v___x_1967_; 
lean_inc(v_l_1966_);
lean_inc(v_a_1965_);
v___x_1967_ = l_List_elem___redArg(v_inst_1964_, v_a_1965_, v_l_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_a_1965_);
lean_ctor_set(v___x_1968_, 1, v_l_1966_);
return v___x_1968_;
}
else
{
lean_dec(v_a_1965_);
return v_l_1966_;
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_zero_1972_; uint8_t v_isZero_1973_; 
v_zero_1972_ = lean_unsigned_to_nat(0u);
v_isZero_1973_ = lean_nat_dec_eq(v_a_1970_, v_zero_1972_);
if (v_isZero_1973_ == 1)
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_a_1969_);
lean_ctor_set(v___x_1974_, 1, v_a_1971_);
return v___x_1974_;
}
else
{
if (lean_obj_tag(v_a_1971_) == 0)
{
lean_dec(v_a_1969_);
return v_a_1971_;
}
else
{
lean_object* v_head_1975_; lean_object* v_tail_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1986_; 
v_head_1975_ = lean_ctor_get(v_a_1971_, 0);
v_tail_1976_ = lean_ctor_get(v_a_1971_, 1);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_a_1971_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1978_ = v_a_1971_;
v_isShared_1979_ = v_isSharedCheck_1986_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_tail_1976_);
lean_inc(v_head_1975_);
lean_dec(v_a_1971_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1986_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_one_1980_; lean_object* v_n_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v_one_1980_ = lean_unsigned_to_nat(1u);
v_n_1981_ = lean_nat_sub(v_a_1970_, v_one_1980_);
v___x_1982_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1969_, v_n_1981_, v_tail_1976_);
lean_dec(v_n_1981_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 1, v___x_1982_);
v___x_1984_ = v___x_1978_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_head_1975_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg___boxed(lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1987_, v_a_1988_, v_a_1989_);
lean_dec(v_a_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg(lean_object* v_xs_1991_, lean_object* v_i_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1993_, v_i_1992_, v_xs_1991_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___boxed(lean_object* v_xs_1995_, lean_object* v_i_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_List_insertIdx___redArg(v_xs_1995_, v_i_1996_, v_a_1997_);
lean_dec(v_i_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx(lean_object* v_00_u03b1_1999_, lean_object* v_xs_2000_, lean_object* v_i_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_2002_, v_i_2001_, v_xs_2000_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___boxed(lean_object* v_00_u03b1_2004_, lean_object* v_xs_2005_, lean_object* v_i_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_List_insertIdx(v_00_u03b1_2004_, v_xs_2005_, v_i_2006_, v_a_2007_);
lean_dec(v_i_2006_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(lean_object* v_00_u03b1_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_2010_, v_a_2011_, v_a_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___boxed(lean_object* v_00_u03b1_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(v_00_u03b1_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_a_2016_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_List_erase___redArg(lean_object* v_inst_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
if (lean_obj_tag(v_x_2020_) == 0)
{
lean_dec(v_x_2021_);
lean_dec_ref(v_inst_2019_);
return v_x_2020_;
}
else
{
lean_object* v_head_2022_; lean_object* v_tail_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2033_; 
v_head_2022_ = lean_ctor_get(v_x_2020_, 0);
v_tail_2023_ = lean_ctor_get(v_x_2020_, 1);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_x_2020_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2025_ = v_x_2020_;
v_isShared_2026_ = v_isSharedCheck_2033_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_tail_2023_);
lean_inc(v_head_2022_);
lean_dec(v_x_2020_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2033_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
lean_inc_ref(v_inst_2019_);
lean_inc(v_x_2021_);
lean_inc(v_head_2022_);
v___x_2027_ = lean_apply_2(v_inst_2019_, v_head_2022_, v_x_2021_);
v___x_2028_ = lean_unbox(v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = l_List_erase___redArg(v_inst_2019_, v_tail_2023_, v_x_2021_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 1, v___x_2029_);
v___x_2031_ = v___x_2025_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_head_2022_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
else
{
lean_del_object(v___x_2025_);
lean_dec(v_head_2022_);
lean_dec(v_x_2021_);
lean_dec_ref(v_inst_2019_);
return v_tail_2023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_erase(lean_object* v_00_u03b1_2034_, lean_object* v_inst_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_List_erase___redArg(v_inst_2035_, v_x_2036_, v_x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v_h__1_2041_, lean_object* v_h__2_2042_){
_start:
{
if (lean_obj_tag(v_x_2039_) == 0)
{
lean_object* v___x_2043_; 
lean_dec(v_h__2_2042_);
v___x_2043_ = lean_apply_1(v_h__1_2041_, v_x_2040_);
return v___x_2043_;
}
else
{
lean_object* v_head_2044_; lean_object* v_tail_2045_; lean_object* v___x_2046_; 
lean_dec(v_h__1_2041_);
v_head_2044_ = lean_ctor_get(v_x_2039_, 0);
lean_inc(v_head_2044_);
v_tail_2045_ = lean_ctor_get(v_x_2039_, 1);
lean_inc(v_tail_2045_);
lean_dec_ref(v_x_2039_);
v___x_2046_ = lean_apply_3(v_h__2_2042_, v_head_2044_, v_tail_2045_, v_x_2040_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object* v_00_u03b1_2047_, lean_object* v_motive_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v_h__1_2051_, lean_object* v_h__2_2052_){
_start:
{
if (lean_obj_tag(v_x_2049_) == 0)
{
lean_object* v___x_2053_; 
lean_dec(v_h__2_2052_);
v___x_2053_ = lean_apply_1(v_h__1_2051_, v_x_2050_);
return v___x_2053_;
}
else
{
lean_object* v_head_2054_; lean_object* v_tail_2055_; lean_object* v___x_2056_; 
lean_dec(v_h__1_2051_);
v_head_2054_ = lean_ctor_get(v_x_2049_, 0);
lean_inc(v_head_2054_);
v_tail_2055_ = lean_ctor_get(v_x_2049_, 1);
lean_inc(v_tail_2055_);
lean_dec_ref(v_x_2049_);
v___x_2056_ = lean_apply_3(v_h__2_2052_, v_head_2054_, v_tail_2055_, v_x_2050_);
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP___redArg(lean_object* v_p_2057_, lean_object* v_x_2058_){
_start:
{
if (lean_obj_tag(v_x_2058_) == 0)
{
lean_dec_ref(v_p_2057_);
return v_x_2058_;
}
else
{
lean_object* v_head_2059_; lean_object* v_tail_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2070_; 
v_head_2059_ = lean_ctor_get(v_x_2058_, 0);
v_tail_2060_ = lean_ctor_get(v_x_2058_, 1);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_x_2058_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2062_ = v_x_2058_;
v_isShared_2063_ = v_isSharedCheck_2070_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_tail_2060_);
lean_inc(v_head_2059_);
lean_dec(v_x_2058_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2070_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
lean_inc_ref(v_p_2057_);
lean_inc(v_head_2059_);
v___x_2064_ = lean_apply_1(v_p_2057_, v_head_2059_);
v___x_2065_ = lean_unbox(v___x_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = l_List_eraseP___redArg(v_p_2057_, v_tail_2060_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 1, v___x_2066_);
v___x_2068_ = v___x_2062_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_head_2059_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
else
{
lean_del_object(v___x_2062_);
lean_dec(v_head_2059_);
lean_dec_ref(v_p_2057_);
return v_tail_2060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP(lean_object* v_00_u03b1_2071_, lean_object* v_p_2072_, lean_object* v_x_2073_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_List_eraseP___redArg(v_p_2072_, v_x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg(lean_object* v_x_2075_, lean_object* v_x_2076_){
_start:
{
if (lean_obj_tag(v_x_2075_) == 0)
{
return v_x_2075_;
}
else
{
lean_object* v_head_2077_; lean_object* v_tail_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2090_; 
v_head_2077_ = lean_ctor_get(v_x_2075_, 0);
v_tail_2078_ = lean_ctor_get(v_x_2075_, 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_x_2075_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2080_ = v_x_2075_;
v_isShared_2081_ = v_isSharedCheck_2090_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_tail_2078_);
lean_inc(v_head_2077_);
lean_dec(v_x_2075_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2090_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_zero_2082_; uint8_t v_isZero_2083_; 
v_zero_2082_ = lean_unsigned_to_nat(0u);
v_isZero_2083_ = lean_nat_dec_eq(v_x_2076_, v_zero_2082_);
if (v_isZero_2083_ == 1)
{
lean_del_object(v___x_2080_);
lean_dec(v_head_2077_);
return v_tail_2078_;
}
else
{
lean_object* v_one_2084_; lean_object* v_n_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v_one_2084_ = lean_unsigned_to_nat(1u);
v_n_2085_ = lean_nat_sub(v_x_2076_, v_one_2084_);
v___x_2086_ = l_List_eraseIdx___redArg(v_tail_2078_, v_n_2085_);
lean_dec(v_n_2085_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 1, v___x_2086_);
v___x_2088_ = v___x_2080_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_head_2077_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg___boxed(lean_object* v_x_2091_, lean_object* v_x_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_List_eraseIdx___redArg(v_x_2091_, v_x_2092_);
lean_dec(v_x_2092_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object* v_00_u03b1_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_List_eraseIdx___redArg(v_x_2095_, v_x_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___boxed(lean_object* v_00_u03b1_2098_, lean_object* v_x_2099_, lean_object* v_x_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_List_eraseIdx(v_00_u03b1_2098_, v_x_2099_, v_x_2100_);
lean_dec(v_x_2100_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object* v_p_2102_, lean_object* v_x_2103_){
_start:
{
if (lean_obj_tag(v_x_2103_) == 0)
{
lean_object* v___x_2104_; 
lean_dec_ref(v_p_2102_);
v___x_2104_ = lean_box(0);
return v___x_2104_;
}
else
{
lean_object* v_head_2105_; lean_object* v_tail_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v_head_2105_ = lean_ctor_get(v_x_2103_, 0);
lean_inc_n(v_head_2105_, 2);
v_tail_2106_ = lean_ctor_get(v_x_2103_, 1);
lean_inc(v_tail_2106_);
lean_dec_ref(v_x_2103_);
lean_inc_ref(v_p_2102_);
v___x_2107_ = lean_apply_1(v_p_2102_, v_head_2105_);
v___x_2108_ = lean_unbox(v___x_2107_);
if (v___x_2108_ == 0)
{
lean_dec(v_head_2105_);
v_x_2103_ = v_tail_2106_;
goto _start;
}
else
{
lean_object* v___x_2110_; 
lean_dec(v_tail_2106_);
lean_dec_ref(v_p_2102_);
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_head_2105_);
return v___x_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object* v_00_u03b1_2111_, lean_object* v_p_2112_, lean_object* v_x_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_List_find_x3f___redArg(v_p_2112_, v_x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object* v_f_2115_, lean_object* v_x_2116_){
_start:
{
if (lean_obj_tag(v_x_2116_) == 0)
{
lean_object* v___x_2117_; 
lean_dec_ref(v_f_2115_);
v___x_2117_ = lean_box(0);
return v___x_2117_;
}
else
{
lean_object* v_head_2118_; lean_object* v_tail_2119_; lean_object* v___x_2120_; 
v_head_2118_ = lean_ctor_get(v_x_2116_, 0);
lean_inc(v_head_2118_);
v_tail_2119_ = lean_ctor_get(v_x_2116_, 1);
lean_inc(v_tail_2119_);
lean_dec_ref(v_x_2116_);
lean_inc_ref(v_f_2115_);
v___x_2120_ = lean_apply_1(v_f_2115_, v_head_2118_);
if (lean_obj_tag(v___x_2120_) == 0)
{
v_x_2116_ = v_tail_2119_;
goto _start;
}
else
{
lean_dec(v_tail_2119_);
lean_dec_ref(v_f_2115_);
return v___x_2120_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object* v_00_u03b1_2122_, lean_object* v_00_u03b2_2123_, lean_object* v_f_2124_, lean_object* v_x_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_List_findSome_x3f___redArg(v_f_2124_, v_x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f___redArg(lean_object* v_p_2127_, lean_object* v_x_2128_){
_start:
{
if (lean_obj_tag(v_x_2128_) == 0)
{
lean_object* v___x_2129_; 
lean_dec_ref(v_p_2127_);
v___x_2129_ = lean_box(0);
return v___x_2129_;
}
else
{
lean_object* v_head_2130_; lean_object* v_tail_2131_; lean_object* v___x_2132_; 
v_head_2130_ = lean_ctor_get(v_x_2128_, 0);
lean_inc(v_head_2130_);
v_tail_2131_ = lean_ctor_get(v_x_2128_, 1);
lean_inc(v_tail_2131_);
lean_dec_ref(v_x_2128_);
lean_inc_ref(v_p_2127_);
v___x_2132_ = l_List_findRev_x3f___redArg(v_p_2127_, v_tail_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; uint8_t v___x_2134_; 
lean_inc(v_head_2130_);
v___x_2133_ = lean_apply_1(v_p_2127_, v_head_2130_);
v___x_2134_ = lean_unbox(v___x_2133_);
if (v___x_2134_ == 0)
{
lean_dec(v_head_2130_);
return v___x_2132_;
}
else
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_head_2130_);
return v___x_2135_;
}
}
else
{
lean_dec(v_head_2130_);
lean_dec_ref(v_p_2127_);
return v___x_2132_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f(lean_object* v_00_u03b1_2136_, lean_object* v_p_2137_, lean_object* v_x_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_List_findRev_x3f___redArg(v_p_2137_, v_x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f___redArg(lean_object* v_f_2140_, lean_object* v_x_2141_){
_start:
{
if (lean_obj_tag(v_x_2141_) == 0)
{
lean_object* v___x_2142_; 
lean_dec_ref(v_f_2140_);
v___x_2142_ = lean_box(0);
return v___x_2142_;
}
else
{
lean_object* v_head_2143_; lean_object* v_tail_2144_; lean_object* v___x_2145_; 
v_head_2143_ = lean_ctor_get(v_x_2141_, 0);
lean_inc(v_head_2143_);
v_tail_2144_ = lean_ctor_get(v_x_2141_, 1);
lean_inc(v_tail_2144_);
lean_dec_ref(v_x_2141_);
lean_inc_ref(v_f_2140_);
v___x_2145_ = l_List_findSomeRev_x3f___redArg(v_f_2140_, v_tail_2144_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_apply_1(v_f_2140_, v_head_2143_);
return v___x_2146_;
}
else
{
lean_dec(v_head_2143_);
lean_dec_ref(v_f_2140_);
return v___x_2145_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f(lean_object* v_00_u03b1_2147_, lean_object* v_00_u03b2_2148_, lean_object* v_f_2149_, lean_object* v_x_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_List_findSomeRev_x3f___redArg(v_f_2149_, v_x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___redArg(lean_object* v_p_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
if (lean_obj_tag(v_a_2153_) == 0)
{
lean_dec_ref(v_p_2152_);
return v_a_2154_;
}
else
{
lean_object* v_head_2155_; lean_object* v_tail_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v_head_2155_ = lean_ctor_get(v_a_2153_, 0);
lean_inc(v_head_2155_);
v_tail_2156_ = lean_ctor_get(v_a_2153_, 1);
lean_inc(v_tail_2156_);
lean_dec_ref(v_a_2153_);
lean_inc_ref(v_p_2152_);
v___x_2157_ = lean_apply_1(v_p_2152_, v_head_2155_);
v___x_2158_ = lean_unbox(v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_unsigned_to_nat(1u);
v___x_2160_ = lean_nat_add(v_a_2154_, v___x_2159_);
lean_dec(v_a_2154_);
v_a_2153_ = v_tail_2156_;
v_a_2154_ = v___x_2160_;
goto _start;
}
else
{
lean_dec(v_tail_2156_);
lean_dec_ref(v_p_2152_);
return v_a_2154_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object* v_00_u03b1_2162_, lean_object* v_p_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_List_findIdx_go___redArg(v_p_2163_, v_a_2164_, v_a_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx___redArg(lean_object* v_p_2167_, lean_object* v_l_2168_){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = lean_unsigned_to_nat(0u);
v___x_2170_ = l_List_findIdx_go___redArg(v_p_2167_, v_l_2168_, v___x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx(lean_object* v_00_u03b1_2171_, lean_object* v_p_2172_, lean_object* v_l_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = l_List_findIdx_go___redArg(v_p_2172_, v_l_2173_, v___x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT uint8_t l_List_idxOf___redArg___lam__0(lean_object* v_inst_2176_, lean_object* v_a_2177_, lean_object* v_x_2178_){
_start:
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_apply_2(v_inst_2176_, v_x_2178_, v_a_2177_);
v___x_2180_ = lean_unbox(v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg___lam__0___boxed(lean_object* v_inst_2181_, lean_object* v_a_2182_, lean_object* v_x_2183_){
_start:
{
uint8_t v_res_2184_; lean_object* v_r_2185_; 
v_res_2184_ = l_List_idxOf___redArg___lam__0(v_inst_2181_, v_a_2182_, v_x_2183_);
v_r_2185_ = lean_box(v_res_2184_);
return v_r_2185_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg(lean_object* v_inst_2186_, lean_object* v_a_2187_, lean_object* v_l_2188_){
_start:
{
lean_object* v___f_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___f_2189_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2189_, 0, v_inst_2186_);
lean_closure_set(v___f_2189_, 1, v_a_2187_);
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = l_List_findIdx_go___redArg(v___f_2189_, v_l_2188_, v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf(lean_object* v_00_u03b1_2192_, lean_object* v_inst_2193_, lean_object* v_a_2194_, lean_object* v_l_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_List_idxOf___redArg(v_inst_2193_, v_a_2194_, v_l_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___redArg(lean_object* v_p_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
if (lean_obj_tag(v_a_2198_) == 0)
{
lean_object* v___x_2200_; 
lean_dec(v_a_2199_);
lean_dec_ref(v_p_2197_);
v___x_2200_ = lean_box(0);
return v___x_2200_;
}
else
{
lean_object* v_head_2201_; lean_object* v_tail_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_head_2201_ = lean_ctor_get(v_a_2198_, 0);
lean_inc(v_head_2201_);
v_tail_2202_ = lean_ctor_get(v_a_2198_, 1);
lean_inc(v_tail_2202_);
lean_dec_ref(v_a_2198_);
lean_inc_ref(v_p_2197_);
v___x_2203_ = lean_apply_1(v_p_2197_, v_head_2201_);
v___x_2204_ = lean_unbox(v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_unsigned_to_nat(1u);
v___x_2206_ = lean_nat_add(v_a_2199_, v___x_2205_);
lean_dec(v_a_2199_);
v_a_2198_ = v_tail_2202_;
v_a_2199_ = v___x_2206_;
goto _start;
}
else
{
lean_object* v___x_2208_; 
lean_dec(v_tail_2202_);
lean_dec_ref(v_p_2197_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_a_2199_);
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go(lean_object* v_00_u03b1_2209_, lean_object* v_p_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_List_findIdx_x3f_go___redArg(v_p_2210_, v_a_2211_, v_a_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f___redArg(lean_object* v_p_2214_, lean_object* v_l_2215_){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_unsigned_to_nat(0u);
v___x_2217_ = l_List_findIdx_x3f_go___redArg(v_p_2214_, v_l_2215_, v___x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object* v_00_u03b1_2218_, lean_object* v_p_2219_, lean_object* v_l_2220_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = l_List_findIdx_x3f_go___redArg(v_p_2219_, v_l_2220_, v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f___redArg(lean_object* v_inst_2223_, lean_object* v_a_2224_, lean_object* v_l_2225_){
_start:
{
lean_object* v___f_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___f_2226_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2226_, 0, v_inst_2223_);
lean_closure_set(v___f_2226_, 1, v_a_2224_);
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = l_List_findIdx_x3f_go___redArg(v___f_2226_, v_l_2225_, v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f(lean_object* v_00_u03b1_2229_, lean_object* v_inst_2230_, lean_object* v_a_2231_, lean_object* v_l_2232_){
_start:
{
lean_object* v___f_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___f_2233_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2233_, 0, v_inst_2230_);
lean_closure_set(v___f_2233_, 1, v_a_2231_);
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = l_List_findIdx_x3f_go___redArg(v___f_2233_, v_l_2232_, v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___redArg(lean_object* v_p_2236_, lean_object* v_l_x27_2237_, lean_object* v_i_2238_){
_start:
{
if (lean_obj_tag(v_l_x27_2237_) == 0)
{
lean_object* v___x_2239_; 
lean_dec(v_i_2238_);
lean_dec_ref(v_p_2236_);
v___x_2239_ = lean_box(0);
return v___x_2239_;
}
else
{
lean_object* v_head_2240_; lean_object* v_tail_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v_head_2240_ = lean_ctor_get(v_l_x27_2237_, 0);
lean_inc(v_head_2240_);
v_tail_2241_ = lean_ctor_get(v_l_x27_2237_, 1);
lean_inc(v_tail_2241_);
lean_dec_ref(v_l_x27_2237_);
lean_inc_ref(v_p_2236_);
v___x_2242_ = lean_apply_1(v_p_2236_, v_head_2240_);
v___x_2243_ = lean_unbox(v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_unsigned_to_nat(1u);
v___x_2245_ = lean_nat_add(v_i_2238_, v___x_2244_);
lean_dec(v_i_2238_);
v_l_x27_2237_ = v_tail_2241_;
v_i_2238_ = v___x_2245_;
goto _start;
}
else
{
lean_object* v___x_2247_; 
lean_dec(v_tail_2241_);
lean_dec_ref(v_p_2236_);
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_i_2238_);
return v___x_2247_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go(lean_object* v_00_u03b1_2248_, lean_object* v_p_2249_, lean_object* v_l_2250_, lean_object* v_l_x27_2251_, lean_object* v_i_2252_, lean_object* v_h_2253_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_List_findFinIdx_x3f_go___redArg(v_p_2249_, v_l_x27_2251_, v_i_2252_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___boxed(lean_object* v_00_u03b1_2255_, lean_object* v_p_2256_, lean_object* v_l_2257_, lean_object* v_l_x27_2258_, lean_object* v_i_2259_, lean_object* v_h_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_List_findFinIdx_x3f_go(v_00_u03b1_2255_, v_p_2256_, v_l_2257_, v_l_x27_2258_, v_i_2259_, v_h_2260_);
lean_dec(v_l_2257_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f___redArg(lean_object* v_p_2262_, lean_object* v_l_2263_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_unsigned_to_nat(0u);
v___x_2265_ = l_List_findFinIdx_x3f_go___redArg(v_p_2262_, v_l_2263_, v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f(lean_object* v_00_u03b1_2266_, lean_object* v_p_2267_, lean_object* v_l_2268_){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = l_List_findFinIdx_x3f_go___redArg(v_p_2267_, v_l_2268_, v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f___redArg(lean_object* v_inst_2271_, lean_object* v_a_2272_, lean_object* v_l_2273_){
_start:
{
lean_object* v___f_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___f_2274_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2274_, 0, v_inst_2271_);
lean_closure_set(v___f_2274_, 1, v_a_2272_);
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = l_List_findFinIdx_x3f_go___redArg(v___f_2274_, v_l_2273_, v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f(lean_object* v_00_u03b1_2277_, lean_object* v_inst_2278_, lean_object* v_a_2279_, lean_object* v_l_2280_){
_start:
{
lean_object* v___f_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___f_2281_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2281_, 0, v_inst_2278_);
lean_closure_set(v___f_2281_, 1, v_a_2279_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = l_List_findFinIdx_x3f_go___redArg(v___f_2281_, v_l_2280_, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___redArg(lean_object* v_p_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
if (lean_obj_tag(v_a_2285_) == 0)
{
lean_dec_ref(v_p_2284_);
return v_a_2286_;
}
else
{
lean_object* v_head_2287_; lean_object* v_tail_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; 
v_head_2287_ = lean_ctor_get(v_a_2285_, 0);
lean_inc(v_head_2287_);
v_tail_2288_ = lean_ctor_get(v_a_2285_, 1);
lean_inc(v_tail_2288_);
lean_dec_ref(v_a_2285_);
lean_inc_ref(v_p_2284_);
v___x_2289_ = lean_apply_1(v_p_2284_, v_head_2287_);
v___x_2290_ = lean_unbox(v___x_2289_);
if (v___x_2290_ == 0)
{
v_a_2285_ = v_tail_2288_;
goto _start;
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_unsigned_to_nat(1u);
v___x_2293_ = lean_nat_add(v_a_2286_, v___x_2292_);
lean_dec(v_a_2286_);
v_a_2285_ = v_tail_2288_;
v_a_2286_ = v___x_2293_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go(lean_object* v_00_u03b1_2295_, lean_object* v_p_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_List_countP_go___redArg(v_p_2296_, v_a_2297_, v_a_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_List_countP___redArg(lean_object* v_p_2300_, lean_object* v_l_2301_){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = l_List_countP_go___redArg(v_p_2300_, v_l_2301_, v___x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_List_countP(lean_object* v_00_u03b1_2304_, lean_object* v_p_2305_, lean_object* v_l_2306_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = lean_unsigned_to_nat(0u);
v___x_2308_ = l_List_countP_go___redArg(v_p_2305_, v_l_2306_, v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_List_count___redArg(lean_object* v_inst_2309_, lean_object* v_a_2310_, lean_object* v_l_2311_){
_start:
{
lean_object* v___f_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___f_2312_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2312_, 0, v_inst_2309_);
lean_closure_set(v___f_2312_, 1, v_a_2310_);
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = l_List_countP_go___redArg(v___f_2312_, v_l_2311_, v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_List_count(lean_object* v_00_u03b1_2315_, lean_object* v_inst_2316_, lean_object* v_a_2317_, lean_object* v_l_2318_){
_start:
{
lean_object* v___f_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___f_2319_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2319_, 0, v_inst_2316_);
lean_closure_set(v___f_2319_, 1, v_a_2317_);
v___x_2320_ = lean_unsigned_to_nat(0u);
v___x_2321_ = l_List_countP_go___redArg(v___f_2319_, v_l_2318_, v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___redArg(lean_object* v_inst_2322_, lean_object* v_x_2323_, lean_object* v_x_2324_){
_start:
{
if (lean_obj_tag(v_x_2324_) == 0)
{
lean_object* v___x_2325_; 
lean_dec(v_x_2323_);
lean_dec_ref(v_inst_2322_);
v___x_2325_ = lean_box(0);
return v___x_2325_;
}
else
{
lean_object* v_head_2326_; lean_object* v_tail_2327_; lean_object* v_fst_2328_; lean_object* v_snd_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_head_2326_ = lean_ctor_get(v_x_2324_, 0);
lean_inc(v_head_2326_);
v_tail_2327_ = lean_ctor_get(v_x_2324_, 1);
lean_inc(v_tail_2327_);
lean_dec_ref(v_x_2324_);
v_fst_2328_ = lean_ctor_get(v_head_2326_, 0);
lean_inc(v_fst_2328_);
v_snd_2329_ = lean_ctor_get(v_head_2326_, 1);
lean_inc(v_snd_2329_);
lean_dec(v_head_2326_);
lean_inc_ref(v_inst_2322_);
lean_inc(v_x_2323_);
v___x_2330_ = lean_apply_2(v_inst_2322_, v_x_2323_, v_fst_2328_);
v___x_2331_ = lean_unbox(v___x_2330_);
if (v___x_2331_ == 0)
{
lean_dec(v_snd_2329_);
v_x_2324_ = v_tail_2327_;
goto _start;
}
else
{
lean_object* v___x_2333_; 
lean_dec(v_tail_2327_);
lean_dec(v_x_2323_);
lean_dec_ref(v_inst_2322_);
v___x_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_snd_2329_);
return v___x_2333_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup(lean_object* v_00_u03b1_2334_, lean_object* v_00_u03b2_2335_, lean_object* v_inst_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_List_lookup___redArg(v_inst_2336_, v_x_2337_, v_x_2338_);
return v___x_2339_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1(void){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0));
v___x_2358_ = l_String_toRawSubstring_x27(v___x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object* v_x_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
lean_inc(v_x_2378_);
v___x_2382_ = l_Lean_Syntax_isOfKind(v_x_2378_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_dec(v_x_2378_);
v___x_2383_ = lean_box(1);
v___x_2384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
lean_ctor_set(v___x_2384_, 1, v_a_2380_);
return v___x_2384_;
}
else
{
lean_object* v_quotContext_2385_; lean_object* v_currMacroScope_2386_; lean_object* v_ref_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_quotContext_2385_ = lean_ctor_get(v_a_2379_, 1);
v_currMacroScope_2386_ = lean_ctor_get(v_a_2379_, 2);
v_ref_2387_ = lean_ctor_get(v_a_2379_, 5);
v___x_2388_ = lean_unsigned_to_nat(0u);
v___x_2389_ = l_Lean_Syntax_getArg(v_x_2378_, v___x_2388_);
v___x_2390_ = lean_unsigned_to_nat(2u);
v___x_2391_ = l_Lean_Syntax_getArg(v_x_2378_, v___x_2390_);
lean_dec(v_x_2378_);
v___x_2392_ = 0;
v___x_2393_ = l_Lean_SourceInfo_fromRef(v_ref_2387_, v___x_2392_);
v___x_2394_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_2395_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
v___x_2396_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2));
lean_inc(v_currMacroScope_2386_);
lean_inc(v_quotContext_2385_);
v___x_2397_ = l_Lean_addMacroScope(v_quotContext_2385_, v___x_2396_, v_currMacroScope_2386_);
v___x_2398_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8));
lean_inc_n(v___x_2393_, 2);
v___x_2399_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2393_);
lean_ctor_set(v___x_2399_, 1, v___x_2395_);
lean_ctor_set(v___x_2399_, 2, v___x_2397_);
lean_ctor_set(v___x_2399_, 3, v___x_2398_);
v___x_2400_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_2401_ = l_Lean_Syntax_node2(v___x_2393_, v___x_2400_, v___x_2389_, v___x_2391_);
v___x_2402_ = l_Lean_Syntax_node2(v___x_2393_, v___x_2394_, v___x_2399_, v___x_2401_);
v___x_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v_a_2380_);
return v___x_2403_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___boxed(lean_object* v_x_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(v_x_2404_, v_a_2405_, v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object* v_x_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2411_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_2408_);
v___x_2412_ = l_Lean_Syntax_isOfKind(v_x_2408_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_dec(v_x_2408_);
v___x_2413_ = lean_box(0);
v___x_2414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
lean_ctor_set(v___x_2414_, 1, v_a_2410_);
return v___x_2414_;
}
else
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = l_Lean_Syntax_getArg(v_x_2408_, v___x_2415_);
v___x_2417_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_2416_);
v___x_2418_ = l_Lean_Syntax_isOfKind(v___x_2416_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
lean_dec(v___x_2416_);
lean_dec(v_x_2408_);
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v_a_2410_);
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2421_ = lean_unsigned_to_nat(1u);
v___x_2422_ = l_Lean_Syntax_getArg(v_x_2408_, v___x_2421_);
lean_dec(v_x_2408_);
v___x_2423_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2422_);
v___x_2424_ = l_Lean_Syntax_matchesNull(v___x_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec(v___x_2422_);
lean_dec(v___x_2416_);
v___x_2425_ = lean_box(0);
v___x_2426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set(v___x_2426_, 1, v_a_2410_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v_ref_2429_; uint8_t v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2427_ = l_Lean_Syntax_getArg(v___x_2422_, v___x_2415_);
v___x_2428_ = l_Lean_Syntax_getArg(v___x_2422_, v___x_2421_);
lean_dec(v___x_2422_);
v_ref_2429_ = l_Lean_replaceRef(v___x_2416_, v_a_2409_);
lean_dec(v___x_2416_);
v___x_2430_ = 0;
v___x_2431_ = l_Lean_SourceInfo_fromRef(v_ref_2429_, v___x_2430_);
lean_dec(v_ref_2429_);
v___x_2432_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
v___x_2433_ = ((lean_object*)(l_List_term___x7e___00__closed__2));
lean_inc(v___x_2431_);
v___x_2434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2431_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = l_Lean_Syntax_node3(v___x_2431_, v___x_2432_, v___x_2427_, v___x_2434_, v___x_2428_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v_a_2410_);
return v___x_2436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object* v_x_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(v_x_2437_, v_a_2438_, v_a_2439_);
lean_dec(v_a_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm___redArg(lean_object* v_inst_2441_, lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
if (lean_obj_tag(v_x_2442_) == 0)
{
uint8_t v___x_2444_; 
lean_dec_ref(v_inst_2441_);
v___x_2444_ = l_List_isEmpty___redArg(v_x_2443_);
lean_dec(v_x_2443_);
return v___x_2444_;
}
else
{
lean_object* v_head_2445_; lean_object* v_tail_2446_; uint8_t v___x_2447_; 
v_head_2445_ = lean_ctor_get(v_x_2442_, 0);
lean_inc_n(v_head_2445_, 2);
v_tail_2446_ = lean_ctor_get(v_x_2442_, 1);
lean_inc(v_tail_2446_);
lean_dec_ref(v_x_2442_);
lean_inc(v_x_2443_);
lean_inc_ref(v_inst_2441_);
v___x_2447_ = l_List_elem___redArg(v_inst_2441_, v_head_2445_, v_x_2443_);
if (v___x_2447_ == 0)
{
lean_dec(v_tail_2446_);
lean_dec(v_head_2445_);
lean_dec(v_x_2443_);
lean_dec_ref(v_inst_2441_);
return v___x_2447_;
}
else
{
lean_object* v___x_2448_; 
lean_inc_ref(v_inst_2441_);
v___x_2448_ = l_List_erase___redArg(v_inst_2441_, v_x_2443_, v_head_2445_);
v_x_2442_ = v_tail_2446_;
v_x_2443_ = v___x_2448_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPerm___redArg___boxed(lean_object* v_inst_2450_, lean_object* v_x_2451_, lean_object* v_x_2452_){
_start:
{
uint8_t v_res_2453_; lean_object* v_r_2454_; 
v_res_2453_ = l_List_isPerm___redArg(v_inst_2450_, v_x_2451_, v_x_2452_);
v_r_2454_ = lean_box(v_res_2453_);
return v_r_2454_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm(lean_object* v_00_u03b1_2455_, lean_object* v_inst_2456_, lean_object* v_x_2457_, lean_object* v_x_2458_){
_start:
{
uint8_t v___x_2459_; 
v___x_2459_ = l_List_isPerm___redArg(v_inst_2456_, v_x_2457_, v_x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_List_isPerm___boxed(lean_object* v_00_u03b1_2460_, lean_object* v_inst_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_){
_start:
{
uint8_t v_res_2464_; lean_object* v_r_2465_; 
v_res_2464_ = l_List_isPerm(v_00_u03b1_2460_, v_inst_2461_, v_x_2462_, v_x_2463_);
v_r_2465_ = lean_box(v_res_2464_);
return v_r_2465_;
}
}
LEAN_EXPORT uint8_t l_List_any___redArg(lean_object* v_x_2466_, lean_object* v_x_2467_){
_start:
{
if (lean_obj_tag(v_x_2466_) == 0)
{
uint8_t v___x_2468_; 
lean_dec_ref(v_x_2467_);
v___x_2468_ = 0;
return v___x_2468_;
}
else
{
lean_object* v_head_2469_; lean_object* v_tail_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v_head_2469_ = lean_ctor_get(v_x_2466_, 0);
lean_inc(v_head_2469_);
v_tail_2470_ = lean_ctor_get(v_x_2466_, 1);
lean_inc(v_tail_2470_);
lean_dec_ref(v_x_2466_);
lean_inc_ref(v_x_2467_);
v___x_2471_ = lean_apply_1(v_x_2467_, v_head_2469_);
v___x_2472_ = lean_unbox(v___x_2471_);
if (v___x_2472_ == 0)
{
v_x_2466_ = v_tail_2470_;
goto _start;
}
else
{
uint8_t v___x_2474_; 
lean_dec(v_tail_2470_);
lean_dec_ref(v_x_2467_);
v___x_2474_ = lean_unbox(v___x_2471_);
return v___x_2474_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___redArg___boxed(lean_object* v_x_2475_, lean_object* v_x_2476_){
_start:
{
uint8_t v_res_2477_; lean_object* v_r_2478_; 
v_res_2477_ = l_List_any___redArg(v_x_2475_, v_x_2476_);
v_r_2478_ = lean_box(v_res_2477_);
return v_r_2478_;
}
}
LEAN_EXPORT uint8_t l_List_any(lean_object* v_00_u03b1_2479_, lean_object* v_x_2480_, lean_object* v_x_2481_){
_start:
{
uint8_t v___x_2482_; 
v___x_2482_ = l_List_any___redArg(v_x_2480_, v_x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_List_any___boxed(lean_object* v_00_u03b1_2483_, lean_object* v_x_2484_, lean_object* v_x_2485_){
_start:
{
uint8_t v_res_2486_; lean_object* v_r_2487_; 
v_res_2486_ = l_List_any(v_00_u03b1_2483_, v_x_2484_, v_x_2485_);
v_r_2487_ = lean_box(v_res_2486_);
return v_r_2487_;
}
}
LEAN_EXPORT uint8_t l_List_all___redArg(lean_object* v_x_2488_, lean_object* v_x_2489_){
_start:
{
if (lean_obj_tag(v_x_2488_) == 0)
{
uint8_t v___x_2490_; 
lean_dec_ref(v_x_2489_);
v___x_2490_ = 1;
return v___x_2490_;
}
else
{
lean_object* v_head_2491_; lean_object* v_tail_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
v_head_2491_ = lean_ctor_get(v_x_2488_, 0);
lean_inc(v_head_2491_);
v_tail_2492_ = lean_ctor_get(v_x_2488_, 1);
lean_inc(v_tail_2492_);
lean_dec_ref(v_x_2488_);
lean_inc_ref(v_x_2489_);
v___x_2493_ = lean_apply_1(v_x_2489_, v_head_2491_);
v___x_2494_ = lean_unbox(v___x_2493_);
if (v___x_2494_ == 0)
{
uint8_t v___x_2495_; 
lean_dec(v_tail_2492_);
lean_dec_ref(v_x_2489_);
v___x_2495_ = lean_unbox(v___x_2493_);
return v___x_2495_;
}
else
{
v_x_2488_ = v_tail_2492_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___redArg___boxed(lean_object* v_x_2497_, lean_object* v_x_2498_){
_start:
{
uint8_t v_res_2499_; lean_object* v_r_2500_; 
v_res_2499_ = l_List_all___redArg(v_x_2497_, v_x_2498_);
v_r_2500_ = lean_box(v_res_2499_);
return v_r_2500_;
}
}
LEAN_EXPORT uint8_t l_List_all(lean_object* v_00_u03b1_2501_, lean_object* v_x_2502_, lean_object* v_x_2503_){
_start:
{
uint8_t v___x_2504_; 
v___x_2504_ = l_List_all___redArg(v_x_2502_, v_x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_List_all___boxed(lean_object* v_00_u03b1_2505_, lean_object* v_x_2506_, lean_object* v_x_2507_){
_start:
{
uint8_t v_res_2508_; lean_object* v_r_2509_; 
v_res_2508_ = l_List_all(v_00_u03b1_2505_, v_x_2506_, v_x_2507_);
v_r_2509_ = lean_box(v_res_2508_);
return v_r_2509_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_or_spec__0(lean_object* v_x_2510_){
_start:
{
if (lean_obj_tag(v_x_2510_) == 0)
{
uint8_t v___x_2511_; 
v___x_2511_ = 0;
return v___x_2511_;
}
else
{
lean_object* v_head_2512_; uint8_t v___x_2513_; 
v_head_2512_ = lean_ctor_get(v_x_2510_, 0);
v___x_2513_ = lean_unbox(v_head_2512_);
if (v___x_2513_ == 0)
{
lean_object* v_tail_2514_; 
v_tail_2514_ = lean_ctor_get(v_x_2510_, 1);
v_x_2510_ = v_tail_2514_;
goto _start;
}
else
{
uint8_t v___x_2516_; 
v___x_2516_ = lean_unbox(v_head_2512_);
return v___x_2516_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_or_spec__0___boxed(lean_object* v_x_2517_){
_start:
{
uint8_t v_res_2518_; lean_object* v_r_2519_; 
v_res_2518_ = l_List_any___at___00List_or_spec__0(v_x_2517_);
lean_dec(v_x_2517_);
v_r_2519_ = lean_box(v_res_2518_);
return v_r_2519_;
}
}
LEAN_EXPORT uint8_t l_List_or(lean_object* v_bs_2520_){
_start:
{
uint8_t v___x_2521_; 
v___x_2521_ = l_List_any___at___00List_or_spec__0(v_bs_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object* v_bs_2522_){
_start:
{
uint8_t v_res_2523_; lean_object* v_r_2524_; 
v_res_2523_ = l_List_or(v_bs_2522_);
lean_dec(v_bs_2522_);
v_r_2524_ = lean_box(v_res_2523_);
return v_r_2524_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00List_and_spec__0(lean_object* v_x_2525_){
_start:
{
if (lean_obj_tag(v_x_2525_) == 0)
{
uint8_t v___x_2526_; 
v___x_2526_ = 1;
return v___x_2526_;
}
else
{
lean_object* v_head_2527_; uint8_t v___x_2528_; 
v_head_2527_ = lean_ctor_get(v_x_2525_, 0);
v___x_2528_ = lean_unbox(v_head_2527_);
if (v___x_2528_ == 0)
{
uint8_t v___x_2529_; 
v___x_2529_ = lean_unbox(v_head_2527_);
return v___x_2529_;
}
else
{
lean_object* v_tail_2530_; 
v_tail_2530_ = lean_ctor_get(v_x_2525_, 1);
v_x_2525_ = v_tail_2530_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00List_and_spec__0___boxed(lean_object* v_x_2532_){
_start:
{
uint8_t v_res_2533_; lean_object* v_r_2534_; 
v_res_2533_ = l_List_all___at___00List_and_spec__0(v_x_2532_);
lean_dec(v_x_2532_);
v_r_2534_ = lean_box(v_res_2533_);
return v_r_2534_;
}
}
LEAN_EXPORT uint8_t l_List_and(lean_object* v_bs_2535_){
_start:
{
uint8_t v___x_2536_; 
v___x_2536_ = l_List_all___at___00List_and_spec__0(v_bs_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object* v_bs_2537_){
_start:
{
uint8_t v_res_2538_; lean_object* v_r_2539_; 
v_res_2538_ = l_List_and(v_bs_2537_);
lean_dec(v_bs_2537_);
v_r_2539_ = lean_box(v_res_2538_);
return v_r_2539_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___redArg(lean_object* v_f_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_){
_start:
{
if (lean_obj_tag(v_x_2541_) == 0)
{
lean_object* v___x_2543_; 
lean_dec(v_x_2542_);
lean_dec(v_f_2540_);
v___x_2543_ = lean_box(0);
return v___x_2543_;
}
else
{
if (lean_obj_tag(v_x_2542_) == 0)
{
lean_object* v___x_2544_; 
lean_dec_ref(v_x_2541_);
lean_dec(v_f_2540_);
v___x_2544_ = lean_box(0);
return v___x_2544_;
}
else
{
lean_object* v_head_2545_; lean_object* v_tail_2546_; lean_object* v_head_2547_; lean_object* v_tail_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2557_; 
v_head_2545_ = lean_ctor_get(v_x_2541_, 0);
lean_inc(v_head_2545_);
v_tail_2546_ = lean_ctor_get(v_x_2541_, 1);
lean_inc(v_tail_2546_);
lean_dec_ref(v_x_2541_);
v_head_2547_ = lean_ctor_get(v_x_2542_, 0);
v_tail_2548_ = lean_ctor_get(v_x_2542_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_x_2542_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2550_ = v_x_2542_;
v_isShared_2551_ = v_isSharedCheck_2557_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_tail_2548_);
lean_inc(v_head_2547_);
lean_dec(v_x_2542_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2557_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
lean_inc(v_f_2540_);
v___x_2552_ = lean_apply_2(v_f_2540_, v_head_2545_, v_head_2547_);
v___x_2553_ = l_List_zipWith___redArg(v_f_2540_, v_tail_2546_, v_tail_2548_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v___x_2553_);
lean_ctor_set(v___x_2550_, 0, v___x_2552_);
v___x_2555_ = v___x_2550_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith(lean_object* v_00_u03b1_2558_, lean_object* v_00_u03b2_2559_, lean_object* v_00_u03b3_2560_, lean_object* v_f_2561_, lean_object* v_x_2562_, lean_object* v_x_2563_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_List_zipWith___redArg(v_f_2561_, v_x_2562_, v_x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object* v_x_2565_, lean_object* v_x_2566_, lean_object* v_h__1_2567_, lean_object* v_h__2_2568_){
_start:
{
if (lean_obj_tag(v_x_2565_) == 0)
{
lean_object* v___x_2569_; 
lean_dec(v_h__1_2567_);
v___x_2569_ = lean_apply_3(v_h__2_2568_, v_x_2565_, v_x_2566_, lean_box(0));
return v___x_2569_;
}
else
{
if (lean_obj_tag(v_x_2566_) == 0)
{
lean_object* v___x_2570_; 
lean_dec(v_h__1_2567_);
v___x_2570_ = lean_apply_3(v_h__2_2568_, v_x_2565_, v_x_2566_, lean_box(0));
return v___x_2570_;
}
else
{
lean_object* v_head_2571_; lean_object* v_tail_2572_; lean_object* v_head_2573_; lean_object* v_tail_2574_; lean_object* v___x_2575_; 
lean_dec(v_h__2_2568_);
v_head_2571_ = lean_ctor_get(v_x_2565_, 0);
lean_inc(v_head_2571_);
v_tail_2572_ = lean_ctor_get(v_x_2565_, 1);
lean_inc(v_tail_2572_);
lean_dec_ref(v_x_2565_);
v_head_2573_ = lean_ctor_get(v_x_2566_, 0);
lean_inc(v_head_2573_);
v_tail_2574_ = lean_ctor_get(v_x_2566_, 1);
lean_inc(v_tail_2574_);
lean_dec_ref(v_x_2566_);
v___x_2575_ = lean_apply_4(v_h__1_2567_, v_head_2571_, v_tail_2572_, v_head_2573_, v_tail_2574_);
return v___x_2575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object* v_00_u03b1_2576_, lean_object* v_00_u03b2_2577_, lean_object* v_motive_2578_, lean_object* v_x_2579_, lean_object* v_x_2580_, lean_object* v_h__1_2581_, lean_object* v_h__2_2582_){
_start:
{
if (lean_obj_tag(v_x_2579_) == 0)
{
lean_object* v___x_2583_; 
lean_dec(v_h__1_2581_);
v___x_2583_ = lean_apply_3(v_h__2_2582_, v_x_2579_, v_x_2580_, lean_box(0));
return v___x_2583_;
}
else
{
if (lean_obj_tag(v_x_2580_) == 0)
{
lean_object* v___x_2584_; 
lean_dec(v_h__1_2581_);
v___x_2584_ = lean_apply_3(v_h__2_2582_, v_x_2579_, v_x_2580_, lean_box(0));
return v___x_2584_;
}
else
{
lean_object* v_head_2585_; lean_object* v_tail_2586_; lean_object* v_head_2587_; lean_object* v_tail_2588_; lean_object* v___x_2589_; 
lean_dec(v_h__2_2582_);
v_head_2585_ = lean_ctor_get(v_x_2579_, 0);
lean_inc(v_head_2585_);
v_tail_2586_ = lean_ctor_get(v_x_2579_, 1);
lean_inc(v_tail_2586_);
lean_dec_ref(v_x_2579_);
v_head_2587_ = lean_ctor_get(v_x_2580_, 0);
lean_inc(v_head_2587_);
v_tail_2588_ = lean_ctor_get(v_x_2580_, 1);
lean_inc(v_tail_2588_);
lean_dec_ref(v_x_2580_);
v___x_2589_ = lean_apply_4(v_h__1_2581_, v_head_2585_, v_tail_2586_, v_head_2587_, v_tail_2588_);
return v___x_2589_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object* v_x_2590_, lean_object* v_x_2591_){
_start:
{
if (lean_obj_tag(v_x_2590_) == 0)
{
lean_object* v___x_2592_; 
lean_dec(v_x_2591_);
v___x_2592_ = lean_box(0);
return v___x_2592_;
}
else
{
if (lean_obj_tag(v_x_2591_) == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref(v_x_2590_);
v___x_2593_ = lean_box(0);
return v___x_2593_;
}
else
{
lean_object* v_head_2594_; lean_object* v_tail_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2612_; 
v_head_2594_ = lean_ctor_get(v_x_2590_, 0);
v_tail_2595_ = lean_ctor_get(v_x_2590_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_x_2590_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2597_ = v_x_2590_;
v_isShared_2598_ = v_isSharedCheck_2612_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_tail_2595_);
lean_inc(v_head_2594_);
lean_dec(v_x_2590_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2612_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v_head_2599_; lean_object* v_tail_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2611_; 
v_head_2599_ = lean_ctor_get(v_x_2591_, 0);
v_tail_2600_ = lean_ctor_get(v_x_2591_, 1);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_x_2591_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2602_ = v_x_2591_;
v_isShared_2603_ = v_isSharedCheck_2611_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_tail_2600_);
lean_inc(v_head_2599_);
lean_dec(v_x_2591_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2611_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set_tag(v___x_2597_, 0);
lean_ctor_set(v___x_2597_, 1, v_head_2599_);
v___x_2605_ = v___x_2597_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_head_2594_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_head_2599_);
v___x_2605_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2606_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_tail_2595_, v_tail_2600_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 1, v___x_2606_);
lean_ctor_set(v___x_2602_, 0, v___x_2605_);
v___x_2608_ = v___x_2602_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zip___redArg(lean_object* v_xs_2613_, lean_object* v_ys_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2613_, v_ys_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_List_zip(lean_object* v_00_u03b1_2616_, lean_object* v_00_u03b2_2617_, lean_object* v_xs_2618_, lean_object* v_ys_2619_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2618_, v_ys_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object* v_00_u03b1_2621_, lean_object* v_00_u03b2_2622_, lean_object* v_x_2623_, lean_object* v_x_2624_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_x_2623_, v_x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__0(lean_object* v_f_2626_, lean_object* v_b_2627_){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v_b_2627_);
v___x_2630_ = lean_apply_2(v_f_2626_, v___x_2628_, v___x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__1(lean_object* v_f_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_a_2632_);
v___x_2634_ = lean_box(0);
v___x_2635_ = lean_apply_2(v_f_2631_, v___x_2633_, v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object* v_f_2636_, lean_object* v_x_2637_, lean_object* v_x_2638_){
_start:
{
if (lean_obj_tag(v_x_2637_) == 0)
{
lean_object* v___f_2639_; lean_object* v___x_2640_; 
v___f_2639_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2639_, 0, v_f_2636_);
v___x_2640_ = l_List_map___redArg(v___f_2639_, v_x_2638_);
return v___x_2640_;
}
else
{
if (lean_obj_tag(v_x_2638_) == 0)
{
lean_object* v___f_2641_; lean_object* v___x_2642_; 
v___f_2641_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2641_, 0, v_f_2636_);
v___x_2642_ = l_List_map___redArg(v___f_2641_, v_x_2637_);
return v___x_2642_;
}
else
{
lean_object* v_head_2643_; lean_object* v_tail_2644_; lean_object* v_head_2645_; lean_object* v_tail_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2657_; 
v_head_2643_ = lean_ctor_get(v_x_2637_, 0);
lean_inc(v_head_2643_);
v_tail_2644_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_tail_2644_);
lean_dec_ref(v_x_2637_);
v_head_2645_ = lean_ctor_get(v_x_2638_, 0);
v_tail_2646_ = lean_ctor_get(v_x_2638_, 1);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_x_2638_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2648_ = v_x_2638_;
v_isShared_2649_ = v_isSharedCheck_2657_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_tail_2646_);
lean_inc(v_head_2645_);
lean_dec(v_x_2638_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2657_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_head_2643_);
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_head_2645_);
lean_inc(v_f_2636_);
v___x_2652_ = lean_apply_2(v_f_2636_, v___x_2650_, v___x_2651_);
v___x_2653_ = l_List_zipWithAll___redArg(v_f_2636_, v_tail_2644_, v_tail_2646_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 1, v___x_2653_);
lean_ctor_set(v___x_2648_, 0, v___x_2652_);
v___x_2655_ = v___x_2648_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object* v_00_u03b1_2658_, lean_object* v_00_u03b2_2659_, lean_object* v_00_u03b3_2660_, lean_object* v_f_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_List_zipWithAll___redArg(v_f_2661_, v_x_2662_, v_x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_List_unzip___redArg(lean_object* v_x_2665_){
_start:
{
if (lean_obj_tag(v_x_2665_) == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = ((lean_object*)(l_List_partition___redArg___closed__0));
return v___x_2666_;
}
else
{
lean_object* v_head_2667_; lean_object* v_tail_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2694_; 
v_head_2667_ = lean_ctor_get(v_x_2665_, 0);
v_tail_2668_ = lean_ctor_get(v_x_2665_, 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_x_2665_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2670_ = v_x_2665_;
v_isShared_2671_ = v_isSharedCheck_2694_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_tail_2668_);
lean_inc(v_head_2667_);
lean_dec(v_x_2665_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2694_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_fst_2672_; lean_object* v_snd_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2693_; 
v_fst_2672_ = lean_ctor_get(v_head_2667_, 0);
v_snd_2673_ = lean_ctor_get(v_head_2667_, 1);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_head_2667_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2675_ = v_head_2667_;
v_isShared_2676_ = v_isSharedCheck_2693_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_snd_2673_);
lean_inc(v_fst_2672_);
lean_dec(v_head_2667_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2693_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v_fst_2678_; lean_object* v_snd_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2692_; 
v___x_2677_ = l_List_unzip___redArg(v_tail_2668_);
v_fst_2678_ = lean_ctor_get(v___x_2677_, 0);
v_snd_2679_ = lean_ctor_get(v___x_2677_, 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2681_ = v___x_2677_;
v_isShared_2682_ = v_isSharedCheck_2692_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_snd_2679_);
lean_inc(v_fst_2678_);
lean_dec(v___x_2677_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2692_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v_fst_2678_);
lean_ctor_set(v___x_2670_, 0, v_fst_2672_);
v___x_2684_ = v___x_2670_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_fst_2672_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_fst_2678_);
v___x_2684_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2686_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set_tag(v___x_2675_, 1);
lean_ctor_set(v___x_2675_, 1, v_snd_2679_);
lean_ctor_set(v___x_2675_, 0, v_snd_2673_);
v___x_2686_ = v___x_2675_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_snd_2673_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_snd_2679_);
v___x_2686_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2688_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 1, v___x_2686_);
lean_ctor_set(v___x_2681_, 0, v___x_2684_);
v___x_2688_ = v___x_2681_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_unzip(lean_object* v_00_u03b1_2695_, lean_object* v_00_u03b2_2696_, lean_object* v_x_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_List_unzip___redArg(v_x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___lam__0(lean_object* v_inst_2699_, lean_object* v_x1_2700_, lean_object* v_x2_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_apply_2(v_inst_2699_, v_x1_2700_, v_x2_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg(lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_l_2705_){
_start:
{
lean_object* v___f_2706_; lean_object* v___x_2707_; 
v___f_2706_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2706_, 0, v_inst_2703_);
v___x_2707_ = l_List_foldr___redArg(v___f_2706_, v_inst_2704_, v_l_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___boxed(lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_l_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_List_sum___redArg(v_inst_2708_, v_inst_2709_, v_l_2710_);
lean_dec(v_inst_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_List_sum(lean_object* v_00_u03b1_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_l_2715_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_List_sum___redArg(v_inst_2713_, v_inst_2714_, v_l_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_List_sum___boxed(lean_object* v_00_u03b1_2717_, lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_l_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_List_sum(v_00_u03b1_2717_, v_inst_2718_, v_inst_2719_, v_l_2720_);
lean_dec(v_inst_2719_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg(lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_l_2724_){
_start:
{
lean_object* v___f_2725_; lean_object* v___x_2726_; 
v___f_2725_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2725_, 0, v_inst_2722_);
v___x_2726_ = l_List_foldr___redArg(v___f_2725_, v_inst_2723_, v_l_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg___boxed(lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_l_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_List_prod___redArg(v_inst_2727_, v_inst_2728_, v_l_2729_);
lean_dec(v_inst_2728_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_List_prod(lean_object* v_00_u03b1_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_l_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_List_prod___redArg(v_inst_2732_, v_inst_2733_, v_l_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_List_prod___boxed(lean_object* v_00_u03b1_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_l_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_List_prod(v_00_u03b1_2736_, v_inst_2737_, v_inst_2738_, v_l_2739_);
lean_dec(v_inst_2738_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_List_range_loop(lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v_zero_2743_; uint8_t v_isZero_2744_; 
v_zero_2743_ = lean_unsigned_to_nat(0u);
v_isZero_2744_ = lean_nat_dec_eq(v_a_2741_, v_zero_2743_);
if (v_isZero_2744_ == 1)
{
lean_dec(v_a_2741_);
return v_a_2742_;
}
else
{
lean_object* v_one_2745_; lean_object* v_n_2746_; lean_object* v___x_2747_; 
v_one_2745_ = lean_unsigned_to_nat(1u);
v_n_2746_ = lean_nat_sub(v_a_2741_, v_one_2745_);
lean_dec(v_a_2741_);
lean_inc(v_n_2746_);
v___x_2747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2747_, 0, v_n_2746_);
lean_ctor_set(v___x_2747_, 1, v_a_2742_);
v_a_2741_ = v_n_2746_;
v_a_2742_ = v___x_2747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range(lean_object* v_n_2749_){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_box(0);
v___x_2751_ = l_List_range_loop(v_n_2749_, v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27(lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_){
_start:
{
lean_object* v_zero_2755_; uint8_t v_isZero_2756_; 
v_zero_2755_ = lean_unsigned_to_nat(0u);
v_isZero_2756_ = lean_nat_dec_eq(v_x_2753_, v_zero_2755_);
if (v_isZero_2756_ == 1)
{
lean_object* v___x_2757_; 
lean_dec(v_x_2752_);
v___x_2757_ = lean_box(0);
return v___x_2757_;
}
else
{
lean_object* v_one_2758_; lean_object* v_n_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_one_2758_ = lean_unsigned_to_nat(1u);
v_n_2759_ = lean_nat_sub(v_x_2753_, v_one_2758_);
v___x_2760_ = lean_nat_add(v_x_2752_, v_x_2754_);
v___x_2761_ = l_List_range_x27(v___x_2760_, v_n_2759_, v_x_2754_);
lean_dec(v_n_2759_);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_x_2752_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
return v___x_2762_;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object* v_x_2763_, lean_object* v_x_2764_, lean_object* v_x_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_List_range_x27(v_x_2763_, v_x_2764_, v_x_2765_);
lean_dec(v_x_2765_);
lean_dec(v_x_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdx___redArg(lean_object* v_x_2767_, lean_object* v_x_2768_){
_start:
{
if (lean_obj_tag(v_x_2767_) == 0)
{
lean_object* v___x_2769_; 
lean_dec(v_x_2768_);
v___x_2769_ = lean_box(0);
return v___x_2769_;
}
else
{
lean_object* v_head_2770_; lean_object* v_tail_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2782_; 
v_head_2770_ = lean_ctor_get(v_x_2767_, 0);
v_tail_2771_ = lean_ctor_get(v_x_2767_, 1);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_x_2767_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2773_ = v_x_2767_;
v_isShared_2774_ = v_isSharedCheck_2782_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_tail_2771_);
lean_inc(v_head_2770_);
lean_dec(v_x_2767_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2782_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
lean_inc(v_x_2768_);
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v_head_2770_);
lean_ctor_set(v___x_2775_, 1, v_x_2768_);
v___x_2776_ = lean_unsigned_to_nat(1u);
v___x_2777_ = lean_nat_add(v_x_2768_, v___x_2776_);
lean_dec(v_x_2768_);
v___x_2778_ = l_List_zipIdx___redArg(v_tail_2771_, v___x_2777_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2778_);
lean_ctor_set(v___x_2773_, 0, v___x_2775_);
v___x_2780_ = v___x_2773_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdx(lean_object* v_00_u03b1_2783_, lean_object* v_x_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_List_zipIdx___redArg(v_x_2784_, v_x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object* v_inst_2787_, lean_object* v_x_2788_){
_start:
{
if (lean_obj_tag(v_x_2788_) == 0)
{
lean_object* v___x_2789_; 
lean_dec(v_inst_2787_);
v___x_2789_ = lean_box(0);
return v___x_2789_;
}
else
{
lean_object* v_head_2790_; lean_object* v_tail_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_head_2790_ = lean_ctor_get(v_x_2788_, 0);
lean_inc(v_head_2790_);
v_tail_2791_ = lean_ctor_get(v_x_2788_, 1);
lean_inc(v_tail_2791_);
lean_dec_ref(v_x_2788_);
v___x_2792_ = l_List_foldl___redArg(v_inst_2787_, v_head_2790_, v_tail_2791_);
v___x_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object* v_00_u03b1_2794_, lean_object* v_inst_2795_, lean_object* v_x_2796_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_List_min_x3f___redArg(v_inst_2795_, v_x_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object* v_inst_2798_, lean_object* v_x_2799_){
_start:
{
lean_object* v_head_2800_; lean_object* v_tail_2801_; lean_object* v___x_2802_; 
v_head_2800_ = lean_ctor_get(v_x_2799_, 0);
lean_inc(v_head_2800_);
v_tail_2801_ = lean_ctor_get(v_x_2799_, 1);
lean_inc(v_tail_2801_);
lean_dec(v_x_2799_);
v___x_2802_ = l_List_foldl___redArg(v_inst_2798_, v_head_2800_, v_tail_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_List_min(lean_object* v_00_u03b1_2803_, lean_object* v_inst_2804_, lean_object* v_x_2805_, lean_object* v_x_2806_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_List_min___redArg(v_inst_2804_, v_x_2805_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object* v_inst_2808_, lean_object* v_x_2809_){
_start:
{
if (lean_obj_tag(v_x_2809_) == 0)
{
lean_object* v___x_2810_; 
lean_dec(v_inst_2808_);
v___x_2810_ = lean_box(0);
return v___x_2810_;
}
else
{
lean_object* v_head_2811_; lean_object* v_tail_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_head_2811_ = lean_ctor_get(v_x_2809_, 0);
lean_inc(v_head_2811_);
v_tail_2812_ = lean_ctor_get(v_x_2809_, 1);
lean_inc(v_tail_2812_);
lean_dec_ref(v_x_2809_);
v___x_2813_ = l_List_foldl___redArg(v_inst_2808_, v_head_2811_, v_tail_2812_);
v___x_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object* v_00_u03b1_2815_, lean_object* v_inst_2816_, lean_object* v_x_2817_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_List_max_x3f___redArg(v_inst_2816_, v_x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object* v_inst_2819_, lean_object* v_x_2820_){
_start:
{
lean_object* v_head_2821_; lean_object* v_tail_2822_; lean_object* v___x_2823_; 
v_head_2821_ = lean_ctor_get(v_x_2820_, 0);
lean_inc(v_head_2821_);
v_tail_2822_ = lean_ctor_get(v_x_2820_, 1);
lean_inc(v_tail_2822_);
lean_dec(v_x_2820_);
v___x_2823_ = l_List_foldl___redArg(v_inst_2819_, v_head_2821_, v_tail_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_List_max(lean_object* v_00_u03b1_2824_, lean_object* v_inst_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_List_max___redArg(v_inst_2825_, v_x_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_List_intersperse___redArg(lean_object* v_sep_2829_, lean_object* v_x_2830_){
_start:
{
if (lean_obj_tag(v_x_2830_) == 0)
{
lean_dec(v_sep_2829_);
return v_x_2830_;
}
else
{
lean_object* v_tail_2831_; 
v_tail_2831_ = lean_ctor_get(v_x_2830_, 1);
if (lean_obj_tag(v_tail_2831_) == 0)
{
lean_dec(v_sep_2829_);
return v_x_2830_;
}
else
{
lean_object* v_head_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2841_; 
lean_inc_ref(v_tail_2831_);
v_head_2832_ = lean_ctor_get(v_x_2830_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_x_2830_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v_x_2830_, 1);
lean_dec(v_unused_2842_);
v___x_2834_ = v_x_2830_;
v_isShared_2835_ = v_isSharedCheck_2841_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_head_2832_);
lean_dec(v_x_2830_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2841_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v___x_2838_; 
lean_inc(v_sep_2829_);
v___x_2836_ = l_List_intersperse___redArg(v_sep_2829_, v_tail_2831_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 1, v___x_2836_);
lean_ctor_set(v___x_2834_, 0, v_sep_2829_);
v___x_2838_ = v___x_2834_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_sep_2829_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2839_, 0, v_head_2832_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
return v___x_2839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperse(lean_object* v_00_u03b1_2843_, lean_object* v_sep_2844_, lean_object* v_x_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_List_intersperse___redArg(v_sep_2844_, v_x_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(lean_object* v___x_2847_, lean_object* v_x_2848_){
_start:
{
if (lean_obj_tag(v_x_2848_) == 0)
{
uint8_t v___x_2849_; 
lean_dec_ref(v___x_2847_);
v___x_2849_ = 0;
return v___x_2849_;
}
else
{
lean_object* v_head_2850_; lean_object* v_tail_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_head_2850_ = lean_ctor_get(v_x_2848_, 0);
lean_inc(v_head_2850_);
v_tail_2851_ = lean_ctor_get(v_x_2848_, 1);
lean_inc(v_tail_2851_);
lean_dec_ref(v_x_2848_);
lean_inc_ref(v___x_2847_);
v___x_2852_ = lean_apply_1(v___x_2847_, v_head_2850_);
v___x_2853_ = lean_unbox(v___x_2852_);
if (v___x_2853_ == 0)
{
v_x_2848_ = v_tail_2851_;
goto _start;
}
else
{
uint8_t v___x_2855_; 
lean_dec(v_tail_2851_);
lean_dec_ref(v___x_2847_);
v___x_2855_ = lean_unbox(v___x_2852_);
return v___x_2855_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg___boxed(lean_object* v___x_2856_, lean_object* v_x_2857_){
_start:
{
uint8_t v_res_2858_; lean_object* v_r_2859_; 
v_res_2858_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2856_, v_x_2857_);
v_r_2859_ = lean_box(v_res_2858_);
return v_r_2859_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object* v_r_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_){
_start:
{
if (lean_obj_tag(v_a_2861_) == 0)
{
lean_object* v___x_2863_; 
lean_dec_ref(v_r_2860_);
v___x_2863_ = l_List_reverse___redArg(v_a_2862_);
return v___x_2863_;
}
else
{
lean_object* v_head_2864_; lean_object* v_tail_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2876_; 
v_head_2864_ = lean_ctor_get(v_a_2861_, 0);
v_tail_2865_ = lean_ctor_get(v_a_2861_, 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_a_2861_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2867_ = v_a_2861_;
v_isShared_2868_ = v_isSharedCheck_2876_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_tail_2865_);
lean_inc(v_head_2864_);
lean_dec(v_a_2861_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2876_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; uint8_t v___x_2870_; 
lean_inc_ref(v_r_2860_);
lean_inc(v_head_2864_);
v___x_2869_ = lean_apply_1(v_r_2860_, v_head_2864_);
lean_inc(v_a_2862_);
v___x_2870_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2869_, v_a_2862_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2872_; 
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v_a_2862_);
v___x_2872_ = v___x_2867_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_head_2864_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_a_2862_);
v___x_2872_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
v_a_2861_ = v_tail_2865_;
v_a_2862_ = v___x_2872_;
goto _start;
}
}
else
{
lean_del_object(v___x_2867_);
lean_dec(v_head_2864_);
v_a_2861_ = v_tail_2865_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object* v_00_u03b1_2877_, lean_object* v_r_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_List_eraseDupsBy_loop___redArg(v_r_2878_, v_a_2879_, v_a_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0(lean_object* v_00_u03b1_2882_, lean_object* v___x_2883_, lean_object* v_x_2884_){
_start:
{
uint8_t v___x_2885_; 
v___x_2885_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2883_, v_x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___boxed(lean_object* v_00_u03b1_2886_, lean_object* v___x_2887_, lean_object* v_x_2888_){
_start:
{
uint8_t v_res_2889_; lean_object* v_r_2890_; 
v_res_2889_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0(v_00_u03b1_2886_, v___x_2887_, v_x_2888_);
v_r_2890_ = lean_box(v_res_2889_);
return v_r_2890_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy___redArg(lean_object* v_r_2891_, lean_object* v_as_2892_){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = lean_box(0);
v___x_2894_ = l_List_eraseDupsBy_loop___redArg(v_r_2891_, v_as_2892_, v___x_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy(lean_object* v_00_u03b1_2895_, lean_object* v_r_2896_, lean_object* v_as_2897_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_List_eraseDupsBy___redArg(v_r_2896_, v_as_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT uint8_t l_List_eraseDups___redArg___lam__0(lean_object* v_inst_2899_, lean_object* v_x1_2900_, lean_object* v_x2_2901_){
_start:
{
lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2902_ = lean_apply_2(v_inst_2899_, v_x1_2900_, v_x2_2901_);
v___x_2903_ = lean_unbox(v___x_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg___lam__0___boxed(lean_object* v_inst_2904_, lean_object* v_x1_2905_, lean_object* v_x2_2906_){
_start:
{
uint8_t v_res_2907_; lean_object* v_r_2908_; 
v_res_2907_ = l_List_eraseDups___redArg___lam__0(v_inst_2904_, v_x1_2905_, v_x2_2906_);
v_r_2908_ = lean_box(v_res_2907_);
return v_r_2908_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg(lean_object* v_inst_2909_, lean_object* v_as_2910_){
_start:
{
lean_object* v___f_2911_; lean_object* v___x_2912_; 
v___f_2911_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2911_, 0, v_inst_2909_);
v___x_2912_ = l_List_eraseDupsBy___redArg(v___f_2911_, v_as_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object* v_00_u03b1_2913_, lean_object* v_inst_2914_, lean_object* v_as_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_List_eraseDups___redArg(v_inst_2914_, v_as_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop___redArg(lean_object* v_r_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
if (lean_obj_tag(v_a_2919_) == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec_ref(v_r_2917_);
v___x_2921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2921_, 0, v_a_2918_);
lean_ctor_set(v___x_2921_, 1, v_a_2920_);
v___x_2922_ = l_List_reverse___redArg(v___x_2921_);
return v___x_2922_;
}
else
{
lean_object* v_head_2923_; lean_object* v_tail_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2935_; 
v_head_2923_ = lean_ctor_get(v_a_2919_, 0);
v_tail_2924_ = lean_ctor_get(v_a_2919_, 1);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_a_2919_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2926_ = v_a_2919_;
v_isShared_2927_ = v_isSharedCheck_2935_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_tail_2924_);
lean_inc(v_head_2923_);
lean_dec(v_a_2919_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2935_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; uint8_t v___x_2929_; 
lean_inc_ref(v_r_2917_);
lean_inc(v_head_2923_);
lean_inc(v_a_2918_);
v___x_2928_ = lean_apply_2(v_r_2917_, v_a_2918_, v_head_2923_);
v___x_2929_ = lean_unbox(v___x_2928_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2931_; 
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 1, v_a_2920_);
lean_ctor_set(v___x_2926_, 0, v_a_2918_);
v___x_2931_ = v___x_2926_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2918_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_a_2920_);
v___x_2931_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
v_a_2918_ = v_head_2923_;
v_a_2919_ = v_tail_2924_;
v_a_2920_ = v___x_2931_;
goto _start;
}
}
else
{
lean_del_object(v___x_2926_);
lean_dec(v_head_2923_);
v_a_2919_ = v_tail_2924_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop(lean_object* v_00_u03b1_2936_, lean_object* v_r_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_List_eraseRepsBy_loop___redArg(v_r_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy___redArg(lean_object* v_r_2942_, lean_object* v_x_2943_){
_start:
{
if (lean_obj_tag(v_x_2943_) == 0)
{
lean_dec_ref(v_r_2942_);
return v_x_2943_;
}
else
{
lean_object* v_head_2944_; lean_object* v_tail_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_head_2944_ = lean_ctor_get(v_x_2943_, 0);
lean_inc(v_head_2944_);
v_tail_2945_ = lean_ctor_get(v_x_2943_, 1);
lean_inc(v_tail_2945_);
lean_dec_ref(v_x_2943_);
v___x_2946_ = lean_box(0);
v___x_2947_ = l_List_eraseRepsBy_loop___redArg(v_r_2942_, v_head_2944_, v_tail_2945_, v___x_2946_);
return v___x_2947_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy(lean_object* v_00_u03b1_2948_, lean_object* v_r_2949_, lean_object* v_x_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_List_eraseRepsBy___redArg(v_r_2949_, v_x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___redArg(lean_object* v_inst_2952_, lean_object* v_as_2953_){
_start:
{
lean_object* v___f_2954_; lean_object* v___x_2955_; 
v___f_2954_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2954_, 0, v_inst_2952_);
v___x_2955_ = l_List_eraseRepsBy___redArg(v___f_2954_, v_as_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object* v_00_u03b1_2956_, lean_object* v_inst_2957_, lean_object* v_as_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_List_eraseReps___redArg(v_inst_2957_, v_as_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___redArg(lean_object* v_p_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_){
_start:
{
if (lean_obj_tag(v_a_2961_) == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
lean_dec_ref(v_p_2960_);
v___x_2963_ = l_List_reverse___redArg(v_a_2962_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v_a_2961_);
return v___x_2964_;
}
else
{
lean_object* v_head_2965_; lean_object* v_tail_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v_head_2965_ = lean_ctor_get(v_a_2961_, 0);
v_tail_2966_ = lean_ctor_get(v_a_2961_, 1);
lean_inc_ref(v_p_2960_);
lean_inc(v_head_2965_);
v___x_2967_ = lean_apply_1(v_p_2960_, v_head_2965_);
v___x_2968_ = lean_unbox(v___x_2967_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec_ref(v_p_2960_);
v___x_2969_ = l_List_reverse___redArg(v_a_2962_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v_a_2961_);
return v___x_2970_;
}
else
{
lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2978_; 
lean_inc(v_tail_2966_);
lean_inc(v_head_2965_);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_a_2961_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; lean_object* v_unused_2980_; 
v_unused_2979_ = lean_ctor_get(v_a_2961_, 1);
lean_dec(v_unused_2979_);
v_unused_2980_ = lean_ctor_get(v_a_2961_, 0);
lean_dec(v_unused_2980_);
v___x_2972_ = v_a_2961_;
v_isShared_2973_ = v_isSharedCheck_2978_;
goto v_resetjp_2971_;
}
else
{
lean_dec(v_a_2961_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2978_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 1, v_a_2962_);
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_head_2965_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_a_2962_);
v___x_2975_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
v_a_2961_ = v_tail_2966_;
v_a_2962_ = v___x_2975_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop(lean_object* v_00_u03b1_2981_, lean_object* v_p_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_List_span_loop___redArg(v_p_2982_, v_a_2983_, v_a_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_List_span___redArg(lean_object* v_p_2986_, lean_object* v_as_2987_){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = lean_box(0);
v___x_2989_ = l_List_span_loop___redArg(v_p_2986_, v_as_2987_, v___x_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_List_span(lean_object* v_00_u03b1_2990_, lean_object* v_p_2991_, lean_object* v_as_2992_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_box(0);
v___x_2994_ = l_List_span_loop___redArg(v_p_2991_, v_as_2992_, v___x_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___redArg(lean_object* v_R_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
if (lean_obj_tag(v_a_2996_) == 0)
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec_ref(v_R_2995_);
v___x_3000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3000_, 0, v_a_2997_);
lean_ctor_set(v___x_3000_, 1, v_a_2998_);
v___x_3001_ = l_List_reverse___redArg(v___x_3000_);
v___x_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set(v___x_3002_, 1, v_a_2999_);
v___x_3003_ = l_List_reverse___redArg(v___x_3002_);
return v___x_3003_;
}
else
{
lean_object* v_head_3004_; lean_object* v_tail_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3022_; 
v_head_3004_ = lean_ctor_get(v_a_2996_, 0);
v_tail_3005_ = lean_ctor_get(v_a_2996_, 1);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_a_2996_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3007_ = v_a_2996_;
v_isShared_3008_ = v_isSharedCheck_3022_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_tail_3005_);
lean_inc(v_head_3004_);
lean_dec(v_a_2996_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3022_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
lean_inc_ref(v_R_2995_);
lean_inc(v_head_3004_);
lean_inc(v_a_2997_);
v___x_3009_ = lean_apply_2(v_R_2995_, v_a_2997_, v_head_3004_);
v___x_3010_ = lean_unbox(v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3011_ = lean_box(0);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 1, v_a_2998_);
lean_ctor_set(v___x_3007_, 0, v_a_2997_);
v___x_3013_ = v___x_3007_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_2997_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_a_2998_);
v___x_3013_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = l_List_reverse___redArg(v___x_3013_);
v___x_3015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
lean_ctor_set(v___x_3015_, 1, v_a_2999_);
v_a_2996_ = v_tail_3005_;
v_a_2997_ = v_head_3004_;
v_a_2998_ = v___x_3011_;
v_a_2999_ = v___x_3015_;
goto _start;
}
}
else
{
lean_object* v___x_3019_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 1, v_a_2998_);
lean_ctor_set(v___x_3007_, 0, v_a_2997_);
v___x_3019_ = v___x_3007_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_2997_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_a_2998_);
v___x_3019_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
v_a_2996_ = v_tail_3005_;
v_a_2997_ = v_head_3004_;
v_a_2998_ = v___x_3019_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop(lean_object* v_00_u03b1_3023_, lean_object* v_R_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_List_splitBy_loop___redArg(v_R_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___redArg(lean_object* v_R_3030_, lean_object* v_x_3031_){
_start:
{
if (lean_obj_tag(v_x_3031_) == 0)
{
lean_object* v___x_3032_; 
lean_dec_ref(v_R_3030_);
v___x_3032_ = lean_box(0);
return v___x_3032_;
}
else
{
lean_object* v_head_3033_; lean_object* v_tail_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v_head_3033_ = lean_ctor_get(v_x_3031_, 0);
lean_inc(v_head_3033_);
v_tail_3034_ = lean_ctor_get(v_x_3031_, 1);
lean_inc(v_tail_3034_);
lean_dec_ref(v_x_3031_);
v___x_3035_ = lean_box(0);
v___x_3036_ = l_List_splitBy_loop___redArg(v_R_3030_, v_tail_3034_, v_head_3033_, v___x_3035_, v___x_3035_);
return v___x_3036_;
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy(lean_object* v_00_u03b1_3037_, lean_object* v_R_3038_, lean_object* v_x_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_List_splitBy___redArg(v_R_3038_, v_x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___redArg___lam__0(lean_object* v_inst_3041_, lean_object* v_ys_3042_, lean_object* v_x_3043_){
_start:
{
uint8_t v___x_3044_; 
v___x_3044_ = l_List_elem___redArg(v_inst_3041_, v_x_3043_, v_ys_3042_);
if (v___x_3044_ == 0)
{
uint8_t v___x_3045_; 
v___x_3045_ = 1;
return v___x_3045_;
}
else
{
uint8_t v___x_3046_; 
v___x_3046_ = 0;
return v___x_3046_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg___lam__0___boxed(lean_object* v_inst_3047_, lean_object* v_ys_3048_, lean_object* v_x_3049_){
_start:
{
uint8_t v_res_3050_; lean_object* v_r_3051_; 
v_res_3050_ = l_List_removeAll___redArg___lam__0(v_inst_3047_, v_ys_3048_, v_x_3049_);
v_r_3051_ = lean_box(v_res_3050_);
return v_r_3051_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg(lean_object* v_inst_3052_, lean_object* v_xs_3053_, lean_object* v_ys_3054_){
_start:
{
lean_object* v___f_3055_; lean_object* v___x_3056_; 
v___f_3055_ = lean_alloc_closure((void*)(l_List_removeAll___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3055_, 0, v_inst_3052_);
lean_closure_set(v___f_3055_, 1, v_ys_3054_);
v___x_3056_ = l_List_filter___redArg(v___f_3055_, v_xs_3053_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll(lean_object* v_00_u03b1_3057_, lean_object* v_inst_3058_, lean_object* v_xs_3059_, lean_object* v_ys_3060_){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = l_List_removeAll___redArg(v_inst_3058_, v_xs_3059_, v_ys_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_3062_, lean_object* v_h__1_3063_, lean_object* v_h__2_3064_){
_start:
{
if (lean_obj_tag(v_ys_3062_) == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_dec(v_h__2_3064_);
v___x_3065_ = lean_box(0);
v___x_3066_ = lean_apply_1(v_h__1_3063_, v___x_3065_);
return v___x_3066_;
}
else
{
lean_object* v_head_3067_; lean_object* v_tail_3068_; lean_object* v___x_3069_; 
lean_dec(v_h__1_3063_);
v_head_3067_ = lean_ctor_get(v_ys_3062_, 0);
lean_inc(v_head_3067_);
v_tail_3068_ = lean_ctor_get(v_ys_3062_, 1);
lean_inc(v_tail_3068_);
lean_dec_ref(v_ys_3062_);
v___x_3069_ = lean_apply_2(v_h__2_3064_, v_head_3067_, v_tail_3068_);
return v___x_3069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_3070_, lean_object* v_motive_3071_, lean_object* v_ys_3072_, lean_object* v_h__1_3073_, lean_object* v_h__2_3074_){
_start:
{
if (lean_obj_tag(v_ys_3072_) == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_dec(v_h__2_3074_);
v___x_3075_ = lean_box(0);
v___x_3076_ = lean_apply_1(v_h__1_3073_, v___x_3075_);
return v___x_3076_;
}
else
{
lean_object* v_head_3077_; lean_object* v_tail_3078_; lean_object* v___x_3079_; 
lean_dec(v_h__1_3073_);
v_head_3077_ = lean_ctor_get(v_ys_3072_, 0);
lean_inc(v_head_3077_);
v_tail_3078_ = lean_ctor_get(v_ys_3072_, 1);
lean_inc(v_tail_3078_);
lean_dec_ref(v_ys_3072_);
v___x_3079_ = lean_apply_2(v_h__2_3074_, v_head_3077_, v_tail_3078_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(lean_object* v_x_3080_, lean_object* v_x_3081_, lean_object* v_h__1_3082_, lean_object* v_h__2_3083_){
_start:
{
if (lean_obj_tag(v_x_3080_) == 0)
{
lean_object* v___x_3084_; 
lean_dec(v_h__2_3083_);
v___x_3084_ = lean_apply_1(v_h__1_3082_, v_x_3081_);
return v___x_3084_;
}
else
{
lean_object* v_head_3085_; lean_object* v_tail_3086_; lean_object* v___x_3087_; 
lean_dec(v_h__1_3082_);
v_head_3085_ = lean_ctor_get(v_x_3080_, 0);
lean_inc(v_head_3085_);
v_tail_3086_ = lean_ctor_get(v_x_3080_, 1);
lean_inc(v_tail_3086_);
lean_dec_ref(v_x_3080_);
v___x_3087_ = lean_apply_3(v_h__2_3083_, v_head_3085_, v_tail_3086_, v_x_3081_);
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(lean_object* v_00_u03b1_3088_, lean_object* v_motive_3089_, lean_object* v_x_3090_, lean_object* v_x_3091_, lean_object* v_h__1_3092_, lean_object* v_h__2_3093_){
_start:
{
if (lean_obj_tag(v_x_3090_) == 0)
{
lean_object* v___x_3094_; 
lean_dec(v_h__2_3093_);
v___x_3094_ = lean_apply_1(v_h__1_3092_, v_x_3091_);
return v___x_3094_;
}
else
{
lean_object* v_head_3095_; lean_object* v_tail_3096_; lean_object* v___x_3097_; 
lean_dec(v_h__1_3092_);
v_head_3095_ = lean_ctor_get(v_x_3090_, 0);
lean_inc(v_head_3095_);
v_tail_3096_ = lean_ctor_get(v_x_3090_, 1);
lean_inc(v_tail_3096_);
lean_dec_ref(v_x_3090_);
v___x_3097_ = lean_apply_3(v_h__2_3093_, v_head_3095_, v_tail_3096_, v_x_3091_);
return v___x_3097_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object* v_f_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
if (lean_obj_tag(v_a_3099_) == 0)
{
lean_object* v___x_3101_; 
lean_dec(v_f_3098_);
v___x_3101_ = l_List_reverse___redArg(v_a_3100_);
return v___x_3101_;
}
else
{
lean_object* v_head_3102_; lean_object* v_tail_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3112_; 
v_head_3102_ = lean_ctor_get(v_a_3099_, 0);
v_tail_3103_ = lean_ctor_get(v_a_3099_, 1);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_a_3099_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3105_ = v_a_3099_;
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_tail_3103_);
lean_inc(v_head_3102_);
lean_dec(v_a_3099_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
lean_inc(v_f_3098_);
v___x_3107_ = lean_apply_1(v_f_3098_, v_head_3102_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 1, v_a_3100_);
lean_ctor_set(v___x_3105_, 0, v___x_3107_);
v___x_3109_ = v___x_3105_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_a_3100_);
v___x_3109_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
v_a_3099_ = v_tail_3103_;
v_a_3100_ = v___x_3109_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object* v_00_u03b1_3113_, lean_object* v_00_u03b2_3114_, lean_object* v_f_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l_List_mapTR_loop___redArg(v_f_3115_, v_a_3116_, v_a_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object* v_f_3119_, lean_object* v_as_3120_){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_box(0);
v___x_3122_ = l_List_mapTR_loop___redArg(v_f_3119_, v_as_3120_, v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR(lean_object* v_00_u03b1_3123_, lean_object* v_00_u03b2_3124_, lean_object* v_f_3125_, lean_object* v_as_3126_){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = lean_box(0);
v___x_3128_ = l_List_mapTR_loop___redArg(v_f_3125_, v_as_3126_, v___x_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(lean_object* v_x_3129_, lean_object* v_x_3130_, lean_object* v_h__1_3131_, lean_object* v_h__2_3132_){
_start:
{
if (lean_obj_tag(v_x_3129_) == 0)
{
lean_object* v___x_3133_; 
lean_dec(v_h__2_3132_);
v___x_3133_ = lean_apply_1(v_h__1_3131_, v_x_3130_);
return v___x_3133_;
}
else
{
lean_object* v_head_3134_; lean_object* v_tail_3135_; lean_object* v___x_3136_; 
lean_dec(v_h__1_3131_);
v_head_3134_ = lean_ctor_get(v_x_3129_, 0);
lean_inc(v_head_3134_);
v_tail_3135_ = lean_ctor_get(v_x_3129_, 1);
lean_inc(v_tail_3135_);
lean_dec_ref(v_x_3129_);
v___x_3136_ = lean_apply_3(v_h__2_3132_, v_head_3134_, v_tail_3135_, v_x_3130_);
return v___x_3136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(lean_object* v_00_u03b1_3137_, lean_object* v_00_u03b2_3138_, lean_object* v_motive_3139_, lean_object* v_x_3140_, lean_object* v_x_3141_, lean_object* v_h__1_3142_, lean_object* v_h__2_3143_){
_start:
{
if (lean_obj_tag(v_x_3140_) == 0)
{
lean_object* v___x_3144_; 
lean_dec(v_h__2_3143_);
v___x_3144_ = lean_apply_1(v_h__1_3142_, v_x_3141_);
return v___x_3144_;
}
else
{
lean_object* v_head_3145_; lean_object* v_tail_3146_; lean_object* v___x_3147_; 
lean_dec(v_h__1_3142_);
v_head_3145_ = lean_ctor_get(v_x_3140_, 0);
lean_inc(v_head_3145_);
v_tail_3146_ = lean_ctor_get(v_x_3140_, 1);
lean_inc(v_tail_3146_);
lean_dec_ref(v_x_3140_);
v___x_3147_ = lean_apply_3(v_h__2_3143_, v_head_3145_, v_tail_3146_, v_x_3141_);
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object* v_p_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
if (lean_obj_tag(v_a_3149_) == 0)
{
lean_object* v___x_3151_; 
lean_dec_ref(v_p_3148_);
v___x_3151_ = l_List_reverse___redArg(v_a_3150_);
return v___x_3151_;
}
else
{
lean_object* v_head_3152_; lean_object* v_tail_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3164_; 
v_head_3152_ = lean_ctor_get(v_a_3149_, 0);
v_tail_3153_ = lean_ctor_get(v_a_3149_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_a_3149_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3155_ = v_a_3149_;
v_isShared_3156_ = v_isSharedCheck_3164_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_tail_3153_);
lean_inc(v_head_3152_);
lean_dec(v_a_3149_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3164_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; uint8_t v___x_3158_; 
lean_inc_ref(v_p_3148_);
lean_inc(v_head_3152_);
v___x_3157_ = lean_apply_1(v_p_3148_, v_head_3152_);
v___x_3158_ = lean_unbox(v___x_3157_);
if (v___x_3158_ == 0)
{
lean_del_object(v___x_3155_);
lean_dec(v_head_3152_);
v_a_3149_ = v_tail_3153_;
goto _start;
}
else
{
lean_object* v___x_3161_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 1, v_a_3150_);
v___x_3161_ = v___x_3155_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_head_3152_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_a_3150_);
v___x_3161_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
v_a_3149_ = v_tail_3153_;
v_a_3150_ = v___x_3161_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object* v_00_u03b1_3165_, lean_object* v_p_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_List_filterTR_loop___redArg(v_p_3166_, v_a_3167_, v_a_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object* v_p_3170_, lean_object* v_as_3171_){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_box(0);
v___x_3173_ = l_List_filterTR_loop___redArg(v_p_3170_, v_as_3171_, v___x_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR(lean_object* v_00_u03b1_3174_, lean_object* v_p_3175_, lean_object* v_as_3176_){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_box(0);
v___x_3178_ = l_List_filterTR_loop___redArg(v_p_3175_, v_as_3176_, v___x_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v_zero_3182_; uint8_t v_isZero_3183_; 
v_zero_3182_ = lean_unsigned_to_nat(0u);
v_isZero_3183_ = lean_nat_dec_eq(v_a_3180_, v_zero_3182_);
if (v_isZero_3183_ == 1)
{
lean_dec(v_a_3180_);
lean_dec(v_a_3179_);
return v_a_3181_;
}
else
{
lean_object* v_one_3184_; lean_object* v_n_3185_; lean_object* v___x_3186_; 
v_one_3184_ = lean_unsigned_to_nat(1u);
v_n_3185_ = lean_nat_sub(v_a_3180_, v_one_3184_);
lean_dec(v_a_3180_);
lean_inc(v_a_3179_);
v___x_3186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3186_, 0, v_a_3179_);
lean_ctor_set(v___x_3186_, 1, v_a_3181_);
v_a_3180_ = v_n_3185_;
v_a_3181_ = v___x_3186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object* v_00_u03b1_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_List_replicateTR_loop___redArg(v_a_3189_, v_a_3190_, v_a_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object* v_n_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_box(0);
v___x_3196_ = l_List_replicateTR_loop___redArg(v_a_3194_, v_n_3193_, v___x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object* v_00_u03b1_3197_, lean_object* v_n_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_List_replicateTR___redArg(v_n_3198_, v_a_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(lean_object* v_x_3201_, lean_object* v_x_3202_, lean_object* v_h__1_3203_, lean_object* v_h__2_3204_){
_start:
{
lean_object* v_zero_3205_; uint8_t v_isZero_3206_; 
v_zero_3205_ = lean_unsigned_to_nat(0u);
v_isZero_3206_ = lean_nat_dec_eq(v_x_3201_, v_zero_3205_);
if (v_isZero_3206_ == 1)
{
lean_object* v___x_3207_; 
lean_dec(v_h__2_3204_);
v___x_3207_ = lean_apply_1(v_h__1_3203_, v_x_3202_);
return v___x_3207_;
}
else
{
lean_object* v_one_3208_; lean_object* v_n_3209_; lean_object* v___x_3210_; 
lean_dec(v_h__1_3203_);
v_one_3208_ = lean_unsigned_to_nat(1u);
v_n_3209_ = lean_nat_sub(v_x_3201_, v_one_3208_);
v___x_3210_ = lean_apply_2(v_h__2_3204_, v_n_3209_, v_x_3202_);
return v___x_3210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_3211_, lean_object* v_x_3212_, lean_object* v_h__1_3213_, lean_object* v_h__2_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(v_x_3211_, v_x_3212_, v_h__1_3213_, v_h__2_3214_);
lean_dec(v_x_3211_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(lean_object* v_00_u03b1_3216_, lean_object* v_motive_3217_, lean_object* v_x_3218_, lean_object* v_x_3219_, lean_object* v_h__1_3220_, lean_object* v_h__2_3221_){
_start:
{
lean_object* v_zero_3222_; uint8_t v_isZero_3223_; 
v_zero_3222_ = lean_unsigned_to_nat(0u);
v_isZero_3223_ = lean_nat_dec_eq(v_x_3218_, v_zero_3222_);
if (v_isZero_3223_ == 1)
{
lean_object* v___x_3224_; 
lean_dec(v_h__2_3221_);
v___x_3224_ = lean_apply_1(v_h__1_3220_, v_x_3219_);
return v___x_3224_;
}
else
{
lean_object* v_one_3225_; lean_object* v_n_3226_; lean_object* v___x_3227_; 
lean_dec(v_h__1_3220_);
v_one_3225_ = lean_unsigned_to_nat(1u);
v_n_3226_ = lean_nat_sub(v_x_3218_, v_one_3225_);
v___x_3227_ = lean_apply_2(v_h__2_3221_, v_n_3226_, v_x_3219_);
return v___x_3227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_3228_, lean_object* v_motive_3229_, lean_object* v_x_3230_, lean_object* v_x_3231_, lean_object* v_h__1_3232_, lean_object* v_h__2_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(v_00_u03b1_3228_, v_motive_3229_, v_x_3230_, v_x_3231_, v_h__1_3232_, v_h__2_3233_);
lean_dec(v_x_3230_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(lean_object* v_x_3235_, lean_object* v_x_3236_, lean_object* v_h__1_3237_, lean_object* v_h__2_3238_){
_start:
{
lean_object* v_zero_3239_; uint8_t v_isZero_3240_; 
v_zero_3239_ = lean_unsigned_to_nat(0u);
v_isZero_3240_ = lean_nat_dec_eq(v_x_3235_, v_zero_3239_);
if (v_isZero_3240_ == 1)
{
lean_object* v___x_3241_; 
lean_dec(v_h__2_3238_);
v___x_3241_ = lean_apply_1(v_h__1_3237_, v_x_3236_);
return v___x_3241_;
}
else
{
lean_object* v_one_3242_; lean_object* v_n_3243_; lean_object* v___x_3244_; 
lean_dec(v_h__1_3237_);
v_one_3242_ = lean_unsigned_to_nat(1u);
v_n_3243_ = lean_nat_sub(v_x_3235_, v_one_3242_);
v___x_3244_ = lean_apply_2(v_h__2_3238_, v_n_3243_, v_x_3236_);
return v___x_3244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_3245_, lean_object* v_x_3246_, lean_object* v_h__1_3247_, lean_object* v_h__2_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(v_x_3245_, v_x_3246_, v_h__1_3247_, v_h__2_3248_);
lean_dec(v_x_3245_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(lean_object* v_00_u03b1_3250_, lean_object* v_motive_3251_, lean_object* v_x_3252_, lean_object* v_x_3253_, lean_object* v_h__1_3254_, lean_object* v_h__2_3255_){
_start:
{
lean_object* v_zero_3256_; uint8_t v_isZero_3257_; 
v_zero_3256_ = lean_unsigned_to_nat(0u);
v_isZero_3257_ = lean_nat_dec_eq(v_x_3252_, v_zero_3256_);
if (v_isZero_3257_ == 1)
{
lean_object* v___x_3258_; 
lean_dec(v_h__2_3255_);
v___x_3258_ = lean_apply_1(v_h__1_3254_, v_x_3253_);
return v___x_3258_;
}
else
{
lean_object* v_one_3259_; lean_object* v_n_3260_; lean_object* v___x_3261_; 
lean_dec(v_h__1_3254_);
v_one_3259_ = lean_unsigned_to_nat(1u);
v_n_3260_ = lean_nat_sub(v_x_3252_, v_one_3259_);
v___x_3261_ = lean_apply_2(v_h__2_3255_, v_n_3260_, v_x_3253_);
return v___x_3261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___boxed(lean_object* v_00_u03b1_3262_, lean_object* v_motive_3263_, lean_object* v_x_3264_, lean_object* v_x_3265_, lean_object* v_h__1_3266_, lean_object* v_h__2_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(v_00_u03b1_3262_, v_motive_3263_, v_x_3264_, v_x_3265_, v_h__1_3266_, v_h__2_3267_);
lean_dec(v_x_3264_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg(lean_object* v_n_3269_, lean_object* v_a_3270_, lean_object* v_l_3271_){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3272_ = l_List_lengthTR___redArg(v_l_3271_);
v___x_3273_ = lean_nat_sub(v_n_3269_, v___x_3272_);
lean_dec(v___x_3272_);
v___x_3274_ = l_List_replicateTR_loop___redArg(v_a_3270_, v___x_3273_, v_l_3271_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg___boxed(lean_object* v_n_3275_, lean_object* v_a_3276_, lean_object* v_l_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_List_leftpadTR___redArg(v_n_3275_, v_a_3276_, v_l_3277_);
lean_dec(v_n_3275_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object* v_00_u03b1_3279_, lean_object* v_n_3280_, lean_object* v_a_3281_, lean_object* v_l_3282_){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3283_ = l_List_lengthTR___redArg(v_l_3282_);
v___x_3284_ = lean_nat_sub(v_n_3280_, v___x_3283_);
lean_dec(v___x_3283_);
v___x_3285_ = l_List_replicateTR_loop___redArg(v_a_3281_, v___x_3284_, v_l_3282_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___boxed(lean_object* v_00_u03b1_3286_, lean_object* v_n_3287_, lean_object* v_a_3288_, lean_object* v_l_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_List_leftpadTR(v_00_u03b1_3286_, v_n_3287_, v_a_3288_, v_l_3289_);
lean_dec(v_n_3287_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg(lean_object* v_init_3291_, lean_object* v_x_3292_){
_start:
{
if (lean_obj_tag(v_x_3292_) == 0)
{
lean_inc_ref(v_init_3291_);
return v_init_3291_;
}
else
{
lean_object* v_head_3293_; lean_object* v_tail_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3320_; 
v_head_3293_ = lean_ctor_get(v_x_3292_, 0);
v_tail_3294_ = lean_ctor_get(v_x_3292_, 1);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_x_3292_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3296_ = v_x_3292_;
v_isShared_3297_ = v_isSharedCheck_3320_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_tail_3294_);
lean_inc(v_head_3293_);
lean_dec(v_x_3292_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3320_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v_fst_3298_; lean_object* v_snd_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3319_; 
v_fst_3298_ = lean_ctor_get(v_head_3293_, 0);
v_snd_3299_ = lean_ctor_get(v_head_3293_, 1);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_head_3293_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3301_ = v_head_3293_;
v_isShared_3302_ = v_isSharedCheck_3319_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_snd_3299_);
lean_inc(v_fst_3298_);
lean_dec(v_head_3293_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3319_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3303_; lean_object* v_fst_3304_; lean_object* v_snd_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3318_; 
v___x_3303_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3291_, v_tail_3294_);
v_fst_3304_ = lean_ctor_get(v___x_3303_, 0);
v_snd_3305_ = lean_ctor_get(v___x_3303_, 1);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3307_ = v___x_3303_;
v_isShared_3308_ = v_isSharedCheck_3318_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_snd_3305_);
lean_inc(v_fst_3304_);
lean_dec(v___x_3303_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3318_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 1, v_fst_3304_);
lean_ctor_set(v___x_3296_, 0, v_fst_3298_);
v___x_3310_ = v___x_3296_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_fst_3298_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_fst_3304_);
v___x_3310_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_object* v___x_3312_; 
if (v_isShared_3302_ == 0)
{
lean_ctor_set_tag(v___x_3301_, 1);
lean_ctor_set(v___x_3301_, 1, v_snd_3305_);
lean_ctor_set(v___x_3301_, 0, v_snd_3299_);
v___x_3312_ = v___x_3301_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_snd_3299_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_snd_3305_);
v___x_3312_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
lean_object* v___x_3314_; 
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 1, v___x_3312_);
lean_ctor_set(v___x_3307_, 0, v___x_3310_);
v___x_3314_ = v___x_3307_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v___x_3312_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg___boxed(lean_object* v_init_3321_, lean_object* v_x_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3321_, v_x_3322_);
lean_dec_ref(v_init_3321_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object* v_l_3324_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_3326_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v___x_3325_, v_l_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object* v_00_u03b1_3327_, lean_object* v_00_u03b2_3328_, lean_object* v_l_3329_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_List_unzipTR___redArg(v_l_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0(lean_object* v_00_u03b1_3331_, lean_object* v_00_u03b2_3332_, lean_object* v_init_3333_, lean_object* v_x_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3333_, v_x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___boxed(lean_object* v_00_u03b1_3336_, lean_object* v_00_u03b2_3337_, lean_object* v_init_3338_, lean_object* v_x_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_List_foldr___at___00List_unzipTR_spec__0(v_00_u03b1_3336_, v_00_u03b2_3337_, v_init_3338_, v_x_3339_);
lean_dec_ref(v_init_3338_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object* v_step_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v_zero_3345_; uint8_t v_isZero_3346_; 
v_zero_3345_ = lean_unsigned_to_nat(0u);
v_isZero_3346_ = lean_nat_dec_eq(v_a_3342_, v_zero_3345_);
if (v_isZero_3346_ == 1)
{
lean_dec(v_a_3343_);
lean_dec(v_a_3342_);
return v_a_3344_;
}
else
{
lean_object* v_one_3347_; lean_object* v_n_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v_one_3347_ = lean_unsigned_to_nat(1u);
v_n_3348_ = lean_nat_sub(v_a_3342_, v_one_3347_);
lean_dec(v_a_3342_);
v___x_3349_ = lean_nat_sub(v_a_3343_, v_step_3341_);
lean_dec(v_a_3343_);
lean_inc(v___x_3349_);
v___x_3350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
lean_ctor_set(v___x_3350_, 1, v_a_3344_);
v_a_3342_ = v_n_3348_;
v_a_3343_ = v___x_3349_;
v_a_3344_ = v___x_3350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object* v_step_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_List_range_x27TR_go(v_step_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
lean_dec(v_step_3352_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object* v_s_3357_, lean_object* v_n_3358_, lean_object* v_step_3359_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3360_ = lean_nat_mul(v_step_3359_, v_n_3358_);
v___x_3361_ = lean_nat_add(v_s_3357_, v___x_3360_);
lean_dec(v___x_3360_);
v___x_3362_ = lean_box(0);
v___x_3363_ = l_List_range_x27TR_go(v_step_3359_, v_n_3358_, v___x_3361_, v___x_3362_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object* v_s_3364_, lean_object* v_n_3365_, lean_object* v_step_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_List_range_x27TR(v_s_3364_, v_n_3365_, v_step_3366_);
lean_dec(v_step_3366_);
lean_dec(v_s_3364_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(lean_object* v_x_3368_, lean_object* v_x_3369_, lean_object* v_x_3370_, lean_object* v_h__1_3371_, lean_object* v_h__2_3372_){
_start:
{
lean_object* v_zero_3373_; uint8_t v_isZero_3374_; 
v_zero_3373_ = lean_unsigned_to_nat(0u);
v_isZero_3374_ = lean_nat_dec_eq(v_x_3368_, v_zero_3373_);
if (v_isZero_3374_ == 1)
{
lean_object* v___x_3375_; 
lean_dec(v_h__2_3372_);
v___x_3375_ = lean_apply_2(v_h__1_3371_, v_x_3369_, v_x_3370_);
return v___x_3375_;
}
else
{
lean_object* v_one_3376_; lean_object* v_n_3377_; lean_object* v___x_3378_; 
lean_dec(v_h__1_3371_);
v_one_3376_ = lean_unsigned_to_nat(1u);
v_n_3377_ = lean_nat_sub(v_x_3368_, v_one_3376_);
v___x_3378_ = lean_apply_3(v_h__2_3372_, v_n_3377_, v_x_3369_, v_x_3370_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(lean_object* v_x_3379_, lean_object* v_x_3380_, lean_object* v_x_3381_, lean_object* v_h__1_3382_, lean_object* v_h__2_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(v_x_3379_, v_x_3380_, v_x_3381_, v_h__1_3382_, v_h__2_3383_);
lean_dec(v_x_3379_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object* v_motive_3385_, lean_object* v_x_3386_, lean_object* v_x_3387_, lean_object* v_x_3388_, lean_object* v_h__1_3389_, lean_object* v_h__2_3390_){
_start:
{
lean_object* v_zero_3391_; uint8_t v_isZero_3392_; 
v_zero_3391_ = lean_unsigned_to_nat(0u);
v_isZero_3392_ = lean_nat_dec_eq(v_x_3386_, v_zero_3391_);
if (v_isZero_3392_ == 1)
{
lean_object* v___x_3393_; 
lean_dec(v_h__2_3390_);
v___x_3393_ = lean_apply_2(v_h__1_3389_, v_x_3387_, v_x_3388_);
return v___x_3393_;
}
else
{
lean_object* v_one_3394_; lean_object* v_n_3395_; lean_object* v___x_3396_; 
lean_dec(v_h__1_3389_);
v_one_3394_ = lean_unsigned_to_nat(1u);
v_n_3395_ = lean_nat_sub(v_x_3386_, v_one_3394_);
v___x_3396_ = lean_apply_3(v_h__2_3390_, v_n_3395_, v_x_3387_, v_x_3388_);
return v___x_3396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(lean_object* v_motive_3397_, lean_object* v_x_3398_, lean_object* v_x_3399_, lean_object* v_x_3400_, lean_object* v_h__1_3401_, lean_object* v_h__2_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(v_motive_3397_, v_x_3398_, v_x_3399_, v_x_3400_, v_h__1_3401_, v_h__2_3402_);
lean_dec(v_x_3398_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg(lean_object* v_sep_3404_, lean_object* v_init_3405_, lean_object* v_x_3406_){
_start:
{
if (lean_obj_tag(v_x_3406_) == 0)
{
lean_dec(v_sep_3404_);
lean_inc(v_init_3405_);
return v_init_3405_;
}
else
{
lean_object* v_head_3407_; lean_object* v_tail_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3417_; 
v_head_3407_ = lean_ctor_get(v_x_3406_, 0);
v_tail_3408_ = lean_ctor_get(v_x_3406_, 1);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_x_3406_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3410_ = v_x_3406_;
v_isShared_3411_ = v_isSharedCheck_3417_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_tail_3408_);
lean_inc(v_head_3407_);
lean_dec(v_x_3406_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3417_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; lean_object* v___x_3414_; 
lean_inc(v_sep_3404_);
v___x_3412_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3404_, v_init_3405_, v_tail_3408_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 1, v___x_3412_);
v___x_3414_ = v___x_3410_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_head_3407_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3415_, 0, v_sep_3404_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
return v___x_3415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(lean_object* v_sep_3418_, lean_object* v_init_3419_, lean_object* v_x_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3418_, v_init_3419_, v_x_3420_);
lean_dec(v_init_3419_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object* v_sep_3422_, lean_object* v_x_3423_){
_start:
{
if (lean_obj_tag(v_x_3423_) == 0)
{
lean_dec(v_sep_3422_);
return v_x_3423_;
}
else
{
lean_object* v_tail_3424_; 
v_tail_3424_ = lean_ctor_get(v_x_3423_, 1);
lean_inc(v_tail_3424_);
if (lean_obj_tag(v_tail_3424_) == 0)
{
lean_dec(v_sep_3422_);
return v_x_3423_;
}
else
{
lean_object* v_head_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3444_; 
v_head_3425_ = lean_ctor_get(v_x_3423_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_x_3423_);
if (v_isSharedCheck_3444_ == 0)
{
lean_object* v_unused_3445_; 
v_unused_3445_ = lean_ctor_get(v_x_3423_, 1);
lean_dec(v_unused_3445_);
v___x_3427_ = v_x_3423_;
v_isShared_3428_ = v_isSharedCheck_3444_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_head_3425_);
lean_dec(v_x_3423_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3444_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v_head_3429_; lean_object* v_tail_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3443_; 
v_head_3429_ = lean_ctor_get(v_tail_3424_, 0);
v_tail_3430_ = lean_ctor_get(v_tail_3424_, 1);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_tail_3424_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3432_ = v_tail_3424_;
v_isShared_3433_ = v_isSharedCheck_3443_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_tail_3430_);
lean_inc(v_head_3429_);
lean_dec(v_tail_3424_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3443_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3434_ = lean_box(0);
lean_inc(v_sep_3422_);
v___x_3435_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3422_, v___x_3434_, v_tail_3430_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3435_);
v___x_3437_ = v___x_3432_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_head_3429_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v___x_3437_);
lean_ctor_set(v___x_3427_, 0, v_sep_3422_);
v___x_3439_ = v___x_3427_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_sep_3422_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3440_, 0, v_head_3425_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
return v___x_3440_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object* v_00_u03b1_3446_, lean_object* v_sep_3447_, lean_object* v_x_3448_){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_List_intersperseTR___redArg(v_sep_3447_, v_x_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0(lean_object* v_00_u03b1_3450_, lean_object* v_sep_3451_, lean_object* v_init_3452_, lean_object* v_x_3453_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3451_, v_init_3452_, v_x_3453_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___boxed(lean_object* v_00_u03b1_3455_, lean_object* v_sep_3456_, lean_object* v_init_3457_, lean_object* v_x_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_List_foldr___at___00List_intersperseTR_spec__0(v_00_u03b1_3455_, v_sep_3456_, v_init_3457_, v_x_3458_);
lean_dec(v_init_3457_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(lean_object* v_x_3460_, lean_object* v_h__1_3461_, lean_object* v_h__2_3462_, lean_object* v_h__3_3463_){
_start:
{
if (lean_obj_tag(v_x_3460_) == 0)
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_dec(v_h__3_3463_);
lean_dec(v_h__2_3462_);
v___x_3464_ = lean_box(0);
v___x_3465_ = lean_apply_1(v_h__1_3461_, v___x_3464_);
return v___x_3465_;
}
else
{
lean_object* v_tail_3466_; 
lean_dec(v_h__1_3461_);
v_tail_3466_ = lean_ctor_get(v_x_3460_, 1);
if (lean_obj_tag(v_tail_3466_) == 0)
{
lean_object* v_head_3467_; lean_object* v___x_3468_; 
lean_dec(v_h__3_3463_);
v_head_3467_ = lean_ctor_get(v_x_3460_, 0);
lean_inc(v_head_3467_);
lean_dec_ref(v_x_3460_);
v___x_3468_ = lean_apply_1(v_h__2_3462_, v_head_3467_);
return v___x_3468_;
}
else
{
lean_object* v_head_3469_; lean_object* v_head_3470_; lean_object* v_tail_3471_; lean_object* v___x_3472_; 
lean_inc_ref(v_tail_3466_);
lean_dec(v_h__2_3462_);
v_head_3469_ = lean_ctor_get(v_x_3460_, 0);
lean_inc(v_head_3469_);
lean_dec_ref(v_x_3460_);
v_head_3470_ = lean_ctor_get(v_tail_3466_, 0);
lean_inc(v_head_3470_);
v_tail_3471_ = lean_ctor_get(v_tail_3466_, 1);
lean_inc(v_tail_3471_);
lean_dec_ref(v_tail_3466_);
v___x_3472_ = lean_apply_3(v_h__3_3463_, v_head_3469_, v_head_3470_, v_tail_3471_);
return v___x_3472_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object* v_00_u03b1_3473_, lean_object* v_motive_3474_, lean_object* v_x_3475_, lean_object* v_h__1_3476_, lean_object* v_h__2_3477_, lean_object* v_h__3_3478_){
_start:
{
if (lean_obj_tag(v_x_3475_) == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_dec(v_h__3_3478_);
lean_dec(v_h__2_3477_);
v___x_3479_ = lean_box(0);
v___x_3480_ = lean_apply_1(v_h__1_3476_, v___x_3479_);
return v___x_3480_;
}
else
{
lean_object* v_tail_3481_; 
lean_dec(v_h__1_3476_);
v_tail_3481_ = lean_ctor_get(v_x_3475_, 1);
if (lean_obj_tag(v_tail_3481_) == 0)
{
lean_object* v_head_3482_; lean_object* v___x_3483_; 
lean_dec(v_h__3_3478_);
v_head_3482_ = lean_ctor_get(v_x_3475_, 0);
lean_inc(v_head_3482_);
lean_dec_ref(v_x_3475_);
v___x_3483_ = lean_apply_1(v_h__2_3477_, v_head_3482_);
return v___x_3483_;
}
else
{
lean_object* v_head_3484_; lean_object* v_head_3485_; lean_object* v_tail_3486_; lean_object* v___x_3487_; 
lean_inc_ref(v_tail_3481_);
lean_dec(v_h__2_3477_);
v_head_3484_ = lean_ctor_get(v_x_3475_, 0);
lean_inc(v_head_3484_);
lean_dec_ref(v_x_3475_);
v_head_3485_ = lean_ctor_get(v_tail_3481_, 0);
lean_inc(v_head_3485_);
v_tail_3486_ = lean_ctor_get(v_tail_3481_, 1);
lean_inc(v_tail_3486_);
lean_dec_ref(v_tail_3481_);
v___x_3487_ = lean_apply_3(v_h__3_3478_, v_head_3484_, v_head_3485_, v_tail_3486_);
return v___x_3487_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_List_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Zero(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
