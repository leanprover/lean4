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
LEAN_EXPORT lean_object* l_List_modify___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modify___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modify(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modify___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdx___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_List_or___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_List_or___lam__0___boxed(lean_object*);
static const lean_closure_object l_List_or___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_or___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_or___closed__0 = (const lean_object*)&l_List_or___closed__0_value;
LEAN_EXPORT uint8_t l_List_or(lean_object*);
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_unzip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_24_; 
v___x_24_ = l___private_Init_Data_List_Basic_0__List_set_match__1_splitter___redArg(v_x_18_, v_x_19_, v_x_20_, v_h__1_21_, v_h__2_22_, v_h__3_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter___redArg(lean_object* v_x_25_, lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
lean_object* v___x_29_; 
lean_dec(v_h__2_28_);
v___x_29_ = lean_apply_1(v_h__1_27_, v_x_26_);
return v___x_29_;
}
else
{
lean_object* v_head_30_; lean_object* v_tail_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_27_);
v_head_30_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_head_30_);
v_tail_31_ = lean_ctor_get(v_x_25_, 1);
lean_inc(v_tail_31_);
lean_dec_ref(v_x_25_);
v___x_32_ = lean_apply_3(v_h__2_28_, v_head_30_, v_tail_31_, v_x_26_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter(lean_object* v_00_u03b1_33_, lean_object* v_motive_34_, lean_object* v_x_35_, lean_object* v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter___redArg(v_x_35_, v_x_36_, v_h__1_37_, v_h__2_38_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t l_List_beq___redArg(lean_object* v_inst_40_, lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
lean_dec_ref(v_inst_40_);
if (lean_obj_tag(v_x_42_) == 0)
{
uint8_t v___x_43_; 
v___x_43_ = 1;
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
lean_dec_ref(v_x_42_);
v___x_44_ = 0;
return v___x_44_;
}
}
else
{
if (lean_obj_tag(v_x_42_) == 0)
{
uint8_t v___x_45_; 
lean_dec_ref(v_x_41_);
lean_dec_ref(v_inst_40_);
v___x_45_ = 0;
return v___x_45_;
}
else
{
lean_object* v_head_46_; lean_object* v_tail_47_; lean_object* v_head_48_; lean_object* v_tail_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_head_46_ = lean_ctor_get(v_x_41_, 0);
lean_inc(v_head_46_);
v_tail_47_ = lean_ctor_get(v_x_41_, 1);
lean_inc(v_tail_47_);
lean_dec_ref(v_x_41_);
v_head_48_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_head_48_);
v_tail_49_ = lean_ctor_get(v_x_42_, 1);
lean_inc(v_tail_49_);
lean_dec_ref(v_x_42_);
lean_inc_ref(v_inst_40_);
v___x_50_ = lean_apply_2(v_inst_40_, v_head_46_, v_head_48_);
v___x_51_ = lean_unbox(v___x_50_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
lean_dec(v_tail_49_);
lean_dec(v_tail_47_);
lean_dec_ref(v_inst_40_);
v___x_52_ = lean_unbox(v___x_50_);
return v___x_52_;
}
else
{
v_x_41_ = v_tail_47_;
v_x_42_ = v_tail_49_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___redArg___boxed(lean_object* v_inst_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_List_beq___redArg(v_inst_54_, v_x_55_, v_x_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint8_t l_List_beq(lean_object* v_00_u03b1_59_, lean_object* v_inst_60_, lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = l_List_beq___redArg(v_inst_60_, v_x_61_, v_x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_List_beq___boxed(lean_object* v_00_u03b1_64_, lean_object* v_inst_65_, lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_List_beq(v_00_u03b1_64_, v_inst_65_, v_x_66_, v_x_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT lean_object* l_List_instBEq___redArg(lean_object* v_inst_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, v_inst_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_List_instBEq(lean_object* v_00_u03b1_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_74_, 0, lean_box(0));
lean_closure_set(v___x_74_, 1, v_inst_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___redArg(lean_object* v_x_75_, lean_object* v_x_76_, lean_object* v_h__1_77_, lean_object* v_h__2_78_, lean_object* v_h__3_79_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_dec(v_h__2_78_);
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_h__3_79_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_1(v_h__1_77_, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v___x_82_; 
lean_dec(v_h__1_77_);
v___x_82_ = lean_apply_4(v_h__3_79_, v_x_75_, v_x_76_, lean_box(0), lean_box(0));
return v___x_82_;
}
}
else
{
lean_dec(v_h__1_77_);
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_83_; 
lean_dec(v_h__2_78_);
v___x_83_ = lean_apply_4(v_h__3_79_, v_x_75_, v_x_76_, lean_box(0), lean_box(0));
return v___x_83_;
}
else
{
lean_object* v_head_84_; lean_object* v_tail_85_; lean_object* v_head_86_; lean_object* v_tail_87_; lean_object* v___x_88_; 
lean_dec(v_h__3_79_);
v_head_84_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_head_84_);
v_tail_85_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_tail_85_);
lean_dec_ref(v_x_75_);
v_head_86_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_head_86_);
v_tail_87_ = lean_ctor_get(v_x_76_, 1);
lean_inc(v_tail_87_);
lean_dec_ref(v_x_76_);
v___x_88_ = lean_apply_4(v_h__2_78_, v_head_84_, v_tail_85_, v_head_86_, v_tail_87_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter(lean_object* v_00_u03b1_89_, lean_object* v_motive_90_, lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_, lean_object* v_h__3_95_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
lean_dec(v_h__2_94_);
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_h__3_95_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_apply_1(v_h__1_93_, v___x_96_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
lean_dec(v_h__1_93_);
v___x_98_ = lean_apply_4(v_h__3_95_, v_x_91_, v_x_92_, lean_box(0), lean_box(0));
return v___x_98_;
}
}
else
{
lean_dec(v_h__1_93_);
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_99_; 
lean_dec(v_h__2_94_);
v___x_99_ = lean_apply_4(v_h__3_95_, v_x_91_, v_x_92_, lean_box(0), lean_box(0));
return v___x_99_;
}
else
{
lean_object* v_head_100_; lean_object* v_tail_101_; lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v___x_104_; 
lean_dec(v_h__3_95_);
v_head_100_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_head_100_);
v_tail_101_ = lean_ctor_get(v_x_91_, 1);
lean_inc(v_tail_101_);
lean_dec_ref(v_x_91_);
v_head_102_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_head_102_);
v_tail_103_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_tail_103_);
lean_dec_ref(v_x_92_);
v___x_104_ = lean_apply_4(v_h__2_94_, v_head_100_, v_tail_101_, v_head_102_, v_tail_103_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_isEqv___redArg(lean_object* v_x_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_dec_ref(v_x_107_);
if (lean_obj_tag(v_x_106_) == 0)
{
uint8_t v___x_108_; 
v___x_108_ = 1;
return v___x_108_;
}
else
{
uint8_t v___x_109_; 
lean_dec_ref(v_x_106_);
v___x_109_ = 0;
return v___x_109_;
}
}
else
{
if (lean_obj_tag(v_x_106_) == 0)
{
uint8_t v___x_110_; 
lean_dec_ref(v_x_105_);
lean_dec_ref(v_x_107_);
v___x_110_ = 0;
return v___x_110_;
}
else
{
lean_object* v_head_111_; lean_object* v_tail_112_; lean_object* v_head_113_; lean_object* v_tail_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_head_111_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_head_111_);
v_tail_112_ = lean_ctor_get(v_x_105_, 1);
lean_inc(v_tail_112_);
lean_dec_ref(v_x_105_);
v_head_113_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_head_113_);
v_tail_114_ = lean_ctor_get(v_x_106_, 1);
lean_inc(v_tail_114_);
lean_dec_ref(v_x_106_);
lean_inc_ref(v_x_107_);
v___x_115_ = lean_apply_2(v_x_107_, v_head_111_, v_head_113_);
v___x_116_ = lean_unbox(v___x_115_);
if (v___x_116_ == 0)
{
uint8_t v___x_117_; 
lean_dec(v_tail_114_);
lean_dec(v_tail_112_);
lean_dec_ref(v_x_107_);
v___x_117_ = lean_unbox(v___x_115_);
return v___x_117_;
}
else
{
v_x_105_ = v_tail_112_;
v_x_106_ = v_tail_114_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___redArg___boxed(lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_List_isEqv___redArg(v_x_119_, v_x_120_, v_x_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv(lean_object* v_00_u03b1_124_, lean_object* v_x_125_, lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = l_List_isEqv___redArg(v_x_125_, v_x_126_, v_x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_List_isEqv___boxed(lean_object* v_00_u03b1_129_, lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_List_isEqv(v_00_u03b1_129_, v_x_130_, v_x_131_, v_x_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLex___redArg(lean_object* v_inst_135_, lean_object* v_h_136_, lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_dec_ref(v_h_136_);
lean_dec_ref(v_inst_135_);
if (lean_obj_tag(v_x_138_) == 0)
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
lean_dec_ref(v_x_138_);
v___x_140_ = 1;
return v___x_140_;
}
}
else
{
lean_object* v_head_141_; lean_object* v_tail_142_; uint8_t v___x_143_; 
v_head_141_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_head_141_);
v_tail_142_ = lean_ctor_get(v_x_137_, 1);
lean_inc(v_tail_142_);
lean_dec_ref(v_x_137_);
v___x_143_ = 0;
if (lean_obj_tag(v_x_138_) == 0)
{
lean_dec(v_tail_142_);
lean_dec(v_head_141_);
lean_dec_ref(v_h_136_);
lean_dec_ref(v_inst_135_);
return v___x_143_;
}
else
{
lean_object* v_head_144_; lean_object* v_tail_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_head_144_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_head_144_);
v_tail_145_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_tail_145_);
lean_dec_ref(v_x_138_);
lean_inc_ref(v_inst_135_);
lean_inc(v_head_144_);
lean_inc(v_head_141_);
v___x_146_ = lean_apply_2(v_inst_135_, v_head_141_, v_head_144_);
lean_inc_ref(v_h_136_);
v___x_147_ = lean_apply_2(v_h_136_, v_head_141_, v_head_144_);
v___x_148_ = lean_unbox(v___x_147_);
if (v___x_148_ == 0)
{
uint8_t v___x_149_; 
v___x_149_ = lean_unbox(v___x_146_);
if (v___x_149_ == 0)
{
lean_dec(v_tail_145_);
lean_dec(v_tail_142_);
lean_dec_ref(v_h_136_);
lean_dec_ref(v_inst_135_);
return v___x_143_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = l_List_decidableLex___redArg(v_inst_135_, v_h_136_, v_tail_142_, v_tail_145_);
if (v___x_150_ == 0)
{
return v___x_143_;
}
else
{
return v___x_150_;
}
}
}
else
{
uint8_t v___x_151_; 
lean_dec(v_tail_145_);
lean_dec(v_tail_142_);
lean_dec_ref(v_h_136_);
lean_dec_ref(v_inst_135_);
v___x_151_ = lean_unbox(v___x_147_);
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableLex___redArg___boxed(lean_object* v_inst_152_, lean_object* v_h_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_List_decidableLex___redArg(v_inst_152_, v_h_153_, v_x_154_, v_x_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLex(lean_object* v_00_u03b1_158_, lean_object* v_inst_159_, lean_object* v_r_160_, lean_object* v_h_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = l_List_decidableLex___redArg(v_inst_159_, v_h_161_, v_x_162_, v_x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLex___boxed(lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_r_167_, lean_object* v_h_168_, lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_List_decidableLex(v_00_u03b1_165_, v_inst_166_, v_r_167_, v_h_168_, v_x_169_, v_x_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_List_instLT(lean_object* v_00_u03b1_173_, lean_object* v_inst_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_box(0);
return v___x_175_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLT___redArg(lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_l_u2081_178_, lean_object* v_l_u2082_179_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = l_List_decidableLex___redArg(v_inst_176_, v_inst_177_, v_l_u2081_178_, v_l_u2082_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLT___redArg___boxed(lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_l_u2081_183_, lean_object* v_l_u2082_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_List_decidableLT___redArg(v_inst_181_, v_inst_182_, v_l_u2081_183_, v_l_u2082_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLT(lean_object* v_00_u03b1_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_l_u2081_191_, lean_object* v_l_u2082_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = l_List_decidableLex___redArg(v_inst_188_, v_inst_190_, v_l_u2081_191_, v_l_u2082_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLT___boxed(lean_object* v_00_u03b1_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_l_u2081_198_, lean_object* v_l_u2082_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_List_decidableLT(v_00_u03b1_194_, v_inst_195_, v_inst_196_, v_inst_197_, v_l_u2081_198_, v_l_u2082_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_List_instLE(lean_object* v_00_u03b1_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(0);
return v___x_204_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLE___redArg(lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_l_u2081_207_, lean_object* v_l_u2082_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = l_List_decidableLex___redArg(v_inst_205_, v_inst_206_, v_l_u2082_208_, v_l_u2081_207_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; 
v___x_210_ = 1;
return v___x_210_;
}
else
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_List_decidableLE___redArg___boxed(lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_l_u2081_214_, lean_object* v_l_u2082_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_List_decidableLE___redArg(v_inst_212_, v_inst_213_, v_l_u2081_214_, v_l_u2082_215_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLE(lean_object* v_00_u03b1_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_l_u2081_222_, lean_object* v_l_u2082_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = l_List_decidableLE___redArg(v_inst_219_, v_inst_221_, v_l_u2081_222_, v_l_u2082_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLE___boxed(lean_object* v_00_u03b1_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_l_u2081_229_, lean_object* v_l_u2082_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_List_decidableLE(v_00_u03b1_225_, v_inst_226_, v_inst_227_, v_inst_228_, v_l_u2081_229_, v_l_u2082_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__12(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l_List_lex___auto__1___closed__10));
v___x_260_ = l_Lean_mkAtom(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_obj_once(&l_List_lex___auto__1___closed__12, &l_List_lex___auto__1___closed__12_once, _init_l_List_lex___auto__1___closed__12);
v___x_262_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_263_ = lean_array_push(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_List_lex___auto__1___closed__19));
v___x_279_ = l_Lean_mkAtom(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__21(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&l_List_lex___auto__1___closed__20, &l_List_lex___auto__1___closed__20_once, _init_l_List_lex___auto__1___closed__20);
v___x_281_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_282_ = lean_array_push(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__25(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = ((lean_object*)(l_List_lex___auto__1___closed__24));
v___x_288_ = lean_string_utf8_byte_size(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = lean_obj_once(&l_List_lex___auto__1___closed__25, &l_List_lex___auto__1___closed__25_once, _init_l_List_lex___auto__1___closed__25);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = ((lean_object*)(l_List_lex___auto__1___closed__24));
v___x_292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_290_);
lean_ctor_set(v___x_292_, 2, v___x_289_);
return v___x_292_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_293_ = lean_box(0);
v___x_294_ = lean_box(0);
v___x_295_ = lean_obj_once(&l_List_lex___auto__1___closed__26, &l_List_lex___auto__1___closed__26_once, _init_l_List_lex___auto__1___closed__26);
v___x_296_ = lean_box(2);
v___x_297_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
lean_ctor_set(v___x_297_, 2, v___x_294_);
lean_ctor_set(v___x_297_, 3, v___x_293_);
return v___x_297_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_List_lex___auto__1___closed__27, &l_List_lex___auto__1___closed__27_once, _init_l_List_lex___auto__1___closed__27);
v___x_299_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_300_ = lean_array_push(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = lean_obj_once(&l_List_lex___auto__1___closed__28, &l_List_lex___auto__1___closed__28_once, _init_l_List_lex___auto__1___closed__28);
v___x_302_ = ((lean_object*)(l_List_lex___auto__1___closed__23));
v___x_303_ = lean_box(2);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_ctor_set(v___x_304_, 2, v___x_301_);
return v___x_304_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_306_ = lean_obj_once(&l_List_lex___auto__1___closed__21, &l_List_lex___auto__1___closed__21_once, _init_l_List_lex___auto__1___closed__21);
v___x_307_ = lean_array_push(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = lean_obj_once(&l_List_lex___auto__1___closed__30, &l_List_lex___auto__1___closed__30_once, _init_l_List_lex___auto__1___closed__30);
v___x_309_ = ((lean_object*)(l_List_lex___auto__1___closed__18));
v___x_310_ = lean_box(2);
v___x_311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
lean_ctor_set(v___x_311_, 2, v___x_308_);
return v___x_311_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_obj_once(&l_List_lex___auto__1___closed__31, &l_List_lex___auto__1___closed__31_once, _init_l_List_lex___auto__1___closed__31);
v___x_313_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_314_ = lean_array_push(v___x_313_, v___x_312_);
return v___x_314_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_List_lex___auto__1___closed__37));
v___x_326_ = l_Lean_mkAtom(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_obj_once(&l_List_lex___auto__1___closed__38, &l_List_lex___auto__1___closed__38_once, _init_l_List_lex___auto__1___closed__38);
v___x_328_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_329_ = lean_array_push(v___x_328_, v___x_327_);
return v___x_329_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_331_ = lean_obj_once(&l_List_lex___auto__1___closed__39, &l_List_lex___auto__1___closed__39_once, _init_l_List_lex___auto__1___closed__39);
v___x_332_ = lean_array_push(v___x_331_, v___x_330_);
return v___x_332_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_333_ = lean_obj_once(&l_List_lex___auto__1___closed__40, &l_List_lex___auto__1___closed__40_once, _init_l_List_lex___auto__1___closed__40);
v___x_334_ = ((lean_object*)(l_List_lex___auto__1___closed__36));
v___x_335_ = lean_box(2);
v___x_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
lean_ctor_set(v___x_336_, 2, v___x_333_);
return v___x_336_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_338_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_339_ = lean_array_push(v___x_338_, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_List_lex___auto__1___closed__43));
v___x_342_ = l_Lean_mkAtom(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_obj_once(&l_List_lex___auto__1___closed__44, &l_List_lex___auto__1___closed__44_once, _init_l_List_lex___auto__1___closed__44);
v___x_344_ = lean_obj_once(&l_List_lex___auto__1___closed__42, &l_List_lex___auto__1___closed__42_once, _init_l_List_lex___auto__1___closed__42);
v___x_345_ = lean_array_push(v___x_344_, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_347_ = lean_obj_once(&l_List_lex___auto__1___closed__45, &l_List_lex___auto__1___closed__45_once, _init_l_List_lex___auto__1___closed__45);
v___x_348_ = lean_array_push(v___x_347_, v___x_346_);
return v___x_348_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_349_ = lean_obj_once(&l_List_lex___auto__1___closed__46, &l_List_lex___auto__1___closed__46_once, _init_l_List_lex___auto__1___closed__46);
v___x_350_ = ((lean_object*)(l_List_lex___auto__1___closed__34));
v___x_351_ = lean_box(2);
v___x_352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
lean_ctor_set(v___x_352_, 2, v___x_349_);
return v___x_352_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__48(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_obj_once(&l_List_lex___auto__1___closed__47, &l_List_lex___auto__1___closed__47_once, _init_l_List_lex___auto__1___closed__47);
v___x_354_ = lean_obj_once(&l_List_lex___auto__1___closed__32, &l_List_lex___auto__1___closed__32_once, _init_l_List_lex___auto__1___closed__32);
v___x_355_ = lean_array_push(v___x_354_, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__50(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l_List_lex___auto__1___closed__49));
v___x_358_ = l_Lean_mkAtom(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__51(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_List_lex___auto__1___closed__50, &l_List_lex___auto__1___closed__50_once, _init_l_List_lex___auto__1___closed__50);
v___x_360_ = lean_obj_once(&l_List_lex___auto__1___closed__48, &l_List_lex___auto__1___closed__48_once, _init_l_List_lex___auto__1___closed__48);
v___x_361_ = lean_array_push(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__52(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = lean_obj_once(&l_List_lex___auto__1___closed__51, &l_List_lex___auto__1___closed__51_once, _init_l_List_lex___auto__1___closed__51);
v___x_363_ = ((lean_object*)(l_List_lex___auto__1___closed__16));
v___x_364_ = lean_box(2);
v___x_365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_362_);
return v___x_365_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__53(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_obj_once(&l_List_lex___auto__1___closed__52, &l_List_lex___auto__1___closed__52_once, _init_l_List_lex___auto__1___closed__52);
v___x_367_ = lean_obj_once(&l_List_lex___auto__1___closed__13, &l_List_lex___auto__1___closed__13_once, _init_l_List_lex___auto__1___closed__13);
v___x_368_ = lean_array_push(v___x_367_, v___x_366_);
return v___x_368_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__54(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_369_ = lean_obj_once(&l_List_lex___auto__1___closed__53, &l_List_lex___auto__1___closed__53_once, _init_l_List_lex___auto__1___closed__53);
v___x_370_ = ((lean_object*)(l_List_lex___auto__1___closed__11));
v___x_371_ = lean_box(2);
v___x_372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
lean_ctor_set(v___x_372_, 2, v___x_369_);
return v___x_372_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__55(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_List_lex___auto__1___closed__54, &l_List_lex___auto__1___closed__54_once, _init_l_List_lex___auto__1___closed__54);
v___x_374_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_375_ = lean_array_push(v___x_374_, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__56(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_376_ = lean_obj_once(&l_List_lex___auto__1___closed__55, &l_List_lex___auto__1___closed__55_once, _init_l_List_lex___auto__1___closed__55);
v___x_377_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_378_ = lean_box(2);
v___x_379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
lean_ctor_set(v___x_379_, 2, v___x_376_);
return v___x_379_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__57(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_obj_once(&l_List_lex___auto__1___closed__56, &l_List_lex___auto__1___closed__56_once, _init_l_List_lex___auto__1___closed__56);
v___x_381_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_382_ = lean_array_push(v___x_381_, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__58(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_383_ = lean_obj_once(&l_List_lex___auto__1___closed__57, &l_List_lex___auto__1___closed__57_once, _init_l_List_lex___auto__1___closed__57);
v___x_384_ = ((lean_object*)(l_List_lex___auto__1___closed__7));
v___x_385_ = lean_box(2);
v___x_386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_384_);
lean_ctor_set(v___x_386_, 2, v___x_383_);
return v___x_386_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__59(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_obj_once(&l_List_lex___auto__1___closed__58, &l_List_lex___auto__1___closed__58_once, _init_l_List_lex___auto__1___closed__58);
v___x_388_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_389_ = lean_array_push(v___x_388_, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__60(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_390_ = lean_obj_once(&l_List_lex___auto__1___closed__59, &l_List_lex___auto__1___closed__59_once, _init_l_List_lex___auto__1___closed__59);
v___x_391_ = ((lean_object*)(l_List_lex___auto__1___closed__4));
v___x_392_ = lean_box(2);
v___x_393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_391_);
lean_ctor_set(v___x_393_, 2, v___x_390_);
return v___x_393_;
}
}
static lean_object* _init_l_List_lex___auto__1(void){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = lean_obj_once(&l_List_lex___auto__1___closed__60, &l_List_lex___auto__1___closed__60_once, _init_l_List_lex___auto__1___closed__60);
return v___x_394_;
}
}
LEAN_EXPORT uint8_t l_List_lex___redArg(lean_object* v_inst_395_, lean_object* v_l_u2081_396_, lean_object* v_l_u2082_397_, lean_object* v_lt_398_){
_start:
{
if (lean_obj_tag(v_l_u2081_396_) == 0)
{
lean_dec_ref(v_lt_398_);
lean_dec_ref(v_inst_395_);
if (lean_obj_tag(v_l_u2082_397_) == 0)
{
uint8_t v___x_399_; 
v___x_399_ = 0;
return v___x_399_;
}
else
{
uint8_t v___x_400_; 
lean_dec_ref(v_l_u2082_397_);
v___x_400_ = 1;
return v___x_400_;
}
}
else
{
if (lean_obj_tag(v_l_u2082_397_) == 0)
{
uint8_t v___x_401_; 
lean_dec_ref(v_l_u2081_396_);
lean_dec_ref(v_lt_398_);
lean_dec_ref(v_inst_395_);
v___x_401_ = 0;
return v___x_401_;
}
else
{
lean_object* v_head_402_; lean_object* v_tail_403_; lean_object* v_head_404_; lean_object* v_tail_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_head_402_ = lean_ctor_get(v_l_u2081_396_, 0);
lean_inc(v_head_402_);
v_tail_403_ = lean_ctor_get(v_l_u2081_396_, 1);
lean_inc(v_tail_403_);
lean_dec_ref(v_l_u2081_396_);
v_head_404_ = lean_ctor_get(v_l_u2082_397_, 0);
lean_inc(v_head_404_);
v_tail_405_ = lean_ctor_get(v_l_u2082_397_, 1);
lean_inc(v_tail_405_);
lean_dec_ref(v_l_u2082_397_);
lean_inc_ref(v_lt_398_);
lean_inc(v_head_404_);
lean_inc(v_head_402_);
v___x_406_ = lean_apply_2(v_lt_398_, v_head_402_, v_head_404_);
v___x_407_ = lean_unbox(v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; uint8_t v___x_409_; 
lean_inc_ref(v_inst_395_);
v___x_408_ = lean_apply_2(v_inst_395_, v_head_402_, v_head_404_);
v___x_409_ = lean_unbox(v___x_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
lean_dec(v_tail_405_);
lean_dec(v_tail_403_);
lean_dec_ref(v_lt_398_);
lean_dec_ref(v_inst_395_);
v___x_410_ = lean_unbox(v___x_408_);
return v___x_410_;
}
else
{
v_l_u2081_396_ = v_tail_403_;
v_l_u2082_397_ = v_tail_405_;
goto _start;
}
}
else
{
uint8_t v___x_412_; 
lean_dec(v_tail_405_);
lean_dec(v_head_404_);
lean_dec(v_tail_403_);
lean_dec(v_head_402_);
lean_dec_ref(v_lt_398_);
lean_dec_ref(v_inst_395_);
v___x_412_ = lean_unbox(v___x_406_);
return v___x_412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_lex___redArg___boxed(lean_object* v_inst_413_, lean_object* v_l_u2081_414_, lean_object* v_l_u2082_415_, lean_object* v_lt_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_List_lex___redArg(v_inst_413_, v_l_u2081_414_, v_l_u2082_415_, v_lt_416_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT uint8_t l_List_lex(lean_object* v_00_u03b1_419_, lean_object* v_inst_420_, lean_object* v_l_u2081_421_, lean_object* v_l_u2082_422_, lean_object* v_lt_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = l_List_lex___redArg(v_inst_420_, v_l_u2081_421_, v_l_u2082_422_, v_lt_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_List_lex___boxed(lean_object* v_00_u03b1_425_, lean_object* v_inst_426_, lean_object* v_l_u2081_427_, lean_object* v_l_u2082_428_, lean_object* v_lt_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_List_lex(v_00_u03b1_425_, v_inst_426_, v_l_u2081_427_, v_l_u2082_428_, v_lt_429_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg(lean_object* v_x_432_){
_start:
{
lean_object* v_tail_433_; 
v_tail_433_ = lean_ctor_get(v_x_432_, 1);
if (lean_obj_tag(v_tail_433_) == 0)
{
lean_object* v_head_434_; 
v_head_434_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_head_434_);
return v_head_434_;
}
else
{
v_x_432_ = v_tail_433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg___boxed(lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_List_getLast___redArg(v_x_436_);
lean_dec(v_x_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_List_getLast(lean_object* v_00_u03b1_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_List_getLast___redArg(v_x_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___boxed(lean_object* v_00_u03b1_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_List_getLast(v_00_u03b1_442_, v_x_443_, v_x_444_);
lean_dec(v_x_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg(lean_object* v_x_446_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
lean_object* v___x_447_; 
v___x_447_ = lean_box(0);
return v___x_447_;
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = l_List_getLast___redArg(v_x_446_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg___boxed(lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_List_getLast_x3f___redArg(v_x_450_);
lean_dec(v_x_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f(lean_object* v_00_u03b1_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_List_getLast_x3f___redArg(v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___boxed(lean_object* v_00_u03b1_455_, lean_object* v_x_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_List_getLast_x3f(v_00_u03b1_455_, v_x_456_);
lean_dec(v_x_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg(lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_inc(v_x_459_);
return v_x_459_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = l_List_getLast___redArg(v_x_458_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg___boxed(lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_List_getLastD___redArg(v_x_461_, v_x_462_);
lean_dec(v_x_462_);
lean_dec(v_x_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD(lean_object* v_00_u03b1_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_List_getLastD___redArg(v_x_465_, v_x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___boxed(lean_object* v_00_u03b1_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_List_getLastD(v_00_u03b1_468_, v_x_469_, v_x_470_);
lean_dec(v_x_470_);
lean_dec(v_x_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg(lean_object* v_x_472_){
_start:
{
lean_object* v_head_473_; 
v_head_473_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_head_473_);
return v_head_473_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg___boxed(lean_object* v_x_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_List_head___redArg(v_x_474_);
lean_dec(v_x_474_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_List_head(lean_object* v_00_u03b1_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v_head_479_; 
v_head_479_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_head_479_);
return v_head_479_;
}
}
LEAN_EXPORT lean_object* l_List_head___boxed(lean_object* v_00_u03b1_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_List_head(v_00_u03b1_480_, v_x_481_, v_x_482_);
lean_dec(v_x_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg(lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v___x_485_; 
v___x_485_ = lean_box(0);
return v___x_485_;
}
else
{
lean_object* v_head_486_; lean_object* v___x_487_; 
v_head_486_ = lean_ctor_get(v_x_484_, 0);
lean_inc(v_head_486_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v_head_486_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg___boxed(lean_object* v_x_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_List_head_x3f___redArg(v_x_488_);
lean_dec(v_x_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f(lean_object* v_00_u03b1_490_, lean_object* v_x_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_List_head_x3f___redArg(v_x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___boxed(lean_object* v_00_u03b1_493_, lean_object* v_x_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_List_head_x3f(v_00_u03b1_493_, v_x_494_);
lean_dec(v_x_494_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg(lean_object* v_x_496_, lean_object* v_x_497_){
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
LEAN_EXPORT lean_object* l_List_headD___redArg___boxed(lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_List_headD___redArg(v_x_499_, v_x_500_);
lean_dec(v_x_500_);
lean_dec(v_x_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_List_headD(lean_object* v_00_u03b1_502_, lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
lean_inc(v_x_504_);
return v_x_504_;
}
else
{
lean_object* v_head_505_; 
v_head_505_ = lean_ctor_get(v_x_503_, 0);
lean_inc(v_head_505_);
return v_head_505_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___boxed(lean_object* v_00_u03b1_506_, lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_List_headD(v_00_u03b1_506_, v_x_507_, v_x_508_);
lean_dec(v_x_508_);
lean_dec(v_x_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg(lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
return v_x_510_;
}
else
{
lean_object* v_tail_511_; 
v_tail_511_ = lean_ctor_get(v_x_510_, 1);
lean_inc(v_tail_511_);
return v_tail_511_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg___boxed(lean_object* v_x_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_List_tail___redArg(v_x_512_);
lean_dec(v_x_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_List_tail(lean_object* v_00_u03b1_514_, lean_object* v_x_515_){
_start:
{
if (lean_obj_tag(v_x_515_) == 0)
{
return v_x_515_;
}
else
{
lean_object* v_tail_516_; 
v_tail_516_ = lean_ctor_get(v_x_515_, 1);
lean_inc(v_tail_516_);
return v_tail_516_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___boxed(lean_object* v_00_u03b1_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_List_tail(v_00_u03b1_517_, v_x_518_);
lean_dec(v_x_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg(lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v___x_521_; 
v___x_521_ = lean_box(0);
return v___x_521_;
}
else
{
lean_object* v_tail_522_; lean_object* v___x_523_; 
v_tail_522_ = lean_ctor_get(v_x_520_, 1);
lean_inc(v_tail_522_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v_tail_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg___boxed(lean_object* v_x_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_List_tail_x3f___redArg(v_x_524_);
lean_dec(v_x_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f(lean_object* v_00_u03b1_526_, lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_List_tail_x3f___redArg(v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___boxed(lean_object* v_00_u03b1_529_, lean_object* v_x_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_List_tail_x3f(v_00_u03b1_529_, v_x_530_);
lean_dec(v_x_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg(lean_object* v_l_532_, lean_object* v_fallback_533_){
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
LEAN_EXPORT lean_object* l_List_tailD___redArg___boxed(lean_object* v_l_535_, lean_object* v_fallback_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_List_tailD___redArg(v_l_535_, v_fallback_536_);
lean_dec(v_fallback_536_);
lean_dec(v_l_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_List_tailD(lean_object* v_00_u03b1_538_, lean_object* v_l_539_, lean_object* v_fallback_540_){
_start:
{
if (lean_obj_tag(v_l_539_) == 0)
{
lean_inc(v_fallback_540_);
return v_fallback_540_;
}
else
{
lean_object* v_tail_541_; 
v_tail_541_ = lean_ctor_get(v_l_539_, 1);
lean_inc(v_tail_541_);
return v_tail_541_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___boxed(lean_object* v_00_u03b1_542_, lean_object* v_l_543_, lean_object* v_fallback_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_List_tailD(v_00_u03b1_542_, v_l_543_, v_fallback_544_);
lean_dec(v_fallback_544_);
lean_dec(v_l_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_List_filter___redArg(lean_object* v_p_546_, lean_object* v_x_547_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_dec_ref(v_p_546_);
return v_x_547_;
}
else
{
lean_object* v_head_548_; lean_object* v_tail_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_560_; 
v_head_548_ = lean_ctor_get(v_x_547_, 0);
v_tail_549_ = lean_ctor_get(v_x_547_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_547_);
if (v_isSharedCheck_560_ == 0)
{
v___x_551_ = v_x_547_;
v_isShared_552_ = v_isSharedCheck_560_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_tail_549_);
lean_inc(v_head_548_);
lean_dec(v_x_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_560_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; uint8_t v___x_554_; 
lean_inc_ref(v_p_546_);
lean_inc(v_head_548_);
v___x_553_ = lean_apply_1(v_p_546_, v_head_548_);
v___x_554_ = lean_unbox(v___x_553_);
if (v___x_554_ == 0)
{
lean_del_object(v___x_551_);
lean_dec(v_head_548_);
v_x_547_ = v_tail_549_;
goto _start;
}
else
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = l_List_filter___redArg(v_p_546_, v_tail_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v___x_556_);
v___x_558_ = v___x_551_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_head_548_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filter(lean_object* v_00_u03b1_561_, lean_object* v_p_562_, lean_object* v_x_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_List_filter___redArg(v_p_562_, v_x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg(lean_object* v_f_565_, lean_object* v_init_566_, lean_object* v_x_567_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_dec(v_f_565_);
lean_inc(v_init_566_);
return v_init_566_;
}
else
{
lean_object* v_head_568_; lean_object* v_tail_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_head_568_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_head_568_);
v_tail_569_ = lean_ctor_get(v_x_567_, 1);
lean_inc(v_tail_569_);
lean_dec_ref(v_x_567_);
lean_inc(v_f_565_);
v___x_570_ = l_List_foldr___redArg(v_f_565_, v_init_566_, v_tail_569_);
v___x_571_ = lean_apply_2(v_f_565_, v_head_568_, v___x_570_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg___boxed(lean_object* v_f_572_, lean_object* v_init_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_List_foldr___redArg(v_f_572_, v_init_573_, v_x_574_);
lean_dec(v_init_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_List_foldr(lean_object* v_00_u03b1_576_, lean_object* v_00_u03b2_577_, lean_object* v_f_578_, lean_object* v_init_579_, lean_object* v_x_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_List_foldr___redArg(v_f_578_, v_init_579_, v_x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___boxed(lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_f_584_, lean_object* v_init_585_, lean_object* v_x_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_List_foldr(v_00_u03b1_582_, v_00_u03b2_583_, v_f_584_, v_init_585_, v_x_586_);
lean_dec(v_init_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_List_reverseAux___redArg(lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
return v_x_589_;
}
else
{
lean_object* v_head_590_; lean_object* v_tail_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_head_590_ = lean_ctor_get(v_x_588_, 0);
v_tail_591_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v_x_588_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_tail_591_);
lean_inc(v_head_590_);
lean_dec(v_x_588_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v_x_589_);
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_head_590_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_x_589_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
v_x_588_ = v_tail_591_;
v_x_589_ = v___x_596_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object* v_00_u03b1_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_List_reverseAux___redArg(v_x_601_, v_x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_List_reverse___redArg(lean_object* v_as_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_box(0);
v___x_606_ = l_List_reverseAux___redArg(v_as_604_, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_List_reverse(lean_object* v_00_u03b1_607_, lean_object* v_as_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_List_reverse___redArg(v_as_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_h__1_612_, lean_object* v_h__2_613_){
_start:
{
if (lean_obj_tag(v_x_610_) == 0)
{
lean_object* v___x_614_; 
lean_dec(v_h__2_613_);
v___x_614_ = lean_apply_1(v_h__1_612_, v_x_611_);
return v___x_614_;
}
else
{
lean_object* v_head_615_; lean_object* v_tail_616_; lean_object* v___x_617_; 
lean_dec(v_h__1_612_);
v_head_615_ = lean_ctor_get(v_x_610_, 0);
lean_inc(v_head_615_);
v_tail_616_ = lean_ctor_get(v_x_610_, 1);
lean_inc(v_tail_616_);
lean_dec_ref(v_x_610_);
v___x_617_ = lean_apply_3(v_h__2_613_, v_head_615_, v_tail_616_, v_x_611_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_618_, lean_object* v_motive_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_h__1_622_, lean_object* v_h__2_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___redArg(v_x_620_, v_x_621_, v_h__1_622_, v_h__2_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR___redArg(lean_object* v_as_625_, lean_object* v_bs_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = l_List_reverse___redArg(v_as_625_);
v___x_628_ = l_List_reverseAux___redArg(v___x_627_, v_bs_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR(lean_object* v_00_u03b1_629_, lean_object* v_as_630_, lean_object* v_bs_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_List_appendTR___redArg(v_as_630_, v_bs_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter___redArg(lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_h__1_635_, lean_object* v_h__2_636_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
lean_object* v___x_637_; 
lean_dec(v_h__2_636_);
v___x_637_ = lean_apply_1(v_h__1_635_, v_x_634_);
return v___x_637_;
}
else
{
lean_object* v_head_638_; lean_object* v_tail_639_; lean_object* v___x_640_; 
lean_dec(v_h__1_635_);
v_head_638_ = lean_ctor_get(v_x_633_, 0);
lean_inc(v_head_638_);
v_tail_639_ = lean_ctor_get(v_x_633_, 1);
lean_inc(v_tail_639_);
lean_dec_ref(v_x_633_);
v___x_640_ = lean_apply_3(v_h__2_636_, v_head_638_, v_tail_639_, v_x_634_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter(lean_object* v_00_u03b1_641_, lean_object* v_motive_642_, lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_h__1_645_, lean_object* v_h__2_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l___private_Init_Data_List_Basic_0__List_append_match__1_splitter___redArg(v_x_643_, v_x_644_, v_h__1_645_, v_h__2_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend(lean_object* v_00_u03b1_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = ((lean_object*)(l_List_instAppend___closed__0));
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_List_singleton___redArg(lean_object* v_a_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_box(0);
v___x_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_653_, 0, v_a_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_List_singleton(lean_object* v_00_u03b1_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_box(0);
v___x_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_657_, 0, v_a_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg(lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
lean_object* v_zero_660_; uint8_t v_isZero_661_; 
v_zero_660_ = lean_unsigned_to_nat(0u);
v_isZero_661_ = lean_nat_dec_eq(v_x_658_, v_zero_660_);
if (v_isZero_661_ == 1)
{
lean_object* v___x_662_; 
lean_dec(v_x_659_);
v___x_662_ = lean_box(0);
return v___x_662_;
}
else
{
lean_object* v_one_663_; lean_object* v_n_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_one_663_ = lean_unsigned_to_nat(1u);
v_n_664_ = lean_nat_sub(v_x_658_, v_one_663_);
lean_inc(v_x_659_);
v___x_665_ = l_List_replicate___redArg(v_n_664_, v_x_659_);
lean_dec(v_n_664_);
v___x_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_666_, 0, v_x_659_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg___boxed(lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_List_replicate___redArg(v_x_667_, v_x_668_);
lean_dec(v_x_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_List_replicate(lean_object* v_00_u03b1_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_List_replicate___redArg(v_x_671_, v_x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___boxed(lean_object* v_00_u03b1_674_, lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_List_replicate(v_00_u03b1_674_, v_x_675_, v_x_676_);
lean_dec(v_x_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg(lean_object* v_n_678_, lean_object* v_a_679_, lean_object* v_l_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_681_ = l_List_length___redArg(v_l_680_);
v___x_682_ = lean_nat_sub(v_n_678_, v___x_681_);
lean_dec(v___x_681_);
v___x_683_ = l_List_replicate___redArg(v___x_682_, v_a_679_);
lean_dec(v___x_682_);
v___x_684_ = l_List_appendTR___redArg(v___x_683_, v_l_680_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg___boxed(lean_object* v_n_685_, lean_object* v_a_686_, lean_object* v_l_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_List_leftpad___redArg(v_n_685_, v_a_686_, v_l_687_);
lean_dec(v_n_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad(lean_object* v_00_u03b1_689_, lean_object* v_n_690_, lean_object* v_a_691_, lean_object* v_l_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_List_leftpad___redArg(v_n_690_, v_a_691_, v_l_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___boxed(lean_object* v_00_u03b1_694_, lean_object* v_n_695_, lean_object* v_a_696_, lean_object* v_l_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_List_leftpad(v_00_u03b1_694_, v_n_695_, v_a_696_, v_l_697_);
lean_dec(v_n_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg(lean_object* v_n_699_, lean_object* v_a_700_, lean_object* v_l_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = l_List_length___redArg(v_l_701_);
v___x_703_ = lean_nat_sub(v_n_699_, v___x_702_);
lean_dec(v___x_702_);
v___x_704_ = l_List_replicate___redArg(v___x_703_, v_a_700_);
lean_dec(v___x_703_);
v___x_705_ = l_List_appendTR___redArg(v_l_701_, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg___boxed(lean_object* v_n_706_, lean_object* v_a_707_, lean_object* v_l_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_List_rightpad___redArg(v_n_706_, v_a_707_, v_l_708_);
lean_dec(v_n_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad(lean_object* v_00_u03b1_710_, lean_object* v_n_711_, lean_object* v_a_712_, lean_object* v_l_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_List_rightpad___redArg(v_n_711_, v_a_712_, v_l_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___boxed(lean_object* v_00_u03b1_715_, lean_object* v_n_716_, lean_object* v_a_717_, lean_object* v_l_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_List_rightpad(v_00_u03b1_715_, v_n_716_, v_a_717_, v_l_718_);
lean_dec(v_n_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object* v_00_u03b1_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_box(0);
return v___x_721_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty___redArg(lean_object* v_x_722_){
_start:
{
if (lean_obj_tag(v_x_722_) == 0)
{
uint8_t v___x_723_; 
v___x_723_ = 1;
return v___x_723_;
}
else
{
uint8_t v___x_724_; 
v___x_724_ = 0;
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___redArg___boxed(lean_object* v_x_725_){
_start:
{
uint8_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l_List_isEmpty___redArg(v_x_725_);
lean_dec(v_x_725_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty(lean_object* v_00_u03b1_728_, lean_object* v_x_729_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = l_List_isEmpty___redArg(v_x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___boxed(lean_object* v_00_u03b1_731_, lean_object* v_x_732_){
_start:
{
uint8_t v_res_733_; lean_object* v_r_734_; 
v_res_733_ = l_List_isEmpty(v_00_u03b1_731_, v_x_732_);
lean_dec(v_x_732_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
LEAN_EXPORT uint8_t l_List_elem___redArg(lean_object* v_inst_735_, lean_object* v_a_736_, lean_object* v_x_737_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
{
uint8_t v___x_738_; 
lean_dec(v_a_736_);
lean_dec_ref(v_inst_735_);
v___x_738_ = 0;
return v___x_738_;
}
else
{
lean_object* v_head_739_; lean_object* v_tail_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_head_739_ = lean_ctor_get(v_x_737_, 0);
lean_inc(v_head_739_);
v_tail_740_ = lean_ctor_get(v_x_737_, 1);
lean_inc(v_tail_740_);
lean_dec_ref(v_x_737_);
lean_inc_ref(v_inst_735_);
lean_inc(v_a_736_);
v___x_741_ = lean_apply_2(v_inst_735_, v_a_736_, v_head_739_);
v___x_742_ = lean_unbox(v___x_741_);
if (v___x_742_ == 0)
{
v_x_737_ = v_tail_740_;
goto _start;
}
else
{
uint8_t v___x_744_; 
lean_dec(v_tail_740_);
lean_dec(v_a_736_);
lean_dec_ref(v_inst_735_);
v___x_744_ = lean_unbox(v___x_741_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___redArg___boxed(lean_object* v_inst_745_, lean_object* v_a_746_, lean_object* v_x_747_){
_start:
{
uint8_t v_res_748_; lean_object* v_r_749_; 
v_res_748_ = l_List_elem___redArg(v_inst_745_, v_a_746_, v_x_747_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT uint8_t l_List_elem(lean_object* v_00_u03b1_750_, lean_object* v_inst_751_, lean_object* v_a_752_, lean_object* v_x_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = l_List_elem___redArg(v_inst_751_, v_a_752_, v_x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_List_elem___boxed(lean_object* v_00_u03b1_755_, lean_object* v_inst_756_, lean_object* v_a_757_, lean_object* v_x_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_List_elem(v_00_u03b1_755_, v_inst_756_, v_a_757_, v_x_758_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l_List_contains___redArg(lean_object* v_inst_761_, lean_object* v_as_762_, lean_object* v_a_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = l_List_elem___redArg(v_inst_761_, v_a_763_, v_as_762_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_List_contains___redArg___boxed(lean_object* v_inst_765_, lean_object* v_as_766_, lean_object* v_a_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_List_contains___redArg(v_inst_765_, v_as_766_, v_a_767_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT uint8_t l_List_contains(lean_object* v_00_u03b1_770_, lean_object* v_inst_771_, lean_object* v_as_772_, lean_object* v_a_773_){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = l_List_elem___redArg(v_inst_771_, v_a_773_, v_as_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_List_contains___boxed(lean_object* v_00_u03b1_775_, lean_object* v_inst_776_, lean_object* v_as_777_, lean_object* v_a_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l_List_contains(v_00_u03b1_775_, v_inst_776_, v_as_777_, v_a_778_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership(lean_object* v_00_u03b1_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = lean_box(0);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_783_, lean_object* v_h__1_784_, lean_object* v_h__2_785_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec(v_h__2_785_);
v___x_786_ = lean_box(0);
v___x_787_ = lean_apply_1(v_h__1_784_, v___x_786_);
return v___x_787_;
}
else
{
lean_object* v_head_788_; lean_object* v_tail_789_; lean_object* v___x_790_; 
lean_dec(v_h__1_784_);
v_head_788_ = lean_ctor_get(v_x_783_, 0);
lean_inc(v_head_788_);
v_tail_789_ = lean_ctor_get(v_x_783_, 1);
lean_inc(v_tail_789_);
lean_dec_ref(v_x_783_);
v___x_790_ = lean_apply_2(v_h__2_785_, v_head_788_, v_tail_789_);
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_791_, lean_object* v_motive_792_, lean_object* v_x_793_, lean_object* v_h__1_794_, lean_object* v_h__2_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___redArg(v_x_793_, v_h__1_794_, v_h__2_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(uint8_t v_x_797_, lean_object* v_h__1_798_, lean_object* v_h__2_799_){
_start:
{
if (v_x_797_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v_h__1_798_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_apply_1(v_h__2_799_, v___x_800_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec(v_h__2_799_);
v___x_802_ = lean_box(0);
v___x_803_ = lean_apply_1(v_h__1_798_, v___x_802_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_804_, lean_object* v_h__1_805_, lean_object* v_h__2_806_){
_start:
{
uint8_t v_x_22__boxed_807_; lean_object* v_res_808_; 
v_x_22__boxed_807_ = lean_unbox(v_x_804_);
v_res_808_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(v_x_22__boxed_807_, v_h__1_805_, v_h__2_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object* v_motive_809_, uint8_t v_x_810_, lean_object* v_h__1_811_, lean_object* v_h__2_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(v_x_810_, v_h__1_811_, v_h__2_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_814_, lean_object* v_x_815_, lean_object* v_h__1_816_, lean_object* v_h__2_817_){
_start:
{
uint8_t v_x_33__boxed_818_; lean_object* v_res_819_; 
v_x_33__boxed_818_ = lean_unbox(v_x_815_);
v_res_819_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(v_motive_814_, v_x_33__boxed_818_, v_h__1_816_, v_h__2_817_);
return v_res_819_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_820_, lean_object* v_a_821_, lean_object* v_as_822_){
_start:
{
uint8_t v___x_823_; 
v___x_823_ = l_List_elem___redArg(v_inst_820_, v_a_821_, v_as_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_824_, lean_object* v_a_825_, lean_object* v_as_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_List_instDecidableMemOfLawfulBEq___redArg(v_inst_824_, v_a_825_, v_as_826_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_a_832_, lean_object* v_as_833_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = l_List_elem___redArg(v_inst_830_, v_a_832_, v_as_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_a_838_, lean_object* v_as_839_){
_start:
{
uint8_t v_res_840_; lean_object* v_r_841_; 
v_res_840_ = l_List_instDecidableMemOfLawfulBEq(v_00_u03b1_835_, v_inst_836_, v_inst_837_, v_a_838_, v_as_839_);
v_r_841_ = lean_box(v_res_840_);
return v_r_841_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx___redArg(lean_object* v_inst_842_, lean_object* v_x_843_){
_start:
{
if (lean_obj_tag(v_x_843_) == 0)
{
uint8_t v___x_844_; 
lean_dec_ref(v_inst_842_);
v___x_844_ = 0;
return v___x_844_;
}
else
{
lean_object* v_head_845_; lean_object* v_tail_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_head_845_ = lean_ctor_get(v_x_843_, 0);
lean_inc(v_head_845_);
v_tail_846_ = lean_ctor_get(v_x_843_, 1);
lean_inc(v_tail_846_);
lean_dec_ref(v_x_843_);
lean_inc_ref(v_inst_842_);
v___x_847_ = lean_apply_1(v_inst_842_, v_head_845_);
v___x_848_ = lean_unbox(v___x_847_);
if (v___x_848_ == 0)
{
v_x_843_ = v_tail_846_;
goto _start;
}
else
{
uint8_t v___x_850_; 
lean_dec(v_tail_846_);
lean_dec_ref(v_inst_842_);
v___x_850_ = lean_unbox(v___x_847_);
return v___x_850_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___redArg___boxed(lean_object* v_inst_851_, lean_object* v_x_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l_List_decidableBEx___redArg(v_inst_851_, v_x_852_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx(lean_object* v_00_u03b1_855_, lean_object* v_p_856_, lean_object* v_inst_857_, lean_object* v_x_858_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = l_List_decidableBEx___redArg(v_inst_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___boxed(lean_object* v_00_u03b1_860_, lean_object* v_p_861_, lean_object* v_inst_862_, lean_object* v_x_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_List_decidableBEx(v_00_u03b1_860_, v_p_861_, v_inst_862_, v_x_863_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll___redArg(lean_object* v_inst_866_, lean_object* v_x_867_){
_start:
{
if (lean_obj_tag(v_x_867_) == 0)
{
uint8_t v___x_868_; 
lean_dec_ref(v_inst_866_);
v___x_868_ = 1;
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
uint8_t v___x_873_; 
lean_dec(v_tail_870_);
lean_dec_ref(v_inst_866_);
v___x_873_ = lean_unbox(v___x_871_);
return v___x_873_;
}
else
{
v_x_867_ = v_tail_870_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___redArg___boxed(lean_object* v_inst_875_, lean_object* v_x_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l_List_decidableBAll___redArg(v_inst_875_, v_x_876_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll(lean_object* v_00_u03b1_879_, lean_object* v_p_880_, lean_object* v_inst_881_, lean_object* v_x_882_){
_start:
{
uint8_t v___x_883_; 
v___x_883_ = l_List_decidableBAll___redArg(v_inst_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___boxed(lean_object* v_00_u03b1_884_, lean_object* v_p_885_, lean_object* v_inst_886_, lean_object* v_x_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l_List_decidableBAll(v_00_u03b1_884_, v_p_885_, v_inst_886_, v_x_887_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
LEAN_EXPORT lean_object* l_List_take___redArg(lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
lean_object* v_zero_892_; uint8_t v_isZero_893_; 
v_zero_892_ = lean_unsigned_to_nat(0u);
v_isZero_893_ = lean_nat_dec_eq(v_x_890_, v_zero_892_);
if (v_isZero_893_ == 1)
{
lean_object* v___x_894_; 
lean_dec(v_x_891_);
v___x_894_ = lean_box(0);
return v___x_894_;
}
else
{
if (lean_obj_tag(v_x_891_) == 0)
{
return v_x_891_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_906_; 
v_head_895_ = lean_ctor_get(v_x_891_, 0);
v_tail_896_ = lean_ctor_get(v_x_891_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_x_891_);
if (v_isSharedCheck_906_ == 0)
{
v___x_898_ = v_x_891_;
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_tail_896_);
lean_inc(v_head_895_);
lean_dec(v_x_891_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_one_900_; lean_object* v_n_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v_one_900_ = lean_unsigned_to_nat(1u);
v_n_901_ = lean_nat_sub(v_x_890_, v_one_900_);
v___x_902_ = l_List_take___redArg(v_n_901_, v_tail_896_);
lean_dec(v_n_901_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_902_);
v___x_904_ = v___x_898_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_head_895_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_take___redArg___boxed(lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_List_take___redArg(v_x_907_, v_x_908_);
lean_dec(v_x_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_List_take(lean_object* v_00_u03b1_910_, lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_List_take___redArg(v_x_911_, v_x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_List_take___boxed(lean_object* v_00_u03b1_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_List_take(v_00_u03b1_914_, v_x_915_, v_x_916_);
lean_dec(v_x_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg(lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
lean_object* v_zero_920_; uint8_t v_isZero_921_; 
v_zero_920_ = lean_unsigned_to_nat(0u);
v_isZero_921_ = lean_nat_dec_eq(v_x_918_, v_zero_920_);
if (v_isZero_921_ == 1)
{
lean_dec(v_x_918_);
lean_inc(v_x_919_);
return v_x_919_;
}
else
{
if (lean_obj_tag(v_x_919_) == 0)
{
lean_dec(v_x_918_);
return v_x_919_;
}
else
{
lean_object* v_tail_922_; lean_object* v_one_923_; lean_object* v_n_924_; 
v_tail_922_ = lean_ctor_get(v_x_919_, 1);
v_one_923_ = lean_unsigned_to_nat(1u);
v_n_924_ = lean_nat_sub(v_x_918_, v_one_923_);
lean_dec(v_x_918_);
v_x_918_ = v_n_924_;
v_x_919_ = v_tail_922_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg___boxed(lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_List_drop___redArg(v_x_926_, v_x_927_);
lean_dec(v_x_927_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_List_drop(lean_object* v_00_u03b1_929_, lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_List_drop___redArg(v_x_930_, v_x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_List_drop___boxed(lean_object* v_00_u03b1_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_List_drop(v_00_u03b1_933_, v_x_934_, v_x_935_);
lean_dec(v_x_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg(lean_object* v_l_937_, lean_object* v_start_938_, lean_object* v_stop_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_nat_sub(v_stop_939_, v_start_938_);
v___x_941_ = l_List_drop___redArg(v_start_938_, v_l_937_);
v___x_942_ = l_List_take___redArg(v___x_940_, v___x_941_);
lean_dec(v___x_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg___boxed(lean_object* v_l_943_, lean_object* v_start_944_, lean_object* v_stop_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_List_extract___redArg(v_l_943_, v_start_944_, v_stop_945_);
lean_dec(v_stop_945_);
lean_dec(v_l_943_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_List_extract(lean_object* v_00_u03b1_947_, lean_object* v_l_948_, lean_object* v_start_949_, lean_object* v_stop_950_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_nat_sub(v_stop_950_, v_start_949_);
v___x_952_ = l_List_drop___redArg(v_start_949_, v_l_948_);
v___x_953_ = l_List_take___redArg(v___x_951_, v___x_952_);
lean_dec(v___x_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_List_extract___boxed(lean_object* v_00_u03b1_954_, lean_object* v_l_955_, lean_object* v_start_956_, lean_object* v_stop_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_List_extract(v_00_u03b1_954_, v_l_955_, v_start_956_, v_stop_957_);
lean_dec(v_stop_957_);
lean_dec(v_l_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhile___redArg(lean_object* v_p_959_, lean_object* v_x_960_){
_start:
{
if (lean_obj_tag(v_x_960_) == 0)
{
lean_dec_ref(v_p_959_);
return v_x_960_;
}
else
{
lean_object* v_head_961_; lean_object* v_tail_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_973_; 
v_head_961_ = lean_ctor_get(v_x_960_, 0);
v_tail_962_ = lean_ctor_get(v_x_960_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_973_ == 0)
{
v___x_964_ = v_x_960_;
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_tail_962_);
lean_inc(v_head_961_);
lean_dec(v_x_960_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; uint8_t v___x_967_; 
lean_inc_ref(v_p_959_);
lean_inc(v_head_961_);
v___x_966_ = lean_apply_1(v_p_959_, v_head_961_);
v___x_967_ = lean_unbox(v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
lean_del_object(v___x_964_);
lean_dec(v_tail_962_);
lean_dec(v_head_961_);
lean_dec_ref(v_p_959_);
v___x_968_ = lean_box(0);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = l_List_takeWhile___redArg(v_p_959_, v_tail_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___x_969_);
v___x_971_ = v___x_964_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_head_961_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_takeWhile(lean_object* v_00_u03b1_974_, lean_object* v_p_975_, lean_object* v_x_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_List_takeWhile___redArg(v_p_975_, v_x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___redArg(lean_object* v_p_978_, lean_object* v_x_979_){
_start:
{
if (lean_obj_tag(v_x_979_) == 0)
{
lean_dec_ref(v_p_978_);
return v_x_979_;
}
else
{
lean_object* v_head_980_; lean_object* v_tail_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_head_980_ = lean_ctor_get(v_x_979_, 0);
v_tail_981_ = lean_ctor_get(v_x_979_, 1);
lean_inc_ref(v_p_978_);
lean_inc(v_head_980_);
v___x_982_ = lean_apply_1(v_p_978_, v_head_980_);
v___x_983_ = lean_unbox(v___x_982_);
if (v___x_983_ == 0)
{
lean_dec_ref(v_p_978_);
return v_x_979_;
}
else
{
lean_inc(v_tail_981_);
lean_dec_ref(v_x_979_);
v_x_979_ = v_tail_981_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object* v_00_u03b1_985_, lean_object* v_p_986_, lean_object* v_x_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_List_dropWhile___redArg(v_p_986_, v_x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___redArg(lean_object* v_p_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
if (lean_obj_tag(v_a_990_) == 0)
{
lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v_p_989_);
v_fst_992_ = lean_ctor_get(v_a_991_, 0);
v_snd_993_ = lean_ctor_get(v_a_991_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_a_991_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_995_ = v_a_991_;
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_inc(v_fst_992_);
lean_dec(v_a_991_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_997_ = l_List_reverse___redArg(v_fst_992_);
v___x_998_ = l_List_reverse___redArg(v_snd_993_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v___x_998_);
lean_ctor_set(v___x_995_, 0, v___x_997_);
v___x_1000_ = v___x_995_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
else
{
lean_object* v_head_1003_; lean_object* v_tail_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1030_; 
v_head_1003_ = lean_ctor_get(v_a_990_, 0);
v_tail_1004_ = lean_ctor_get(v_a_990_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_a_990_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1006_ = v_a_990_;
v_isShared_1007_ = v_isSharedCheck_1030_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_tail_1004_);
lean_inc(v_head_1003_);
lean_dec(v_a_990_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1030_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_fst_1008_; lean_object* v_snd_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1029_; 
v_fst_1008_ = lean_ctor_get(v_a_991_, 0);
v_snd_1009_ = lean_ctor_get(v_a_991_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_a_991_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1011_ = v_a_991_;
v_isShared_1012_ = v_isSharedCheck_1029_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_snd_1009_);
lean_inc(v_fst_1008_);
lean_dec(v_a_991_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1029_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
lean_inc_ref(v_p_989_);
lean_inc(v_head_1003_);
v___x_1013_ = lean_apply_1(v_p_989_, v_head_1003_);
v___x_1014_ = lean_unbox(v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1016_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v_snd_1009_);
v___x_1016_ = v___x_1006_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_head_1003_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_snd_1009_);
v___x_1016_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v___x_1016_);
v___x_1018_ = v___x_1011_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_fst_1008_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
v_a_990_ = v_tail_1004_;
v_a_991_ = v___x_1018_;
goto _start;
}
}
}
else
{
lean_object* v___x_1023_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v_fst_1008_);
v___x_1023_ = v___x_1006_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_head_1003_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_fst_1008_);
v___x_1023_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1025_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1023_);
v___x_1025_ = v___x_1011_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_snd_1009_);
v___x_1025_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
v_a_990_ = v_tail_1004_;
v_a_991_ = v___x_1025_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object* v_00_u03b1_1031_, lean_object* v_p_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_List_partition_loop___redArg(v_p_1032_, v_a_1033_, v_a_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_List_partition___redArg(lean_object* v_p_1038_, lean_object* v_as_1039_){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1041_ = l_List_partition_loop___redArg(v_p_1038_, v_as_1039_, v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_List_partition(lean_object* v_00_u03b1_1042_, lean_object* v_p_1043_, lean_object* v_as_1044_){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1046_ = l_List_partition_loop___redArg(v_p_1043_, v_as_1044_, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_List_dropLast___redArg(lean_object* v_x_1047_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
return v_x_1047_;
}
else
{
lean_object* v_tail_1048_; 
v_tail_1048_ = lean_ctor_get(v_x_1047_, 1);
lean_inc(v_tail_1048_);
if (lean_obj_tag(v_tail_1048_) == 0)
{
lean_dec_ref(v_x_1047_);
return v_tail_1048_;
}
else
{
lean_object* v_head_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
v_head_1049_ = lean_ctor_get(v_x_1047_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v_x_1047_, 1);
lean_dec(v_unused_1058_);
v___x_1051_ = v_x_1047_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_head_1049_);
lean_dec(v_x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = l_List_dropLast___redArg(v_tail_1048_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_head_1049_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropLast(lean_object* v_00_u03b1_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_List_dropLast___redArg(v_x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_1062_, lean_object* v_h__1_1063_, lean_object* v_h__2_1064_, lean_object* v_h__3_1065_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec(v_h__3_1065_);
lean_dec(v_h__2_1064_);
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_apply_1(v_h__1_1063_, v___x_1066_);
return v___x_1067_;
}
else
{
lean_object* v_tail_1068_; 
lean_dec(v_h__1_1063_);
v_tail_1068_ = lean_ctor_get(v_x_1062_, 1);
if (lean_obj_tag(v_tail_1068_) == 0)
{
lean_object* v_head_1069_; lean_object* v___x_1070_; 
lean_dec(v_h__3_1065_);
v_head_1069_ = lean_ctor_get(v_x_1062_, 0);
lean_inc(v_head_1069_);
lean_dec_ref(v_x_1062_);
v___x_1070_ = lean_apply_1(v_h__2_1064_, v_head_1069_);
return v___x_1070_;
}
else
{
lean_object* v_head_1071_; lean_object* v___x_1072_; 
lean_inc_ref(v_tail_1068_);
lean_dec(v_h__2_1064_);
v_head_1071_ = lean_ctor_get(v_x_1062_, 0);
lean_inc(v_head_1071_);
lean_dec_ref(v_x_1062_);
v___x_1072_ = lean_apply_3(v_h__3_1065_, v_head_1071_, v_tail_1068_, lean_box(0));
return v___x_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_1073_, lean_object* v_motive_1074_, lean_object* v_x_1075_, lean_object* v_h__1_1076_, lean_object* v_h__2_1077_, lean_object* v_h__3_1078_){
_start:
{
if (lean_obj_tag(v_x_1075_) == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
lean_dec(v_h__3_1078_);
lean_dec(v_h__2_1077_);
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_apply_1(v_h__1_1076_, v___x_1079_);
return v___x_1080_;
}
else
{
lean_object* v_tail_1081_; 
lean_dec(v_h__1_1076_);
v_tail_1081_ = lean_ctor_get(v_x_1075_, 1);
if (lean_obj_tag(v_tail_1081_) == 0)
{
lean_object* v_head_1082_; lean_object* v___x_1083_; 
lean_dec(v_h__3_1078_);
v_head_1082_ = lean_ctor_get(v_x_1075_, 0);
lean_inc(v_head_1082_);
lean_dec_ref(v_x_1075_);
v___x_1083_ = lean_apply_1(v_h__2_1077_, v_head_1082_);
return v___x_1083_;
}
else
{
lean_object* v_head_1084_; lean_object* v___x_1085_; 
lean_inc_ref(v_tail_1081_);
lean_dec(v_h__2_1077_);
v_head_1084_ = lean_ctor_get(v_x_1075_, 0);
lean_inc(v_head_1084_);
lean_dec_ref(v_x_1075_);
v___x_1085_ = lean_apply_3(v_h__3_1078_, v_head_1084_, v_tail_1081_, lean_box(0));
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object* v_00_u03b1_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_box(0);
return v___x_1087_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(lean_object* v___f_1088_, lean_object* v_x_1089_, lean_object* v_a_1090_){
_start:
{
uint8_t v___x_1091_; 
v___x_1091_ = l_List_elem___redArg(v___f_1088_, v_a_1090_, v_x_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(lean_object* v___f_1092_, lean_object* v_x_1093_, lean_object* v_a_1094_){
_start:
{
uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_res_1095_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(v___f_1092_, v_x_1093_, v_a_1094_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg(lean_object* v_inst_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
lean_object* v___f_1100_; lean_object* v___f_1101_; uint8_t v___x_1102_; 
v___f_1100_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1100_, 0, v_inst_1097_);
v___f_1101_ = lean_alloc_closure((void*)(l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1101_, 0, v___f_1100_);
lean_closure_set(v___f_1101_, 1, v_x_1099_);
v___x_1102_ = l_List_decidableBAll___redArg(v___f_1101_, v_x_1098_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(lean_object* v_inst_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
uint8_t v_res_1106_; lean_object* v_r_1107_; 
v_res_1106_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1103_, v_x_1104_, v_x_1105_);
v_r_1107_ = lean_box(v_res_1106_);
return v_r_1107_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq(lean_object* v_00_u03b1_1108_, lean_object* v_inst_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1109_, v_x_1110_, v_x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___boxed(lean_object* v_00_u03b1_1113_, lean_object* v_inst_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_res_1117_ = l_List_instDecidableRelSubsetOfDecidableEq(v_00_u03b1_1113_, v_inst_1114_, v_x_1115_, v_x_1116_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2));
v___x_1153_ = l_String_toRawSubstring_x27(v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object* v_x_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
lean_inc(v_x_1173_);
v___x_1177_ = l_Lean_Syntax_isOfKind(v_x_1173_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec_ref(v_a_1174_);
lean_dec(v_x_1173_);
v___x_1178_ = lean_box(1);
v___x_1179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v_a_1175_);
return v___x_1179_;
}
else
{
lean_object* v_quotContext_1180_; lean_object* v_currMacroScope_1181_; lean_object* v_ref_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_quotContext_1180_ = lean_ctor_get(v_a_1174_, 1);
lean_inc(v_quotContext_1180_);
v_currMacroScope_1181_ = lean_ctor_get(v_a_1174_, 2);
lean_inc(v_currMacroScope_1181_);
v_ref_1182_ = lean_ctor_get(v_a_1174_, 5);
lean_inc(v_ref_1182_);
lean_dec_ref(v_a_1174_);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = l_Lean_Syntax_getArg(v_x_1173_, v___x_1183_);
v___x_1185_ = lean_unsigned_to_nat(2u);
v___x_1186_ = l_Lean_Syntax_getArg(v_x_1173_, v___x_1185_);
lean_dec(v_x_1173_);
v___x_1187_ = 0;
v___x_1188_ = l_Lean_SourceInfo_fromRef(v_ref_1182_, v___x_1187_);
lean_dec(v_ref_1182_);
v___x_1189_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1190_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
v___x_1191_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4));
v___x_1192_ = l_Lean_addMacroScope(v_quotContext_1180_, v___x_1191_, v_currMacroScope_1181_);
v___x_1193_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10));
lean_inc(v___x_1188_);
v___x_1194_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1188_);
lean_ctor_set(v___x_1194_, 1, v___x_1190_);
lean_ctor_set(v___x_1194_, 2, v___x_1192_);
lean_ctor_set(v___x_1194_, 3, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
lean_inc(v___x_1188_);
v___x_1196_ = l_Lean_Syntax_node2(v___x_1188_, v___x_1195_, v___x_1184_, v___x_1186_);
v___x_1197_ = l_Lean_Syntax_node2(v___x_1188_, v___x_1189_, v___x_1194_, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v_a_1175_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object* v_x_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1202_);
v___x_1206_ = l_Lean_Syntax_isOfKind(v_x_1202_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_dec(v_x_1202_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v_a_1204_);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = l_Lean_Syntax_getArg(v_x_1202_, v___x_1209_);
v___x_1211_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1210_);
v___x_1212_ = l_Lean_Syntax_isOfKind(v___x_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec(v___x_1210_);
lean_dec(v_x_1202_);
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v_a_1204_);
return v___x_1214_;
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = l_Lean_Syntax_getArg(v_x_1202_, v___x_1215_);
lean_dec(v_x_1202_);
v___x_1217_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1216_);
v___x_1218_ = l_Lean_Syntax_matchesNull(v___x_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec(v___x_1216_);
lean_dec(v___x_1210_);
v___x_1219_ = lean_box(0);
v___x_1220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v_a_1204_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_ref_1223_; uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1221_ = l_Lean_Syntax_getArg(v___x_1216_, v___x_1209_);
v___x_1222_ = l_Lean_Syntax_getArg(v___x_1216_, v___x_1215_);
lean_dec(v___x_1216_);
v_ref_1223_ = l_Lean_replaceRef(v___x_1210_, v_a_1203_);
lean_dec(v___x_1210_);
v___x_1224_ = 0;
v___x_1225_ = l_Lean_SourceInfo_fromRef(v_ref_1223_, v___x_1224_);
lean_dec(v_ref_1223_);
v___x_1226_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
v___x_1227_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__5));
lean_inc(v___x_1225_);
v___x_1228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1225_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_Syntax_node3(v___x_1225_, v___x_1226_, v___x_1221_, v___x_1228_, v___x_1222_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v_a_1204_);
return v___x_1230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object* v_x_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(v_x_1231_, v_a_1232_, v_a_1233_);
lean_dec(v_a_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist___redArg(lean_object* v_inst_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_){
_start:
{
if (lean_obj_tag(v_x_1236_) == 0)
{
uint8_t v___x_1238_; 
lean_dec(v_x_1237_);
lean_dec_ref(v_inst_1235_);
v___x_1238_ = 1;
return v___x_1238_;
}
else
{
if (lean_obj_tag(v_x_1237_) == 0)
{
uint8_t v___x_1239_; 
lean_dec_ref(v_x_1236_);
lean_dec_ref(v_inst_1235_);
v___x_1239_ = 0;
return v___x_1239_;
}
else
{
lean_object* v_head_1240_; lean_object* v_tail_1241_; lean_object* v_head_1242_; lean_object* v_tail_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_head_1240_ = lean_ctor_get(v_x_1236_, 0);
v_tail_1241_ = lean_ctor_get(v_x_1236_, 1);
v_head_1242_ = lean_ctor_get(v_x_1237_, 0);
lean_inc(v_head_1242_);
v_tail_1243_ = lean_ctor_get(v_x_1237_, 1);
lean_inc(v_tail_1243_);
lean_dec_ref(v_x_1237_);
lean_inc_ref(v_inst_1235_);
lean_inc(v_head_1240_);
v___x_1244_ = lean_apply_2(v_inst_1235_, v_head_1240_, v_head_1242_);
v___x_1245_ = lean_unbox(v___x_1244_);
if (v___x_1245_ == 0)
{
v_x_1237_ = v_tail_1243_;
goto _start;
}
else
{
lean_inc(v_tail_1241_);
lean_dec_ref(v_x_1236_);
v_x_1236_ = v_tail_1241_;
v_x_1237_ = v_tail_1243_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSublist___redArg___boxed(lean_object* v_inst_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_List_isSublist___redArg(v_inst_1248_, v_x_1249_, v_x_1250_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist(lean_object* v_00_u03b1_1253_, lean_object* v_inst_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = l_List_isSublist___redArg(v_inst_1254_, v_x_1255_, v_x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_List_isSublist___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_inst_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
uint8_t v_res_1262_; lean_object* v_r_1263_; 
v_res_1262_ = l_List_isSublist(v_00_u03b1_1258_, v_inst_1259_, v_x_1260_, v_x_1261_);
v_r_1263_ = lean_box(v_res_1262_);
return v_r_1263_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0));
v___x_1282_ = l_String_toRawSubstring_x27(v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object* v_x_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
lean_inc(v_x_1294_);
v___x_1298_ = l_Lean_Syntax_isOfKind(v_x_1294_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v_a_1295_);
lean_dec(v_x_1294_);
v___x_1299_ = lean_box(1);
v___x_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v_a_1296_);
return v___x_1300_;
}
else
{
lean_object* v_quotContext_1301_; lean_object* v_currMacroScope_1302_; lean_object* v_ref_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_quotContext_1301_ = lean_ctor_get(v_a_1295_, 1);
lean_inc(v_quotContext_1301_);
v_currMacroScope_1302_ = lean_ctor_get(v_a_1295_, 2);
lean_inc(v_currMacroScope_1302_);
v_ref_1303_ = lean_ctor_get(v_a_1295_, 5);
lean_inc(v_ref_1303_);
lean_dec_ref(v_a_1295_);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = l_Lean_Syntax_getArg(v_x_1294_, v___x_1304_);
v___x_1306_ = lean_unsigned_to_nat(2u);
v___x_1307_ = l_Lean_Syntax_getArg(v_x_1294_, v___x_1306_);
lean_dec(v_x_1294_);
v___x_1308_ = 0;
v___x_1309_ = l_Lean_SourceInfo_fromRef(v_ref_1303_, v___x_1308_);
lean_dec(v_ref_1303_);
v___x_1310_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1311_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
v___x_1312_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2));
v___x_1313_ = l_Lean_addMacroScope(v_quotContext_1301_, v___x_1312_, v_currMacroScope_1302_);
v___x_1314_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5));
lean_inc(v___x_1309_);
v___x_1315_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1309_);
lean_ctor_set(v___x_1315_, 1, v___x_1311_);
lean_ctor_set(v___x_1315_, 2, v___x_1313_);
lean_ctor_set(v___x_1315_, 3, v___x_1314_);
v___x_1316_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
lean_inc(v___x_1309_);
v___x_1317_ = l_Lean_Syntax_node2(v___x_1309_, v___x_1316_, v___x_1305_, v___x_1307_);
v___x_1318_ = l_Lean_Syntax_node2(v___x_1309_, v___x_1310_, v___x_1315_, v___x_1317_);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v_a_1296_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object* v_x_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1320_);
v___x_1324_ = l_Lean_Syntax_isOfKind(v_x_1320_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec(v_x_1320_);
v___x_1325_ = lean_box(0);
v___x_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v_a_1322_);
return v___x_1326_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = l_Lean_Syntax_getArg(v_x_1320_, v___x_1327_);
v___x_1329_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1328_);
v___x_1330_ = l_Lean_Syntax_isOfKind(v___x_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec(v___x_1328_);
lean_dec(v_x_1320_);
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v_a_1322_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1333_ = lean_unsigned_to_nat(1u);
v___x_1334_ = l_Lean_Syntax_getArg(v_x_1320_, v___x_1333_);
lean_dec(v_x_1320_);
v___x_1335_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1334_);
v___x_1336_ = l_Lean_Syntax_matchesNull(v___x_1334_, v___x_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec(v___x_1334_);
lean_dec(v___x_1328_);
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v_a_1322_);
return v___x_1338_;
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v_ref_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1339_ = l_Lean_Syntax_getArg(v___x_1334_, v___x_1327_);
v___x_1340_ = l_Lean_Syntax_getArg(v___x_1334_, v___x_1333_);
lean_dec(v___x_1334_);
v_ref_1341_ = l_Lean_replaceRef(v___x_1328_, v_a_1321_);
lean_dec(v___x_1328_);
v___x_1342_ = 0;
v___x_1343_ = l_Lean_SourceInfo_fromRef(v_ref_1341_, v___x_1342_);
lean_dec(v_ref_1341_);
v___x_1344_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
v___x_1345_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__2));
lean_inc(v___x_1343_);
v___x_1346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1343_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = l_Lean_Syntax_node3(v___x_1343_, v___x_1344_, v___x_1339_, v___x_1346_, v___x_1340_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v_a_1322_);
return v___x_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object* v_x_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(v_x_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf___redArg(lean_object* v_inst_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
if (lean_obj_tag(v_x_1354_) == 0)
{
uint8_t v___x_1356_; 
lean_dec(v_x_1355_);
lean_dec_ref(v_inst_1353_);
v___x_1356_ = 1;
return v___x_1356_;
}
else
{
if (lean_obj_tag(v_x_1355_) == 0)
{
uint8_t v___x_1357_; 
lean_dec_ref(v_x_1354_);
lean_dec_ref(v_inst_1353_);
v___x_1357_ = 0;
return v___x_1357_;
}
else
{
lean_object* v_head_1358_; lean_object* v_tail_1359_; lean_object* v_head_1360_; lean_object* v_tail_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_head_1358_ = lean_ctor_get(v_x_1354_, 0);
lean_inc(v_head_1358_);
v_tail_1359_ = lean_ctor_get(v_x_1354_, 1);
lean_inc(v_tail_1359_);
lean_dec_ref(v_x_1354_);
v_head_1360_ = lean_ctor_get(v_x_1355_, 0);
lean_inc(v_head_1360_);
v_tail_1361_ = lean_ctor_get(v_x_1355_, 1);
lean_inc(v_tail_1361_);
lean_dec_ref(v_x_1355_);
lean_inc_ref(v_inst_1353_);
v___x_1362_ = lean_apply_2(v_inst_1353_, v_head_1358_, v_head_1360_);
v___x_1363_ = lean_unbox(v___x_1362_);
if (v___x_1363_ == 0)
{
uint8_t v___x_1364_; 
lean_dec(v_tail_1361_);
lean_dec(v_tail_1359_);
lean_dec_ref(v_inst_1353_);
v___x_1364_ = lean_unbox(v___x_1362_);
return v___x_1364_;
}
else
{
v_x_1354_ = v_tail_1359_;
v_x_1355_ = v_tail_1361_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___redArg___boxed(lean_object* v_inst_1366_, lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_res_1369_ = l_List_isPrefixOf___redArg(v_inst_1366_, v_x_1367_, v_x_1368_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf(lean_object* v_00_u03b1_1371_, lean_object* v_inst_1372_, lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
uint8_t v___x_1375_; 
v___x_1375_ = l_List_isPrefixOf___redArg(v_inst_1372_, v_x_1373_, v_x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___boxed(lean_object* v_00_u03b1_1376_, lean_object* v_inst_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_){
_start:
{
uint8_t v_res_1380_; lean_object* v_r_1381_; 
v_res_1380_ = l_List_isPrefixOf(v_00_u03b1_1376_, v_inst_1377_, v_x_1378_, v_x_1379_);
v_r_1381_ = lean_box(v_res_1380_);
return v_r_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_1382_, lean_object* v_x_1383_, lean_object* v_h__1_1384_, lean_object* v_h__2_1385_, lean_object* v_h__3_1386_){
_start:
{
if (lean_obj_tag(v_x_1382_) == 0)
{
lean_object* v___x_1387_; 
lean_dec(v_h__3_1386_);
lean_dec(v_h__2_1385_);
v___x_1387_ = lean_apply_1(v_h__1_1384_, v_x_1383_);
return v___x_1387_;
}
else
{
lean_dec(v_h__1_1384_);
if (lean_obj_tag(v_x_1383_) == 0)
{
lean_object* v___x_1388_; 
lean_dec(v_h__3_1386_);
v___x_1388_ = lean_apply_2(v_h__2_1385_, v_x_1382_, lean_box(0));
return v___x_1388_;
}
else
{
lean_object* v_head_1389_; lean_object* v_tail_1390_; lean_object* v_head_1391_; lean_object* v_tail_1392_; lean_object* v___x_1393_; 
lean_dec(v_h__2_1385_);
v_head_1389_ = lean_ctor_get(v_x_1382_, 0);
lean_inc(v_head_1389_);
v_tail_1390_ = lean_ctor_get(v_x_1382_, 1);
lean_inc(v_tail_1390_);
lean_dec_ref(v_x_1382_);
v_head_1391_ = lean_ctor_get(v_x_1383_, 0);
lean_inc(v_head_1391_);
v_tail_1392_ = lean_ctor_get(v_x_1383_, 1);
lean_inc(v_tail_1392_);
lean_dec_ref(v_x_1383_);
v___x_1393_ = lean_apply_4(v_h__3_1386_, v_head_1389_, v_tail_1390_, v_head_1391_, v_tail_1392_);
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object* v_00_u03b1_1394_, lean_object* v_motive_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_, lean_object* v_h__1_1398_, lean_object* v_h__2_1399_, lean_object* v_h__3_1400_){
_start:
{
if (lean_obj_tag(v_x_1396_) == 0)
{
lean_object* v___x_1401_; 
lean_dec(v_h__3_1400_);
lean_dec(v_h__2_1399_);
v___x_1401_ = lean_apply_1(v_h__1_1398_, v_x_1397_);
return v___x_1401_;
}
else
{
lean_dec(v_h__1_1398_);
if (lean_obj_tag(v_x_1397_) == 0)
{
lean_object* v___x_1402_; 
lean_dec(v_h__3_1400_);
v___x_1402_ = lean_apply_2(v_h__2_1399_, v_x_1396_, lean_box(0));
return v___x_1402_;
}
else
{
lean_object* v_head_1403_; lean_object* v_tail_1404_; lean_object* v_head_1405_; lean_object* v_tail_1406_; lean_object* v___x_1407_; 
lean_dec(v_h__2_1399_);
v_head_1403_ = lean_ctor_get(v_x_1396_, 0);
lean_inc(v_head_1403_);
v_tail_1404_ = lean_ctor_get(v_x_1396_, 1);
lean_inc(v_tail_1404_);
lean_dec_ref(v_x_1396_);
v_head_1405_ = lean_ctor_get(v_x_1397_, 0);
lean_inc(v_head_1405_);
v_tail_1406_ = lean_ctor_get(v_x_1397_, 1);
lean_inc(v_tail_1406_);
lean_dec_ref(v_x_1397_);
v___x_1407_ = lean_apply_4(v_h__3_1400_, v_head_1403_, v_tail_1404_, v_head_1405_, v_tail_1406_);
return v___x_1407_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___redArg(lean_object* v_inst_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 0)
{
lean_object* v___x_1411_; 
lean_dec_ref(v_inst_1408_);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_x_1410_);
return v___x_1411_;
}
else
{
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_object* v___x_1412_; 
lean_dec_ref(v_x_1409_);
lean_dec_ref(v_inst_1408_);
v___x_1412_ = lean_box(0);
return v___x_1412_;
}
else
{
lean_object* v_head_1413_; lean_object* v_tail_1414_; lean_object* v_head_1415_; lean_object* v_tail_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_head_1413_ = lean_ctor_get(v_x_1409_, 0);
lean_inc(v_head_1413_);
v_tail_1414_ = lean_ctor_get(v_x_1409_, 1);
lean_inc(v_tail_1414_);
lean_dec_ref(v_x_1409_);
v_head_1415_ = lean_ctor_get(v_x_1410_, 0);
lean_inc(v_head_1415_);
v_tail_1416_ = lean_ctor_get(v_x_1410_, 1);
lean_inc(v_tail_1416_);
lean_dec_ref(v_x_1410_);
lean_inc_ref(v_inst_1408_);
v___x_1417_ = lean_apply_2(v_inst_1408_, v_head_1413_, v_head_1415_);
v___x_1418_ = lean_unbox(v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
lean_dec(v_tail_1416_);
lean_dec(v_tail_1414_);
lean_dec_ref(v_inst_1408_);
v___x_1419_ = lean_box(0);
return v___x_1419_;
}
else
{
v_x_1409_ = v_tail_1414_;
v_x_1410_ = v_tail_1416_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object* v_00_u03b1_1421_, lean_object* v_inst_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_List_isPrefixOf_x3f___redArg(v_inst_1422_, v_x_1423_, v_x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf___redArg(lean_object* v_inst_1426_, lean_object* v_l_u2081_1427_, lean_object* v_l_u2082_1428_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1429_ = l_List_reverse___redArg(v_l_u2081_1427_);
v___x_1430_ = l_List_reverse___redArg(v_l_u2082_1428_);
v___x_1431_ = l_List_isPrefixOf___redArg(v_inst_1426_, v___x_1429_, v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___redArg___boxed(lean_object* v_inst_1432_, lean_object* v_l_u2081_1433_, lean_object* v_l_u2082_1434_){
_start:
{
uint8_t v_res_1435_; lean_object* v_r_1436_; 
v_res_1435_ = l_List_isSuffixOf___redArg(v_inst_1432_, v_l_u2081_1433_, v_l_u2082_1434_);
v_r_1436_ = lean_box(v_res_1435_);
return v_r_1436_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf(lean_object* v_00_u03b1_1437_, lean_object* v_inst_1438_, lean_object* v_l_u2081_1439_, lean_object* v_l_u2082_1440_){
_start:
{
uint8_t v___x_1441_; 
v___x_1441_ = l_List_isSuffixOf___redArg(v_inst_1438_, v_l_u2081_1439_, v_l_u2082_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___boxed(lean_object* v_00_u03b1_1442_, lean_object* v_inst_1443_, lean_object* v_l_u2081_1444_, lean_object* v_l_u2082_1445_){
_start:
{
uint8_t v_res_1446_; lean_object* v_r_1447_; 
v_res_1446_ = l_List_isSuffixOf(v_00_u03b1_1442_, v_inst_1443_, v_l_u2081_1444_, v_l_u2082_1445_);
v_r_1447_ = lean_box(v_res_1446_);
return v_r_1447_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___redArg(lean_object* v_inst_1448_, lean_object* v_l_u2081_1449_, lean_object* v_l_u2082_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = l_List_reverse___redArg(v_l_u2081_1449_);
v___x_1452_ = l_List_reverse___redArg(v_l_u2082_1450_);
v___x_1453_ = l_List_isPrefixOf_x3f___redArg(v_inst_1448_, v___x_1451_, v___x_1452_);
if (lean_obj_tag(v___x_1453_) == 0)
{
return v___x_1453_;
}
else
{
lean_object* v_val_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1462_; 
v_val_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_val_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = l_List_reverse___redArg(v_val_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1460_ = v___x_1456_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object* v_00_u03b1_1463_, lean_object* v_inst_1464_, lean_object* v_l_u2081_1465_, lean_object* v_l_u2082_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_List_isSuffixOf_x3f___redArg(v_inst_1464_, v_l_u2081_1465_, v_l_u2082_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0));
v___x_1486_ = l_String_toRawSubstring_x27(v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object* v_x_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
lean_inc(v_x_1498_);
v___x_1502_ = l_Lean_Syntax_isOfKind(v_x_1498_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref(v_a_1499_);
lean_dec(v_x_1498_);
v___x_1503_ = lean_box(1);
v___x_1504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v_a_1500_);
return v___x_1504_;
}
else
{
lean_object* v_quotContext_1505_; lean_object* v_currMacroScope_1506_; lean_object* v_ref_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_quotContext_1505_ = lean_ctor_get(v_a_1499_, 1);
lean_inc(v_quotContext_1505_);
v_currMacroScope_1506_ = lean_ctor_get(v_a_1499_, 2);
lean_inc(v_currMacroScope_1506_);
v_ref_1507_ = lean_ctor_get(v_a_1499_, 5);
lean_inc(v_ref_1507_);
lean_dec_ref(v_a_1499_);
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = l_Lean_Syntax_getArg(v_x_1498_, v___x_1508_);
v___x_1510_ = lean_unsigned_to_nat(2u);
v___x_1511_ = l_Lean_Syntax_getArg(v_x_1498_, v___x_1510_);
lean_dec(v_x_1498_);
v___x_1512_ = 0;
v___x_1513_ = l_Lean_SourceInfo_fromRef(v_ref_1507_, v___x_1512_);
lean_dec(v_ref_1507_);
v___x_1514_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1515_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
v___x_1516_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2));
v___x_1517_ = l_Lean_addMacroScope(v_quotContext_1505_, v___x_1516_, v_currMacroScope_1506_);
v___x_1518_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5));
lean_inc(v___x_1513_);
v___x_1519_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1513_);
lean_ctor_set(v___x_1519_, 1, v___x_1515_);
lean_ctor_set(v___x_1519_, 2, v___x_1517_);
lean_ctor_set(v___x_1519_, 3, v___x_1518_);
v___x_1520_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
lean_inc(v___x_1513_);
v___x_1521_ = l_Lean_Syntax_node2(v___x_1513_, v___x_1520_, v___x_1509_, v___x_1511_);
v___x_1522_ = l_Lean_Syntax_node2(v___x_1513_, v___x_1514_, v___x_1519_, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v_a_1500_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object* v_x_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1524_);
v___x_1528_ = l_Lean_Syntax_isOfKind(v_x_1524_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_x_1524_);
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v_a_1526_);
return v___x_1530_;
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = l_Lean_Syntax_getArg(v_x_1524_, v___x_1531_);
v___x_1533_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1532_);
v___x_1534_ = l_Lean_Syntax_isOfKind(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v___x_1532_);
lean_dec(v_x_1524_);
v___x_1535_ = lean_box(0);
v___x_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v_a_1526_);
return v___x_1536_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = l_Lean_Syntax_getArg(v_x_1524_, v___x_1537_);
lean_dec(v_x_1524_);
v___x_1539_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1538_);
v___x_1540_ = l_Lean_Syntax_matchesNull(v___x_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_dec(v___x_1538_);
lean_dec(v___x_1532_);
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v_a_1526_);
return v___x_1542_;
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_ref_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1543_ = l_Lean_Syntax_getArg(v___x_1538_, v___x_1531_);
v___x_1544_ = l_Lean_Syntax_getArg(v___x_1538_, v___x_1537_);
lean_dec(v___x_1538_);
v_ref_1545_ = l_Lean_replaceRef(v___x_1532_, v_a_1525_);
lean_dec(v___x_1532_);
v___x_1546_ = 0;
v___x_1547_ = l_Lean_SourceInfo_fromRef(v_ref_1545_, v___x_1546_);
lean_dec(v_ref_1545_);
v___x_1548_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
v___x_1549_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__2));
lean_inc(v___x_1547_);
v___x_1550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1547_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = l_Lean_Syntax_node3(v___x_1547_, v___x_1548_, v___x_1543_, v___x_1550_, v___x_1544_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v_a_1526_);
return v___x_1552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object* v_x_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(v_x_1553_, v_a_1554_, v_a_1555_);
lean_dec(v_a_1554_);
return v_res_1556_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0));
v___x_1575_ = l_String_toRawSubstring_x27(v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object* v_x_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
lean_inc(v_x_1587_);
v___x_1591_ = l_Lean_Syntax_isOfKind(v_x_1587_, v___x_1590_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec_ref(v_a_1588_);
lean_dec(v_x_1587_);
v___x_1592_ = lean_box(1);
v___x_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v_a_1589_);
return v___x_1593_;
}
else
{
lean_object* v_quotContext_1594_; lean_object* v_currMacroScope_1595_; lean_object* v_ref_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_quotContext_1594_ = lean_ctor_get(v_a_1588_, 1);
lean_inc(v_quotContext_1594_);
v_currMacroScope_1595_ = lean_ctor_get(v_a_1588_, 2);
lean_inc(v_currMacroScope_1595_);
v_ref_1596_ = lean_ctor_get(v_a_1588_, 5);
lean_inc(v_ref_1596_);
lean_dec_ref(v_a_1588_);
v___x_1597_ = lean_unsigned_to_nat(0u);
v___x_1598_ = l_Lean_Syntax_getArg(v_x_1587_, v___x_1597_);
v___x_1599_ = lean_unsigned_to_nat(2u);
v___x_1600_ = l_Lean_Syntax_getArg(v_x_1587_, v___x_1599_);
lean_dec(v_x_1587_);
v___x_1601_ = 0;
v___x_1602_ = l_Lean_SourceInfo_fromRef(v_ref_1596_, v___x_1601_);
lean_dec(v_ref_1596_);
v___x_1603_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1604_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
v___x_1605_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2));
v___x_1606_ = l_Lean_addMacroScope(v_quotContext_1594_, v___x_1605_, v_currMacroScope_1595_);
v___x_1607_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5));
lean_inc(v___x_1602_);
v___x_1608_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1602_);
lean_ctor_set(v___x_1608_, 1, v___x_1604_);
lean_ctor_set(v___x_1608_, 2, v___x_1606_);
lean_ctor_set(v___x_1608_, 3, v___x_1607_);
v___x_1609_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
lean_inc(v___x_1602_);
v___x_1610_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1609_, v___x_1598_, v___x_1600_);
v___x_1611_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1603_, v___x_1608_, v___x_1610_);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v_a_1589_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object* v_x_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1613_);
v___x_1617_ = l_Lean_Syntax_isOfKind(v_x_1613_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_x_1613_);
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v_a_1615_);
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = l_Lean_Syntax_getArg(v_x_1613_, v___x_1620_);
v___x_1622_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1621_);
v___x_1623_ = l_Lean_Syntax_isOfKind(v___x_1621_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec(v___x_1621_);
lean_dec(v_x_1613_);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v_a_1615_);
return v___x_1625_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1626_ = lean_unsigned_to_nat(1u);
v___x_1627_ = l_Lean_Syntax_getArg(v_x_1613_, v___x_1626_);
lean_dec(v_x_1613_);
v___x_1628_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1627_);
v___x_1629_ = l_Lean_Syntax_matchesNull(v___x_1627_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec(v___x_1627_);
lean_dec(v___x_1621_);
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v_a_1615_);
return v___x_1631_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v_ref_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1632_ = l_Lean_Syntax_getArg(v___x_1627_, v___x_1620_);
v___x_1633_ = l_Lean_Syntax_getArg(v___x_1627_, v___x_1626_);
lean_dec(v___x_1627_);
v_ref_1634_ = l_Lean_replaceRef(v___x_1621_, v_a_1614_);
lean_dec(v___x_1621_);
v___x_1635_ = 0;
v___x_1636_ = l_Lean_SourceInfo_fromRef(v_ref_1634_, v___x_1635_);
lean_dec(v_ref_1634_);
v___x_1637_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
v___x_1638_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__2));
lean_inc(v___x_1636_);
v___x_1639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1636_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Lean_Syntax_node3(v___x_1636_, v___x_1637_, v___x_1632_, v___x_1639_, v___x_1633_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v_a_1615_);
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object* v_x_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(v_x_1642_, v_a_1643_, v_a_1644_);
lean_dec(v_a_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal___redArg(lean_object* v_inst_1646_, lean_object* v_l_u2081_1647_, lean_object* v_l_u2082_1648_){
_start:
{
uint8_t v___x_1649_; 
lean_inc(v_l_u2082_1648_);
lean_inc(v_l_u2081_1647_);
lean_inc_ref(v_inst_1646_);
v___x_1649_ = l_List_isPrefixOf___redArg(v_inst_1646_, v_l_u2081_1647_, v_l_u2082_1648_);
if (v___x_1649_ == 0)
{
if (lean_obj_tag(v_l_u2082_1648_) == 0)
{
lean_dec(v_l_u2081_1647_);
lean_dec_ref(v_inst_1646_);
return v___x_1649_;
}
else
{
lean_object* v_tail_1650_; 
v_tail_1650_ = lean_ctor_get(v_l_u2082_1648_, 1);
lean_inc(v_tail_1650_);
lean_dec_ref(v_l_u2082_1648_);
v_l_u2082_1648_ = v_tail_1650_;
goto _start;
}
}
else
{
lean_dec(v_l_u2082_1648_);
lean_dec(v_l_u2081_1647_);
lean_dec_ref(v_inst_1646_);
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___redArg___boxed(lean_object* v_inst_1652_, lean_object* v_l_u2081_1653_, lean_object* v_l_u2082_1654_){
_start:
{
uint8_t v_res_1655_; lean_object* v_r_1656_; 
v_res_1655_ = l_List_isInfixOf__internal___redArg(v_inst_1652_, v_l_u2081_1653_, v_l_u2082_1654_);
v_r_1656_ = lean_box(v_res_1655_);
return v_r_1656_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal(lean_object* v_00_u03b1_1657_, lean_object* v_inst_1658_, lean_object* v_l_u2081_1659_, lean_object* v_l_u2082_1660_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = l_List_isInfixOf__internal___redArg(v_inst_1658_, v_l_u2081_1659_, v_l_u2082_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___boxed(lean_object* v_00_u03b1_1662_, lean_object* v_inst_1663_, lean_object* v_l_u2081_1664_, lean_object* v_l_u2082_1665_){
_start:
{
uint8_t v_res_1666_; lean_object* v_r_1667_; 
v_res_1666_ = l_List_isInfixOf__internal(v_00_u03b1_1662_, v_inst_1663_, v_l_u2081_1664_, v_l_u2082_1665_);
v_r_1667_ = lean_box(v_res_1666_);
return v_r_1667_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go___redArg(lean_object* v_l_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
if (lean_obj_tag(v_a_1669_) == 0)
{
lean_object* v___x_1672_; 
lean_dec(v_a_1671_);
lean_dec(v_a_1670_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_l_1668_);
lean_ctor_set(v___x_1672_, 1, v_a_1669_);
return v___x_1672_;
}
else
{
lean_object* v_head_1673_; lean_object* v_tail_1674_; lean_object* v_zero_1675_; uint8_t v_isZero_1676_; 
v_head_1673_ = lean_ctor_get(v_a_1669_, 0);
v_tail_1674_ = lean_ctor_get(v_a_1669_, 1);
v_zero_1675_ = lean_unsigned_to_nat(0u);
v_isZero_1676_ = lean_nat_dec_eq(v_a_1670_, v_zero_1675_);
if (v_isZero_1676_ == 1)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v_a_1670_);
lean_dec(v_l_1668_);
v___x_1677_ = l_List_reverse___redArg(v_a_1671_);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v_a_1669_);
return v___x_1678_;
}
else
{
lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1688_; 
lean_inc(v_tail_1674_);
lean_inc(v_head_1673_);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_a_1669_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; lean_object* v_unused_1690_; 
v_unused_1689_ = lean_ctor_get(v_a_1669_, 1);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_a_1669_, 0);
lean_dec(v_unused_1690_);
v___x_1680_ = v_a_1669_;
v_isShared_1681_ = v_isSharedCheck_1688_;
goto v_resetjp_1679_;
}
else
{
lean_dec(v_a_1669_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1688_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v_one_1682_; lean_object* v_n_1683_; lean_object* v___x_1685_; 
v_one_1682_ = lean_unsigned_to_nat(1u);
v_n_1683_ = lean_nat_sub(v_a_1670_, v_one_1682_);
lean_dec(v_a_1670_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v_a_1671_);
v___x_1685_ = v___x_1680_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_head_1673_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_a_1671_);
v___x_1685_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
v_a_1669_ = v_tail_1674_;
v_a_1670_ = v_n_1683_;
v_a_1671_ = v___x_1685_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object* v_00_u03b1_1691_, lean_object* v_l_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_List_splitAt_go___redArg(v_l_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt___redArg(lean_object* v_n_1697_, lean_object* v_l_1698_){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = lean_box(0);
lean_inc(v_l_1698_);
v___x_1700_ = l_List_splitAt_go___redArg(v_l_1698_, v_l_1698_, v_n_1697_, v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt(lean_object* v_00_u03b1_1701_, lean_object* v_n_1702_, lean_object* v_l_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_List_splitAt___redArg(v_n_1702_, v_l_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg(lean_object* v_xs_1705_, lean_object* v_i_1706_){
_start:
{
lean_object* v_len_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_len_1707_ = l_List_length___redArg(v_xs_1705_);
v___x_1708_ = lean_unsigned_to_nat(1u);
v___x_1709_ = lean_nat_dec_le(v_len_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v_i_1710_; lean_object* v_ys_1711_; lean_object* v_zs_1712_; lean_object* v___x_1713_; 
v_i_1710_ = lean_nat_mod(v_i_1706_, v_len_1707_);
lean_dec(v_len_1707_);
lean_inc(v_xs_1705_);
v_ys_1711_ = l_List_take___redArg(v_i_1710_, v_xs_1705_);
v_zs_1712_ = l_List_drop___redArg(v_i_1710_, v_xs_1705_);
lean_dec(v_xs_1705_);
v___x_1713_ = l_List_appendTR___redArg(v_zs_1712_, v_ys_1711_);
return v___x_1713_;
}
else
{
lean_dec(v_len_1707_);
return v_xs_1705_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg___boxed(lean_object* v_xs_1714_, lean_object* v_i_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_List_rotateLeft___redArg(v_xs_1714_, v_i_1715_);
lean_dec(v_i_1715_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft(lean_object* v_00_u03b1_1717_, lean_object* v_xs_1718_, lean_object* v_i_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_List_rotateLeft___redArg(v_xs_1718_, v_i_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___boxed(lean_object* v_00_u03b1_1721_, lean_object* v_xs_1722_, lean_object* v_i_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_List_rotateLeft(v_00_u03b1_1721_, v_xs_1722_, v_i_1723_);
lean_dec(v_i_1723_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg(lean_object* v_xs_1725_, lean_object* v_i_1726_){
_start:
{
lean_object* v_len_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_len_1727_ = l_List_length___redArg(v_xs_1725_);
v___x_1728_ = lean_unsigned_to_nat(1u);
v___x_1729_ = lean_nat_dec_le(v_len_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v_i_1731_; lean_object* v_ys_1732_; lean_object* v_zs_1733_; lean_object* v___x_1734_; 
v___x_1730_ = lean_nat_mod(v_i_1726_, v_len_1727_);
v_i_1731_ = lean_nat_sub(v_len_1727_, v___x_1730_);
lean_dec(v___x_1730_);
lean_dec(v_len_1727_);
lean_inc(v_xs_1725_);
v_ys_1732_ = l_List_take___redArg(v_i_1731_, v_xs_1725_);
v_zs_1733_ = l_List_drop___redArg(v_i_1731_, v_xs_1725_);
lean_dec(v_xs_1725_);
v___x_1734_ = l_List_appendTR___redArg(v_zs_1733_, v_ys_1732_);
return v___x_1734_;
}
else
{
lean_dec(v_len_1727_);
return v_xs_1725_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg___boxed(lean_object* v_xs_1735_, lean_object* v_i_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_List_rotateRight___redArg(v_xs_1735_, v_i_1736_);
lean_dec(v_i_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight(lean_object* v_00_u03b1_1738_, lean_object* v_xs_1739_, lean_object* v_i_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_List_rotateRight___redArg(v_xs_1739_, v_i_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___boxed(lean_object* v_00_u03b1_1742_, lean_object* v_xs_1743_, lean_object* v_i_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_List_rotateRight(v_00_u03b1_1742_, v_xs_1743_, v_i_1744_);
lean_dec(v_i_1744_);
return v_res_1745_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise___redArg(lean_object* v_inst_1746_, lean_object* v_x_1747_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
uint8_t v___x_1748_; 
lean_dec_ref(v_inst_1746_);
v___x_1748_ = 1;
return v___x_1748_;
}
else
{
lean_object* v_head_1749_; lean_object* v_tail_1750_; uint8_t v___x_1751_; 
v_head_1749_ = lean_ctor_get(v_x_1747_, 0);
lean_inc(v_head_1749_);
v_tail_1750_ = lean_ctor_get(v_x_1747_, 1);
lean_inc(v_tail_1750_);
lean_dec_ref(v_x_1747_);
lean_inc(v_tail_1750_);
lean_inc_ref(v_inst_1746_);
v___x_1751_ = l_List_instDecidablePairwise___redArg(v_inst_1746_, v_tail_1750_);
if (v___x_1751_ == 0)
{
lean_dec(v_tail_1750_);
lean_dec(v_head_1749_);
lean_dec_ref(v_inst_1746_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1752_ = lean_apply_1(v_inst_1746_, v_head_1749_);
v___x_1753_ = l_List_decidableBAll___redArg(v___x_1752_, v_tail_1750_);
return v___x_1753_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___redArg___boxed(lean_object* v_inst_1754_, lean_object* v_x_1755_){
_start:
{
uint8_t v_res_1756_; lean_object* v_r_1757_; 
v_res_1756_ = l_List_instDecidablePairwise___redArg(v_inst_1754_, v_x_1755_);
v_r_1757_ = lean_box(v_res_1756_);
return v_r_1757_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise(lean_object* v_00_u03b1_1758_, lean_object* v_R_1759_, lean_object* v_inst_1760_, lean_object* v_x_1761_){
_start:
{
uint8_t v___x_1762_; 
v___x_1762_ = l_List_instDecidablePairwise___redArg(v_inst_1760_, v_x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_R_1764_, lean_object* v_inst_1765_, lean_object* v_x_1766_){
_start:
{
uint8_t v_res_1767_; lean_object* v_r_1768_; 
v_res_1767_ = l_List_instDecidablePairwise(v_00_u03b1_1763_, v_R_1764_, v_inst_1765_, v_x_1766_);
v_r_1768_ = lean_box(v_res_1767_);
return v_r_1768_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg___lam__0(lean_object* v_inst_1769_, lean_object* v_a_1770_, lean_object* v_b_1771_){
_start:
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = lean_apply_2(v_inst_1769_, v_a_1770_, v_b_1771_);
v___x_1773_ = lean_unbox(v___x_1772_);
if (v___x_1773_ == 0)
{
uint8_t v___x_1774_; 
v___x_1774_ = 1;
return v___x_1774_;
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = 0;
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___lam__0___boxed(lean_object* v_inst_1776_, lean_object* v_a_1777_, lean_object* v_b_1778_){
_start:
{
uint8_t v_res_1779_; lean_object* v_r_1780_; 
v_res_1779_ = l_List_nodupDecidable___redArg___lam__0(v_inst_1776_, v_a_1777_, v_b_1778_);
v_r_1780_ = lean_box(v_res_1779_);
return v_r_1780_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg(lean_object* v_inst_1781_, lean_object* v_l_1782_){
_start:
{
lean_object* v___f_1783_; uint8_t v___x_1784_; 
v___f_1783_ = lean_alloc_closure((void*)(l_List_nodupDecidable___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1783_, 0, v_inst_1781_);
v___x_1784_ = l_List_instDecidablePairwise___redArg(v___f_1783_, v_l_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___boxed(lean_object* v_inst_1785_, lean_object* v_l_1786_){
_start:
{
uint8_t v_res_1787_; lean_object* v_r_1788_; 
v_res_1787_ = l_List_nodupDecidable___redArg(v_inst_1785_, v_l_1786_);
v_r_1788_ = lean_box(v_res_1787_);
return v_r_1788_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable(lean_object* v_00_u03b1_1789_, lean_object* v_inst_1790_, lean_object* v_l_1791_){
_start:
{
uint8_t v___x_1792_; 
v___x_1792_ = l_List_nodupDecidable___redArg(v_inst_1790_, v_l_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___boxed(lean_object* v_00_u03b1_1793_, lean_object* v_inst_1794_, lean_object* v_l_1795_){
_start:
{
uint8_t v_res_1796_; lean_object* v_r_1797_; 
v_res_1796_ = l_List_nodupDecidable(v_00_u03b1_1793_, v_inst_1794_, v_l_1795_);
v_r_1797_ = lean_box(v_res_1796_);
return v_r_1797_;
}
}
LEAN_EXPORT lean_object* l_List_replace___redArg(lean_object* v_inst_1798_, lean_object* v_x_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_){
_start:
{
if (lean_obj_tag(v_x_1799_) == 0)
{
lean_dec(v_x_1801_);
lean_dec(v_x_1800_);
lean_dec_ref(v_inst_1798_);
return v_x_1799_;
}
else
{
lean_object* v_head_1802_; lean_object* v_tail_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1816_; 
v_head_1802_ = lean_ctor_get(v_x_1799_, 0);
v_tail_1803_ = lean_ctor_get(v_x_1799_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_x_1799_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1805_ = v_x_1799_;
v_isShared_1806_ = v_isSharedCheck_1816_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_tail_1803_);
lean_inc(v_head_1802_);
lean_dec(v_x_1799_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1816_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_inc_ref(v_inst_1798_);
lean_inc(v_head_1802_);
lean_inc(v_x_1800_);
v___x_1807_ = lean_apply_2(v_inst_1798_, v_x_1800_, v_head_1802_);
v___x_1808_ = lean_unbox(v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = l_List_replace___redArg(v_inst_1798_, v_tail_1803_, v_x_1800_, v_x_1801_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1809_);
v___x_1811_ = v___x_1805_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_head_1802_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
else
{
lean_object* v___x_1814_; 
lean_dec(v_head_1802_);
lean_dec(v_x_1800_);
lean_dec_ref(v_inst_1798_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v_x_1801_);
v___x_1814_ = v___x_1805_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_x_1801_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_tail_1803_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_replace(lean_object* v_00_u03b1_1817_, lean_object* v_inst_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_List_replace___redArg(v_inst_1818_, v_x_1819_, v_x_1820_, v_x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg(lean_object* v_f_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_zero_1826_; uint8_t v_isZero_1827_; 
v_zero_1826_ = lean_unsigned_to_nat(0u);
v_isZero_1827_ = lean_nat_dec_eq(v_a_1824_, v_zero_1826_);
if (v_isZero_1827_ == 1)
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_apply_1(v_f_1823_, v_a_1825_);
return v___x_1828_;
}
else
{
if (lean_obj_tag(v_a_1825_) == 0)
{
lean_dec_ref(v_f_1823_);
return v_a_1825_;
}
else
{
lean_object* v_head_1829_; lean_object* v_tail_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1840_; 
v_head_1829_ = lean_ctor_get(v_a_1825_, 0);
v_tail_1830_ = lean_ctor_get(v_a_1825_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_a_1825_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1832_ = v_a_1825_;
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_tail_1830_);
lean_inc(v_head_1829_);
lean_dec(v_a_1825_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_one_1834_; lean_object* v_n_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v_one_1834_ = lean_unsigned_to_nat(1u);
v_n_1835_ = lean_nat_sub(v_a_1824_, v_one_1834_);
v___x_1836_ = l_List_modifyTailIdx_go___redArg(v_f_1823_, v_n_1835_, v_tail_1830_);
lean_dec(v_n_1835_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v___x_1836_);
v___x_1838_ = v___x_1832_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_head_1829_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1836_);
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
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg___boxed(lean_object* v_f_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_List_modifyTailIdx_go___redArg(v_f_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_a_1842_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go(lean_object* v_00_u03b1_1845_, lean_object* v_f_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_List_modifyTailIdx_go___redArg(v_f_1846_, v_a_1847_, v_a_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___boxed(lean_object* v_00_u03b1_1850_, lean_object* v_f_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_List_modifyTailIdx_go(v_00_u03b1_1850_, v_f_1851_, v_a_1852_, v_a_1853_);
lean_dec(v_a_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg(lean_object* v_l_1855_, lean_object* v_i_1856_, lean_object* v_f_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_List_modifyTailIdx_go___redArg(v_f_1857_, v_i_1856_, v_l_1855_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg___boxed(lean_object* v_l_1859_, lean_object* v_i_1860_, lean_object* v_f_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_List_modifyTailIdx___redArg(v_l_1859_, v_i_1860_, v_f_1861_);
lean_dec(v_i_1860_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx(lean_object* v_00_u03b1_1863_, lean_object* v_l_1864_, lean_object* v_i_1865_, lean_object* v_f_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_List_modifyTailIdx_go___redArg(v_f_1866_, v_i_1865_, v_l_1864_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___boxed(lean_object* v_00_u03b1_1868_, lean_object* v_l_1869_, lean_object* v_i_1870_, lean_object* v_f_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_List_modifyTailIdx(v_00_u03b1_1868_, v_l_1869_, v_i_1870_, v_f_1871_);
lean_dec(v_i_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_List_modifyHead___redArg(lean_object* v_f_1873_, lean_object* v_x_1874_){
_start:
{
if (lean_obj_tag(v_x_1874_) == 0)
{
lean_dec(v_f_1873_);
return v_x_1874_;
}
else
{
lean_object* v_head_1875_; lean_object* v_tail_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1884_; 
v_head_1875_ = lean_ctor_get(v_x_1874_, 0);
v_tail_1876_ = lean_ctor_get(v_x_1874_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_x_1874_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1878_ = v_x_1874_;
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_tail_1876_);
lean_inc(v_head_1875_);
lean_dec(v_x_1874_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1880_ = lean_apply_1(v_f_1873_, v_head_1875_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1880_);
v___x_1882_ = v___x_1878_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_tail_1876_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyHead(lean_object* v_00_u03b1_1885_, lean_object* v_f_1886_, lean_object* v_x_1887_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_dec(v_f_1886_);
return v_x_1887_;
}
else
{
lean_object* v_head_1888_; lean_object* v_tail_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1897_; 
v_head_1888_ = lean_ctor_get(v_x_1887_, 0);
v_tail_1889_ = lean_ctor_get(v_x_1887_, 1);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_x_1887_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1891_ = v_x_1887_;
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_tail_1889_);
lean_inc(v_head_1888_);
lean_dec(v_x_1887_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_apply_1(v_f_1886_, v_head_1888_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_tail_1889_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg___lam__0(lean_object* v_f_1898_, lean_object* v___y_1899_){
_start:
{
if (lean_obj_tag(v___y_1899_) == 0)
{
lean_dec(v_f_1898_);
return v___y_1899_;
}
else
{
lean_object* v_head_1900_; lean_object* v_tail_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1909_; 
v_head_1900_ = lean_ctor_get(v___y_1899_, 0);
v_tail_1901_ = lean_ctor_get(v___y_1899_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___y_1899_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1903_ = v___y_1899_;
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_tail_1901_);
lean_inc(v_head_1900_);
lean_dec(v___y_1899_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_apply_1(v_f_1898_, v_head_1900_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_tail_1901_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg(lean_object* v_l_1910_, lean_object* v_i_1911_, lean_object* v_f_1912_){
_start:
{
lean_object* v___f_1913_; lean_object* v___x_1914_; 
v___f_1913_ = lean_alloc_closure((void*)(l_List_modify___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1913_, 0, v_f_1912_);
v___x_1914_ = l_List_modifyTailIdx_go___redArg(v___f_1913_, v_i_1911_, v_l_1910_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg___boxed(lean_object* v_l_1915_, lean_object* v_i_1916_, lean_object* v_f_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_List_modify___redArg(v_l_1915_, v_i_1916_, v_f_1917_);
lean_dec(v_i_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_List_modify(lean_object* v_00_u03b1_1919_, lean_object* v_l_1920_, lean_object* v_i_1921_, lean_object* v_f_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_List_modify___redArg(v_l_1920_, v_i_1921_, v_f_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_List_modify___boxed(lean_object* v_00_u03b1_1924_, lean_object* v_l_1925_, lean_object* v_i_1926_, lean_object* v_f_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_List_modify(v_00_u03b1_1924_, v_l_1925_, v_i_1926_, v_f_1927_);
lean_dec(v_i_1926_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object* v_inst_1929_, lean_object* v_a_1930_, lean_object* v_l_1931_){
_start:
{
uint8_t v___x_1932_; 
lean_inc(v_l_1931_);
lean_inc(v_a_1930_);
v___x_1932_ = l_List_elem___redArg(v_inst_1929_, v_a_1930_, v_l_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1933_, 0, v_a_1930_);
lean_ctor_set(v___x_1933_, 1, v_l_1931_);
return v___x_1933_;
}
else
{
lean_dec(v_a_1930_);
return v_l_1931_;
}
}
}
LEAN_EXPORT lean_object* l_List_insert(lean_object* v_00_u03b1_1934_, lean_object* v_inst_1935_, lean_object* v_a_1936_, lean_object* v_l_1937_){
_start:
{
uint8_t v___x_1938_; 
lean_inc(v_l_1937_);
lean_inc(v_a_1936_);
v___x_1938_ = l_List_elem___redArg(v_inst_1935_, v_a_1936_, v_l_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1939_, 0, v_a_1936_);
lean_ctor_set(v___x_1939_, 1, v_l_1937_);
return v___x_1939_;
}
else
{
lean_dec(v_a_1936_);
return v_l_1937_;
}
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___lam__0(lean_object* v_a_1940_, lean_object* v_tail_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1942_, 0, v_a_1940_);
lean_ctor_set(v___x_1942_, 1, v_tail_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg(lean_object* v_xs_1943_, lean_object* v_i_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___f_1946_; lean_object* v___x_1947_; 
v___f_1946_ = lean_alloc_closure((void*)(l_List_insertIdx___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1946_, 0, v_a_1945_);
v___x_1947_ = l_List_modifyTailIdx_go___redArg(v___f_1946_, v_i_1944_, v_xs_1943_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___boxed(lean_object* v_xs_1948_, lean_object* v_i_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_List_insertIdx___redArg(v_xs_1948_, v_i_1949_, v_a_1950_);
lean_dec(v_i_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx(lean_object* v_00_u03b1_1952_, lean_object* v_xs_1953_, lean_object* v_i_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_List_insertIdx___redArg(v_xs_1953_, v_i_1954_, v_a_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___boxed(lean_object* v_00_u03b1_1957_, lean_object* v_xs_1958_, lean_object* v_i_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_List_insertIdx(v_00_u03b1_1957_, v_xs_1958_, v_i_1959_, v_a_1960_);
lean_dec(v_i_1959_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_List_erase___redArg(lean_object* v_inst_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_){
_start:
{
if (lean_obj_tag(v_x_1963_) == 0)
{
lean_dec(v_x_1964_);
lean_dec_ref(v_inst_1962_);
return v_x_1963_;
}
else
{
lean_object* v_head_1965_; lean_object* v_tail_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1976_; 
v_head_1965_ = lean_ctor_get(v_x_1963_, 0);
v_tail_1966_ = lean_ctor_get(v_x_1963_, 1);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1963_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1968_ = v_x_1963_;
v_isShared_1969_ = v_isSharedCheck_1976_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_tail_1966_);
lean_inc(v_head_1965_);
lean_dec(v_x_1963_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1976_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; uint8_t v___x_1971_; 
lean_inc_ref(v_inst_1962_);
lean_inc(v_x_1964_);
lean_inc(v_head_1965_);
v___x_1970_ = lean_apply_2(v_inst_1962_, v_head_1965_, v_x_1964_);
v___x_1971_ = lean_unbox(v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1972_ = l_List_erase___redArg(v_inst_1962_, v_tail_1966_, v_x_1964_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 1, v___x_1972_);
v___x_1974_ = v___x_1968_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_head_1965_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
else
{
lean_del_object(v___x_1968_);
lean_dec(v_head_1965_);
lean_dec(v_x_1964_);
lean_dec_ref(v_inst_1962_);
return v_tail_1966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_erase(lean_object* v_00_u03b1_1977_, lean_object* v_inst_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_List_erase___redArg(v_inst_1978_, v_x_1979_, v_x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v_h__1_1984_, lean_object* v_h__2_1985_){
_start:
{
if (lean_obj_tag(v_x_1982_) == 0)
{
lean_object* v___x_1986_; 
lean_dec(v_h__2_1985_);
v___x_1986_ = lean_apply_1(v_h__1_1984_, v_x_1983_);
return v___x_1986_;
}
else
{
lean_object* v_head_1987_; lean_object* v_tail_1988_; lean_object* v___x_1989_; 
lean_dec(v_h__1_1984_);
v_head_1987_ = lean_ctor_get(v_x_1982_, 0);
lean_inc(v_head_1987_);
v_tail_1988_ = lean_ctor_get(v_x_1982_, 1);
lean_inc(v_tail_1988_);
lean_dec_ref(v_x_1982_);
v___x_1989_ = lean_apply_3(v_h__2_1985_, v_head_1987_, v_tail_1988_, v_x_1983_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object* v_00_u03b1_1990_, lean_object* v_motive_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_h__1_1994_, lean_object* v_h__2_1995_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(v_x_1992_, v_x_1993_, v_h__1_1994_, v_h__2_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_List_eraseP___redArg(lean_object* v_p_1997_, lean_object* v_x_1998_){
_start:
{
if (lean_obj_tag(v_x_1998_) == 0)
{
lean_dec_ref(v_p_1997_);
return v_x_1998_;
}
else
{
lean_object* v_head_1999_; lean_object* v_tail_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2010_; 
v_head_1999_ = lean_ctor_get(v_x_1998_, 0);
v_tail_2000_ = lean_ctor_get(v_x_1998_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_x_1998_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2002_ = v_x_1998_;
v_isShared_2003_ = v_isSharedCheck_2010_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_tail_2000_);
lean_inc(v_head_1999_);
lean_dec(v_x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2010_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
lean_inc_ref(v_p_1997_);
lean_inc(v_head_1999_);
v___x_2004_ = lean_apply_1(v_p_1997_, v_head_1999_);
v___x_2005_ = lean_unbox(v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2006_ = l_List_eraseP___redArg(v_p_1997_, v_tail_2000_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v___x_2006_);
v___x_2008_ = v___x_2002_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_head_1999_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
else
{
lean_del_object(v___x_2002_);
lean_dec(v_head_1999_);
lean_dec_ref(v_p_1997_);
return v_tail_2000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP(lean_object* v_00_u03b1_2011_, lean_object* v_p_2012_, lean_object* v_x_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_List_eraseP___redArg(v_p_2012_, v_x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg(lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
if (lean_obj_tag(v_x_2015_) == 0)
{
return v_x_2015_;
}
else
{
lean_object* v_head_2017_; lean_object* v_tail_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2030_; 
v_head_2017_ = lean_ctor_get(v_x_2015_, 0);
v_tail_2018_ = lean_ctor_get(v_x_2015_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_x_2015_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2020_ = v_x_2015_;
v_isShared_2021_ = v_isSharedCheck_2030_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_tail_2018_);
lean_inc(v_head_2017_);
lean_dec(v_x_2015_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2030_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v_zero_2022_; uint8_t v_isZero_2023_; 
v_zero_2022_ = lean_unsigned_to_nat(0u);
v_isZero_2023_ = lean_nat_dec_eq(v_x_2016_, v_zero_2022_);
if (v_isZero_2023_ == 1)
{
lean_del_object(v___x_2020_);
lean_dec(v_head_2017_);
return v_tail_2018_;
}
else
{
lean_object* v_one_2024_; lean_object* v_n_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v_one_2024_ = lean_unsigned_to_nat(1u);
v_n_2025_ = lean_nat_sub(v_x_2016_, v_one_2024_);
v___x_2026_ = l_List_eraseIdx___redArg(v_tail_2018_, v_n_2025_);
lean_dec(v_n_2025_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 1, v___x_2026_);
v___x_2028_ = v___x_2020_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_head_2017_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg___boxed(lean_object* v_x_2031_, lean_object* v_x_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_List_eraseIdx___redArg(v_x_2031_, v_x_2032_);
lean_dec(v_x_2032_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object* v_00_u03b1_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_List_eraseIdx___redArg(v_x_2035_, v_x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___boxed(lean_object* v_00_u03b1_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_List_eraseIdx(v_00_u03b1_2038_, v_x_2039_, v_x_2040_);
lean_dec(v_x_2040_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object* v_p_2042_, lean_object* v_x_2043_){
_start:
{
if (lean_obj_tag(v_x_2043_) == 0)
{
lean_object* v___x_2044_; 
lean_dec_ref(v_p_2042_);
v___x_2044_ = lean_box(0);
return v___x_2044_;
}
else
{
lean_object* v_head_2045_; lean_object* v_tail_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_head_2045_ = lean_ctor_get(v_x_2043_, 0);
lean_inc(v_head_2045_);
v_tail_2046_ = lean_ctor_get(v_x_2043_, 1);
lean_inc(v_tail_2046_);
lean_dec_ref(v_x_2043_);
lean_inc_ref(v_p_2042_);
lean_inc(v_head_2045_);
v___x_2047_ = lean_apply_1(v_p_2042_, v_head_2045_);
v___x_2048_ = lean_unbox(v___x_2047_);
if (v___x_2048_ == 0)
{
lean_dec(v_head_2045_);
v_x_2043_ = v_tail_2046_;
goto _start;
}
else
{
lean_object* v___x_2050_; 
lean_dec(v_tail_2046_);
lean_dec_ref(v_p_2042_);
v___x_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_head_2045_);
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object* v_00_u03b1_2051_, lean_object* v_p_2052_, lean_object* v_x_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_List_find_x3f___redArg(v_p_2052_, v_x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object* v_f_2055_, lean_object* v_x_2056_){
_start:
{
if (lean_obj_tag(v_x_2056_) == 0)
{
lean_object* v___x_2057_; 
lean_dec_ref(v_f_2055_);
v___x_2057_ = lean_box(0);
return v___x_2057_;
}
else
{
lean_object* v_head_2058_; lean_object* v_tail_2059_; lean_object* v___x_2060_; 
v_head_2058_ = lean_ctor_get(v_x_2056_, 0);
lean_inc(v_head_2058_);
v_tail_2059_ = lean_ctor_get(v_x_2056_, 1);
lean_inc(v_tail_2059_);
lean_dec_ref(v_x_2056_);
lean_inc_ref(v_f_2055_);
v___x_2060_ = lean_apply_1(v_f_2055_, v_head_2058_);
if (lean_obj_tag(v___x_2060_) == 0)
{
v_x_2056_ = v_tail_2059_;
goto _start;
}
else
{
lean_dec(v_tail_2059_);
lean_dec_ref(v_f_2055_);
return v___x_2060_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object* v_00_u03b1_2062_, lean_object* v_00_u03b2_2063_, lean_object* v_f_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_List_findSome_x3f___redArg(v_f_2064_, v_x_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f___redArg(lean_object* v_p_2067_, lean_object* v_x_2068_){
_start:
{
if (lean_obj_tag(v_x_2068_) == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref(v_p_2067_);
v___x_2069_ = lean_box(0);
return v___x_2069_;
}
else
{
lean_object* v_head_2070_; lean_object* v_tail_2071_; lean_object* v___x_2072_; 
v_head_2070_ = lean_ctor_get(v_x_2068_, 0);
lean_inc(v_head_2070_);
v_tail_2071_ = lean_ctor_get(v_x_2068_, 1);
lean_inc(v_tail_2071_);
lean_dec_ref(v_x_2068_);
lean_inc_ref(v_p_2067_);
v___x_2072_ = l_List_findRev_x3f___redArg(v_p_2067_, v_tail_2071_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
lean_inc(v_head_2070_);
v___x_2073_ = lean_apply_1(v_p_2067_, v_head_2070_);
v___x_2074_ = lean_unbox(v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec(v_head_2070_);
return v___x_2072_;
}
else
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_head_2070_);
return v___x_2075_;
}
}
else
{
lean_dec(v_head_2070_);
lean_dec_ref(v_p_2067_);
return v___x_2072_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f(lean_object* v_00_u03b1_2076_, lean_object* v_p_2077_, lean_object* v_x_2078_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_List_findRev_x3f___redArg(v_p_2077_, v_x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f___redArg(lean_object* v_f_2080_, lean_object* v_x_2081_){
_start:
{
if (lean_obj_tag(v_x_2081_) == 0)
{
lean_object* v___x_2082_; 
lean_dec_ref(v_f_2080_);
v___x_2082_ = lean_box(0);
return v___x_2082_;
}
else
{
lean_object* v_head_2083_; lean_object* v_tail_2084_; lean_object* v___x_2085_; 
v_head_2083_ = lean_ctor_get(v_x_2081_, 0);
lean_inc(v_head_2083_);
v_tail_2084_ = lean_ctor_get(v_x_2081_, 1);
lean_inc(v_tail_2084_);
lean_dec_ref(v_x_2081_);
lean_inc_ref(v_f_2080_);
v___x_2085_ = l_List_findSomeRev_x3f___redArg(v_f_2080_, v_tail_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_apply_1(v_f_2080_, v_head_2083_);
return v___x_2086_;
}
else
{
lean_dec(v_head_2083_);
lean_dec_ref(v_f_2080_);
return v___x_2085_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f(lean_object* v_00_u03b1_2087_, lean_object* v_00_u03b2_2088_, lean_object* v_f_2089_, lean_object* v_x_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_List_findSomeRev_x3f___redArg(v_f_2089_, v_x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___redArg(lean_object* v_p_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
if (lean_obj_tag(v_a_2093_) == 0)
{
lean_dec_ref(v_p_2092_);
return v_a_2094_;
}
else
{
lean_object* v_head_2095_; lean_object* v_tail_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_head_2095_ = lean_ctor_get(v_a_2093_, 0);
lean_inc(v_head_2095_);
v_tail_2096_ = lean_ctor_get(v_a_2093_, 1);
lean_inc(v_tail_2096_);
lean_dec_ref(v_a_2093_);
lean_inc_ref(v_p_2092_);
v___x_2097_ = lean_apply_1(v_p_2092_, v_head_2095_);
v___x_2098_ = lean_unbox(v___x_2097_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_nat_add(v_a_2094_, v___x_2099_);
lean_dec(v_a_2094_);
v_a_2093_ = v_tail_2096_;
v_a_2094_ = v___x_2100_;
goto _start;
}
else
{
lean_dec(v_tail_2096_);
lean_dec_ref(v_p_2092_);
return v_a_2094_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object* v_00_u03b1_2102_, lean_object* v_p_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_List_findIdx_go___redArg(v_p_2103_, v_a_2104_, v_a_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx___redArg(lean_object* v_p_2107_, lean_object* v_l_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = l_List_findIdx_go___redArg(v_p_2107_, v_l_2108_, v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx(lean_object* v_00_u03b1_2111_, lean_object* v_p_2112_, lean_object* v_l_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = l_List_findIdx_go___redArg(v_p_2112_, v_l_2113_, v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT uint8_t l_List_idxOf___redArg___lam__0(lean_object* v_inst_2116_, lean_object* v_a_2117_, lean_object* v_x_2118_){
_start:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = lean_apply_2(v_inst_2116_, v_x_2118_, v_a_2117_);
v___x_2120_ = lean_unbox(v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg___lam__0___boxed(lean_object* v_inst_2121_, lean_object* v_a_2122_, lean_object* v_x_2123_){
_start:
{
uint8_t v_res_2124_; lean_object* v_r_2125_; 
v_res_2124_ = l_List_idxOf___redArg___lam__0(v_inst_2121_, v_a_2122_, v_x_2123_);
v_r_2125_ = lean_box(v_res_2124_);
return v_r_2125_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg(lean_object* v_inst_2126_, lean_object* v_a_2127_, lean_object* v_l_2128_){
_start:
{
lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___f_2129_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2129_, 0, v_inst_2126_);
lean_closure_set(v___f_2129_, 1, v_a_2127_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = l_List_findIdx_go___redArg(v___f_2129_, v_l_2128_, v___x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf(lean_object* v_00_u03b1_2132_, lean_object* v_inst_2133_, lean_object* v_a_2134_, lean_object* v_l_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_List_idxOf___redArg(v_inst_2133_, v_a_2134_, v_l_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___redArg(lean_object* v_p_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
if (lean_obj_tag(v_a_2138_) == 0)
{
lean_object* v___x_2140_; 
lean_dec(v_a_2139_);
lean_dec_ref(v_p_2137_);
v___x_2140_ = lean_box(0);
return v___x_2140_;
}
else
{
lean_object* v_head_2141_; lean_object* v_tail_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_head_2141_ = lean_ctor_get(v_a_2138_, 0);
lean_inc(v_head_2141_);
v_tail_2142_ = lean_ctor_get(v_a_2138_, 1);
lean_inc(v_tail_2142_);
lean_dec_ref(v_a_2138_);
lean_inc_ref(v_p_2137_);
v___x_2143_ = lean_apply_1(v_p_2137_, v_head_2141_);
v___x_2144_ = lean_unbox(v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_add(v_a_2139_, v___x_2145_);
lean_dec(v_a_2139_);
v_a_2138_ = v_tail_2142_;
v_a_2139_ = v___x_2146_;
goto _start;
}
else
{
lean_object* v___x_2148_; 
lean_dec(v_tail_2142_);
lean_dec_ref(v_p_2137_);
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_a_2139_);
return v___x_2148_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go(lean_object* v_00_u03b1_2149_, lean_object* v_p_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_List_findIdx_x3f_go___redArg(v_p_2150_, v_a_2151_, v_a_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f___redArg(lean_object* v_p_2154_, lean_object* v_l_2155_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = l_List_findIdx_x3f_go___redArg(v_p_2154_, v_l_2155_, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object* v_00_u03b1_2158_, lean_object* v_p_2159_, lean_object* v_l_2160_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_List_findIdx_x3f___redArg(v_p_2159_, v_l_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f___redArg(lean_object* v_inst_2162_, lean_object* v_a_2163_, lean_object* v_l_2164_){
_start:
{
lean_object* v___f_2165_; lean_object* v___x_2166_; 
v___f_2165_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2165_, 0, v_inst_2162_);
lean_closure_set(v___f_2165_, 1, v_a_2163_);
v___x_2166_ = l_List_findIdx_x3f___redArg(v___f_2165_, v_l_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f(lean_object* v_00_u03b1_2167_, lean_object* v_inst_2168_, lean_object* v_a_2169_, lean_object* v_l_2170_){
_start:
{
lean_object* v___f_2171_; lean_object* v___x_2172_; 
v___f_2171_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2171_, 0, v_inst_2168_);
lean_closure_set(v___f_2171_, 1, v_a_2169_);
v___x_2172_ = l_List_findIdx_x3f___redArg(v___f_2171_, v_l_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___redArg(lean_object* v_p_2173_, lean_object* v_l_x27_2174_, lean_object* v_i_2175_){
_start:
{
if (lean_obj_tag(v_l_x27_2174_) == 0)
{
lean_object* v___x_2176_; 
lean_dec(v_i_2175_);
lean_dec_ref(v_p_2173_);
v___x_2176_ = lean_box(0);
return v___x_2176_;
}
else
{
lean_object* v_head_2177_; lean_object* v_tail_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v_head_2177_ = lean_ctor_get(v_l_x27_2174_, 0);
lean_inc(v_head_2177_);
v_tail_2178_ = lean_ctor_get(v_l_x27_2174_, 1);
lean_inc(v_tail_2178_);
lean_dec_ref(v_l_x27_2174_);
lean_inc_ref(v_p_2173_);
v___x_2179_ = lean_apply_1(v_p_2173_, v_head_2177_);
v___x_2180_ = lean_unbox(v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_unsigned_to_nat(1u);
v___x_2182_ = lean_nat_add(v_i_2175_, v___x_2181_);
lean_dec(v_i_2175_);
v_l_x27_2174_ = v_tail_2178_;
v_i_2175_ = v___x_2182_;
goto _start;
}
else
{
lean_object* v___x_2184_; 
lean_dec(v_tail_2178_);
lean_dec_ref(v_p_2173_);
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_i_2175_);
return v___x_2184_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go(lean_object* v_00_u03b1_2185_, lean_object* v_p_2186_, lean_object* v_l_2187_, lean_object* v_l_x27_2188_, lean_object* v_i_2189_, lean_object* v_h_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_List_findFinIdx_x3f_go___redArg(v_p_2186_, v_l_x27_2188_, v_i_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___boxed(lean_object* v_00_u03b1_2192_, lean_object* v_p_2193_, lean_object* v_l_2194_, lean_object* v_l_x27_2195_, lean_object* v_i_2196_, lean_object* v_h_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_List_findFinIdx_x3f_go(v_00_u03b1_2192_, v_p_2193_, v_l_2194_, v_l_x27_2195_, v_i_2196_, v_h_2197_);
lean_dec(v_l_2194_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f___redArg(lean_object* v_p_2199_, lean_object* v_l_2200_){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = l_List_findFinIdx_x3f_go___redArg(v_p_2199_, v_l_2200_, v___x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f(lean_object* v_00_u03b1_2203_, lean_object* v_p_2204_, lean_object* v_l_2205_){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = l_List_findFinIdx_x3f_go___redArg(v_p_2204_, v_l_2205_, v___x_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f___redArg(lean_object* v_inst_2208_, lean_object* v_a_2209_, lean_object* v_l_2210_){
_start:
{
lean_object* v___f_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___f_2211_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2211_, 0, v_inst_2208_);
lean_closure_set(v___f_2211_, 1, v_a_2209_);
v___x_2212_ = lean_unsigned_to_nat(0u);
v___x_2213_ = l_List_findFinIdx_x3f_go___redArg(v___f_2211_, v_l_2210_, v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f(lean_object* v_00_u03b1_2214_, lean_object* v_inst_2215_, lean_object* v_a_2216_, lean_object* v_l_2217_){
_start:
{
lean_object* v___f_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___f_2218_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2218_, 0, v_inst_2215_);
lean_closure_set(v___f_2218_, 1, v_a_2216_);
v___x_2219_ = lean_unsigned_to_nat(0u);
v___x_2220_ = l_List_findFinIdx_x3f_go___redArg(v___f_2218_, v_l_2217_, v___x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___redArg(lean_object* v_p_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
if (lean_obj_tag(v_a_2222_) == 0)
{
lean_dec_ref(v_p_2221_);
return v_a_2223_;
}
else
{
lean_object* v_head_2224_; lean_object* v_tail_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v_head_2224_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_head_2224_);
v_tail_2225_ = lean_ctor_get(v_a_2222_, 1);
lean_inc(v_tail_2225_);
lean_dec_ref(v_a_2222_);
lean_inc_ref(v_p_2221_);
v___x_2226_ = lean_apply_1(v_p_2221_, v_head_2224_);
v___x_2227_ = lean_unbox(v___x_2226_);
if (v___x_2227_ == 0)
{
v_a_2222_ = v_tail_2225_;
goto _start;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_nat_add(v_a_2223_, v___x_2229_);
lean_dec(v_a_2223_);
v_a_2222_ = v_tail_2225_;
v_a_2223_ = v___x_2230_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go(lean_object* v_00_u03b1_2232_, lean_object* v_p_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_List_countP_go___redArg(v_p_2233_, v_a_2234_, v_a_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_List_countP___redArg(lean_object* v_p_2237_, lean_object* v_l_2238_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = l_List_countP_go___redArg(v_p_2237_, v_l_2238_, v___x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_List_countP(lean_object* v_00_u03b1_2241_, lean_object* v_p_2242_, lean_object* v_l_2243_){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = l_List_countP_go___redArg(v_p_2242_, v_l_2243_, v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_List_count___redArg(lean_object* v_inst_2246_, lean_object* v_a_2247_, lean_object* v_l_2248_){
_start:
{
lean_object* v___f_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___f_2249_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2249_, 0, v_inst_2246_);
lean_closure_set(v___f_2249_, 1, v_a_2247_);
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = l_List_countP_go___redArg(v___f_2249_, v_l_2248_, v___x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_List_count(lean_object* v_00_u03b1_2252_, lean_object* v_inst_2253_, lean_object* v_a_2254_, lean_object* v_l_2255_){
_start:
{
lean_object* v___f_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___f_2256_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2256_, 0, v_inst_2253_);
lean_closure_set(v___f_2256_, 1, v_a_2254_);
v___x_2257_ = lean_unsigned_to_nat(0u);
v___x_2258_ = l_List_countP_go___redArg(v___f_2256_, v_l_2255_, v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___redArg(lean_object* v_inst_2259_, lean_object* v_x_2260_, lean_object* v_x_2261_){
_start:
{
if (lean_obj_tag(v_x_2261_) == 0)
{
lean_object* v___x_2262_; 
lean_dec(v_x_2260_);
lean_dec_ref(v_inst_2259_);
v___x_2262_ = lean_box(0);
return v___x_2262_;
}
else
{
lean_object* v_head_2263_; lean_object* v_tail_2264_; lean_object* v_fst_2265_; lean_object* v_snd_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_head_2263_ = lean_ctor_get(v_x_2261_, 0);
lean_inc(v_head_2263_);
v_tail_2264_ = lean_ctor_get(v_x_2261_, 1);
lean_inc(v_tail_2264_);
lean_dec_ref(v_x_2261_);
v_fst_2265_ = lean_ctor_get(v_head_2263_, 0);
lean_inc(v_fst_2265_);
v_snd_2266_ = lean_ctor_get(v_head_2263_, 1);
lean_inc(v_snd_2266_);
lean_dec(v_head_2263_);
lean_inc_ref(v_inst_2259_);
lean_inc(v_x_2260_);
v___x_2267_ = lean_apply_2(v_inst_2259_, v_x_2260_, v_fst_2265_);
v___x_2268_ = lean_unbox(v___x_2267_);
if (v___x_2268_ == 0)
{
lean_dec(v_snd_2266_);
v_x_2261_ = v_tail_2264_;
goto _start;
}
else
{
lean_object* v___x_2270_; 
lean_dec(v_tail_2264_);
lean_dec(v_x_2260_);
lean_dec_ref(v_inst_2259_);
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v_snd_2266_);
return v___x_2270_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup(lean_object* v_00_u03b1_2271_, lean_object* v_00_u03b2_2272_, lean_object* v_inst_2273_, lean_object* v_x_2274_, lean_object* v_x_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_List_lookup___redArg(v_inst_2273_, v_x_2274_, v_x_2275_);
return v___x_2276_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0));
v___x_2295_ = l_String_toRawSubstring_x27(v___x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object* v_x_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
lean_inc(v_x_2315_);
v___x_2319_ = l_Lean_Syntax_isOfKind(v_x_2315_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec_ref(v_a_2316_);
lean_dec(v_x_2315_);
v___x_2320_ = lean_box(1);
v___x_2321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
lean_ctor_set(v___x_2321_, 1, v_a_2317_);
return v___x_2321_;
}
else
{
lean_object* v_quotContext_2322_; lean_object* v_currMacroScope_2323_; lean_object* v_ref_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v_quotContext_2322_ = lean_ctor_get(v_a_2316_, 1);
lean_inc(v_quotContext_2322_);
v_currMacroScope_2323_ = lean_ctor_get(v_a_2316_, 2);
lean_inc(v_currMacroScope_2323_);
v_ref_2324_ = lean_ctor_get(v_a_2316_, 5);
lean_inc(v_ref_2324_);
lean_dec_ref(v_a_2316_);
v___x_2325_ = lean_unsigned_to_nat(0u);
v___x_2326_ = l_Lean_Syntax_getArg(v_x_2315_, v___x_2325_);
v___x_2327_ = lean_unsigned_to_nat(2u);
v___x_2328_ = l_Lean_Syntax_getArg(v_x_2315_, v___x_2327_);
lean_dec(v_x_2315_);
v___x_2329_ = 0;
v___x_2330_ = l_Lean_SourceInfo_fromRef(v_ref_2324_, v___x_2329_);
lean_dec(v_ref_2324_);
v___x_2331_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_2332_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
v___x_2333_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2));
v___x_2334_ = l_Lean_addMacroScope(v_quotContext_2322_, v___x_2333_, v_currMacroScope_2323_);
v___x_2335_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8));
lean_inc(v___x_2330_);
v___x_2336_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2330_);
lean_ctor_set(v___x_2336_, 1, v___x_2332_);
lean_ctor_set(v___x_2336_, 2, v___x_2334_);
lean_ctor_set(v___x_2336_, 3, v___x_2335_);
v___x_2337_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
lean_inc(v___x_2330_);
v___x_2338_ = l_Lean_Syntax_node2(v___x_2330_, v___x_2337_, v___x_2326_, v___x_2328_);
v___x_2339_ = l_Lean_Syntax_node2(v___x_2330_, v___x_2331_, v___x_2336_, v___x_2338_);
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v_a_2317_);
return v___x_2340_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object* v_x_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_2341_);
v___x_2345_ = l_Lean_Syntax_isOfKind(v_x_2341_, v___x_2344_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_dec(v_x_2341_);
v___x_2346_ = lean_box(0);
v___x_2347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
lean_ctor_set(v___x_2347_, 1, v_a_2343_);
return v___x_2347_;
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = l_Lean_Syntax_getArg(v_x_2341_, v___x_2348_);
v___x_2350_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_2349_);
v___x_2351_ = l_Lean_Syntax_isOfKind(v___x_2349_, v___x_2350_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v___x_2349_);
lean_dec(v_x_2341_);
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v_a_2343_);
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = l_Lean_Syntax_getArg(v_x_2341_, v___x_2354_);
lean_dec(v_x_2341_);
v___x_2356_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2355_);
v___x_2357_ = l_Lean_Syntax_matchesNull(v___x_2355_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec(v___x_2355_);
lean_dec(v___x_2349_);
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v_a_2343_);
return v___x_2359_;
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v_ref_2362_; uint8_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2360_ = l_Lean_Syntax_getArg(v___x_2355_, v___x_2348_);
v___x_2361_ = l_Lean_Syntax_getArg(v___x_2355_, v___x_2354_);
lean_dec(v___x_2355_);
v_ref_2362_ = l_Lean_replaceRef(v___x_2349_, v_a_2342_);
lean_dec(v___x_2349_);
v___x_2363_ = 0;
v___x_2364_ = l_Lean_SourceInfo_fromRef(v_ref_2362_, v___x_2363_);
lean_dec(v_ref_2362_);
v___x_2365_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
v___x_2366_ = ((lean_object*)(l_List_term___x7e___00__closed__2));
lean_inc(v___x_2364_);
v___x_2367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2364_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node3(v___x_2364_, v___x_2365_, v___x_2360_, v___x_2367_, v___x_2361_);
v___x_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
lean_ctor_set(v___x_2369_, 1, v_a_2343_);
return v___x_2369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object* v_x_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(v_x_2370_, v_a_2371_, v_a_2372_);
lean_dec(v_a_2371_);
return v_res_2373_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm___redArg(lean_object* v_inst_2374_, lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
if (lean_obj_tag(v_x_2375_) == 0)
{
uint8_t v___x_2377_; 
lean_dec_ref(v_inst_2374_);
v___x_2377_ = l_List_isEmpty___redArg(v_x_2376_);
lean_dec(v_x_2376_);
return v___x_2377_;
}
else
{
lean_object* v_head_2378_; lean_object* v_tail_2379_; uint8_t v___x_2380_; 
v_head_2378_ = lean_ctor_get(v_x_2375_, 0);
lean_inc(v_head_2378_);
v_tail_2379_ = lean_ctor_get(v_x_2375_, 1);
lean_inc(v_tail_2379_);
lean_dec_ref(v_x_2375_);
lean_inc(v_x_2376_);
lean_inc(v_head_2378_);
lean_inc_ref(v_inst_2374_);
v___x_2380_ = l_List_elem___redArg(v_inst_2374_, v_head_2378_, v_x_2376_);
if (v___x_2380_ == 0)
{
lean_dec(v_tail_2379_);
lean_dec(v_head_2378_);
lean_dec(v_x_2376_);
lean_dec_ref(v_inst_2374_);
return v___x_2380_;
}
else
{
lean_object* v___x_2381_; 
lean_inc_ref(v_inst_2374_);
v___x_2381_ = l_List_erase___redArg(v_inst_2374_, v_x_2376_, v_head_2378_);
v_x_2375_ = v_tail_2379_;
v_x_2376_ = v___x_2381_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPerm___redArg___boxed(lean_object* v_inst_2383_, lean_object* v_x_2384_, lean_object* v_x_2385_){
_start:
{
uint8_t v_res_2386_; lean_object* v_r_2387_; 
v_res_2386_ = l_List_isPerm___redArg(v_inst_2383_, v_x_2384_, v_x_2385_);
v_r_2387_ = lean_box(v_res_2386_);
return v_r_2387_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm(lean_object* v_00_u03b1_2388_, lean_object* v_inst_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
uint8_t v___x_2392_; 
v___x_2392_ = l_List_isPerm___redArg(v_inst_2389_, v_x_2390_, v_x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_List_isPerm___boxed(lean_object* v_00_u03b1_2393_, lean_object* v_inst_2394_, lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
uint8_t v_res_2397_; lean_object* v_r_2398_; 
v_res_2397_ = l_List_isPerm(v_00_u03b1_2393_, v_inst_2394_, v_x_2395_, v_x_2396_);
v_r_2398_ = lean_box(v_res_2397_);
return v_r_2398_;
}
}
LEAN_EXPORT uint8_t l_List_any___redArg(lean_object* v_x_2399_, lean_object* v_x_2400_){
_start:
{
if (lean_obj_tag(v_x_2399_) == 0)
{
uint8_t v___x_2401_; 
lean_dec_ref(v_x_2400_);
v___x_2401_ = 0;
return v___x_2401_;
}
else
{
lean_object* v_head_2402_; lean_object* v_tail_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v_head_2402_ = lean_ctor_get(v_x_2399_, 0);
lean_inc(v_head_2402_);
v_tail_2403_ = lean_ctor_get(v_x_2399_, 1);
lean_inc(v_tail_2403_);
lean_dec_ref(v_x_2399_);
lean_inc_ref(v_x_2400_);
v___x_2404_ = lean_apply_1(v_x_2400_, v_head_2402_);
v___x_2405_ = lean_unbox(v___x_2404_);
if (v___x_2405_ == 0)
{
v_x_2399_ = v_tail_2403_;
goto _start;
}
else
{
uint8_t v___x_2407_; 
lean_dec(v_tail_2403_);
lean_dec_ref(v_x_2400_);
v___x_2407_ = lean_unbox(v___x_2404_);
return v___x_2407_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___redArg___boxed(lean_object* v_x_2408_, lean_object* v_x_2409_){
_start:
{
uint8_t v_res_2410_; lean_object* v_r_2411_; 
v_res_2410_ = l_List_any___redArg(v_x_2408_, v_x_2409_);
v_r_2411_ = lean_box(v_res_2410_);
return v_r_2411_;
}
}
LEAN_EXPORT uint8_t l_List_any(lean_object* v_00_u03b1_2412_, lean_object* v_x_2413_, lean_object* v_x_2414_){
_start:
{
uint8_t v___x_2415_; 
v___x_2415_ = l_List_any___redArg(v_x_2413_, v_x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_List_any___boxed(lean_object* v_00_u03b1_2416_, lean_object* v_x_2417_, lean_object* v_x_2418_){
_start:
{
uint8_t v_res_2419_; lean_object* v_r_2420_; 
v_res_2419_ = l_List_any(v_00_u03b1_2416_, v_x_2417_, v_x_2418_);
v_r_2420_ = lean_box(v_res_2419_);
return v_r_2420_;
}
}
LEAN_EXPORT uint8_t l_List_all___redArg(lean_object* v_x_2421_, lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2421_) == 0)
{
uint8_t v___x_2423_; 
lean_dec_ref(v_x_2422_);
v___x_2423_ = 1;
return v___x_2423_;
}
else
{
lean_object* v_head_2424_; lean_object* v_tail_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v_head_2424_ = lean_ctor_get(v_x_2421_, 0);
lean_inc(v_head_2424_);
v_tail_2425_ = lean_ctor_get(v_x_2421_, 1);
lean_inc(v_tail_2425_);
lean_dec_ref(v_x_2421_);
lean_inc_ref(v_x_2422_);
v___x_2426_ = lean_apply_1(v_x_2422_, v_head_2424_);
v___x_2427_ = lean_unbox(v___x_2426_);
if (v___x_2427_ == 0)
{
uint8_t v___x_2428_; 
lean_dec(v_tail_2425_);
lean_dec_ref(v_x_2422_);
v___x_2428_ = lean_unbox(v___x_2426_);
return v___x_2428_;
}
else
{
v_x_2421_ = v_tail_2425_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___redArg___boxed(lean_object* v_x_2430_, lean_object* v_x_2431_){
_start:
{
uint8_t v_res_2432_; lean_object* v_r_2433_; 
v_res_2432_ = l_List_all___redArg(v_x_2430_, v_x_2431_);
v_r_2433_ = lean_box(v_res_2432_);
return v_r_2433_;
}
}
LEAN_EXPORT uint8_t l_List_all(lean_object* v_00_u03b1_2434_, lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
uint8_t v___x_2437_; 
v___x_2437_ = l_List_all___redArg(v_x_2435_, v_x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_List_all___boxed(lean_object* v_00_u03b1_2438_, lean_object* v_x_2439_, lean_object* v_x_2440_){
_start:
{
uint8_t v_res_2441_; lean_object* v_r_2442_; 
v_res_2441_ = l_List_all(v_00_u03b1_2438_, v_x_2439_, v_x_2440_);
v_r_2442_ = lean_box(v_res_2441_);
return v_r_2442_;
}
}
LEAN_EXPORT uint8_t l_List_or___lam__0(uint8_t v___y_2443_){
_start:
{
return v___y_2443_;
}
}
LEAN_EXPORT lean_object* l_List_or___lam__0___boxed(lean_object* v___y_2444_){
_start:
{
uint8_t v___y_7__boxed_2445_; uint8_t v_res_2446_; lean_object* v_r_2447_; 
v___y_7__boxed_2445_ = lean_unbox(v___y_2444_);
v_res_2446_ = l_List_or___lam__0(v___y_7__boxed_2445_);
v_r_2447_ = lean_box(v_res_2446_);
return v_r_2447_;
}
}
LEAN_EXPORT uint8_t l_List_or(lean_object* v_bs_2449_){
_start:
{
lean_object* v___f_2450_; uint8_t v___x_2451_; 
v___f_2450_ = ((lean_object*)(l_List_or___closed__0));
v___x_2451_ = l_List_any___redArg(v_bs_2449_, v___f_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object* v_bs_2452_){
_start:
{
uint8_t v_res_2453_; lean_object* v_r_2454_; 
v_res_2453_ = l_List_or(v_bs_2452_);
v_r_2454_ = lean_box(v_res_2453_);
return v_r_2454_;
}
}
LEAN_EXPORT uint8_t l_List_and(lean_object* v_bs_2455_){
_start:
{
lean_object* v___f_2456_; uint8_t v___x_2457_; 
v___f_2456_ = ((lean_object*)(l_List_or___closed__0));
v___x_2457_ = l_List_all___redArg(v_bs_2455_, v___f_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object* v_bs_2458_){
_start:
{
uint8_t v_res_2459_; lean_object* v_r_2460_; 
v_res_2459_ = l_List_and(v_bs_2458_);
v_r_2460_ = lean_box(v_res_2459_);
return v_r_2460_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___redArg(lean_object* v_f_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_){
_start:
{
if (lean_obj_tag(v_x_2462_) == 0)
{
lean_object* v___x_2464_; 
lean_dec(v_x_2463_);
lean_dec(v_f_2461_);
v___x_2464_ = lean_box(0);
return v___x_2464_;
}
else
{
if (lean_obj_tag(v_x_2463_) == 0)
{
lean_object* v___x_2465_; 
lean_dec_ref(v_x_2462_);
lean_dec(v_f_2461_);
v___x_2465_ = lean_box(0);
return v___x_2465_;
}
else
{
lean_object* v_head_2466_; lean_object* v_tail_2467_; lean_object* v_head_2468_; lean_object* v_tail_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2478_; 
v_head_2466_ = lean_ctor_get(v_x_2462_, 0);
lean_inc(v_head_2466_);
v_tail_2467_ = lean_ctor_get(v_x_2462_, 1);
lean_inc(v_tail_2467_);
lean_dec_ref(v_x_2462_);
v_head_2468_ = lean_ctor_get(v_x_2463_, 0);
v_tail_2469_ = lean_ctor_get(v_x_2463_, 1);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_x_2463_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2471_ = v_x_2463_;
v_isShared_2472_ = v_isSharedCheck_2478_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_tail_2469_);
lean_inc(v_head_2468_);
lean_dec(v_x_2463_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2478_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
lean_inc(v_f_2461_);
v___x_2473_ = lean_apply_2(v_f_2461_, v_head_2466_, v_head_2468_);
v___x_2474_ = l_List_zipWith___redArg(v_f_2461_, v_tail_2467_, v_tail_2469_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 1, v___x_2474_);
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2476_ = v___x_2471_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith(lean_object* v_00_u03b1_2479_, lean_object* v_00_u03b2_2480_, lean_object* v_00_u03b3_2481_, lean_object* v_f_2482_, lean_object* v_x_2483_, lean_object* v_x_2484_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_List_zipWith___redArg(v_f_2482_, v_x_2483_, v_x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object* v_x_2486_, lean_object* v_x_2487_, lean_object* v_h__1_2488_, lean_object* v_h__2_2489_){
_start:
{
if (lean_obj_tag(v_x_2486_) == 0)
{
lean_object* v___x_2490_; 
lean_dec(v_h__1_2488_);
v___x_2490_ = lean_apply_3(v_h__2_2489_, v_x_2486_, v_x_2487_, lean_box(0));
return v___x_2490_;
}
else
{
if (lean_obj_tag(v_x_2487_) == 0)
{
lean_object* v___x_2491_; 
lean_dec(v_h__1_2488_);
v___x_2491_ = lean_apply_3(v_h__2_2489_, v_x_2486_, v_x_2487_, lean_box(0));
return v___x_2491_;
}
else
{
lean_object* v_head_2492_; lean_object* v_tail_2493_; lean_object* v_head_2494_; lean_object* v_tail_2495_; lean_object* v___x_2496_; 
lean_dec(v_h__2_2489_);
v_head_2492_ = lean_ctor_get(v_x_2486_, 0);
lean_inc(v_head_2492_);
v_tail_2493_ = lean_ctor_get(v_x_2486_, 1);
lean_inc(v_tail_2493_);
lean_dec_ref(v_x_2486_);
v_head_2494_ = lean_ctor_get(v_x_2487_, 0);
lean_inc(v_head_2494_);
v_tail_2495_ = lean_ctor_get(v_x_2487_, 1);
lean_inc(v_tail_2495_);
lean_dec_ref(v_x_2487_);
v___x_2496_ = lean_apply_4(v_h__1_2488_, v_head_2492_, v_tail_2493_, v_head_2494_, v_tail_2495_);
return v___x_2496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object* v_00_u03b1_2497_, lean_object* v_00_u03b2_2498_, lean_object* v_motive_2499_, lean_object* v_x_2500_, lean_object* v_x_2501_, lean_object* v_h__1_2502_, lean_object* v_h__2_2503_){
_start:
{
if (lean_obj_tag(v_x_2500_) == 0)
{
lean_object* v___x_2504_; 
lean_dec(v_h__1_2502_);
v___x_2504_ = lean_apply_3(v_h__2_2503_, v_x_2500_, v_x_2501_, lean_box(0));
return v___x_2504_;
}
else
{
if (lean_obj_tag(v_x_2501_) == 0)
{
lean_object* v___x_2505_; 
lean_dec(v_h__1_2502_);
v___x_2505_ = lean_apply_3(v_h__2_2503_, v_x_2500_, v_x_2501_, lean_box(0));
return v___x_2505_;
}
else
{
lean_object* v_head_2506_; lean_object* v_tail_2507_; lean_object* v_head_2508_; lean_object* v_tail_2509_; lean_object* v___x_2510_; 
lean_dec(v_h__2_2503_);
v_head_2506_ = lean_ctor_get(v_x_2500_, 0);
lean_inc(v_head_2506_);
v_tail_2507_ = lean_ctor_get(v_x_2500_, 1);
lean_inc(v_tail_2507_);
lean_dec_ref(v_x_2500_);
v_head_2508_ = lean_ctor_get(v_x_2501_, 0);
lean_inc(v_head_2508_);
v_tail_2509_ = lean_ctor_get(v_x_2501_, 1);
lean_inc(v_tail_2509_);
lean_dec_ref(v_x_2501_);
v___x_2510_ = lean_apply_4(v_h__1_2502_, v_head_2506_, v_tail_2507_, v_head_2508_, v_tail_2509_);
return v___x_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object* v_x_2511_, lean_object* v_x_2512_){
_start:
{
if (lean_obj_tag(v_x_2511_) == 0)
{
lean_object* v___x_2513_; 
lean_dec(v_x_2512_);
v___x_2513_ = lean_box(0);
return v___x_2513_;
}
else
{
if (lean_obj_tag(v_x_2512_) == 0)
{
lean_object* v___x_2514_; 
lean_dec_ref(v_x_2511_);
v___x_2514_ = lean_box(0);
return v___x_2514_;
}
else
{
lean_object* v_head_2515_; lean_object* v_tail_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2533_; 
v_head_2515_ = lean_ctor_get(v_x_2511_, 0);
v_tail_2516_ = lean_ctor_get(v_x_2511_, 1);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2518_ = v_x_2511_;
v_isShared_2519_ = v_isSharedCheck_2533_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_tail_2516_);
lean_inc(v_head_2515_);
lean_dec(v_x_2511_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2533_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_head_2520_; lean_object* v_tail_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2532_; 
v_head_2520_ = lean_ctor_get(v_x_2512_, 0);
v_tail_2521_ = lean_ctor_get(v_x_2512_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_x_2512_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2523_ = v_x_2512_;
v_isShared_2524_ = v_isSharedCheck_2532_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_tail_2521_);
lean_inc(v_head_2520_);
lean_dec(v_x_2512_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2532_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 0);
lean_ctor_set(v___x_2518_, 1, v_head_2520_);
v___x_2526_ = v___x_2518_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_head_2515_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_head_2520_);
v___x_2526_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_tail_2516_, v_tail_2521_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v___x_2527_);
lean_ctor_set(v___x_2523_, 0, v___x_2526_);
v___x_2529_ = v___x_2523_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zip___redArg(lean_object* v_xs_2534_, lean_object* v_ys_2535_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2534_, v_ys_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_List_zip(lean_object* v_00_u03b1_2537_, lean_object* v_00_u03b2_2538_, lean_object* v_xs_2539_, lean_object* v_ys_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2539_, v_ys_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object* v_00_u03b1_2542_, lean_object* v_00_u03b2_2543_, lean_object* v_x_2544_, lean_object* v_x_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_x_2544_, v_x_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__0___redArg(lean_object* v_f_2547_, lean_object* v_x_2548_){
_start:
{
if (lean_obj_tag(v_x_2548_) == 0)
{
lean_object* v___x_2549_; 
lean_dec(v_f_2547_);
v___x_2549_ = lean_box(0);
return v___x_2549_;
}
else
{
lean_object* v_head_2550_; lean_object* v_tail_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2562_; 
v_head_2550_ = lean_ctor_get(v_x_2548_, 0);
v_tail_2551_ = lean_ctor_get(v_x_2548_, 1);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_x_2548_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2553_ = v_x_2548_;
v_isShared_2554_ = v_isSharedCheck_2562_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_tail_2551_);
lean_inc(v_head_2550_);
lean_dec(v_x_2548_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2562_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2555_ = lean_box(0);
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_head_2550_);
lean_inc(v_f_2547_);
v___x_2557_ = lean_apply_2(v_f_2547_, v___x_2555_, v___x_2556_);
v___x_2558_ = l_List_map___at___00List_zipWithAll_spec__0___redArg(v_f_2547_, v_tail_2551_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 1, v___x_2558_);
lean_ctor_set(v___x_2553_, 0, v___x_2557_);
v___x_2560_ = v___x_2553_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__1___redArg(lean_object* v_f_2563_, lean_object* v_x_2564_){
_start:
{
if (lean_obj_tag(v_x_2564_) == 0)
{
lean_object* v___x_2565_; 
lean_dec(v_f_2563_);
v___x_2565_ = lean_box(0);
return v___x_2565_;
}
else
{
lean_object* v_head_2566_; lean_object* v_tail_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2578_; 
v_head_2566_ = lean_ctor_get(v_x_2564_, 0);
v_tail_2567_ = lean_ctor_get(v_x_2564_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_x_2564_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2569_ = v_x_2564_;
v_isShared_2570_ = v_isSharedCheck_2578_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_tail_2567_);
lean_inc(v_head_2566_);
lean_dec(v_x_2564_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2578_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_head_2566_);
v___x_2572_ = lean_box(0);
lean_inc(v_f_2563_);
v___x_2573_ = lean_apply_2(v_f_2563_, v___x_2571_, v___x_2572_);
v___x_2574_ = l_List_map___at___00List_zipWithAll_spec__1___redArg(v_f_2563_, v_tail_2567_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 1, v___x_2574_);
lean_ctor_set(v___x_2569_, 0, v___x_2573_);
v___x_2576_ = v___x_2569_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object* v_f_2579_, lean_object* v_x_2580_, lean_object* v_x_2581_){
_start:
{
if (lean_obj_tag(v_x_2580_) == 0)
{
lean_object* v___x_2582_; 
v___x_2582_ = l_List_map___at___00List_zipWithAll_spec__0___redArg(v_f_2579_, v_x_2581_);
return v___x_2582_;
}
else
{
if (lean_obj_tag(v_x_2581_) == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = l_List_map___at___00List_zipWithAll_spec__1___redArg(v_f_2579_, v_x_2580_);
return v___x_2583_;
}
else
{
lean_object* v_head_2584_; lean_object* v_tail_2585_; lean_object* v_head_2586_; lean_object* v_tail_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2598_; 
v_head_2584_ = lean_ctor_get(v_x_2580_, 0);
lean_inc(v_head_2584_);
v_tail_2585_ = lean_ctor_get(v_x_2580_, 1);
lean_inc(v_tail_2585_);
lean_dec_ref(v_x_2580_);
v_head_2586_ = lean_ctor_get(v_x_2581_, 0);
v_tail_2587_ = lean_ctor_get(v_x_2581_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_x_2581_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2589_ = v_x_2581_;
v_isShared_2590_ = v_isSharedCheck_2598_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_tail_2587_);
lean_inc(v_head_2586_);
lean_dec(v_x_2581_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2598_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2591_, 0, v_head_2584_);
v___x_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2592_, 0, v_head_2586_);
lean_inc(v_f_2579_);
v___x_2593_ = lean_apply_2(v_f_2579_, v___x_2591_, v___x_2592_);
v___x_2594_ = l_List_zipWithAll___redArg(v_f_2579_, v_tail_2585_, v_tail_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v___x_2594_);
lean_ctor_set(v___x_2589_, 0, v___x_2593_);
v___x_2596_ = v___x_2589_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object* v_00_u03b1_2599_, lean_object* v_00_u03b2_2600_, lean_object* v_00_u03b3_2601_, lean_object* v_f_2602_, lean_object* v_x_2603_, lean_object* v_x_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_List_zipWithAll___redArg(v_f_2602_, v_x_2603_, v_x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__0(lean_object* v_00_u03b2_2606_, lean_object* v_00_u03b3_2607_, lean_object* v_00_u03b1_2608_, lean_object* v_f_2609_, lean_object* v_x_2610_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_List_map___at___00List_zipWithAll_spec__0___redArg(v_f_2609_, v_x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__1(lean_object* v_00_u03b1_2612_, lean_object* v_00_u03b3_2613_, lean_object* v_00_u03b2_2614_, lean_object* v_f_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_List_map___at___00List_zipWithAll_spec__1___redArg(v_f_2615_, v_x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_List_unzip___redArg(lean_object* v_x_2618_){
_start:
{
if (lean_obj_tag(v_x_2618_) == 0)
{
lean_object* v___x_2619_; 
v___x_2619_ = ((lean_object*)(l_List_partition___redArg___closed__0));
return v___x_2619_;
}
else
{
lean_object* v_head_2620_; lean_object* v_tail_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2647_; 
v_head_2620_ = lean_ctor_get(v_x_2618_, 0);
v_tail_2621_ = lean_ctor_get(v_x_2618_, 1);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_x_2618_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2623_ = v_x_2618_;
v_isShared_2624_ = v_isSharedCheck_2647_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_tail_2621_);
lean_inc(v_head_2620_);
lean_dec(v_x_2618_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2647_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v_fst_2625_; lean_object* v_snd_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2646_; 
v_fst_2625_ = lean_ctor_get(v_head_2620_, 0);
v_snd_2626_ = lean_ctor_get(v_head_2620_, 1);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_head_2620_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2628_ = v_head_2620_;
v_isShared_2629_ = v_isSharedCheck_2646_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_snd_2626_);
lean_inc(v_fst_2625_);
lean_dec(v_head_2620_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2646_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; lean_object* v_fst_2631_; lean_object* v_snd_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2645_; 
v___x_2630_ = l_List_unzip___redArg(v_tail_2621_);
v_fst_2631_ = lean_ctor_get(v___x_2630_, 0);
v_snd_2632_ = lean_ctor_get(v___x_2630_, 1);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2634_ = v___x_2630_;
v_isShared_2635_ = v_isSharedCheck_2645_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_snd_2632_);
lean_inc(v_fst_2631_);
lean_dec(v___x_2630_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2645_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 1, v_fst_2631_);
lean_ctor_set(v___x_2623_, 0, v_fst_2625_);
v___x_2637_ = v___x_2623_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_fst_2625_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_fst_2631_);
v___x_2637_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2639_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set_tag(v___x_2628_, 1);
lean_ctor_set(v___x_2628_, 1, v_snd_2632_);
lean_ctor_set(v___x_2628_, 0, v_snd_2626_);
v___x_2639_ = v___x_2628_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_snd_2626_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_snd_2632_);
v___x_2639_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 1, v___x_2639_);
lean_ctor_set(v___x_2634_, 0, v___x_2637_);
v___x_2641_ = v___x_2634_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_unzip(lean_object* v_00_u03b1_2648_, lean_object* v_00_u03b2_2649_, lean_object* v_x_2650_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_List_unzip___redArg(v_x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___lam__0(lean_object* v_inst_2652_, lean_object* v_x1_2653_, lean_object* v_x2_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_apply_2(v_inst_2652_, v_x1_2653_, v_x2_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg(lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_l_2658_){
_start:
{
lean_object* v___f_2659_; lean_object* v___x_2660_; 
v___f_2659_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2659_, 0, v_inst_2656_);
v___x_2660_ = l_List_foldr___redArg(v___f_2659_, v_inst_2657_, v_l_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___boxed(lean_object* v_inst_2661_, lean_object* v_inst_2662_, lean_object* v_l_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_List_sum___redArg(v_inst_2661_, v_inst_2662_, v_l_2663_);
lean_dec(v_inst_2662_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_List_sum(lean_object* v_00_u03b1_2665_, lean_object* v_inst_2666_, lean_object* v_inst_2667_, lean_object* v_l_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_List_sum___redArg(v_inst_2666_, v_inst_2667_, v_l_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_List_sum___boxed(lean_object* v_00_u03b1_2670_, lean_object* v_inst_2671_, lean_object* v_inst_2672_, lean_object* v_l_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_List_sum(v_00_u03b1_2670_, v_inst_2671_, v_inst_2672_, v_l_2673_);
lean_dec(v_inst_2672_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_List_range_loop(lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v_zero_2677_; uint8_t v_isZero_2678_; 
v_zero_2677_ = lean_unsigned_to_nat(0u);
v_isZero_2678_ = lean_nat_dec_eq(v_a_2675_, v_zero_2677_);
if (v_isZero_2678_ == 1)
{
lean_dec(v_a_2675_);
return v_a_2676_;
}
else
{
lean_object* v_one_2679_; lean_object* v_n_2680_; lean_object* v___x_2681_; 
v_one_2679_ = lean_unsigned_to_nat(1u);
v_n_2680_ = lean_nat_sub(v_a_2675_, v_one_2679_);
lean_dec(v_a_2675_);
lean_inc(v_n_2680_);
v___x_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2681_, 0, v_n_2680_);
lean_ctor_set(v___x_2681_, 1, v_a_2676_);
v_a_2675_ = v_n_2680_;
v_a_2676_ = v___x_2681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range(lean_object* v_n_2683_){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_box(0);
v___x_2685_ = l_List_range_loop(v_n_2683_, v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27(lean_object* v_x_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
lean_object* v_zero_2689_; uint8_t v_isZero_2690_; 
v_zero_2689_ = lean_unsigned_to_nat(0u);
v_isZero_2690_ = lean_nat_dec_eq(v_x_2687_, v_zero_2689_);
if (v_isZero_2690_ == 1)
{
lean_object* v___x_2691_; 
lean_dec(v_x_2686_);
v___x_2691_ = lean_box(0);
return v___x_2691_;
}
else
{
lean_object* v_one_2692_; lean_object* v_n_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_one_2692_ = lean_unsigned_to_nat(1u);
v_n_2693_ = lean_nat_sub(v_x_2687_, v_one_2692_);
v___x_2694_ = lean_nat_add(v_x_2686_, v_x_2688_);
v___x_2695_ = l_List_range_x27(v___x_2694_, v_n_2693_, v_x_2688_);
lean_dec(v_n_2693_);
v___x_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2696_, 0, v_x_2686_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
return v___x_2696_;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object* v_x_2697_, lean_object* v_x_2698_, lean_object* v_x_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_List_range_x27(v_x_2697_, v_x_2698_, v_x_2699_);
lean_dec(v_x_2699_);
lean_dec(v_x_2698_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdx___redArg(lean_object* v_x_2701_, lean_object* v_x_2702_){
_start:
{
if (lean_obj_tag(v_x_2701_) == 0)
{
lean_object* v___x_2703_; 
lean_dec(v_x_2702_);
v___x_2703_ = lean_box(0);
return v___x_2703_;
}
else
{
lean_object* v_head_2704_; lean_object* v_tail_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2716_; 
v_head_2704_ = lean_ctor_get(v_x_2701_, 0);
v_tail_2705_ = lean_ctor_get(v_x_2701_, 1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_x_2701_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2707_ = v_x_2701_;
v_isShared_2708_ = v_isSharedCheck_2716_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_tail_2705_);
lean_inc(v_head_2704_);
lean_dec(v_x_2701_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2716_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
lean_inc(v_x_2702_);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v_head_2704_);
lean_ctor_set(v___x_2709_, 1, v_x_2702_);
v___x_2710_ = lean_unsigned_to_nat(1u);
v___x_2711_ = lean_nat_add(v_x_2702_, v___x_2710_);
lean_dec(v_x_2702_);
v___x_2712_ = l_List_zipIdx___redArg(v_tail_2705_, v___x_2711_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 1, v___x_2712_);
lean_ctor_set(v___x_2707_, 0, v___x_2709_);
v___x_2714_ = v___x_2707_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2709_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdx(lean_object* v_00_u03b1_2717_, lean_object* v_x_2718_, lean_object* v_x_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_List_zipIdx___redArg(v_x_2718_, v_x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object* v_inst_2721_, lean_object* v_x_2722_){
_start:
{
if (lean_obj_tag(v_x_2722_) == 0)
{
lean_object* v___x_2723_; 
lean_dec(v_inst_2721_);
v___x_2723_ = lean_box(0);
return v___x_2723_;
}
else
{
lean_object* v_head_2724_; lean_object* v_tail_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v_head_2724_ = lean_ctor_get(v_x_2722_, 0);
lean_inc(v_head_2724_);
v_tail_2725_ = lean_ctor_get(v_x_2722_, 1);
lean_inc(v_tail_2725_);
lean_dec_ref(v_x_2722_);
v___x_2726_ = l_List_foldl___redArg(v_inst_2721_, v_head_2724_, v_tail_2725_);
v___x_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
return v___x_2727_;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object* v_00_u03b1_2728_, lean_object* v_inst_2729_, lean_object* v_x_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_List_min_x3f___redArg(v_inst_2729_, v_x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object* v_inst_2732_, lean_object* v_x_2733_){
_start:
{
lean_object* v_head_2734_; lean_object* v_tail_2735_; lean_object* v___x_2736_; 
v_head_2734_ = lean_ctor_get(v_x_2733_, 0);
lean_inc(v_head_2734_);
v_tail_2735_ = lean_ctor_get(v_x_2733_, 1);
lean_inc(v_tail_2735_);
lean_dec(v_x_2733_);
v___x_2736_ = l_List_foldl___redArg(v_inst_2732_, v_head_2734_, v_tail_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_List_min(lean_object* v_00_u03b1_2737_, lean_object* v_inst_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_List_min___redArg(v_inst_2738_, v_x_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object* v_inst_2742_, lean_object* v_x_2743_){
_start:
{
if (lean_obj_tag(v_x_2743_) == 0)
{
lean_object* v___x_2744_; 
lean_dec(v_inst_2742_);
v___x_2744_ = lean_box(0);
return v___x_2744_;
}
else
{
lean_object* v_head_2745_; lean_object* v_tail_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v_head_2745_ = lean_ctor_get(v_x_2743_, 0);
lean_inc(v_head_2745_);
v_tail_2746_ = lean_ctor_get(v_x_2743_, 1);
lean_inc(v_tail_2746_);
lean_dec_ref(v_x_2743_);
v___x_2747_ = l_List_foldl___redArg(v_inst_2742_, v_head_2745_, v_tail_2746_);
v___x_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
return v___x_2748_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object* v_00_u03b1_2749_, lean_object* v_inst_2750_, lean_object* v_x_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_List_max_x3f___redArg(v_inst_2750_, v_x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object* v_inst_2753_, lean_object* v_x_2754_){
_start:
{
lean_object* v_head_2755_; lean_object* v_tail_2756_; lean_object* v___x_2757_; 
v_head_2755_ = lean_ctor_get(v_x_2754_, 0);
lean_inc(v_head_2755_);
v_tail_2756_ = lean_ctor_get(v_x_2754_, 1);
lean_inc(v_tail_2756_);
lean_dec(v_x_2754_);
v___x_2757_ = l_List_foldl___redArg(v_inst_2753_, v_head_2755_, v_tail_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_List_max(lean_object* v_00_u03b1_2758_, lean_object* v_inst_2759_, lean_object* v_x_2760_, lean_object* v_x_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_List_max___redArg(v_inst_2759_, v_x_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_List_intersperse___redArg(lean_object* v_sep_2763_, lean_object* v_x_2764_){
_start:
{
if (lean_obj_tag(v_x_2764_) == 0)
{
lean_dec(v_sep_2763_);
return v_x_2764_;
}
else
{
lean_object* v_tail_2765_; 
v_tail_2765_ = lean_ctor_get(v_x_2764_, 1);
if (lean_obj_tag(v_tail_2765_) == 0)
{
lean_dec(v_sep_2763_);
return v_x_2764_;
}
else
{
lean_object* v_head_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2775_; 
lean_inc_ref(v_tail_2765_);
v_head_2766_ = lean_ctor_get(v_x_2764_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_x_2764_);
if (v_isSharedCheck_2775_ == 0)
{
lean_object* v_unused_2776_; 
v_unused_2776_ = lean_ctor_get(v_x_2764_, 1);
lean_dec(v_unused_2776_);
v___x_2768_ = v_x_2764_;
v_isShared_2769_ = v_isSharedCheck_2775_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_head_2766_);
lean_dec(v_x_2764_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2775_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_inc(v_sep_2763_);
v___x_2770_ = l_List_intersperse___redArg(v_sep_2763_, v_tail_2765_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 1, v___x_2770_);
lean_ctor_set(v___x_2768_, 0, v_sep_2763_);
v___x_2772_ = v___x_2768_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_sep_2763_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2773_, 0, v_head_2766_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
return v___x_2773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperse(lean_object* v_00_u03b1_2777_, lean_object* v_sep_2778_, lean_object* v_x_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_List_intersperse___redArg(v_sep_2778_, v_x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object* v_r_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
if (lean_obj_tag(v_a_2782_) == 0)
{
lean_object* v___x_2784_; 
lean_dec_ref(v_r_2781_);
v___x_2784_ = l_List_reverse___redArg(v_a_2783_);
return v___x_2784_;
}
else
{
lean_object* v_head_2785_; lean_object* v_tail_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2797_; 
v_head_2785_ = lean_ctor_get(v_a_2782_, 0);
v_tail_2786_ = lean_ctor_get(v_a_2782_, 1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_a_2782_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2788_ = v_a_2782_;
v_isShared_2789_ = v_isSharedCheck_2797_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_tail_2786_);
lean_inc(v_head_2785_);
lean_dec(v_a_2782_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2797_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; uint8_t v___x_2791_; 
lean_inc_ref(v_r_2781_);
lean_inc(v_head_2785_);
v___x_2790_ = lean_apply_1(v_r_2781_, v_head_2785_);
lean_inc(v_a_2783_);
v___x_2791_ = l_List_any___redArg(v_a_2783_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2793_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 1, v_a_2783_);
v___x_2793_ = v___x_2788_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_head_2785_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_a_2783_);
v___x_2793_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
v_a_2782_ = v_tail_2786_;
v_a_2783_ = v___x_2793_;
goto _start;
}
}
else
{
lean_del_object(v___x_2788_);
lean_dec(v_head_2785_);
v_a_2782_ = v_tail_2786_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object* v_00_u03b1_2798_, lean_object* v_r_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_List_eraseDupsBy_loop___redArg(v_r_2799_, v_a_2800_, v_a_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy___redArg(lean_object* v_r_2803_, lean_object* v_as_2804_){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = lean_box(0);
v___x_2806_ = l_List_eraseDupsBy_loop___redArg(v_r_2803_, v_as_2804_, v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy(lean_object* v_00_u03b1_2807_, lean_object* v_r_2808_, lean_object* v_as_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_List_eraseDupsBy___redArg(v_r_2808_, v_as_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT uint8_t l_List_eraseDups___redArg___lam__0(lean_object* v_inst_2811_, lean_object* v_x1_2812_, lean_object* v_x2_2813_){
_start:
{
lean_object* v___x_2814_; uint8_t v___x_2815_; 
v___x_2814_ = lean_apply_2(v_inst_2811_, v_x1_2812_, v_x2_2813_);
v___x_2815_ = lean_unbox(v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg___lam__0___boxed(lean_object* v_inst_2816_, lean_object* v_x1_2817_, lean_object* v_x2_2818_){
_start:
{
uint8_t v_res_2819_; lean_object* v_r_2820_; 
v_res_2819_ = l_List_eraseDups___redArg___lam__0(v_inst_2816_, v_x1_2817_, v_x2_2818_);
v_r_2820_ = lean_box(v_res_2819_);
return v_r_2820_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg(lean_object* v_inst_2821_, lean_object* v_as_2822_){
_start:
{
lean_object* v___f_2823_; lean_object* v___x_2824_; 
v___f_2823_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2823_, 0, v_inst_2821_);
v___x_2824_ = l_List_eraseDupsBy___redArg(v___f_2823_, v_as_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object* v_00_u03b1_2825_, lean_object* v_inst_2826_, lean_object* v_as_2827_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_List_eraseDups___redArg(v_inst_2826_, v_as_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop___redArg(lean_object* v_r_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
if (lean_obj_tag(v_a_2831_) == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref(v_r_2829_);
v___x_2833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2830_);
lean_ctor_set(v___x_2833_, 1, v_a_2832_);
v___x_2834_ = l_List_reverse___redArg(v___x_2833_);
return v___x_2834_;
}
else
{
lean_object* v_head_2835_; lean_object* v_tail_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2847_; 
v_head_2835_ = lean_ctor_get(v_a_2831_, 0);
v_tail_2836_ = lean_ctor_get(v_a_2831_, 1);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_a_2831_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2838_ = v_a_2831_;
v_isShared_2839_ = v_isSharedCheck_2847_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_tail_2836_);
lean_inc(v_head_2835_);
lean_dec(v_a_2831_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2847_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; uint8_t v___x_2841_; 
lean_inc_ref(v_r_2829_);
lean_inc(v_head_2835_);
lean_inc(v_a_2830_);
v___x_2840_ = lean_apply_2(v_r_2829_, v_a_2830_, v_head_2835_);
v___x_2841_ = lean_unbox(v___x_2840_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2843_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v_a_2832_);
lean_ctor_set(v___x_2838_, 0, v_a_2830_);
v___x_2843_ = v___x_2838_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2830_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_a_2832_);
v___x_2843_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
v_a_2830_ = v_head_2835_;
v_a_2831_ = v_tail_2836_;
v_a_2832_ = v___x_2843_;
goto _start;
}
}
else
{
lean_del_object(v___x_2838_);
lean_dec(v_head_2835_);
v_a_2831_ = v_tail_2836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop(lean_object* v_00_u03b1_2848_, lean_object* v_r_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_List_eraseRepsBy_loop___redArg(v_r_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy___redArg(lean_object* v_r_2854_, lean_object* v_x_2855_){
_start:
{
if (lean_obj_tag(v_x_2855_) == 0)
{
lean_dec_ref(v_r_2854_);
return v_x_2855_;
}
else
{
lean_object* v_head_2856_; lean_object* v_tail_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_head_2856_ = lean_ctor_get(v_x_2855_, 0);
lean_inc(v_head_2856_);
v_tail_2857_ = lean_ctor_get(v_x_2855_, 1);
lean_inc(v_tail_2857_);
lean_dec_ref(v_x_2855_);
v___x_2858_ = lean_box(0);
v___x_2859_ = l_List_eraseRepsBy_loop___redArg(v_r_2854_, v_head_2856_, v_tail_2857_, v___x_2858_);
return v___x_2859_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy(lean_object* v_00_u03b1_2860_, lean_object* v_r_2861_, lean_object* v_x_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_List_eraseRepsBy___redArg(v_r_2861_, v_x_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___redArg(lean_object* v_inst_2864_, lean_object* v_as_2865_){
_start:
{
lean_object* v___f_2866_; lean_object* v___x_2867_; 
v___f_2866_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2866_, 0, v_inst_2864_);
v___x_2867_ = l_List_eraseRepsBy___redArg(v___f_2866_, v_as_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object* v_00_u03b1_2868_, lean_object* v_inst_2869_, lean_object* v_as_2870_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_List_eraseReps___redArg(v_inst_2869_, v_as_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___redArg(lean_object* v_p_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
if (lean_obj_tag(v_a_2873_) == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_dec_ref(v_p_2872_);
v___x_2875_ = l_List_reverse___redArg(v_a_2874_);
v___x_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v_a_2873_);
return v___x_2876_;
}
else
{
lean_object* v_head_2877_; lean_object* v_tail_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v_head_2877_ = lean_ctor_get(v_a_2873_, 0);
v_tail_2878_ = lean_ctor_get(v_a_2873_, 1);
lean_inc_ref(v_p_2872_);
lean_inc(v_head_2877_);
v___x_2879_ = lean_apply_1(v_p_2872_, v_head_2877_);
v___x_2880_ = lean_unbox(v___x_2879_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_dec_ref(v_p_2872_);
v___x_2881_ = l_List_reverse___redArg(v_a_2874_);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v_a_2873_);
return v___x_2882_;
}
else
{
lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2890_; 
lean_inc(v_tail_2878_);
lean_inc(v_head_2877_);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_a_2873_);
if (v_isSharedCheck_2890_ == 0)
{
lean_object* v_unused_2891_; lean_object* v_unused_2892_; 
v_unused_2891_ = lean_ctor_get(v_a_2873_, 1);
lean_dec(v_unused_2891_);
v_unused_2892_ = lean_ctor_get(v_a_2873_, 0);
lean_dec(v_unused_2892_);
v___x_2884_ = v_a_2873_;
v_isShared_2885_ = v_isSharedCheck_2890_;
goto v_resetjp_2883_;
}
else
{
lean_dec(v_a_2873_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2890_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 1, v_a_2874_);
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_head_2877_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_a_2874_);
v___x_2887_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
v_a_2873_ = v_tail_2878_;
v_a_2874_ = v___x_2887_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop(lean_object* v_00_u03b1_2893_, lean_object* v_p_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_List_span_loop___redArg(v_p_2894_, v_a_2895_, v_a_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_List_span___redArg(lean_object* v_p_2898_, lean_object* v_as_2899_){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = lean_box(0);
v___x_2901_ = l_List_span_loop___redArg(v_p_2898_, v_as_2899_, v___x_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_List_span(lean_object* v_00_u03b1_2902_, lean_object* v_p_2903_, lean_object* v_as_2904_){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = lean_box(0);
v___x_2906_ = l_List_span_loop___redArg(v_p_2903_, v_as_2904_, v___x_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___redArg(lean_object* v_R_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
if (lean_obj_tag(v_a_2908_) == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_dec_ref(v_R_2907_);
v___x_2912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2909_);
lean_ctor_set(v___x_2912_, 1, v_a_2910_);
v___x_2913_ = l_List_reverse___redArg(v___x_2912_);
v___x_2914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
lean_ctor_set(v___x_2914_, 1, v_a_2911_);
v___x_2915_ = l_List_reverse___redArg(v___x_2914_);
return v___x_2915_;
}
else
{
lean_object* v_head_2916_; lean_object* v_tail_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2934_; 
v_head_2916_ = lean_ctor_get(v_a_2908_, 0);
v_tail_2917_ = lean_ctor_get(v_a_2908_, 1);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_a_2908_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2919_ = v_a_2908_;
v_isShared_2920_ = v_isSharedCheck_2934_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_tail_2917_);
lean_inc(v_head_2916_);
lean_dec(v_a_2908_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2934_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2921_; uint8_t v___x_2922_; 
lean_inc_ref(v_R_2907_);
lean_inc(v_head_2916_);
lean_inc(v_a_2909_);
v___x_2921_ = lean_apply_2(v_R_2907_, v_a_2909_, v_head_2916_);
v___x_2922_ = lean_unbox(v___x_2921_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2925_; 
v___x_2923_ = lean_box(0);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v_a_2910_);
lean_ctor_set(v___x_2919_, 0, v_a_2909_);
v___x_2925_ = v___x_2919_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2909_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_a_2910_);
v___x_2925_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = l_List_reverse___redArg(v___x_2925_);
v___x_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v_a_2911_);
v_a_2908_ = v_tail_2917_;
v_a_2909_ = v_head_2916_;
v_a_2910_ = v___x_2923_;
v_a_2911_ = v___x_2927_;
goto _start;
}
}
else
{
lean_object* v___x_2931_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v_a_2910_);
lean_ctor_set(v___x_2919_, 0, v_a_2909_);
v___x_2931_ = v___x_2919_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2909_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_a_2910_);
v___x_2931_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
v_a_2908_ = v_tail_2917_;
v_a_2909_ = v_head_2916_;
v_a_2910_ = v___x_2931_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop(lean_object* v_00_u03b1_2935_, lean_object* v_R_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_List_splitBy_loop___redArg(v_R_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___redArg(lean_object* v_R_2942_, lean_object* v_x_2943_){
_start:
{
if (lean_obj_tag(v_x_2943_) == 0)
{
lean_object* v___x_2944_; 
lean_dec_ref(v_R_2942_);
v___x_2944_ = lean_box(0);
return v___x_2944_;
}
else
{
lean_object* v_head_2945_; lean_object* v_tail_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_head_2945_ = lean_ctor_get(v_x_2943_, 0);
lean_inc(v_head_2945_);
v_tail_2946_ = lean_ctor_get(v_x_2943_, 1);
lean_inc(v_tail_2946_);
lean_dec_ref(v_x_2943_);
v___x_2947_ = lean_box(0);
v___x_2948_ = l_List_splitBy_loop___redArg(v_R_2942_, v_tail_2946_, v_head_2945_, v___x_2947_, v___x_2947_);
return v___x_2948_;
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy(lean_object* v_00_u03b1_2949_, lean_object* v_R_2950_, lean_object* v_x_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_List_splitBy___redArg(v_R_2950_, v_x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___redArg___lam__0(lean_object* v_inst_2953_, lean_object* v_ys_2954_, lean_object* v_x_2955_){
_start:
{
uint8_t v___x_2956_; 
v___x_2956_ = l_List_elem___redArg(v_inst_2953_, v_x_2955_, v_ys_2954_);
if (v___x_2956_ == 0)
{
uint8_t v___x_2957_; 
v___x_2957_ = 1;
return v___x_2957_;
}
else
{
uint8_t v___x_2958_; 
v___x_2958_ = 0;
return v___x_2958_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg___lam__0___boxed(lean_object* v_inst_2959_, lean_object* v_ys_2960_, lean_object* v_x_2961_){
_start:
{
uint8_t v_res_2962_; lean_object* v_r_2963_; 
v_res_2962_ = l_List_removeAll___redArg___lam__0(v_inst_2959_, v_ys_2960_, v_x_2961_);
v_r_2963_ = lean_box(v_res_2962_);
return v_r_2963_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg(lean_object* v_inst_2964_, lean_object* v_xs_2965_, lean_object* v_ys_2966_){
_start:
{
lean_object* v___f_2967_; lean_object* v___x_2968_; 
v___f_2967_ = lean_alloc_closure((void*)(l_List_removeAll___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2967_, 0, v_inst_2964_);
lean_closure_set(v___f_2967_, 1, v_ys_2966_);
v___x_2968_ = l_List_filter___redArg(v___f_2967_, v_xs_2965_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll(lean_object* v_00_u03b1_2969_, lean_object* v_inst_2970_, lean_object* v_xs_2971_, lean_object* v_ys_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_List_removeAll___redArg(v_inst_2970_, v_xs_2971_, v_ys_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_2974_, lean_object* v_h__1_2975_, lean_object* v_h__2_2976_){
_start:
{
if (lean_obj_tag(v_ys_2974_) == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec(v_h__2_2976_);
v___x_2977_ = lean_box(0);
v___x_2978_ = lean_apply_1(v_h__1_2975_, v___x_2977_);
return v___x_2978_;
}
else
{
lean_object* v_head_2979_; lean_object* v_tail_2980_; lean_object* v___x_2981_; 
lean_dec(v_h__1_2975_);
v_head_2979_ = lean_ctor_get(v_ys_2974_, 0);
lean_inc(v_head_2979_);
v_tail_2980_ = lean_ctor_get(v_ys_2974_, 1);
lean_inc(v_tail_2980_);
lean_dec_ref(v_ys_2974_);
v___x_2981_ = lean_apply_2(v_h__2_2976_, v_head_2979_, v_tail_2980_);
return v___x_2981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_2982_, lean_object* v_motive_2983_, lean_object* v_ys_2984_, lean_object* v_h__1_2985_, lean_object* v_h__2_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(v_ys_2984_, v_h__1_2985_, v_h__2_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(lean_object* v_x_2988_, lean_object* v_x_2989_, lean_object* v_h__1_2990_, lean_object* v_h__2_2991_){
_start:
{
if (lean_obj_tag(v_x_2988_) == 0)
{
lean_object* v___x_2992_; 
lean_dec(v_h__2_2991_);
v___x_2992_ = lean_apply_1(v_h__1_2990_, v_x_2989_);
return v___x_2992_;
}
else
{
lean_object* v_head_2993_; lean_object* v_tail_2994_; lean_object* v___x_2995_; 
lean_dec(v_h__1_2990_);
v_head_2993_ = lean_ctor_get(v_x_2988_, 0);
lean_inc(v_head_2993_);
v_tail_2994_ = lean_ctor_get(v_x_2988_, 1);
lean_inc(v_tail_2994_);
lean_dec_ref(v_x_2988_);
v___x_2995_ = lean_apply_3(v_h__2_2991_, v_head_2993_, v_tail_2994_, v_x_2989_);
return v___x_2995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(lean_object* v_00_u03b1_2996_, lean_object* v_motive_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_, lean_object* v_h__1_3000_, lean_object* v_h__2_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(v_x_2998_, v_x_2999_, v_h__1_3000_, v_h__2_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object* v_f_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
if (lean_obj_tag(v_a_3004_) == 0)
{
lean_object* v___x_3006_; 
lean_dec(v_f_3003_);
v___x_3006_ = l_List_reverse___redArg(v_a_3005_);
return v___x_3006_;
}
else
{
lean_object* v_head_3007_; lean_object* v_tail_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3017_; 
v_head_3007_ = lean_ctor_get(v_a_3004_, 0);
v_tail_3008_ = lean_ctor_get(v_a_3004_, 1);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_a_3004_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3010_ = v_a_3004_;
v_isShared_3011_ = v_isSharedCheck_3017_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_tail_3008_);
lean_inc(v_head_3007_);
lean_dec(v_a_3004_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3017_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3014_; 
lean_inc(v_f_3003_);
v___x_3012_ = lean_apply_1(v_f_3003_, v_head_3007_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 1, v_a_3005_);
lean_ctor_set(v___x_3010_, 0, v___x_3012_);
v___x_3014_ = v___x_3010_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_a_3005_);
v___x_3014_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
v_a_3004_ = v_tail_3008_;
v_a_3005_ = v___x_3014_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object* v_00_u03b1_3018_, lean_object* v_00_u03b2_3019_, lean_object* v_f_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l_List_mapTR_loop___redArg(v_f_3020_, v_a_3021_, v_a_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object* v_f_3024_, lean_object* v_as_3025_){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = lean_box(0);
v___x_3027_ = l_List_mapTR_loop___redArg(v_f_3024_, v_as_3025_, v___x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR(lean_object* v_00_u03b1_3028_, lean_object* v_00_u03b2_3029_, lean_object* v_f_3030_, lean_object* v_as_3031_){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_box(0);
v___x_3033_ = l_List_mapTR_loop___redArg(v_f_3030_, v_as_3031_, v___x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(lean_object* v_x_3034_, lean_object* v_x_3035_, lean_object* v_h__1_3036_, lean_object* v_h__2_3037_){
_start:
{
if (lean_obj_tag(v_x_3034_) == 0)
{
lean_object* v___x_3038_; 
lean_dec(v_h__2_3037_);
v___x_3038_ = lean_apply_1(v_h__1_3036_, v_x_3035_);
return v___x_3038_;
}
else
{
lean_object* v_head_3039_; lean_object* v_tail_3040_; lean_object* v___x_3041_; 
lean_dec(v_h__1_3036_);
v_head_3039_ = lean_ctor_get(v_x_3034_, 0);
lean_inc(v_head_3039_);
v_tail_3040_ = lean_ctor_get(v_x_3034_, 1);
lean_inc(v_tail_3040_);
lean_dec_ref(v_x_3034_);
v___x_3041_ = lean_apply_3(v_h__2_3037_, v_head_3039_, v_tail_3040_, v_x_3035_);
return v___x_3041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(lean_object* v_00_u03b1_3042_, lean_object* v_00_u03b2_3043_, lean_object* v_motive_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v_h__1_3047_, lean_object* v_h__2_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(v_x_3045_, v_x_3046_, v_h__1_3047_, v_h__2_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object* v_p_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
if (lean_obj_tag(v_a_3051_) == 0)
{
lean_object* v___x_3053_; 
lean_dec_ref(v_p_3050_);
v___x_3053_ = l_List_reverse___redArg(v_a_3052_);
return v___x_3053_;
}
else
{
lean_object* v_head_3054_; lean_object* v_tail_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3066_; 
v_head_3054_ = lean_ctor_get(v_a_3051_, 0);
v_tail_3055_ = lean_ctor_get(v_a_3051_, 1);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_a_3051_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3057_ = v_a_3051_;
v_isShared_3058_ = v_isSharedCheck_3066_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_tail_3055_);
lean_inc(v_head_3054_);
lean_dec(v_a_3051_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3066_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; uint8_t v___x_3060_; 
lean_inc_ref(v_p_3050_);
lean_inc(v_head_3054_);
v___x_3059_ = lean_apply_1(v_p_3050_, v_head_3054_);
v___x_3060_ = lean_unbox(v___x_3059_);
if (v___x_3060_ == 0)
{
lean_del_object(v___x_3057_);
lean_dec(v_head_3054_);
v_a_3051_ = v_tail_3055_;
goto _start;
}
else
{
lean_object* v___x_3063_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 1, v_a_3052_);
v___x_3063_ = v___x_3057_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_head_3054_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_a_3052_);
v___x_3063_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
v_a_3051_ = v_tail_3055_;
v_a_3052_ = v___x_3063_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object* v_00_u03b1_3067_, lean_object* v_p_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_List_filterTR_loop___redArg(v_p_3068_, v_a_3069_, v_a_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object* v_p_3072_, lean_object* v_as_3073_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_box(0);
v___x_3075_ = l_List_filterTR_loop___redArg(v_p_3072_, v_as_3073_, v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR(lean_object* v_00_u03b1_3076_, lean_object* v_p_3077_, lean_object* v_as_3078_){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_box(0);
v___x_3080_ = l_List_filterTR_loop___redArg(v_p_3077_, v_as_3078_, v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v_zero_3084_; uint8_t v_isZero_3085_; 
v_zero_3084_ = lean_unsigned_to_nat(0u);
v_isZero_3085_ = lean_nat_dec_eq(v_a_3082_, v_zero_3084_);
if (v_isZero_3085_ == 1)
{
lean_dec(v_a_3082_);
lean_dec(v_a_3081_);
return v_a_3083_;
}
else
{
lean_object* v_one_3086_; lean_object* v_n_3087_; lean_object* v___x_3088_; 
v_one_3086_ = lean_unsigned_to_nat(1u);
v_n_3087_ = lean_nat_sub(v_a_3082_, v_one_3086_);
lean_dec(v_a_3082_);
lean_inc(v_a_3081_);
v___x_3088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3088_, 0, v_a_3081_);
lean_ctor_set(v___x_3088_, 1, v_a_3083_);
v_a_3082_ = v_n_3087_;
v_a_3083_ = v___x_3088_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object* v_00_u03b1_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l_List_replicateTR_loop___redArg(v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object* v_n_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = lean_box(0);
v___x_3098_ = l_List_replicateTR_loop___redArg(v_a_3096_, v_n_3095_, v___x_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object* v_00_u03b1_3099_, lean_object* v_n_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_List_replicateTR___redArg(v_n_3100_, v_a_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(lean_object* v_x_3103_, lean_object* v_x_3104_, lean_object* v_h__1_3105_, lean_object* v_h__2_3106_){
_start:
{
lean_object* v_zero_3107_; uint8_t v_isZero_3108_; 
v_zero_3107_ = lean_unsigned_to_nat(0u);
v_isZero_3108_ = lean_nat_dec_eq(v_x_3103_, v_zero_3107_);
if (v_isZero_3108_ == 1)
{
lean_object* v___x_3109_; 
lean_dec(v_h__2_3106_);
v___x_3109_ = lean_apply_1(v_h__1_3105_, v_x_3104_);
return v___x_3109_;
}
else
{
lean_object* v_one_3110_; lean_object* v_n_3111_; lean_object* v___x_3112_; 
lean_dec(v_h__1_3105_);
v_one_3110_ = lean_unsigned_to_nat(1u);
v_n_3111_ = lean_nat_sub(v_x_3103_, v_one_3110_);
v___x_3112_ = lean_apply_2(v_h__2_3106_, v_n_3111_, v_x_3104_);
return v___x_3112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_3113_, lean_object* v_x_3114_, lean_object* v_h__1_3115_, lean_object* v_h__2_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(v_x_3113_, v_x_3114_, v_h__1_3115_, v_h__2_3116_);
lean_dec(v_x_3113_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(lean_object* v_00_u03b1_3118_, lean_object* v_motive_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_, lean_object* v_h__1_3122_, lean_object* v_h__2_3123_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(v_x_3120_, v_x_3121_, v_h__1_3122_, v_h__2_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_3125_, lean_object* v_motive_3126_, lean_object* v_x_3127_, lean_object* v_x_3128_, lean_object* v_h__1_3129_, lean_object* v_h__2_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(v_00_u03b1_3125_, v_motive_3126_, v_x_3127_, v_x_3128_, v_h__1_3129_, v_h__2_3130_);
lean_dec(v_x_3127_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(lean_object* v_x_3132_, lean_object* v_x_3133_, lean_object* v_h__1_3134_, lean_object* v_h__2_3135_){
_start:
{
lean_object* v_zero_3136_; uint8_t v_isZero_3137_; 
v_zero_3136_ = lean_unsigned_to_nat(0u);
v_isZero_3137_ = lean_nat_dec_eq(v_x_3132_, v_zero_3136_);
if (v_isZero_3137_ == 1)
{
lean_object* v___x_3138_; 
lean_dec(v_h__2_3135_);
v___x_3138_ = lean_apply_1(v_h__1_3134_, v_x_3133_);
return v___x_3138_;
}
else
{
lean_object* v_one_3139_; lean_object* v_n_3140_; lean_object* v___x_3141_; 
lean_dec(v_h__1_3134_);
v_one_3139_ = lean_unsigned_to_nat(1u);
v_n_3140_ = lean_nat_sub(v_x_3132_, v_one_3139_);
v___x_3141_ = lean_apply_2(v_h__2_3135_, v_n_3140_, v_x_3133_);
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_3142_, lean_object* v_x_3143_, lean_object* v_h__1_3144_, lean_object* v_h__2_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(v_x_3142_, v_x_3143_, v_h__1_3144_, v_h__2_3145_);
lean_dec(v_x_3142_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(lean_object* v_00_u03b1_3147_, lean_object* v_motive_3148_, lean_object* v_x_3149_, lean_object* v_x_3150_, lean_object* v_h__1_3151_, lean_object* v_h__2_3152_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(v_x_3149_, v_x_3150_, v_h__1_3151_, v_h__2_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___boxed(lean_object* v_00_u03b1_3154_, lean_object* v_motive_3155_, lean_object* v_x_3156_, lean_object* v_x_3157_, lean_object* v_h__1_3158_, lean_object* v_h__2_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(v_00_u03b1_3154_, v_motive_3155_, v_x_3156_, v_x_3157_, v_h__1_3158_, v_h__2_3159_);
lean_dec(v_x_3156_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg(lean_object* v_n_3161_, lean_object* v_a_3162_, lean_object* v_l_3163_){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = l_List_lengthTR___redArg(v_l_3163_);
v___x_3165_ = lean_nat_sub(v_n_3161_, v___x_3164_);
lean_dec(v___x_3164_);
v___x_3166_ = l_List_replicateTR_loop___redArg(v_a_3162_, v___x_3165_, v_l_3163_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg___boxed(lean_object* v_n_3167_, lean_object* v_a_3168_, lean_object* v_l_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_List_leftpadTR___redArg(v_n_3167_, v_a_3168_, v_l_3169_);
lean_dec(v_n_3167_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object* v_00_u03b1_3171_, lean_object* v_n_3172_, lean_object* v_a_3173_, lean_object* v_l_3174_){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = l_List_lengthTR___redArg(v_l_3174_);
v___x_3176_ = lean_nat_sub(v_n_3172_, v___x_3175_);
lean_dec(v___x_3175_);
v___x_3177_ = l_List_replicateTR_loop___redArg(v_a_3173_, v___x_3176_, v_l_3174_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___boxed(lean_object* v_00_u03b1_3178_, lean_object* v_n_3179_, lean_object* v_a_3180_, lean_object* v_l_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_List_leftpadTR(v_00_u03b1_3178_, v_n_3179_, v_a_3180_, v_l_3181_);
lean_dec(v_n_3179_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg(lean_object* v_init_3183_, lean_object* v_x_3184_){
_start:
{
if (lean_obj_tag(v_x_3184_) == 0)
{
lean_inc_ref(v_init_3183_);
return v_init_3183_;
}
else
{
lean_object* v_head_3185_; lean_object* v_tail_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3212_; 
v_head_3185_ = lean_ctor_get(v_x_3184_, 0);
v_tail_3186_ = lean_ctor_get(v_x_3184_, 1);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_x_3184_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3188_ = v_x_3184_;
v_isShared_3189_ = v_isSharedCheck_3212_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_tail_3186_);
lean_inc(v_head_3185_);
lean_dec(v_x_3184_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3212_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v_fst_3190_; lean_object* v_snd_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3211_; 
v_fst_3190_ = lean_ctor_get(v_head_3185_, 0);
v_snd_3191_ = lean_ctor_get(v_head_3185_, 1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_head_3185_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3193_ = v_head_3185_;
v_isShared_3194_ = v_isSharedCheck_3211_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_snd_3191_);
lean_inc(v_fst_3190_);
lean_dec(v_head_3185_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3211_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v_fst_3196_; lean_object* v_snd_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3210_; 
v___x_3195_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3183_, v_tail_3186_);
v_fst_3196_ = lean_ctor_get(v___x_3195_, 0);
v_snd_3197_ = lean_ctor_get(v___x_3195_, 1);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3199_ = v___x_3195_;
v_isShared_3200_ = v_isSharedCheck_3210_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_snd_3197_);
lean_inc(v_fst_3196_);
lean_dec(v___x_3195_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3210_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 1, v_fst_3196_);
lean_ctor_set(v___x_3188_, 0, v_fst_3190_);
v___x_3202_ = v___x_3188_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_fst_3190_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_fst_3196_);
v___x_3202_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3204_; 
if (v_isShared_3194_ == 0)
{
lean_ctor_set_tag(v___x_3193_, 1);
lean_ctor_set(v___x_3193_, 1, v_snd_3197_);
lean_ctor_set(v___x_3193_, 0, v_snd_3191_);
v___x_3204_ = v___x_3193_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_snd_3191_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_snd_3197_);
v___x_3204_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3206_; 
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 1, v___x_3204_);
lean_ctor_set(v___x_3199_, 0, v___x_3202_);
v___x_3206_ = v___x_3199_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg___boxed(lean_object* v_init_3213_, lean_object* v_x_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3213_, v_x_3214_);
lean_dec_ref(v_init_3213_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object* v_l_3216_){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_3218_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v___x_3217_, v_l_3216_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object* v_00_u03b1_3219_, lean_object* v_00_u03b2_3220_, lean_object* v_l_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_List_unzipTR___redArg(v_l_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0(lean_object* v_00_u03b1_3223_, lean_object* v_00_u03b2_3224_, lean_object* v_init_3225_, lean_object* v_x_3226_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3225_, v_x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___boxed(lean_object* v_00_u03b1_3228_, lean_object* v_00_u03b2_3229_, lean_object* v_init_3230_, lean_object* v_x_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_List_foldr___at___00List_unzipTR_spec__0(v_00_u03b1_3228_, v_00_u03b2_3229_, v_init_3230_, v_x_3231_);
lean_dec_ref(v_init_3230_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object* v_step_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_zero_3237_; uint8_t v_isZero_3238_; 
v_zero_3237_ = lean_unsigned_to_nat(0u);
v_isZero_3238_ = lean_nat_dec_eq(v_a_3234_, v_zero_3237_);
if (v_isZero_3238_ == 1)
{
lean_dec(v_a_3235_);
lean_dec(v_a_3234_);
return v_a_3236_;
}
else
{
lean_object* v_one_3239_; lean_object* v_n_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_one_3239_ = lean_unsigned_to_nat(1u);
v_n_3240_ = lean_nat_sub(v_a_3234_, v_one_3239_);
lean_dec(v_a_3234_);
v___x_3241_ = lean_nat_sub(v_a_3235_, v_step_3233_);
lean_dec(v_a_3235_);
lean_inc(v___x_3241_);
v___x_3242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
lean_ctor_set(v___x_3242_, 1, v_a_3236_);
v_a_3234_ = v_n_3240_;
v_a_3235_ = v___x_3241_;
v_a_3236_ = v___x_3242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object* v_step_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_List_range_x27TR_go(v_step_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
lean_dec(v_step_3244_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object* v_s_3249_, lean_object* v_n_3250_, lean_object* v_step_3251_){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3252_ = lean_nat_mul(v_step_3251_, v_n_3250_);
v___x_3253_ = lean_nat_add(v_s_3249_, v___x_3252_);
lean_dec(v___x_3252_);
v___x_3254_ = lean_box(0);
v___x_3255_ = l_List_range_x27TR_go(v_step_3251_, v_n_3250_, v___x_3253_, v___x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object* v_s_3256_, lean_object* v_n_3257_, lean_object* v_step_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_List_range_x27TR(v_s_3256_, v_n_3257_, v_step_3258_);
lean_dec(v_step_3258_);
lean_dec(v_s_3256_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(lean_object* v_x_3260_, lean_object* v_x_3261_, lean_object* v_x_3262_, lean_object* v_h__1_3263_, lean_object* v_h__2_3264_){
_start:
{
lean_object* v_zero_3265_; uint8_t v_isZero_3266_; 
v_zero_3265_ = lean_unsigned_to_nat(0u);
v_isZero_3266_ = lean_nat_dec_eq(v_x_3260_, v_zero_3265_);
if (v_isZero_3266_ == 1)
{
lean_object* v___x_3267_; 
lean_dec(v_h__2_3264_);
v___x_3267_ = lean_apply_2(v_h__1_3263_, v_x_3261_, v_x_3262_);
return v___x_3267_;
}
else
{
lean_object* v_one_3268_; lean_object* v_n_3269_; lean_object* v___x_3270_; 
lean_dec(v_h__1_3263_);
v_one_3268_ = lean_unsigned_to_nat(1u);
v_n_3269_ = lean_nat_sub(v_x_3260_, v_one_3268_);
v___x_3270_ = lean_apply_3(v_h__2_3264_, v_n_3269_, v_x_3261_, v_x_3262_);
return v___x_3270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(lean_object* v_x_3271_, lean_object* v_x_3272_, lean_object* v_x_3273_, lean_object* v_h__1_3274_, lean_object* v_h__2_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(v_x_3271_, v_x_3272_, v_x_3273_, v_h__1_3274_, v_h__2_3275_);
lean_dec(v_x_3271_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object* v_motive_3277_, lean_object* v_x_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_, lean_object* v_h__1_3281_, lean_object* v_h__2_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(v_x_3278_, v_x_3279_, v_x_3280_, v_h__1_3281_, v_h__2_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(lean_object* v_motive_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_, lean_object* v_h__1_3288_, lean_object* v_h__2_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(v_motive_3284_, v_x_3285_, v_x_3286_, v_x_3287_, v_h__1_3288_, v_h__2_3289_);
lean_dec(v_x_3285_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg(lean_object* v_sep_3291_, lean_object* v_init_3292_, lean_object* v_x_3293_){
_start:
{
if (lean_obj_tag(v_x_3293_) == 0)
{
lean_dec(v_sep_3291_);
lean_inc(v_init_3292_);
return v_init_3292_;
}
else
{
lean_object* v_head_3294_; lean_object* v_tail_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3304_; 
v_head_3294_ = lean_ctor_get(v_x_3293_, 0);
v_tail_3295_ = lean_ctor_get(v_x_3293_, 1);
v_isSharedCheck_3304_ = !lean_is_exclusive(v_x_3293_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3297_ = v_x_3293_;
v_isShared_3298_ = v_isSharedCheck_3304_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_tail_3295_);
lean_inc(v_head_3294_);
lean_dec(v_x_3293_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3304_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; lean_object* v___x_3301_; 
lean_inc(v_sep_3291_);
v___x_3299_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3291_, v_init_3292_, v_tail_3295_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 1, v___x_3299_);
v___x_3301_ = v___x_3297_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_head_3294_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v___x_3299_);
v___x_3301_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3302_, 0, v_sep_3291_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
return v___x_3302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(lean_object* v_sep_3305_, lean_object* v_init_3306_, lean_object* v_x_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3305_, v_init_3306_, v_x_3307_);
lean_dec(v_init_3306_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object* v_sep_3309_, lean_object* v_x_3310_){
_start:
{
if (lean_obj_tag(v_x_3310_) == 0)
{
lean_dec(v_sep_3309_);
return v_x_3310_;
}
else
{
lean_object* v_tail_3311_; 
v_tail_3311_ = lean_ctor_get(v_x_3310_, 1);
lean_inc(v_tail_3311_);
if (lean_obj_tag(v_tail_3311_) == 0)
{
lean_dec(v_sep_3309_);
return v_x_3310_;
}
else
{
lean_object* v_head_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3331_; 
v_head_3312_ = lean_ctor_get(v_x_3310_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_x_3310_);
if (v_isSharedCheck_3331_ == 0)
{
lean_object* v_unused_3332_; 
v_unused_3332_ = lean_ctor_get(v_x_3310_, 1);
lean_dec(v_unused_3332_);
v___x_3314_ = v_x_3310_;
v_isShared_3315_ = v_isSharedCheck_3331_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_head_3312_);
lean_dec(v_x_3310_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3331_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v_head_3316_; lean_object* v_tail_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3330_; 
v_head_3316_ = lean_ctor_get(v_tail_3311_, 0);
v_tail_3317_ = lean_ctor_get(v_tail_3311_, 1);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_tail_3311_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3319_ = v_tail_3311_;
v_isShared_3320_ = v_isSharedCheck_3330_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_tail_3317_);
lean_inc(v_head_3316_);
lean_dec(v_tail_3311_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3330_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v___x_3321_ = lean_box(0);
lean_inc(v_sep_3309_);
v___x_3322_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3309_, v___x_3321_, v_tail_3317_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 1, v___x_3322_);
v___x_3324_ = v___x_3319_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_head_3316_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3326_; 
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 1, v___x_3324_);
lean_ctor_set(v___x_3314_, 0, v_sep_3309_);
v___x_3326_ = v___x_3314_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_sep_3309_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3327_, 0, v_head_3312_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
return v___x_3327_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object* v_00_u03b1_3333_, lean_object* v_sep_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_List_intersperseTR___redArg(v_sep_3334_, v_x_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0(lean_object* v_00_u03b1_3337_, lean_object* v_sep_3338_, lean_object* v_init_3339_, lean_object* v_x_3340_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3338_, v_init_3339_, v_x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___boxed(lean_object* v_00_u03b1_3342_, lean_object* v_sep_3343_, lean_object* v_init_3344_, lean_object* v_x_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_List_foldr___at___00List_intersperseTR_spec__0(v_00_u03b1_3342_, v_sep_3343_, v_init_3344_, v_x_3345_);
lean_dec(v_init_3344_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(lean_object* v_x_3347_, lean_object* v_h__1_3348_, lean_object* v_h__2_3349_, lean_object* v_h__3_3350_){
_start:
{
if (lean_obj_tag(v_x_3347_) == 0)
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_dec(v_h__3_3350_);
lean_dec(v_h__2_3349_);
v___x_3351_ = lean_box(0);
v___x_3352_ = lean_apply_1(v_h__1_3348_, v___x_3351_);
return v___x_3352_;
}
else
{
lean_object* v_tail_3353_; 
lean_dec(v_h__1_3348_);
v_tail_3353_ = lean_ctor_get(v_x_3347_, 1);
if (lean_obj_tag(v_tail_3353_) == 0)
{
lean_object* v_head_3354_; lean_object* v___x_3355_; 
lean_dec(v_h__3_3350_);
v_head_3354_ = lean_ctor_get(v_x_3347_, 0);
lean_inc(v_head_3354_);
lean_dec_ref(v_x_3347_);
v___x_3355_ = lean_apply_1(v_h__2_3349_, v_head_3354_);
return v___x_3355_;
}
else
{
lean_object* v_head_3356_; lean_object* v_head_3357_; lean_object* v_tail_3358_; lean_object* v___x_3359_; 
lean_inc_ref(v_tail_3353_);
lean_dec(v_h__2_3349_);
v_head_3356_ = lean_ctor_get(v_x_3347_, 0);
lean_inc(v_head_3356_);
lean_dec_ref(v_x_3347_);
v_head_3357_ = lean_ctor_get(v_tail_3353_, 0);
lean_inc(v_head_3357_);
v_tail_3358_ = lean_ctor_get(v_tail_3353_, 1);
lean_inc(v_tail_3358_);
lean_dec_ref(v_tail_3353_);
v___x_3359_ = lean_apply_3(v_h__3_3350_, v_head_3356_, v_head_3357_, v_tail_3358_);
return v___x_3359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object* v_00_u03b1_3360_, lean_object* v_motive_3361_, lean_object* v_x_3362_, lean_object* v_h__1_3363_, lean_object* v_h__2_3364_, lean_object* v_h__3_3365_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(v_x_3362_, v_h__1_3363_, v_h__2_3364_, v_h__3_3365_);
return v___x_3366_;
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
