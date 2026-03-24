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
lean_inc(v_head_155_);
v_tail_156_ = lean_ctor_get(v_x_149_, 1);
lean_inc(v_tail_156_);
lean_dec_ref(v_x_149_);
lean_inc_ref(v_inst_146_);
lean_inc(v_head_155_);
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
lean_inc(v_head_413_);
v_tail_414_ = lean_ctor_get(v_l_u2081_407_, 1);
lean_inc(v_tail_414_);
lean_dec_ref(v_l_u2081_407_);
v_head_415_ = lean_ctor_get(v_l_u2082_408_, 0);
lean_inc(v_head_415_);
v_tail_416_ = lean_ctor_get(v_l_u2082_408_, 1);
lean_inc(v_tail_416_);
lean_dec_ref(v_l_u2082_408_);
lean_inc_ref(v_lt_409_);
lean_inc(v_head_415_);
lean_inc(v_head_413_);
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
lean_dec_ref(v_a_1198_);
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
lean_inc(v_quotContext_1204_);
v_currMacroScope_1205_ = lean_ctor_get(v_a_1198_, 2);
lean_inc(v_currMacroScope_1205_);
v_ref_1206_ = lean_ctor_get(v_a_1198_, 5);
lean_inc(v_ref_1206_);
lean_dec_ref(v_a_1198_);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = l_Lean_Syntax_getArg(v_x_1197_, v___x_1207_);
v___x_1209_ = lean_unsigned_to_nat(2u);
v___x_1210_ = l_Lean_Syntax_getArg(v_x_1197_, v___x_1209_);
lean_dec(v_x_1197_);
v___x_1211_ = 0;
v___x_1212_ = l_Lean_SourceInfo_fromRef(v_ref_1206_, v___x_1211_);
lean_dec(v_ref_1206_);
v___x_1213_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1214_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
v___x_1215_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4));
v___x_1216_ = l_Lean_addMacroScope(v_quotContext_1204_, v___x_1215_, v_currMacroScope_1205_);
v___x_1217_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10));
lean_inc(v___x_1212_);
v___x_1218_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1212_);
lean_ctor_set(v___x_1218_, 1, v___x_1214_);
lean_ctor_set(v___x_1218_, 2, v___x_1216_);
lean_ctor_set(v___x_1218_, 3, v___x_1217_);
v___x_1219_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
lean_inc(v___x_1212_);
v___x_1220_ = l_Lean_Syntax_node2(v___x_1212_, v___x_1219_, v___x_1208_, v___x_1210_);
v___x_1221_ = l_Lean_Syntax_node2(v___x_1212_, v___x_1213_, v___x_1218_, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_a_1199_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object* v_x_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1226_);
v___x_1230_ = l_Lean_Syntax_isOfKind(v_x_1226_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec(v_x_1226_);
v___x_1231_ = lean_box(0);
v___x_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v_a_1228_);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = l_Lean_Syntax_getArg(v_x_1226_, v___x_1233_);
v___x_1235_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1234_);
v___x_1236_ = l_Lean_Syntax_isOfKind(v___x_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v___x_1234_);
lean_dec(v_x_1226_);
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v_a_1228_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = l_Lean_Syntax_getArg(v_x_1226_, v___x_1239_);
lean_dec(v_x_1226_);
v___x_1241_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1240_);
v___x_1242_ = l_Lean_Syntax_matchesNull(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v___x_1240_);
lean_dec(v___x_1234_);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v_a_1228_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v_ref_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1245_ = l_Lean_Syntax_getArg(v___x_1240_, v___x_1233_);
v___x_1246_ = l_Lean_Syntax_getArg(v___x_1240_, v___x_1239_);
lean_dec(v___x_1240_);
v_ref_1247_ = l_Lean_replaceRef(v___x_1234_, v_a_1227_);
lean_dec(v___x_1234_);
v___x_1248_ = 0;
v___x_1249_ = l_Lean_SourceInfo_fromRef(v_ref_1247_, v___x_1248_);
lean_dec(v_ref_1247_);
v___x_1250_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
v___x_1251_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__5));
lean_inc(v___x_1249_);
v___x_1252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1249_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = l_Lean_Syntax_node3(v___x_1249_, v___x_1250_, v___x_1245_, v___x_1252_, v___x_1246_);
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v_a_1228_);
return v___x_1254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object* v_x_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(v_x_1255_, v_a_1256_, v_a_1257_);
lean_dec(v_a_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist___redArg(lean_object* v_inst_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
if (lean_obj_tag(v_x_1260_) == 0)
{
uint8_t v___x_1262_; 
lean_dec(v_x_1261_);
lean_dec_ref(v_inst_1259_);
v___x_1262_ = 1;
return v___x_1262_;
}
else
{
if (lean_obj_tag(v_x_1261_) == 0)
{
uint8_t v___x_1263_; 
lean_dec_ref(v_x_1260_);
lean_dec_ref(v_inst_1259_);
v___x_1263_ = 0;
return v___x_1263_;
}
else
{
lean_object* v_head_1264_; lean_object* v_tail_1265_; lean_object* v_head_1266_; lean_object* v_tail_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_head_1264_ = lean_ctor_get(v_x_1260_, 0);
v_tail_1265_ = lean_ctor_get(v_x_1260_, 1);
v_head_1266_ = lean_ctor_get(v_x_1261_, 0);
lean_inc(v_head_1266_);
v_tail_1267_ = lean_ctor_get(v_x_1261_, 1);
lean_inc(v_tail_1267_);
lean_dec_ref(v_x_1261_);
lean_inc_ref(v_inst_1259_);
lean_inc(v_head_1264_);
v___x_1268_ = lean_apply_2(v_inst_1259_, v_head_1264_, v_head_1266_);
v___x_1269_ = lean_unbox(v___x_1268_);
if (v___x_1269_ == 0)
{
v_x_1261_ = v_tail_1267_;
goto _start;
}
else
{
lean_inc(v_tail_1265_);
lean_dec_ref(v_x_1260_);
v_x_1260_ = v_tail_1265_;
v_x_1261_ = v_tail_1267_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSublist___redArg___boxed(lean_object* v_inst_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
uint8_t v_res_1275_; lean_object* v_r_1276_; 
v_res_1275_ = l_List_isSublist___redArg(v_inst_1272_, v_x_1273_, v_x_1274_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist(lean_object* v_00_u03b1_1277_, lean_object* v_inst_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = l_List_isSublist___redArg(v_inst_1278_, v_x_1279_, v_x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_List_isSublist___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_inst_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
uint8_t v_res_1286_; lean_object* v_r_1287_; 
v_res_1286_ = l_List_isSublist(v_00_u03b1_1282_, v_inst_1283_, v_x_1284_, v_x_1285_);
v_r_1287_ = lean_box(v_res_1286_);
return v_r_1287_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0));
v___x_1306_ = l_String_toRawSubstring_x27(v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object* v_x_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
lean_inc(v_x_1318_);
v___x_1322_ = l_Lean_Syntax_isOfKind(v_x_1318_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec_ref(v_a_1319_);
lean_dec(v_x_1318_);
v___x_1323_ = lean_box(1);
v___x_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_a_1320_);
return v___x_1324_;
}
else
{
lean_object* v_quotContext_1325_; lean_object* v_currMacroScope_1326_; lean_object* v_ref_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_quotContext_1325_ = lean_ctor_get(v_a_1319_, 1);
lean_inc(v_quotContext_1325_);
v_currMacroScope_1326_ = lean_ctor_get(v_a_1319_, 2);
lean_inc(v_currMacroScope_1326_);
v_ref_1327_ = lean_ctor_get(v_a_1319_, 5);
lean_inc(v_ref_1327_);
lean_dec_ref(v_a_1319_);
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = l_Lean_Syntax_getArg(v_x_1318_, v___x_1328_);
v___x_1330_ = lean_unsigned_to_nat(2u);
v___x_1331_ = l_Lean_Syntax_getArg(v_x_1318_, v___x_1330_);
lean_dec(v_x_1318_);
v___x_1332_ = 0;
v___x_1333_ = l_Lean_SourceInfo_fromRef(v_ref_1327_, v___x_1332_);
lean_dec(v_ref_1327_);
v___x_1334_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1335_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
v___x_1336_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2));
v___x_1337_ = l_Lean_addMacroScope(v_quotContext_1325_, v___x_1336_, v_currMacroScope_1326_);
v___x_1338_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5));
lean_inc(v___x_1333_);
v___x_1339_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1333_);
lean_ctor_set(v___x_1339_, 1, v___x_1335_);
lean_ctor_set(v___x_1339_, 2, v___x_1337_);
lean_ctor_set(v___x_1339_, 3, v___x_1338_);
v___x_1340_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
lean_inc(v___x_1333_);
v___x_1341_ = l_Lean_Syntax_node2(v___x_1333_, v___x_1340_, v___x_1329_, v___x_1331_);
v___x_1342_ = l_Lean_Syntax_node2(v___x_1333_, v___x_1334_, v___x_1339_, v___x_1341_);
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v_a_1320_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object* v_x_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1344_);
v___x_1348_ = l_Lean_Syntax_isOfKind(v_x_1344_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_x_1344_);
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v_a_1346_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = l_Lean_Syntax_getArg(v_x_1344_, v___x_1351_);
v___x_1353_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1352_);
v___x_1354_ = l_Lean_Syntax_isOfKind(v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v___x_1352_);
lean_dec(v_x_1344_);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v_a_1346_);
return v___x_1356_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = l_Lean_Syntax_getArg(v_x_1344_, v___x_1357_);
lean_dec(v_x_1344_);
v___x_1359_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1358_);
v___x_1360_ = l_Lean_Syntax_matchesNull(v___x_1358_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v___x_1358_);
lean_dec(v___x_1352_);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v_a_1346_);
return v___x_1362_;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_ref_1365_; uint8_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1363_ = l_Lean_Syntax_getArg(v___x_1358_, v___x_1351_);
v___x_1364_ = l_Lean_Syntax_getArg(v___x_1358_, v___x_1357_);
lean_dec(v___x_1358_);
v_ref_1365_ = l_Lean_replaceRef(v___x_1352_, v_a_1345_);
lean_dec(v___x_1352_);
v___x_1366_ = 0;
v___x_1367_ = l_Lean_SourceInfo_fromRef(v_ref_1365_, v___x_1366_);
lean_dec(v_ref_1365_);
v___x_1368_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
v___x_1369_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__2));
lean_inc(v___x_1367_);
v___x_1370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1367_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = l_Lean_Syntax_node3(v___x_1367_, v___x_1368_, v___x_1363_, v___x_1370_, v___x_1364_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v_a_1346_);
return v___x_1372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object* v_x_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(v_x_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1374_);
return v_res_1376_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf___redArg(lean_object* v_inst_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_){
_start:
{
if (lean_obj_tag(v_x_1378_) == 0)
{
uint8_t v___x_1380_; 
lean_dec(v_x_1379_);
lean_dec_ref(v_inst_1377_);
v___x_1380_ = 1;
return v___x_1380_;
}
else
{
if (lean_obj_tag(v_x_1379_) == 0)
{
uint8_t v___x_1381_; 
lean_dec_ref(v_x_1378_);
lean_dec_ref(v_inst_1377_);
v___x_1381_ = 0;
return v___x_1381_;
}
else
{
lean_object* v_head_1382_; lean_object* v_tail_1383_; lean_object* v_head_1384_; lean_object* v_tail_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_head_1382_ = lean_ctor_get(v_x_1378_, 0);
lean_inc(v_head_1382_);
v_tail_1383_ = lean_ctor_get(v_x_1378_, 1);
lean_inc(v_tail_1383_);
lean_dec_ref(v_x_1378_);
v_head_1384_ = lean_ctor_get(v_x_1379_, 0);
lean_inc(v_head_1384_);
v_tail_1385_ = lean_ctor_get(v_x_1379_, 1);
lean_inc(v_tail_1385_);
lean_dec_ref(v_x_1379_);
lean_inc_ref(v_inst_1377_);
v___x_1386_ = lean_apply_2(v_inst_1377_, v_head_1382_, v_head_1384_);
v___x_1387_ = lean_unbox(v___x_1386_);
if (v___x_1387_ == 0)
{
uint8_t v___x_1388_; 
lean_dec(v_tail_1385_);
lean_dec(v_tail_1383_);
lean_dec_ref(v_inst_1377_);
v___x_1388_ = lean_unbox(v___x_1386_);
return v___x_1388_;
}
else
{
v_x_1378_ = v_tail_1383_;
v_x_1379_ = v_tail_1385_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___redArg___boxed(lean_object* v_inst_1390_, lean_object* v_x_1391_, lean_object* v_x_1392_){
_start:
{
uint8_t v_res_1393_; lean_object* v_r_1394_; 
v_res_1393_ = l_List_isPrefixOf___redArg(v_inst_1390_, v_x_1391_, v_x_1392_);
v_r_1394_ = lean_box(v_res_1393_);
return v_r_1394_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf(lean_object* v_00_u03b1_1395_, lean_object* v_inst_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_){
_start:
{
uint8_t v___x_1399_; 
v___x_1399_ = l_List_isPrefixOf___redArg(v_inst_1396_, v_x_1397_, v_x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___boxed(lean_object* v_00_u03b1_1400_, lean_object* v_inst_1401_, lean_object* v_x_1402_, lean_object* v_x_1403_){
_start:
{
uint8_t v_res_1404_; lean_object* v_r_1405_; 
v_res_1404_ = l_List_isPrefixOf(v_00_u03b1_1400_, v_inst_1401_, v_x_1402_, v_x_1403_);
v_r_1405_ = lean_box(v_res_1404_);
return v_r_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_1406_, lean_object* v_x_1407_, lean_object* v_h__1_1408_, lean_object* v_h__2_1409_, lean_object* v_h__3_1410_){
_start:
{
if (lean_obj_tag(v_x_1406_) == 0)
{
lean_object* v___x_1411_; 
lean_dec(v_h__3_1410_);
lean_dec(v_h__2_1409_);
v___x_1411_ = lean_apply_1(v_h__1_1408_, v_x_1407_);
return v___x_1411_;
}
else
{
lean_dec(v_h__1_1408_);
if (lean_obj_tag(v_x_1407_) == 0)
{
lean_object* v___x_1412_; 
lean_dec(v_h__3_1410_);
v___x_1412_ = lean_apply_2(v_h__2_1409_, v_x_1406_, lean_box(0));
return v___x_1412_;
}
else
{
lean_object* v_head_1413_; lean_object* v_tail_1414_; lean_object* v_head_1415_; lean_object* v_tail_1416_; lean_object* v___x_1417_; 
lean_dec(v_h__2_1409_);
v_head_1413_ = lean_ctor_get(v_x_1406_, 0);
lean_inc(v_head_1413_);
v_tail_1414_ = lean_ctor_get(v_x_1406_, 1);
lean_inc(v_tail_1414_);
lean_dec_ref(v_x_1406_);
v_head_1415_ = lean_ctor_get(v_x_1407_, 0);
lean_inc(v_head_1415_);
v_tail_1416_ = lean_ctor_get(v_x_1407_, 1);
lean_inc(v_tail_1416_);
lean_dec_ref(v_x_1407_);
v___x_1417_ = lean_apply_4(v_h__3_1410_, v_head_1413_, v_tail_1414_, v_head_1415_, v_tail_1416_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object* v_00_u03b1_1418_, lean_object* v_motive_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_, lean_object* v_h__1_1422_, lean_object* v_h__2_1423_, lean_object* v_h__3_1424_){
_start:
{
if (lean_obj_tag(v_x_1420_) == 0)
{
lean_object* v___x_1425_; 
lean_dec(v_h__3_1424_);
lean_dec(v_h__2_1423_);
v___x_1425_ = lean_apply_1(v_h__1_1422_, v_x_1421_);
return v___x_1425_;
}
else
{
lean_dec(v_h__1_1422_);
if (lean_obj_tag(v_x_1421_) == 0)
{
lean_object* v___x_1426_; 
lean_dec(v_h__3_1424_);
v___x_1426_ = lean_apply_2(v_h__2_1423_, v_x_1420_, lean_box(0));
return v___x_1426_;
}
else
{
lean_object* v_head_1427_; lean_object* v_tail_1428_; lean_object* v_head_1429_; lean_object* v_tail_1430_; lean_object* v___x_1431_; 
lean_dec(v_h__2_1423_);
v_head_1427_ = lean_ctor_get(v_x_1420_, 0);
lean_inc(v_head_1427_);
v_tail_1428_ = lean_ctor_get(v_x_1420_, 1);
lean_inc(v_tail_1428_);
lean_dec_ref(v_x_1420_);
v_head_1429_ = lean_ctor_get(v_x_1421_, 0);
lean_inc(v_head_1429_);
v_tail_1430_ = lean_ctor_get(v_x_1421_, 1);
lean_inc(v_tail_1430_);
lean_dec_ref(v_x_1421_);
v___x_1431_ = lean_apply_4(v_h__3_1424_, v_head_1427_, v_tail_1428_, v_head_1429_, v_tail_1430_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___redArg(lean_object* v_inst_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
if (lean_obj_tag(v_x_1433_) == 0)
{
lean_object* v___x_1435_; 
lean_dec_ref(v_inst_1432_);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_x_1434_);
return v___x_1435_;
}
else
{
if (lean_obj_tag(v_x_1434_) == 0)
{
lean_object* v___x_1436_; 
lean_dec_ref(v_x_1433_);
lean_dec_ref(v_inst_1432_);
v___x_1436_ = lean_box(0);
return v___x_1436_;
}
else
{
lean_object* v_head_1437_; lean_object* v_tail_1438_; lean_object* v_head_1439_; lean_object* v_tail_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_head_1437_ = lean_ctor_get(v_x_1433_, 0);
lean_inc(v_head_1437_);
v_tail_1438_ = lean_ctor_get(v_x_1433_, 1);
lean_inc(v_tail_1438_);
lean_dec_ref(v_x_1433_);
v_head_1439_ = lean_ctor_get(v_x_1434_, 0);
lean_inc(v_head_1439_);
v_tail_1440_ = lean_ctor_get(v_x_1434_, 1);
lean_inc(v_tail_1440_);
lean_dec_ref(v_x_1434_);
lean_inc_ref(v_inst_1432_);
v___x_1441_ = lean_apply_2(v_inst_1432_, v_head_1437_, v_head_1439_);
v___x_1442_ = lean_unbox(v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v_tail_1440_);
lean_dec(v_tail_1438_);
lean_dec_ref(v_inst_1432_);
v___x_1443_ = lean_box(0);
return v___x_1443_;
}
else
{
v_x_1433_ = v_tail_1438_;
v_x_1434_ = v_tail_1440_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object* v_00_u03b1_1445_, lean_object* v_inst_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_List_isPrefixOf_x3f___redArg(v_inst_1446_, v_x_1447_, v_x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf___redArg(lean_object* v_inst_1450_, lean_object* v_l_u2081_1451_, lean_object* v_l_u2082_1452_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1453_ = l_List_reverse___redArg(v_l_u2081_1451_);
v___x_1454_ = l_List_reverse___redArg(v_l_u2082_1452_);
v___x_1455_ = l_List_isPrefixOf___redArg(v_inst_1450_, v___x_1453_, v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___redArg___boxed(lean_object* v_inst_1456_, lean_object* v_l_u2081_1457_, lean_object* v_l_u2082_1458_){
_start:
{
uint8_t v_res_1459_; lean_object* v_r_1460_; 
v_res_1459_ = l_List_isSuffixOf___redArg(v_inst_1456_, v_l_u2081_1457_, v_l_u2082_1458_);
v_r_1460_ = lean_box(v_res_1459_);
return v_r_1460_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf(lean_object* v_00_u03b1_1461_, lean_object* v_inst_1462_, lean_object* v_l_u2081_1463_, lean_object* v_l_u2082_1464_){
_start:
{
uint8_t v___x_1465_; 
v___x_1465_ = l_List_isSuffixOf___redArg(v_inst_1462_, v_l_u2081_1463_, v_l_u2082_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___boxed(lean_object* v_00_u03b1_1466_, lean_object* v_inst_1467_, lean_object* v_l_u2081_1468_, lean_object* v_l_u2082_1469_){
_start:
{
uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_res_1470_ = l_List_isSuffixOf(v_00_u03b1_1466_, v_inst_1467_, v_l_u2081_1468_, v_l_u2082_1469_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___redArg(lean_object* v_inst_1472_, lean_object* v_l_u2081_1473_, lean_object* v_l_u2082_1474_){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = l_List_reverse___redArg(v_l_u2081_1473_);
v___x_1476_ = l_List_reverse___redArg(v_l_u2082_1474_);
v___x_1477_ = l_List_isPrefixOf_x3f___redArg(v_inst_1472_, v___x_1475_, v___x_1476_);
if (lean_obj_tag(v___x_1477_) == 0)
{
return v___x_1477_;
}
else
{
lean_object* v_val_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_val_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_val_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = l_List_reverse___redArg(v_val_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1482_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object* v_00_u03b1_1487_, lean_object* v_inst_1488_, lean_object* v_l_u2081_1489_, lean_object* v_l_u2082_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_List_isSuffixOf_x3f___redArg(v_inst_1488_, v_l_u2081_1489_, v_l_u2082_1490_);
return v___x_1491_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0));
v___x_1510_ = l_String_toRawSubstring_x27(v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object* v_x_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
lean_inc(v_x_1522_);
v___x_1526_ = l_Lean_Syntax_isOfKind(v_x_1522_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec_ref(v_a_1523_);
lean_dec(v_x_1522_);
v___x_1527_ = lean_box(1);
v___x_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
lean_ctor_set(v___x_1528_, 1, v_a_1524_);
return v___x_1528_;
}
else
{
lean_object* v_quotContext_1529_; lean_object* v_currMacroScope_1530_; lean_object* v_ref_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_quotContext_1529_ = lean_ctor_get(v_a_1523_, 1);
lean_inc(v_quotContext_1529_);
v_currMacroScope_1530_ = lean_ctor_get(v_a_1523_, 2);
lean_inc(v_currMacroScope_1530_);
v_ref_1531_ = lean_ctor_get(v_a_1523_, 5);
lean_inc(v_ref_1531_);
lean_dec_ref(v_a_1523_);
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = l_Lean_Syntax_getArg(v_x_1522_, v___x_1532_);
v___x_1534_ = lean_unsigned_to_nat(2u);
v___x_1535_ = l_Lean_Syntax_getArg(v_x_1522_, v___x_1534_);
lean_dec(v_x_1522_);
v___x_1536_ = 0;
v___x_1537_ = l_Lean_SourceInfo_fromRef(v_ref_1531_, v___x_1536_);
lean_dec(v_ref_1531_);
v___x_1538_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1539_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
v___x_1540_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2));
v___x_1541_ = l_Lean_addMacroScope(v_quotContext_1529_, v___x_1540_, v_currMacroScope_1530_);
v___x_1542_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5));
lean_inc(v___x_1537_);
v___x_1543_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1537_);
lean_ctor_set(v___x_1543_, 1, v___x_1539_);
lean_ctor_set(v___x_1543_, 2, v___x_1541_);
lean_ctor_set(v___x_1543_, 3, v___x_1542_);
v___x_1544_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
lean_inc(v___x_1537_);
v___x_1545_ = l_Lean_Syntax_node2(v___x_1537_, v___x_1544_, v___x_1533_, v___x_1535_);
v___x_1546_ = l_Lean_Syntax_node2(v___x_1537_, v___x_1538_, v___x_1543_, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v_a_1524_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object* v_x_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1548_);
v___x_1552_ = l_Lean_Syntax_isOfKind(v_x_1548_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec(v_x_1548_);
v___x_1553_ = lean_box(0);
v___x_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v_a_1550_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = l_Lean_Syntax_getArg(v_x_1548_, v___x_1555_);
v___x_1557_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1556_);
v___x_1558_ = l_Lean_Syntax_isOfKind(v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec(v___x_1556_);
lean_dec(v_x_1548_);
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v_a_1550_);
return v___x_1560_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1561_ = lean_unsigned_to_nat(1u);
v___x_1562_ = l_Lean_Syntax_getArg(v_x_1548_, v___x_1561_);
lean_dec(v_x_1548_);
v___x_1563_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1562_);
v___x_1564_ = l_Lean_Syntax_matchesNull(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v___x_1562_);
lean_dec(v___x_1556_);
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v_a_1550_);
return v___x_1566_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v_ref_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1567_ = l_Lean_Syntax_getArg(v___x_1562_, v___x_1555_);
v___x_1568_ = l_Lean_Syntax_getArg(v___x_1562_, v___x_1561_);
lean_dec(v___x_1562_);
v_ref_1569_ = l_Lean_replaceRef(v___x_1556_, v_a_1549_);
lean_dec(v___x_1556_);
v___x_1570_ = 0;
v___x_1571_ = l_Lean_SourceInfo_fromRef(v_ref_1569_, v___x_1570_);
lean_dec(v_ref_1569_);
v___x_1572_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
v___x_1573_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__2));
lean_inc(v___x_1571_);
v___x_1574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1571_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = l_Lean_Syntax_node3(v___x_1571_, v___x_1572_, v___x_1567_, v___x_1574_, v___x_1568_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v_a_1550_);
return v___x_1576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object* v_x_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(v_x_1577_, v_a_1578_, v_a_1579_);
lean_dec(v_a_1578_);
return v_res_1580_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0));
v___x_1599_ = l_String_toRawSubstring_x27(v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object* v_x_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
lean_inc(v_x_1611_);
v___x_1615_ = l_Lean_Syntax_isOfKind(v_x_1611_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v_a_1612_);
lean_dec(v_x_1611_);
v___x_1616_ = lean_box(1);
v___x_1617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v_a_1613_);
return v___x_1617_;
}
else
{
lean_object* v_quotContext_1618_; lean_object* v_currMacroScope_1619_; lean_object* v_ref_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_quotContext_1618_ = lean_ctor_get(v_a_1612_, 1);
lean_inc(v_quotContext_1618_);
v_currMacroScope_1619_ = lean_ctor_get(v_a_1612_, 2);
lean_inc(v_currMacroScope_1619_);
v_ref_1620_ = lean_ctor_get(v_a_1612_, 5);
lean_inc(v_ref_1620_);
lean_dec_ref(v_a_1612_);
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = l_Lean_Syntax_getArg(v_x_1611_, v___x_1621_);
v___x_1623_ = lean_unsigned_to_nat(2u);
v___x_1624_ = l_Lean_Syntax_getArg(v_x_1611_, v___x_1623_);
lean_dec(v_x_1611_);
v___x_1625_ = 0;
v___x_1626_ = l_Lean_SourceInfo_fromRef(v_ref_1620_, v___x_1625_);
lean_dec(v_ref_1620_);
v___x_1627_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1628_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
v___x_1629_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2));
v___x_1630_ = l_Lean_addMacroScope(v_quotContext_1618_, v___x_1629_, v_currMacroScope_1619_);
v___x_1631_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5));
lean_inc(v___x_1626_);
v___x_1632_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1626_);
lean_ctor_set(v___x_1632_, 1, v___x_1628_);
lean_ctor_set(v___x_1632_, 2, v___x_1630_);
lean_ctor_set(v___x_1632_, 3, v___x_1631_);
v___x_1633_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
lean_inc(v___x_1626_);
v___x_1634_ = l_Lean_Syntax_node2(v___x_1626_, v___x_1633_, v___x_1622_, v___x_1624_);
v___x_1635_ = l_Lean_Syntax_node2(v___x_1626_, v___x_1627_, v___x_1632_, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v_a_1613_);
return v___x_1636_;
}
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
lean_dec_ref(v_l_u2082_1672_);
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
lean_object* v_head_1773_; lean_object* v_tail_1774_; uint8_t v___x_1775_; 
v_head_1773_ = lean_ctor_get(v_x_1771_, 0);
lean_inc(v_head_1773_);
v_tail_1774_ = lean_ctor_get(v_x_1771_, 1);
lean_inc(v_tail_1774_);
lean_dec_ref(v_x_1771_);
lean_inc(v_tail_1774_);
lean_inc_ref(v_inst_1770_);
v___x_1775_ = l_List_instDecidablePairwise___redArg(v_inst_1770_, v_tail_1774_);
if (v___x_1775_ == 0)
{
lean_dec(v_tail_1774_);
lean_dec(v_head_1773_);
lean_dec_ref(v_inst_1770_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_apply_1(v_inst_1770_, v_head_1773_);
v___x_1777_ = l_List_decidableBAll___redArg(v___x_1776_, v_tail_1774_);
return v___x_1777_;
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
LEAN_EXPORT lean_object* l_List_modify___redArg___lam__0(lean_object* v_f_1922_, lean_object* v___y_1923_){
_start:
{
if (lean_obj_tag(v___y_1923_) == 0)
{
lean_dec(v_f_1922_);
return v___y_1923_;
}
else
{
lean_object* v_head_1924_; lean_object* v_tail_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1933_; 
v_head_1924_ = lean_ctor_get(v___y_1923_, 0);
v_tail_1925_ = lean_ctor_get(v___y_1923_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___y_1923_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1927_ = v___y_1923_;
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_tail_1925_);
lean_inc(v_head_1924_);
lean_dec(v___y_1923_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1929_ = lean_apply_1(v_f_1922_, v_head_1924_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1929_);
v___x_1931_ = v___x_1927_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_tail_1925_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg(lean_object* v_l_1934_, lean_object* v_i_1935_, lean_object* v_f_1936_){
_start:
{
lean_object* v___f_1937_; lean_object* v___x_1938_; 
v___f_1937_ = lean_alloc_closure((void*)(l_List_modify___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1937_, 0, v_f_1936_);
v___x_1938_ = l_List_modifyTailIdx_go___redArg(v___f_1937_, v_i_1935_, v_l_1934_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg___boxed(lean_object* v_l_1939_, lean_object* v_i_1940_, lean_object* v_f_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_List_modify___redArg(v_l_1939_, v_i_1940_, v_f_1941_);
lean_dec(v_i_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_List_modify(lean_object* v_00_u03b1_1943_, lean_object* v_l_1944_, lean_object* v_i_1945_, lean_object* v_f_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_List_modify___redArg(v_l_1944_, v_i_1945_, v_f_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_List_modify___boxed(lean_object* v_00_u03b1_1948_, lean_object* v_l_1949_, lean_object* v_i_1950_, lean_object* v_f_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_List_modify(v_00_u03b1_1948_, v_l_1949_, v_i_1950_, v_f_1951_);
lean_dec(v_i_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object* v_inst_1953_, lean_object* v_a_1954_, lean_object* v_l_1955_){
_start:
{
uint8_t v___x_1956_; 
lean_inc(v_l_1955_);
lean_inc(v_a_1954_);
v___x_1956_ = l_List_elem___redArg(v_inst_1953_, v_a_1954_, v_l_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1957_, 0, v_a_1954_);
lean_ctor_set(v___x_1957_, 1, v_l_1955_);
return v___x_1957_;
}
else
{
lean_dec(v_a_1954_);
return v_l_1955_;
}
}
}
LEAN_EXPORT lean_object* l_List_insert(lean_object* v_00_u03b1_1958_, lean_object* v_inst_1959_, lean_object* v_a_1960_, lean_object* v_l_1961_){
_start:
{
uint8_t v___x_1962_; 
lean_inc(v_l_1961_);
lean_inc(v_a_1960_);
v___x_1962_ = l_List_elem___redArg(v_inst_1959_, v_a_1960_, v_l_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
v___x_1963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1963_, 0, v_a_1960_);
lean_ctor_set(v___x_1963_, 1, v_l_1961_);
return v___x_1963_;
}
else
{
lean_dec(v_a_1960_);
return v_l_1961_;
}
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___lam__0(lean_object* v_a_1964_, lean_object* v_tail_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_a_1964_);
lean_ctor_set(v___x_1966_, 1, v_tail_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg(lean_object* v_xs_1967_, lean_object* v_i_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v___f_1970_; lean_object* v___x_1971_; 
v___f_1970_ = lean_alloc_closure((void*)(l_List_insertIdx___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1970_, 0, v_a_1969_);
v___x_1971_ = l_List_modifyTailIdx_go___redArg(v___f_1970_, v_i_1968_, v_xs_1967_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___boxed(lean_object* v_xs_1972_, lean_object* v_i_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_List_insertIdx___redArg(v_xs_1972_, v_i_1973_, v_a_1974_);
lean_dec(v_i_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx(lean_object* v_00_u03b1_1976_, lean_object* v_xs_1977_, lean_object* v_i_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_List_insertIdx___redArg(v_xs_1977_, v_i_1978_, v_a_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___boxed(lean_object* v_00_u03b1_1981_, lean_object* v_xs_1982_, lean_object* v_i_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_List_insertIdx(v_00_u03b1_1981_, v_xs_1982_, v_i_1983_, v_a_1984_);
lean_dec(v_i_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_List_erase___redArg(lean_object* v_inst_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_){
_start:
{
if (lean_obj_tag(v_x_1987_) == 0)
{
lean_dec(v_x_1988_);
lean_dec_ref(v_inst_1986_);
return v_x_1987_;
}
else
{
lean_object* v_head_1989_; lean_object* v_tail_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2000_; 
v_head_1989_ = lean_ctor_get(v_x_1987_, 0);
v_tail_1990_ = lean_ctor_get(v_x_1987_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_x_1987_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1992_ = v_x_1987_;
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_tail_1990_);
lean_inc(v_head_1989_);
lean_dec(v_x_1987_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; uint8_t v___x_1995_; 
lean_inc_ref(v_inst_1986_);
lean_inc(v_x_1988_);
lean_inc(v_head_1989_);
v___x_1994_ = lean_apply_2(v_inst_1986_, v_head_1989_, v_x_1988_);
v___x_1995_ = lean_unbox(v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1996_ = l_List_erase___redArg(v_inst_1986_, v_tail_1990_, v_x_1988_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v___x_1996_);
v___x_1998_ = v___x_1992_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_head_1989_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
else
{
lean_del_object(v___x_1992_);
lean_dec(v_head_1989_);
lean_dec(v_x_1988_);
lean_dec_ref(v_inst_1986_);
return v_tail_1990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_erase(lean_object* v_00_u03b1_2001_, lean_object* v_inst_2002_, lean_object* v_x_2003_, lean_object* v_x_2004_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_List_erase___redArg(v_inst_2002_, v_x_2003_, v_x_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_h__1_2008_, lean_object* v_h__2_2009_){
_start:
{
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v___x_2010_; 
lean_dec(v_h__2_2009_);
v___x_2010_ = lean_apply_1(v_h__1_2008_, v_x_2007_);
return v___x_2010_;
}
else
{
lean_object* v_head_2011_; lean_object* v_tail_2012_; lean_object* v___x_2013_; 
lean_dec(v_h__1_2008_);
v_head_2011_ = lean_ctor_get(v_x_2006_, 0);
lean_inc(v_head_2011_);
v_tail_2012_ = lean_ctor_get(v_x_2006_, 1);
lean_inc(v_tail_2012_);
lean_dec_ref(v_x_2006_);
v___x_2013_ = lean_apply_3(v_h__2_2009_, v_head_2011_, v_tail_2012_, v_x_2007_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object* v_00_u03b1_2014_, lean_object* v_motive_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_, lean_object* v_h__1_2018_, lean_object* v_h__2_2019_){
_start:
{
if (lean_obj_tag(v_x_2016_) == 0)
{
lean_object* v___x_2020_; 
lean_dec(v_h__2_2019_);
v___x_2020_ = lean_apply_1(v_h__1_2018_, v_x_2017_);
return v___x_2020_;
}
else
{
lean_object* v_head_2021_; lean_object* v_tail_2022_; lean_object* v___x_2023_; 
lean_dec(v_h__1_2018_);
v_head_2021_ = lean_ctor_get(v_x_2016_, 0);
lean_inc(v_head_2021_);
v_tail_2022_ = lean_ctor_get(v_x_2016_, 1);
lean_inc(v_tail_2022_);
lean_dec_ref(v_x_2016_);
v___x_2023_ = lean_apply_3(v_h__2_2019_, v_head_2021_, v_tail_2022_, v_x_2017_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP___redArg(lean_object* v_p_2024_, lean_object* v_x_2025_){
_start:
{
if (lean_obj_tag(v_x_2025_) == 0)
{
lean_dec_ref(v_p_2024_);
return v_x_2025_;
}
else
{
lean_object* v_head_2026_; lean_object* v_tail_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2037_; 
v_head_2026_ = lean_ctor_get(v_x_2025_, 0);
v_tail_2027_ = lean_ctor_get(v_x_2025_, 1);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_x_2025_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2029_ = v_x_2025_;
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_tail_2027_);
lean_inc(v_head_2026_);
lean_dec(v_x_2025_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; uint8_t v___x_2032_; 
lean_inc_ref(v_p_2024_);
lean_inc(v_head_2026_);
v___x_2031_ = lean_apply_1(v_p_2024_, v_head_2026_);
v___x_2032_ = lean_unbox(v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2033_ = l_List_eraseP___redArg(v_p_2024_, v_tail_2027_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v___x_2033_);
v___x_2035_ = v___x_2029_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_head_2026_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
else
{
lean_del_object(v___x_2029_);
lean_dec(v_head_2026_);
lean_dec_ref(v_p_2024_);
return v_tail_2027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP(lean_object* v_00_u03b1_2038_, lean_object* v_p_2039_, lean_object* v_x_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_List_eraseP___redArg(v_p_2039_, v_x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg(lean_object* v_x_2042_, lean_object* v_x_2043_){
_start:
{
if (lean_obj_tag(v_x_2042_) == 0)
{
return v_x_2042_;
}
else
{
lean_object* v_head_2044_; lean_object* v_tail_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2057_; 
v_head_2044_ = lean_ctor_get(v_x_2042_, 0);
v_tail_2045_ = lean_ctor_get(v_x_2042_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_x_2042_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2047_ = v_x_2042_;
v_isShared_2048_ = v_isSharedCheck_2057_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_tail_2045_);
lean_inc(v_head_2044_);
lean_dec(v_x_2042_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2057_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v_zero_2049_; uint8_t v_isZero_2050_; 
v_zero_2049_ = lean_unsigned_to_nat(0u);
v_isZero_2050_ = lean_nat_dec_eq(v_x_2043_, v_zero_2049_);
if (v_isZero_2050_ == 1)
{
lean_del_object(v___x_2047_);
lean_dec(v_head_2044_);
return v_tail_2045_;
}
else
{
lean_object* v_one_2051_; lean_object* v_n_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v_one_2051_ = lean_unsigned_to_nat(1u);
v_n_2052_ = lean_nat_sub(v_x_2043_, v_one_2051_);
v___x_2053_ = l_List_eraseIdx___redArg(v_tail_2045_, v_n_2052_);
lean_dec(v_n_2052_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v___x_2053_);
v___x_2055_ = v___x_2047_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_head_2044_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg___boxed(lean_object* v_x_2058_, lean_object* v_x_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_List_eraseIdx___redArg(v_x_2058_, v_x_2059_);
lean_dec(v_x_2059_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object* v_00_u03b1_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_List_eraseIdx___redArg(v_x_2062_, v_x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___boxed(lean_object* v_00_u03b1_2065_, lean_object* v_x_2066_, lean_object* v_x_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_List_eraseIdx(v_00_u03b1_2065_, v_x_2066_, v_x_2067_);
lean_dec(v_x_2067_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object* v_p_2069_, lean_object* v_x_2070_){
_start:
{
if (lean_obj_tag(v_x_2070_) == 0)
{
lean_object* v___x_2071_; 
lean_dec_ref(v_p_2069_);
v___x_2071_ = lean_box(0);
return v___x_2071_;
}
else
{
lean_object* v_head_2072_; lean_object* v_tail_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_head_2072_ = lean_ctor_get(v_x_2070_, 0);
lean_inc(v_head_2072_);
v_tail_2073_ = lean_ctor_get(v_x_2070_, 1);
lean_inc(v_tail_2073_);
lean_dec_ref(v_x_2070_);
lean_inc_ref(v_p_2069_);
lean_inc(v_head_2072_);
v___x_2074_ = lean_apply_1(v_p_2069_, v_head_2072_);
v___x_2075_ = lean_unbox(v___x_2074_);
if (v___x_2075_ == 0)
{
lean_dec(v_head_2072_);
v_x_2070_ = v_tail_2073_;
goto _start;
}
else
{
lean_object* v___x_2077_; 
lean_dec(v_tail_2073_);
lean_dec_ref(v_p_2069_);
v___x_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2077_, 0, v_head_2072_);
return v___x_2077_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object* v_00_u03b1_2078_, lean_object* v_p_2079_, lean_object* v_x_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_List_find_x3f___redArg(v_p_2079_, v_x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object* v_f_2082_, lean_object* v_x_2083_){
_start:
{
if (lean_obj_tag(v_x_2083_) == 0)
{
lean_object* v___x_2084_; 
lean_dec_ref(v_f_2082_);
v___x_2084_ = lean_box(0);
return v___x_2084_;
}
else
{
lean_object* v_head_2085_; lean_object* v_tail_2086_; lean_object* v___x_2087_; 
v_head_2085_ = lean_ctor_get(v_x_2083_, 0);
lean_inc(v_head_2085_);
v_tail_2086_ = lean_ctor_get(v_x_2083_, 1);
lean_inc(v_tail_2086_);
lean_dec_ref(v_x_2083_);
lean_inc_ref(v_f_2082_);
v___x_2087_ = lean_apply_1(v_f_2082_, v_head_2085_);
if (lean_obj_tag(v___x_2087_) == 0)
{
v_x_2083_ = v_tail_2086_;
goto _start;
}
else
{
lean_dec(v_tail_2086_);
lean_dec_ref(v_f_2082_);
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object* v_00_u03b1_2089_, lean_object* v_00_u03b2_2090_, lean_object* v_f_2091_, lean_object* v_x_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_List_findSome_x3f___redArg(v_f_2091_, v_x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f___redArg(lean_object* v_p_2094_, lean_object* v_x_2095_){
_start:
{
if (lean_obj_tag(v_x_2095_) == 0)
{
lean_object* v___x_2096_; 
lean_dec_ref(v_p_2094_);
v___x_2096_ = lean_box(0);
return v___x_2096_;
}
else
{
lean_object* v_head_2097_; lean_object* v_tail_2098_; lean_object* v___x_2099_; 
v_head_2097_ = lean_ctor_get(v_x_2095_, 0);
lean_inc(v_head_2097_);
v_tail_2098_ = lean_ctor_get(v_x_2095_, 1);
lean_inc(v_tail_2098_);
lean_dec_ref(v_x_2095_);
lean_inc_ref(v_p_2094_);
v___x_2099_ = l_List_findRev_x3f___redArg(v_p_2094_, v_tail_2098_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
lean_inc(v_head_2097_);
v___x_2100_ = lean_apply_1(v_p_2094_, v_head_2097_);
v___x_2101_ = lean_unbox(v___x_2100_);
if (v___x_2101_ == 0)
{
lean_dec(v_head_2097_);
return v___x_2099_;
}
else
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v_head_2097_);
return v___x_2102_;
}
}
else
{
lean_dec(v_head_2097_);
lean_dec_ref(v_p_2094_);
return v___x_2099_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f(lean_object* v_00_u03b1_2103_, lean_object* v_p_2104_, lean_object* v_x_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_List_findRev_x3f___redArg(v_p_2104_, v_x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f___redArg(lean_object* v_f_2107_, lean_object* v_x_2108_){
_start:
{
if (lean_obj_tag(v_x_2108_) == 0)
{
lean_object* v___x_2109_; 
lean_dec_ref(v_f_2107_);
v___x_2109_ = lean_box(0);
return v___x_2109_;
}
else
{
lean_object* v_head_2110_; lean_object* v_tail_2111_; lean_object* v___x_2112_; 
v_head_2110_ = lean_ctor_get(v_x_2108_, 0);
lean_inc(v_head_2110_);
v_tail_2111_ = lean_ctor_get(v_x_2108_, 1);
lean_inc(v_tail_2111_);
lean_dec_ref(v_x_2108_);
lean_inc_ref(v_f_2107_);
v___x_2112_ = l_List_findSomeRev_x3f___redArg(v_f_2107_, v_tail_2111_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_apply_1(v_f_2107_, v_head_2110_);
return v___x_2113_;
}
else
{
lean_dec(v_head_2110_);
lean_dec_ref(v_f_2107_);
return v___x_2112_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f(lean_object* v_00_u03b1_2114_, lean_object* v_00_u03b2_2115_, lean_object* v_f_2116_, lean_object* v_x_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_List_findSomeRev_x3f___redArg(v_f_2116_, v_x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___redArg(lean_object* v_p_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
if (lean_obj_tag(v_a_2120_) == 0)
{
lean_dec_ref(v_p_2119_);
return v_a_2121_;
}
else
{
lean_object* v_head_2122_; lean_object* v_tail_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v_head_2122_ = lean_ctor_get(v_a_2120_, 0);
lean_inc(v_head_2122_);
v_tail_2123_ = lean_ctor_get(v_a_2120_, 1);
lean_inc(v_tail_2123_);
lean_dec_ref(v_a_2120_);
lean_inc_ref(v_p_2119_);
v___x_2124_ = lean_apply_1(v_p_2119_, v_head_2122_);
v___x_2125_ = lean_unbox(v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_unsigned_to_nat(1u);
v___x_2127_ = lean_nat_add(v_a_2121_, v___x_2126_);
lean_dec(v_a_2121_);
v_a_2120_ = v_tail_2123_;
v_a_2121_ = v___x_2127_;
goto _start;
}
else
{
lean_dec(v_tail_2123_);
lean_dec_ref(v_p_2119_);
return v_a_2121_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object* v_00_u03b1_2129_, lean_object* v_p_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_List_findIdx_go___redArg(v_p_2130_, v_a_2131_, v_a_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx___redArg(lean_object* v_p_2134_, lean_object* v_l_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = l_List_findIdx_go___redArg(v_p_2134_, v_l_2135_, v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx(lean_object* v_00_u03b1_2138_, lean_object* v_p_2139_, lean_object* v_l_2140_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = l_List_findIdx_go___redArg(v_p_2139_, v_l_2140_, v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT uint8_t l_List_idxOf___redArg___lam__0(lean_object* v_inst_2143_, lean_object* v_a_2144_, lean_object* v_x_2145_){
_start:
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = lean_apply_2(v_inst_2143_, v_x_2145_, v_a_2144_);
v___x_2147_ = lean_unbox(v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg___lam__0___boxed(lean_object* v_inst_2148_, lean_object* v_a_2149_, lean_object* v_x_2150_){
_start:
{
uint8_t v_res_2151_; lean_object* v_r_2152_; 
v_res_2151_ = l_List_idxOf___redArg___lam__0(v_inst_2148_, v_a_2149_, v_x_2150_);
v_r_2152_ = lean_box(v_res_2151_);
return v_r_2152_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg(lean_object* v_inst_2153_, lean_object* v_a_2154_, lean_object* v_l_2155_){
_start:
{
lean_object* v___f_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___f_2156_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2156_, 0, v_inst_2153_);
lean_closure_set(v___f_2156_, 1, v_a_2154_);
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = l_List_findIdx_go___redArg(v___f_2156_, v_l_2155_, v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf(lean_object* v_00_u03b1_2159_, lean_object* v_inst_2160_, lean_object* v_a_2161_, lean_object* v_l_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_List_idxOf___redArg(v_inst_2160_, v_a_2161_, v_l_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___redArg(lean_object* v_p_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
if (lean_obj_tag(v_a_2165_) == 0)
{
lean_object* v___x_2167_; 
lean_dec(v_a_2166_);
lean_dec_ref(v_p_2164_);
v___x_2167_ = lean_box(0);
return v___x_2167_;
}
else
{
lean_object* v_head_2168_; lean_object* v_tail_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_head_2168_ = lean_ctor_get(v_a_2165_, 0);
lean_inc(v_head_2168_);
v_tail_2169_ = lean_ctor_get(v_a_2165_, 1);
lean_inc(v_tail_2169_);
lean_dec_ref(v_a_2165_);
lean_inc_ref(v_p_2164_);
v___x_2170_ = lean_apply_1(v_p_2164_, v_head_2168_);
v___x_2171_ = lean_unbox(v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_unsigned_to_nat(1u);
v___x_2173_ = lean_nat_add(v_a_2166_, v___x_2172_);
lean_dec(v_a_2166_);
v_a_2165_ = v_tail_2169_;
v_a_2166_ = v___x_2173_;
goto _start;
}
else
{
lean_object* v___x_2175_; 
lean_dec(v_tail_2169_);
lean_dec_ref(v_p_2164_);
v___x_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2175_, 0, v_a_2166_);
return v___x_2175_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go(lean_object* v_00_u03b1_2176_, lean_object* v_p_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_List_findIdx_x3f_go___redArg(v_p_2177_, v_a_2178_, v_a_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f___redArg(lean_object* v_p_2181_, lean_object* v_l_2182_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_unsigned_to_nat(0u);
v___x_2184_ = l_List_findIdx_x3f_go___redArg(v_p_2181_, v_l_2182_, v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object* v_00_u03b1_2185_, lean_object* v_p_2186_, lean_object* v_l_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_List_findIdx_x3f___redArg(v_p_2186_, v_l_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f___redArg(lean_object* v_inst_2189_, lean_object* v_a_2190_, lean_object* v_l_2191_){
_start:
{
lean_object* v___f_2192_; lean_object* v___x_2193_; 
v___f_2192_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2192_, 0, v_inst_2189_);
lean_closure_set(v___f_2192_, 1, v_a_2190_);
v___x_2193_ = l_List_findIdx_x3f___redArg(v___f_2192_, v_l_2191_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f(lean_object* v_00_u03b1_2194_, lean_object* v_inst_2195_, lean_object* v_a_2196_, lean_object* v_l_2197_){
_start:
{
lean_object* v___f_2198_; lean_object* v___x_2199_; 
v___f_2198_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2198_, 0, v_inst_2195_);
lean_closure_set(v___f_2198_, 1, v_a_2196_);
v___x_2199_ = l_List_findIdx_x3f___redArg(v___f_2198_, v_l_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___redArg(lean_object* v_p_2200_, lean_object* v_l_x27_2201_, lean_object* v_i_2202_){
_start:
{
if (lean_obj_tag(v_l_x27_2201_) == 0)
{
lean_object* v___x_2203_; 
lean_dec(v_i_2202_);
lean_dec_ref(v_p_2200_);
v___x_2203_ = lean_box(0);
return v___x_2203_;
}
else
{
lean_object* v_head_2204_; lean_object* v_tail_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v_head_2204_ = lean_ctor_get(v_l_x27_2201_, 0);
lean_inc(v_head_2204_);
v_tail_2205_ = lean_ctor_get(v_l_x27_2201_, 1);
lean_inc(v_tail_2205_);
lean_dec_ref(v_l_x27_2201_);
lean_inc_ref(v_p_2200_);
v___x_2206_ = lean_apply_1(v_p_2200_, v_head_2204_);
v___x_2207_ = lean_unbox(v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_unsigned_to_nat(1u);
v___x_2209_ = lean_nat_add(v_i_2202_, v___x_2208_);
lean_dec(v_i_2202_);
v_l_x27_2201_ = v_tail_2205_;
v_i_2202_ = v___x_2209_;
goto _start;
}
else
{
lean_object* v___x_2211_; 
lean_dec(v_tail_2205_);
lean_dec_ref(v_p_2200_);
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_i_2202_);
return v___x_2211_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go(lean_object* v_00_u03b1_2212_, lean_object* v_p_2213_, lean_object* v_l_2214_, lean_object* v_l_x27_2215_, lean_object* v_i_2216_, lean_object* v_h_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_List_findFinIdx_x3f_go___redArg(v_p_2213_, v_l_x27_2215_, v_i_2216_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___boxed(lean_object* v_00_u03b1_2219_, lean_object* v_p_2220_, lean_object* v_l_2221_, lean_object* v_l_x27_2222_, lean_object* v_i_2223_, lean_object* v_h_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_List_findFinIdx_x3f_go(v_00_u03b1_2219_, v_p_2220_, v_l_2221_, v_l_x27_2222_, v_i_2223_, v_h_2224_);
lean_dec(v_l_2221_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f___redArg(lean_object* v_p_2226_, lean_object* v_l_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = l_List_findFinIdx_x3f_go___redArg(v_p_2226_, v_l_2227_, v___x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f(lean_object* v_00_u03b1_2230_, lean_object* v_p_2231_, lean_object* v_l_2232_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = l_List_findFinIdx_x3f_go___redArg(v_p_2231_, v_l_2232_, v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f___redArg(lean_object* v_inst_2235_, lean_object* v_a_2236_, lean_object* v_l_2237_){
_start:
{
lean_object* v___f_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___f_2238_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2238_, 0, v_inst_2235_);
lean_closure_set(v___f_2238_, 1, v_a_2236_);
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = l_List_findFinIdx_x3f_go___redArg(v___f_2238_, v_l_2237_, v___x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f(lean_object* v_00_u03b1_2241_, lean_object* v_inst_2242_, lean_object* v_a_2243_, lean_object* v_l_2244_){
_start:
{
lean_object* v___f_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___f_2245_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2245_, 0, v_inst_2242_);
lean_closure_set(v___f_2245_, 1, v_a_2243_);
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = l_List_findFinIdx_x3f_go___redArg(v___f_2245_, v_l_2244_, v___x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___redArg(lean_object* v_p_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
if (lean_obj_tag(v_a_2249_) == 0)
{
lean_dec_ref(v_p_2248_);
return v_a_2250_;
}
else
{
lean_object* v_head_2251_; lean_object* v_tail_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v_head_2251_ = lean_ctor_get(v_a_2249_, 0);
lean_inc(v_head_2251_);
v_tail_2252_ = lean_ctor_get(v_a_2249_, 1);
lean_inc(v_tail_2252_);
lean_dec_ref(v_a_2249_);
lean_inc_ref(v_p_2248_);
v___x_2253_ = lean_apply_1(v_p_2248_, v_head_2251_);
v___x_2254_ = lean_unbox(v___x_2253_);
if (v___x_2254_ == 0)
{
v_a_2249_ = v_tail_2252_;
goto _start;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_nat_add(v_a_2250_, v___x_2256_);
lean_dec(v_a_2250_);
v_a_2249_ = v_tail_2252_;
v_a_2250_ = v___x_2257_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go(lean_object* v_00_u03b1_2259_, lean_object* v_p_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_List_countP_go___redArg(v_p_2260_, v_a_2261_, v_a_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_List_countP___redArg(lean_object* v_p_2264_, lean_object* v_l_2265_){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = l_List_countP_go___redArg(v_p_2264_, v_l_2265_, v___x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_List_countP(lean_object* v_00_u03b1_2268_, lean_object* v_p_2269_, lean_object* v_l_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = l_List_countP_go___redArg(v_p_2269_, v_l_2270_, v___x_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_List_count___redArg(lean_object* v_inst_2273_, lean_object* v_a_2274_, lean_object* v_l_2275_){
_start:
{
lean_object* v___f_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___f_2276_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2276_, 0, v_inst_2273_);
lean_closure_set(v___f_2276_, 1, v_a_2274_);
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = l_List_countP_go___redArg(v___f_2276_, v_l_2275_, v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_List_count(lean_object* v_00_u03b1_2279_, lean_object* v_inst_2280_, lean_object* v_a_2281_, lean_object* v_l_2282_){
_start:
{
lean_object* v___f_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___f_2283_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2283_, 0, v_inst_2280_);
lean_closure_set(v___f_2283_, 1, v_a_2281_);
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2285_ = l_List_countP_go___redArg(v___f_2283_, v_l_2282_, v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___redArg(lean_object* v_inst_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_){
_start:
{
if (lean_obj_tag(v_x_2288_) == 0)
{
lean_object* v___x_2289_; 
lean_dec(v_x_2287_);
lean_dec_ref(v_inst_2286_);
v___x_2289_ = lean_box(0);
return v___x_2289_;
}
else
{
lean_object* v_head_2290_; lean_object* v_tail_2291_; lean_object* v_fst_2292_; lean_object* v_snd_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_head_2290_ = lean_ctor_get(v_x_2288_, 0);
lean_inc(v_head_2290_);
v_tail_2291_ = lean_ctor_get(v_x_2288_, 1);
lean_inc(v_tail_2291_);
lean_dec_ref(v_x_2288_);
v_fst_2292_ = lean_ctor_get(v_head_2290_, 0);
lean_inc(v_fst_2292_);
v_snd_2293_ = lean_ctor_get(v_head_2290_, 1);
lean_inc(v_snd_2293_);
lean_dec(v_head_2290_);
lean_inc_ref(v_inst_2286_);
lean_inc(v_x_2287_);
v___x_2294_ = lean_apply_2(v_inst_2286_, v_x_2287_, v_fst_2292_);
v___x_2295_ = lean_unbox(v___x_2294_);
if (v___x_2295_ == 0)
{
lean_dec(v_snd_2293_);
v_x_2288_ = v_tail_2291_;
goto _start;
}
else
{
lean_object* v___x_2297_; 
lean_dec(v_tail_2291_);
lean_dec(v_x_2287_);
lean_dec_ref(v_inst_2286_);
v___x_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2297_, 0, v_snd_2293_);
return v___x_2297_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup(lean_object* v_00_u03b1_2298_, lean_object* v_00_u03b2_2299_, lean_object* v_inst_2300_, lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_List_lookup___redArg(v_inst_2300_, v_x_2301_, v_x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0));
v___x_2322_ = l_String_toRawSubstring_x27(v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object* v_x_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
lean_inc(v_x_2342_);
v___x_2346_ = l_Lean_Syntax_isOfKind(v_x_2342_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec_ref(v_a_2343_);
lean_dec(v_x_2342_);
v___x_2347_ = lean_box(1);
v___x_2348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v_a_2344_);
return v___x_2348_;
}
else
{
lean_object* v_quotContext_2349_; lean_object* v_currMacroScope_2350_; lean_object* v_ref_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_quotContext_2349_ = lean_ctor_get(v_a_2343_, 1);
lean_inc(v_quotContext_2349_);
v_currMacroScope_2350_ = lean_ctor_get(v_a_2343_, 2);
lean_inc(v_currMacroScope_2350_);
v_ref_2351_ = lean_ctor_get(v_a_2343_, 5);
lean_inc(v_ref_2351_);
lean_dec_ref(v_a_2343_);
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = l_Lean_Syntax_getArg(v_x_2342_, v___x_2352_);
v___x_2354_ = lean_unsigned_to_nat(2u);
v___x_2355_ = l_Lean_Syntax_getArg(v_x_2342_, v___x_2354_);
lean_dec(v_x_2342_);
v___x_2356_ = 0;
v___x_2357_ = l_Lean_SourceInfo_fromRef(v_ref_2351_, v___x_2356_);
lean_dec(v_ref_2351_);
v___x_2358_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_2359_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
v___x_2360_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2));
v___x_2361_ = l_Lean_addMacroScope(v_quotContext_2349_, v___x_2360_, v_currMacroScope_2350_);
v___x_2362_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8));
lean_inc(v___x_2357_);
v___x_2363_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2357_);
lean_ctor_set(v___x_2363_, 1, v___x_2359_);
lean_ctor_set(v___x_2363_, 2, v___x_2361_);
lean_ctor_set(v___x_2363_, 3, v___x_2362_);
v___x_2364_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
lean_inc(v___x_2357_);
v___x_2365_ = l_Lean_Syntax_node2(v___x_2357_, v___x_2364_, v___x_2353_, v___x_2355_);
v___x_2366_ = l_Lean_Syntax_node2(v___x_2357_, v___x_2358_, v___x_2363_, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_ctor_set(v___x_2367_, 1, v_a_2344_);
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object* v_x_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2371_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_2368_);
v___x_2372_ = l_Lean_Syntax_isOfKind(v_x_2368_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec(v_x_2368_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v_a_2370_);
return v___x_2374_;
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2375_ = lean_unsigned_to_nat(0u);
v___x_2376_ = l_Lean_Syntax_getArg(v_x_2368_, v___x_2375_);
v___x_2377_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_2376_);
v___x_2378_ = l_Lean_Syntax_isOfKind(v___x_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_dec(v___x_2376_);
lean_dec(v_x_2368_);
v___x_2379_ = lean_box(0);
v___x_2380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v_a_2370_);
return v___x_2380_;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v___x_2381_ = lean_unsigned_to_nat(1u);
v___x_2382_ = l_Lean_Syntax_getArg(v_x_2368_, v___x_2381_);
lean_dec(v_x_2368_);
v___x_2383_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2382_);
v___x_2384_ = l_Lean_Syntax_matchesNull(v___x_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec(v___x_2382_);
lean_dec(v___x_2376_);
v___x_2385_ = lean_box(0);
v___x_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v_a_2370_);
return v___x_2386_;
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v_ref_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2387_ = l_Lean_Syntax_getArg(v___x_2382_, v___x_2375_);
v___x_2388_ = l_Lean_Syntax_getArg(v___x_2382_, v___x_2381_);
lean_dec(v___x_2382_);
v_ref_2389_ = l_Lean_replaceRef(v___x_2376_, v_a_2369_);
lean_dec(v___x_2376_);
v___x_2390_ = 0;
v___x_2391_ = l_Lean_SourceInfo_fromRef(v_ref_2389_, v___x_2390_);
lean_dec(v_ref_2389_);
v___x_2392_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
v___x_2393_ = ((lean_object*)(l_List_term___x7e___00__closed__2));
lean_inc(v___x_2391_);
v___x_2394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2391_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Lean_Syntax_node3(v___x_2391_, v___x_2392_, v___x_2387_, v___x_2394_, v___x_2388_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v_a_2370_);
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object* v_x_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(v_x_2397_, v_a_2398_, v_a_2399_);
lean_dec(v_a_2398_);
return v_res_2400_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm___redArg(lean_object* v_inst_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
if (lean_obj_tag(v_x_2402_) == 0)
{
uint8_t v___x_2404_; 
lean_dec_ref(v_inst_2401_);
v___x_2404_ = l_List_isEmpty___redArg(v_x_2403_);
lean_dec(v_x_2403_);
return v___x_2404_;
}
else
{
lean_object* v_head_2405_; lean_object* v_tail_2406_; uint8_t v___x_2407_; 
v_head_2405_ = lean_ctor_get(v_x_2402_, 0);
lean_inc(v_head_2405_);
v_tail_2406_ = lean_ctor_get(v_x_2402_, 1);
lean_inc(v_tail_2406_);
lean_dec_ref(v_x_2402_);
lean_inc(v_x_2403_);
lean_inc(v_head_2405_);
lean_inc_ref(v_inst_2401_);
v___x_2407_ = l_List_elem___redArg(v_inst_2401_, v_head_2405_, v_x_2403_);
if (v___x_2407_ == 0)
{
lean_dec(v_tail_2406_);
lean_dec(v_head_2405_);
lean_dec(v_x_2403_);
lean_dec_ref(v_inst_2401_);
return v___x_2407_;
}
else
{
lean_object* v___x_2408_; 
lean_inc_ref(v_inst_2401_);
v___x_2408_ = l_List_erase___redArg(v_inst_2401_, v_x_2403_, v_head_2405_);
v_x_2402_ = v_tail_2406_;
v_x_2403_ = v___x_2408_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPerm___redArg___boxed(lean_object* v_inst_2410_, lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_res_2413_ = l_List_isPerm___redArg(v_inst_2410_, v_x_2411_, v_x_2412_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm(lean_object* v_00_u03b1_2415_, lean_object* v_inst_2416_, lean_object* v_x_2417_, lean_object* v_x_2418_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = l_List_isPerm___redArg(v_inst_2416_, v_x_2417_, v_x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_List_isPerm___boxed(lean_object* v_00_u03b1_2420_, lean_object* v_inst_2421_, lean_object* v_x_2422_, lean_object* v_x_2423_){
_start:
{
uint8_t v_res_2424_; lean_object* v_r_2425_; 
v_res_2424_ = l_List_isPerm(v_00_u03b1_2420_, v_inst_2421_, v_x_2422_, v_x_2423_);
v_r_2425_ = lean_box(v_res_2424_);
return v_r_2425_;
}
}
LEAN_EXPORT uint8_t l_List_any___redArg(lean_object* v_x_2426_, lean_object* v_x_2427_){
_start:
{
if (lean_obj_tag(v_x_2426_) == 0)
{
uint8_t v___x_2428_; 
lean_dec_ref(v_x_2427_);
v___x_2428_ = 0;
return v___x_2428_;
}
else
{
lean_object* v_head_2429_; lean_object* v_tail_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v_head_2429_ = lean_ctor_get(v_x_2426_, 0);
lean_inc(v_head_2429_);
v_tail_2430_ = lean_ctor_get(v_x_2426_, 1);
lean_inc(v_tail_2430_);
lean_dec_ref(v_x_2426_);
lean_inc_ref(v_x_2427_);
v___x_2431_ = lean_apply_1(v_x_2427_, v_head_2429_);
v___x_2432_ = lean_unbox(v___x_2431_);
if (v___x_2432_ == 0)
{
v_x_2426_ = v_tail_2430_;
goto _start;
}
else
{
uint8_t v___x_2434_; 
lean_dec(v_tail_2430_);
lean_dec_ref(v_x_2427_);
v___x_2434_ = lean_unbox(v___x_2431_);
return v___x_2434_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___redArg___boxed(lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
uint8_t v_res_2437_; lean_object* v_r_2438_; 
v_res_2437_ = l_List_any___redArg(v_x_2435_, v_x_2436_);
v_r_2438_ = lean_box(v_res_2437_);
return v_r_2438_;
}
}
LEAN_EXPORT uint8_t l_List_any(lean_object* v_00_u03b1_2439_, lean_object* v_x_2440_, lean_object* v_x_2441_){
_start:
{
uint8_t v___x_2442_; 
v___x_2442_ = l_List_any___redArg(v_x_2440_, v_x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_List_any___boxed(lean_object* v_00_u03b1_2443_, lean_object* v_x_2444_, lean_object* v_x_2445_){
_start:
{
uint8_t v_res_2446_; lean_object* v_r_2447_; 
v_res_2446_ = l_List_any(v_00_u03b1_2443_, v_x_2444_, v_x_2445_);
v_r_2447_ = lean_box(v_res_2446_);
return v_r_2447_;
}
}
LEAN_EXPORT uint8_t l_List_all___redArg(lean_object* v_x_2448_, lean_object* v_x_2449_){
_start:
{
if (lean_obj_tag(v_x_2448_) == 0)
{
uint8_t v___x_2450_; 
lean_dec_ref(v_x_2449_);
v___x_2450_ = 1;
return v___x_2450_;
}
else
{
lean_object* v_head_2451_; lean_object* v_tail_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v_head_2451_ = lean_ctor_get(v_x_2448_, 0);
lean_inc(v_head_2451_);
v_tail_2452_ = lean_ctor_get(v_x_2448_, 1);
lean_inc(v_tail_2452_);
lean_dec_ref(v_x_2448_);
lean_inc_ref(v_x_2449_);
v___x_2453_ = lean_apply_1(v_x_2449_, v_head_2451_);
v___x_2454_ = lean_unbox(v___x_2453_);
if (v___x_2454_ == 0)
{
uint8_t v___x_2455_; 
lean_dec(v_tail_2452_);
lean_dec_ref(v_x_2449_);
v___x_2455_ = lean_unbox(v___x_2453_);
return v___x_2455_;
}
else
{
v_x_2448_ = v_tail_2452_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___redArg___boxed(lean_object* v_x_2457_, lean_object* v_x_2458_){
_start:
{
uint8_t v_res_2459_; lean_object* v_r_2460_; 
v_res_2459_ = l_List_all___redArg(v_x_2457_, v_x_2458_);
v_r_2460_ = lean_box(v_res_2459_);
return v_r_2460_;
}
}
LEAN_EXPORT uint8_t l_List_all(lean_object* v_00_u03b1_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_){
_start:
{
uint8_t v___x_2464_; 
v___x_2464_ = l_List_all___redArg(v_x_2462_, v_x_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_List_all___boxed(lean_object* v_00_u03b1_2465_, lean_object* v_x_2466_, lean_object* v_x_2467_){
_start:
{
uint8_t v_res_2468_; lean_object* v_r_2469_; 
v_res_2468_ = l_List_all(v_00_u03b1_2465_, v_x_2466_, v_x_2467_);
v_r_2469_ = lean_box(v_res_2468_);
return v_r_2469_;
}
}
LEAN_EXPORT uint8_t l_List_or___lam__0(uint8_t v___y_2470_){
_start:
{
return v___y_2470_;
}
}
LEAN_EXPORT lean_object* l_List_or___lam__0___boxed(lean_object* v___y_2471_){
_start:
{
uint8_t v___y_7__boxed_2472_; uint8_t v_res_2473_; lean_object* v_r_2474_; 
v___y_7__boxed_2472_ = lean_unbox(v___y_2471_);
v_res_2473_ = l_List_or___lam__0(v___y_7__boxed_2472_);
v_r_2474_ = lean_box(v_res_2473_);
return v_r_2474_;
}
}
LEAN_EXPORT uint8_t l_List_or(lean_object* v_bs_2476_){
_start:
{
lean_object* v___f_2477_; uint8_t v___x_2478_; 
v___f_2477_ = ((lean_object*)(l_List_or___closed__0));
v___x_2478_ = l_List_any___redArg(v_bs_2476_, v___f_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object* v_bs_2479_){
_start:
{
uint8_t v_res_2480_; lean_object* v_r_2481_; 
v_res_2480_ = l_List_or(v_bs_2479_);
v_r_2481_ = lean_box(v_res_2480_);
return v_r_2481_;
}
}
LEAN_EXPORT uint8_t l_List_and(lean_object* v_bs_2482_){
_start:
{
lean_object* v___f_2483_; uint8_t v___x_2484_; 
v___f_2483_ = ((lean_object*)(l_List_or___closed__0));
v___x_2484_ = l_List_all___redArg(v_bs_2482_, v___f_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object* v_bs_2485_){
_start:
{
uint8_t v_res_2486_; lean_object* v_r_2487_; 
v_res_2486_ = l_List_and(v_bs_2485_);
v_r_2487_ = lean_box(v_res_2486_);
return v_r_2487_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___redArg(lean_object* v_f_2488_, lean_object* v_x_2489_, lean_object* v_x_2490_){
_start:
{
if (lean_obj_tag(v_x_2489_) == 0)
{
lean_object* v___x_2491_; 
lean_dec(v_x_2490_);
lean_dec(v_f_2488_);
v___x_2491_ = lean_box(0);
return v___x_2491_;
}
else
{
if (lean_obj_tag(v_x_2490_) == 0)
{
lean_object* v___x_2492_; 
lean_dec_ref(v_x_2489_);
lean_dec(v_f_2488_);
v___x_2492_ = lean_box(0);
return v___x_2492_;
}
else
{
lean_object* v_head_2493_; lean_object* v_tail_2494_; lean_object* v_head_2495_; lean_object* v_tail_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2505_; 
v_head_2493_ = lean_ctor_get(v_x_2489_, 0);
lean_inc(v_head_2493_);
v_tail_2494_ = lean_ctor_get(v_x_2489_, 1);
lean_inc(v_tail_2494_);
lean_dec_ref(v_x_2489_);
v_head_2495_ = lean_ctor_get(v_x_2490_, 0);
v_tail_2496_ = lean_ctor_get(v_x_2490_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_x_2490_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2498_ = v_x_2490_;
v_isShared_2499_ = v_isSharedCheck_2505_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_tail_2496_);
lean_inc(v_head_2495_);
lean_dec(v_x_2490_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2505_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
lean_inc(v_f_2488_);
v___x_2500_ = lean_apply_2(v_f_2488_, v_head_2493_, v_head_2495_);
v___x_2501_ = l_List_zipWith___redArg(v_f_2488_, v_tail_2494_, v_tail_2496_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v___x_2501_);
lean_ctor_set(v___x_2498_, 0, v___x_2500_);
v___x_2503_ = v___x_2498_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith(lean_object* v_00_u03b1_2506_, lean_object* v_00_u03b2_2507_, lean_object* v_00_u03b3_2508_, lean_object* v_f_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_List_zipWith___redArg(v_f_2509_, v_x_2510_, v_x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object* v_x_2513_, lean_object* v_x_2514_, lean_object* v_h__1_2515_, lean_object* v_h__2_2516_){
_start:
{
if (lean_obj_tag(v_x_2513_) == 0)
{
lean_object* v___x_2517_; 
lean_dec(v_h__1_2515_);
v___x_2517_ = lean_apply_3(v_h__2_2516_, v_x_2513_, v_x_2514_, lean_box(0));
return v___x_2517_;
}
else
{
if (lean_obj_tag(v_x_2514_) == 0)
{
lean_object* v___x_2518_; 
lean_dec(v_h__1_2515_);
v___x_2518_ = lean_apply_3(v_h__2_2516_, v_x_2513_, v_x_2514_, lean_box(0));
return v___x_2518_;
}
else
{
lean_object* v_head_2519_; lean_object* v_tail_2520_; lean_object* v_head_2521_; lean_object* v_tail_2522_; lean_object* v___x_2523_; 
lean_dec(v_h__2_2516_);
v_head_2519_ = lean_ctor_get(v_x_2513_, 0);
lean_inc(v_head_2519_);
v_tail_2520_ = lean_ctor_get(v_x_2513_, 1);
lean_inc(v_tail_2520_);
lean_dec_ref(v_x_2513_);
v_head_2521_ = lean_ctor_get(v_x_2514_, 0);
lean_inc(v_head_2521_);
v_tail_2522_ = lean_ctor_get(v_x_2514_, 1);
lean_inc(v_tail_2522_);
lean_dec_ref(v_x_2514_);
v___x_2523_ = lean_apply_4(v_h__1_2515_, v_head_2519_, v_tail_2520_, v_head_2521_, v_tail_2522_);
return v___x_2523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object* v_00_u03b1_2524_, lean_object* v_00_u03b2_2525_, lean_object* v_motive_2526_, lean_object* v_x_2527_, lean_object* v_x_2528_, lean_object* v_h__1_2529_, lean_object* v_h__2_2530_){
_start:
{
if (lean_obj_tag(v_x_2527_) == 0)
{
lean_object* v___x_2531_; 
lean_dec(v_h__1_2529_);
v___x_2531_ = lean_apply_3(v_h__2_2530_, v_x_2527_, v_x_2528_, lean_box(0));
return v___x_2531_;
}
else
{
if (lean_obj_tag(v_x_2528_) == 0)
{
lean_object* v___x_2532_; 
lean_dec(v_h__1_2529_);
v___x_2532_ = lean_apply_3(v_h__2_2530_, v_x_2527_, v_x_2528_, lean_box(0));
return v___x_2532_;
}
else
{
lean_object* v_head_2533_; lean_object* v_tail_2534_; lean_object* v_head_2535_; lean_object* v_tail_2536_; lean_object* v___x_2537_; 
lean_dec(v_h__2_2530_);
v_head_2533_ = lean_ctor_get(v_x_2527_, 0);
lean_inc(v_head_2533_);
v_tail_2534_ = lean_ctor_get(v_x_2527_, 1);
lean_inc(v_tail_2534_);
lean_dec_ref(v_x_2527_);
v_head_2535_ = lean_ctor_get(v_x_2528_, 0);
lean_inc(v_head_2535_);
v_tail_2536_ = lean_ctor_get(v_x_2528_, 1);
lean_inc(v_tail_2536_);
lean_dec_ref(v_x_2528_);
v___x_2537_ = lean_apply_4(v_h__1_2529_, v_head_2533_, v_tail_2534_, v_head_2535_, v_tail_2536_);
return v___x_2537_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object* v_x_2538_, lean_object* v_x_2539_){
_start:
{
if (lean_obj_tag(v_x_2538_) == 0)
{
lean_object* v___x_2540_; 
lean_dec(v_x_2539_);
v___x_2540_ = lean_box(0);
return v___x_2540_;
}
else
{
if (lean_obj_tag(v_x_2539_) == 0)
{
lean_object* v___x_2541_; 
lean_dec_ref(v_x_2538_);
v___x_2541_ = lean_box(0);
return v___x_2541_;
}
else
{
lean_object* v_head_2542_; lean_object* v_tail_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2560_; 
v_head_2542_ = lean_ctor_get(v_x_2538_, 0);
v_tail_2543_ = lean_ctor_get(v_x_2538_, 1);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_x_2538_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2545_ = v_x_2538_;
v_isShared_2546_ = v_isSharedCheck_2560_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_tail_2543_);
lean_inc(v_head_2542_);
lean_dec(v_x_2538_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2560_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_head_2547_; lean_object* v_tail_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2559_; 
v_head_2547_ = lean_ctor_get(v_x_2539_, 0);
v_tail_2548_ = lean_ctor_get(v_x_2539_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_x_2539_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2550_ = v_x_2539_;
v_isShared_2551_ = v_isSharedCheck_2559_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_tail_2548_);
lean_inc(v_head_2547_);
lean_dec(v_x_2539_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2559_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set_tag(v___x_2545_, 0);
lean_ctor_set(v___x_2545_, 1, v_head_2547_);
v___x_2553_ = v___x_2545_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_head_2542_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_head_2547_);
v___x_2553_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2554_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_tail_2543_, v_tail_2548_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v___x_2554_);
lean_ctor_set(v___x_2550_, 0, v___x_2553_);
v___x_2556_ = v___x_2550_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zip___redArg(lean_object* v_xs_2561_, lean_object* v_ys_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2561_, v_ys_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_List_zip(lean_object* v_00_u03b1_2564_, lean_object* v_00_u03b2_2565_, lean_object* v_xs_2566_, lean_object* v_ys_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2566_, v_ys_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object* v_00_u03b1_2569_, lean_object* v_00_u03b2_2570_, lean_object* v_x_2571_, lean_object* v_x_2572_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_x_2571_, v_x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__0___redArg(lean_object* v_f_2574_, lean_object* v_x_2575_){
_start:
{
if (lean_obj_tag(v_x_2575_) == 0)
{
lean_object* v___x_2576_; 
lean_dec(v_f_2574_);
v___x_2576_ = lean_box(0);
return v___x_2576_;
}
else
{
lean_object* v_head_2577_; lean_object* v_tail_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2589_; 
v_head_2577_ = lean_ctor_get(v_x_2575_, 0);
v_tail_2578_ = lean_ctor_get(v_x_2575_, 1);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_x_2575_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2580_ = v_x_2575_;
v_isShared_2581_ = v_isSharedCheck_2589_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_tail_2578_);
lean_inc(v_head_2577_);
lean_dec(v_x_2575_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2589_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2583_, 0, v_head_2577_);
lean_inc(v_f_2574_);
v___x_2584_ = lean_apply_2(v_f_2574_, v___x_2582_, v___x_2583_);
v___x_2585_ = l_List_map___at___00List_zipWithAll_spec__0___redArg(v_f_2574_, v_tail_2578_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 1, v___x_2585_);
lean_ctor_set(v___x_2580_, 0, v___x_2584_);
v___x_2587_ = v___x_2580_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__1___redArg(lean_object* v_f_2590_, lean_object* v_x_2591_){
_start:
{
if (lean_obj_tag(v_x_2591_) == 0)
{
lean_object* v___x_2592_; 
lean_dec(v_f_2590_);
v___x_2592_ = lean_box(0);
return v___x_2592_;
}
else
{
lean_object* v_head_2593_; lean_object* v_tail_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2605_; 
v_head_2593_ = lean_ctor_get(v_x_2591_, 0);
v_tail_2594_ = lean_ctor_get(v_x_2591_, 1);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_x_2591_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2596_ = v_x_2591_;
v_isShared_2597_ = v_isSharedCheck_2605_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_tail_2594_);
lean_inc(v_head_2593_);
lean_dec(v_x_2591_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2605_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2598_, 0, v_head_2593_);
v___x_2599_ = lean_box(0);
lean_inc(v_f_2590_);
v___x_2600_ = lean_apply_2(v_f_2590_, v___x_2598_, v___x_2599_);
v___x_2601_ = l_List_map___at___00List_zipWithAll_spec__1___redArg(v_f_2590_, v_tail_2594_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 1, v___x_2601_);
lean_ctor_set(v___x_2596_, 0, v___x_2600_);
v___x_2603_ = v___x_2596_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object* v_f_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_){
_start:
{
if (lean_obj_tag(v_x_2607_) == 0)
{
lean_object* v___x_2609_; 
v___x_2609_ = l_List_map___at___00List_zipWithAll_spec__0___redArg(v_f_2606_, v_x_2608_);
return v___x_2609_;
}
else
{
if (lean_obj_tag(v_x_2608_) == 0)
{
lean_object* v___x_2610_; 
v___x_2610_ = l_List_map___at___00List_zipWithAll_spec__1___redArg(v_f_2606_, v_x_2607_);
return v___x_2610_;
}
else
{
lean_object* v_head_2611_; lean_object* v_tail_2612_; lean_object* v_head_2613_; lean_object* v_tail_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2625_; 
v_head_2611_ = lean_ctor_get(v_x_2607_, 0);
lean_inc(v_head_2611_);
v_tail_2612_ = lean_ctor_get(v_x_2607_, 1);
lean_inc(v_tail_2612_);
lean_dec_ref(v_x_2607_);
v_head_2613_ = lean_ctor_get(v_x_2608_, 0);
v_tail_2614_ = lean_ctor_get(v_x_2608_, 1);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_x_2608_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2616_ = v_x_2608_;
v_isShared_2617_ = v_isSharedCheck_2625_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_tail_2614_);
lean_inc(v_head_2613_);
lean_dec(v_x_2608_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2625_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v_head_2611_);
v___x_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_head_2613_);
lean_inc(v_f_2606_);
v___x_2620_ = lean_apply_2(v_f_2606_, v___x_2618_, v___x_2619_);
v___x_2621_ = l_List_zipWithAll___redArg(v_f_2606_, v_tail_2612_, v_tail_2614_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 1, v___x_2621_);
lean_ctor_set(v___x_2616_, 0, v___x_2620_);
v___x_2623_ = v___x_2616_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object* v_00_u03b1_2626_, lean_object* v_00_u03b2_2627_, lean_object* v_00_u03b3_2628_, lean_object* v_f_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_List_zipWithAll___redArg(v_f_2629_, v_x_2630_, v_x_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__0(lean_object* v_00_u03b2_2633_, lean_object* v_00_u03b3_2634_, lean_object* v_00_u03b1_2635_, lean_object* v_f_2636_, lean_object* v_x_2637_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_List_map___at___00List_zipWithAll_spec__0___redArg(v_f_2636_, v_x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll_spec__1(lean_object* v_00_u03b1_2639_, lean_object* v_00_u03b3_2640_, lean_object* v_00_u03b2_2641_, lean_object* v_f_2642_, lean_object* v_x_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_List_map___at___00List_zipWithAll_spec__1___redArg(v_f_2642_, v_x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_List_unzip___redArg(lean_object* v_x_2645_){
_start:
{
if (lean_obj_tag(v_x_2645_) == 0)
{
lean_object* v___x_2646_; 
v___x_2646_ = ((lean_object*)(l_List_partition___redArg___closed__0));
return v___x_2646_;
}
else
{
lean_object* v_head_2647_; lean_object* v_tail_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2674_; 
v_head_2647_ = lean_ctor_get(v_x_2645_, 0);
v_tail_2648_ = lean_ctor_get(v_x_2645_, 1);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_x_2645_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2650_ = v_x_2645_;
v_isShared_2651_ = v_isSharedCheck_2674_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_tail_2648_);
lean_inc(v_head_2647_);
lean_dec(v_x_2645_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2674_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v_fst_2652_; lean_object* v_snd_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2673_; 
v_fst_2652_ = lean_ctor_get(v_head_2647_, 0);
v_snd_2653_ = lean_ctor_get(v_head_2647_, 1);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_head_2647_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2655_ = v_head_2647_;
v_isShared_2656_ = v_isSharedCheck_2673_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snd_2653_);
lean_inc(v_fst_2652_);
lean_dec(v_head_2647_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2673_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2672_; 
v___x_2657_ = l_List_unzip___redArg(v_tail_2648_);
v_fst_2658_ = lean_ctor_get(v___x_2657_, 0);
v_snd_2659_ = lean_ctor_get(v___x_2657_, 1);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2661_ = v___x_2657_;
v_isShared_2662_ = v_isSharedCheck_2672_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_snd_2659_);
lean_inc(v_fst_2658_);
lean_dec(v___x_2657_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2672_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 1, v_fst_2658_);
lean_ctor_set(v___x_2650_, 0, v_fst_2652_);
v___x_2664_ = v___x_2650_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_fst_2652_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_fst_2658_);
v___x_2664_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2666_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 1);
lean_ctor_set(v___x_2655_, 1, v_snd_2659_);
lean_ctor_set(v___x_2655_, 0, v_snd_2653_);
v___x_2666_ = v___x_2655_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_snd_2653_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_snd_2659_);
v___x_2666_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2668_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2666_);
lean_ctor_set(v___x_2661_, 0, v___x_2664_);
v___x_2668_ = v___x_2661_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_unzip(lean_object* v_00_u03b1_2675_, lean_object* v_00_u03b2_2676_, lean_object* v_x_2677_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_List_unzip___redArg(v_x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___lam__0(lean_object* v_inst_2679_, lean_object* v_x1_2680_, lean_object* v_x2_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_apply_2(v_inst_2679_, v_x1_2680_, v_x2_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg(lean_object* v_inst_2683_, lean_object* v_inst_2684_, lean_object* v_l_2685_){
_start:
{
lean_object* v___f_2686_; lean_object* v___x_2687_; 
v___f_2686_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2686_, 0, v_inst_2683_);
v___x_2687_ = l_List_foldr___redArg(v___f_2686_, v_inst_2684_, v_l_2685_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___boxed(lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_l_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_List_sum___redArg(v_inst_2688_, v_inst_2689_, v_l_2690_);
lean_dec(v_inst_2689_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_List_sum(lean_object* v_00_u03b1_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_l_2695_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_List_sum___redArg(v_inst_2693_, v_inst_2694_, v_l_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_List_sum___boxed(lean_object* v_00_u03b1_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_l_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_List_sum(v_00_u03b1_2697_, v_inst_2698_, v_inst_2699_, v_l_2700_);
lean_dec(v_inst_2699_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_List_range_loop(lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v_zero_2704_; uint8_t v_isZero_2705_; 
v_zero_2704_ = lean_unsigned_to_nat(0u);
v_isZero_2705_ = lean_nat_dec_eq(v_a_2702_, v_zero_2704_);
if (v_isZero_2705_ == 1)
{
lean_dec(v_a_2702_);
return v_a_2703_;
}
else
{
lean_object* v_one_2706_; lean_object* v_n_2707_; lean_object* v___x_2708_; 
v_one_2706_ = lean_unsigned_to_nat(1u);
v_n_2707_ = lean_nat_sub(v_a_2702_, v_one_2706_);
lean_dec(v_a_2702_);
lean_inc(v_n_2707_);
v___x_2708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2708_, 0, v_n_2707_);
lean_ctor_set(v___x_2708_, 1, v_a_2703_);
v_a_2702_ = v_n_2707_;
v_a_2703_ = v___x_2708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range(lean_object* v_n_2710_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = lean_box(0);
v___x_2712_ = l_List_range_loop(v_n_2710_, v___x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27(lean_object* v_x_2713_, lean_object* v_x_2714_, lean_object* v_x_2715_){
_start:
{
lean_object* v_zero_2716_; uint8_t v_isZero_2717_; 
v_zero_2716_ = lean_unsigned_to_nat(0u);
v_isZero_2717_ = lean_nat_dec_eq(v_x_2714_, v_zero_2716_);
if (v_isZero_2717_ == 1)
{
lean_object* v___x_2718_; 
lean_dec(v_x_2713_);
v___x_2718_ = lean_box(0);
return v___x_2718_;
}
else
{
lean_object* v_one_2719_; lean_object* v_n_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v_one_2719_ = lean_unsigned_to_nat(1u);
v_n_2720_ = lean_nat_sub(v_x_2714_, v_one_2719_);
v___x_2721_ = lean_nat_add(v_x_2713_, v_x_2715_);
v___x_2722_ = l_List_range_x27(v___x_2721_, v_n_2720_, v_x_2715_);
lean_dec(v_n_2720_);
v___x_2723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2723_, 0, v_x_2713_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object* v_x_2724_, lean_object* v_x_2725_, lean_object* v_x_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_List_range_x27(v_x_2724_, v_x_2725_, v_x_2726_);
lean_dec(v_x_2726_);
lean_dec(v_x_2725_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdx___redArg(lean_object* v_x_2728_, lean_object* v_x_2729_){
_start:
{
if (lean_obj_tag(v_x_2728_) == 0)
{
lean_object* v___x_2730_; 
lean_dec(v_x_2729_);
v___x_2730_ = lean_box(0);
return v___x_2730_;
}
else
{
lean_object* v_head_2731_; lean_object* v_tail_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2743_; 
v_head_2731_ = lean_ctor_get(v_x_2728_, 0);
v_tail_2732_ = lean_ctor_get(v_x_2728_, 1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_x_2728_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2734_ = v_x_2728_;
v_isShared_2735_ = v_isSharedCheck_2743_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_tail_2732_);
lean_inc(v_head_2731_);
lean_dec(v_x_2728_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2743_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
lean_inc(v_x_2729_);
v___x_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2736_, 0, v_head_2731_);
lean_ctor_set(v___x_2736_, 1, v_x_2729_);
v___x_2737_ = lean_unsigned_to_nat(1u);
v___x_2738_ = lean_nat_add(v_x_2729_, v___x_2737_);
lean_dec(v_x_2729_);
v___x_2739_ = l_List_zipIdx___redArg(v_tail_2732_, v___x_2738_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2739_);
lean_ctor_set(v___x_2734_, 0, v___x_2736_);
v___x_2741_ = v___x_2734_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdx(lean_object* v_00_u03b1_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_List_zipIdx___redArg(v_x_2745_, v_x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object* v_inst_2748_, lean_object* v_x_2749_){
_start:
{
if (lean_obj_tag(v_x_2749_) == 0)
{
lean_object* v___x_2750_; 
lean_dec(v_inst_2748_);
v___x_2750_ = lean_box(0);
return v___x_2750_;
}
else
{
lean_object* v_head_2751_; lean_object* v_tail_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v_head_2751_ = lean_ctor_get(v_x_2749_, 0);
lean_inc(v_head_2751_);
v_tail_2752_ = lean_ctor_get(v_x_2749_, 1);
lean_inc(v_tail_2752_);
lean_dec_ref(v_x_2749_);
v___x_2753_ = l_List_foldl___redArg(v_inst_2748_, v_head_2751_, v_tail_2752_);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
return v___x_2754_;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object* v_00_u03b1_2755_, lean_object* v_inst_2756_, lean_object* v_x_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_List_min_x3f___redArg(v_inst_2756_, v_x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object* v_inst_2759_, lean_object* v_x_2760_){
_start:
{
lean_object* v_head_2761_; lean_object* v_tail_2762_; lean_object* v___x_2763_; 
v_head_2761_ = lean_ctor_get(v_x_2760_, 0);
lean_inc(v_head_2761_);
v_tail_2762_ = lean_ctor_get(v_x_2760_, 1);
lean_inc(v_tail_2762_);
lean_dec(v_x_2760_);
v___x_2763_ = l_List_foldl___redArg(v_inst_2759_, v_head_2761_, v_tail_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_List_min(lean_object* v_00_u03b1_2764_, lean_object* v_inst_2765_, lean_object* v_x_2766_, lean_object* v_x_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_List_min___redArg(v_inst_2765_, v_x_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object* v_inst_2769_, lean_object* v_x_2770_){
_start:
{
if (lean_obj_tag(v_x_2770_) == 0)
{
lean_object* v___x_2771_; 
lean_dec(v_inst_2769_);
v___x_2771_ = lean_box(0);
return v___x_2771_;
}
else
{
lean_object* v_head_2772_; lean_object* v_tail_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_head_2772_ = lean_ctor_get(v_x_2770_, 0);
lean_inc(v_head_2772_);
v_tail_2773_ = lean_ctor_get(v_x_2770_, 1);
lean_inc(v_tail_2773_);
lean_dec_ref(v_x_2770_);
v___x_2774_ = l_List_foldl___redArg(v_inst_2769_, v_head_2772_, v_tail_2773_);
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
return v___x_2775_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object* v_00_u03b1_2776_, lean_object* v_inst_2777_, lean_object* v_x_2778_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_List_max_x3f___redArg(v_inst_2777_, v_x_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object* v_inst_2780_, lean_object* v_x_2781_){
_start:
{
lean_object* v_head_2782_; lean_object* v_tail_2783_; lean_object* v___x_2784_; 
v_head_2782_ = lean_ctor_get(v_x_2781_, 0);
lean_inc(v_head_2782_);
v_tail_2783_ = lean_ctor_get(v_x_2781_, 1);
lean_inc(v_tail_2783_);
lean_dec(v_x_2781_);
v___x_2784_ = l_List_foldl___redArg(v_inst_2780_, v_head_2782_, v_tail_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_List_max(lean_object* v_00_u03b1_2785_, lean_object* v_inst_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_List_max___redArg(v_inst_2786_, v_x_2787_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_List_intersperse___redArg(lean_object* v_sep_2790_, lean_object* v_x_2791_){
_start:
{
if (lean_obj_tag(v_x_2791_) == 0)
{
lean_dec(v_sep_2790_);
return v_x_2791_;
}
else
{
lean_object* v_tail_2792_; 
v_tail_2792_ = lean_ctor_get(v_x_2791_, 1);
if (lean_obj_tag(v_tail_2792_) == 0)
{
lean_dec(v_sep_2790_);
return v_x_2791_;
}
else
{
lean_object* v_head_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2802_; 
lean_inc_ref(v_tail_2792_);
v_head_2793_ = lean_ctor_get(v_x_2791_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_x_2791_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v_x_2791_, 1);
lean_dec(v_unused_2803_);
v___x_2795_ = v_x_2791_;
v_isShared_2796_ = v_isSharedCheck_2802_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_head_2793_);
lean_dec(v_x_2791_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2802_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2797_; lean_object* v___x_2799_; 
lean_inc(v_sep_2790_);
v___x_2797_ = l_List_intersperse___redArg(v_sep_2790_, v_tail_2792_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 1, v___x_2797_);
lean_ctor_set(v___x_2795_, 0, v_sep_2790_);
v___x_2799_ = v___x_2795_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_sep_2790_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2800_, 0, v_head_2793_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
return v___x_2800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperse(lean_object* v_00_u03b1_2804_, lean_object* v_sep_2805_, lean_object* v_x_2806_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_List_intersperse___redArg(v_sep_2805_, v_x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object* v_r_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
if (lean_obj_tag(v_a_2809_) == 0)
{
lean_object* v___x_2811_; 
lean_dec_ref(v_r_2808_);
v___x_2811_ = l_List_reverse___redArg(v_a_2810_);
return v___x_2811_;
}
else
{
lean_object* v_head_2812_; lean_object* v_tail_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2824_; 
v_head_2812_ = lean_ctor_get(v_a_2809_, 0);
v_tail_2813_ = lean_ctor_get(v_a_2809_, 1);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_a_2809_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2815_ = v_a_2809_;
v_isShared_2816_ = v_isSharedCheck_2824_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_tail_2813_);
lean_inc(v_head_2812_);
lean_dec(v_a_2809_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2824_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; uint8_t v___x_2818_; 
lean_inc_ref(v_r_2808_);
lean_inc(v_head_2812_);
v___x_2817_ = lean_apply_1(v_r_2808_, v_head_2812_);
lean_inc(v_a_2810_);
v___x_2818_ = l_List_any___redArg(v_a_2810_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2820_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v_a_2810_);
v___x_2820_ = v___x_2815_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_head_2812_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_a_2810_);
v___x_2820_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
v_a_2809_ = v_tail_2813_;
v_a_2810_ = v___x_2820_;
goto _start;
}
}
else
{
lean_del_object(v___x_2815_);
lean_dec(v_head_2812_);
v_a_2809_ = v_tail_2813_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object* v_00_u03b1_2825_, lean_object* v_r_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_List_eraseDupsBy_loop___redArg(v_r_2826_, v_a_2827_, v_a_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy___redArg(lean_object* v_r_2830_, lean_object* v_as_2831_){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_box(0);
v___x_2833_ = l_List_eraseDupsBy_loop___redArg(v_r_2830_, v_as_2831_, v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy(lean_object* v_00_u03b1_2834_, lean_object* v_r_2835_, lean_object* v_as_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_List_eraseDupsBy___redArg(v_r_2835_, v_as_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT uint8_t l_List_eraseDups___redArg___lam__0(lean_object* v_inst_2838_, lean_object* v_x1_2839_, lean_object* v_x2_2840_){
_start:
{
lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2841_ = lean_apply_2(v_inst_2838_, v_x1_2839_, v_x2_2840_);
v___x_2842_ = lean_unbox(v___x_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg___lam__0___boxed(lean_object* v_inst_2843_, lean_object* v_x1_2844_, lean_object* v_x2_2845_){
_start:
{
uint8_t v_res_2846_; lean_object* v_r_2847_; 
v_res_2846_ = l_List_eraseDups___redArg___lam__0(v_inst_2843_, v_x1_2844_, v_x2_2845_);
v_r_2847_ = lean_box(v_res_2846_);
return v_r_2847_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg(lean_object* v_inst_2848_, lean_object* v_as_2849_){
_start:
{
lean_object* v___f_2850_; lean_object* v___x_2851_; 
v___f_2850_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2850_, 0, v_inst_2848_);
v___x_2851_ = l_List_eraseDupsBy___redArg(v___f_2850_, v_as_2849_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object* v_00_u03b1_2852_, lean_object* v_inst_2853_, lean_object* v_as_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_List_eraseDups___redArg(v_inst_2853_, v_as_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop___redArg(lean_object* v_r_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
if (lean_obj_tag(v_a_2858_) == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_dec_ref(v_r_2856_);
v___x_2860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2860_, 0, v_a_2857_);
lean_ctor_set(v___x_2860_, 1, v_a_2859_);
v___x_2861_ = l_List_reverse___redArg(v___x_2860_);
return v___x_2861_;
}
else
{
lean_object* v_head_2862_; lean_object* v_tail_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2874_; 
v_head_2862_ = lean_ctor_get(v_a_2858_, 0);
v_tail_2863_ = lean_ctor_get(v_a_2858_, 1);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_a_2858_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2865_ = v_a_2858_;
v_isShared_2866_ = v_isSharedCheck_2874_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_tail_2863_);
lean_inc(v_head_2862_);
lean_dec(v_a_2858_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2874_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; uint8_t v___x_2868_; 
lean_inc_ref(v_r_2856_);
lean_inc(v_head_2862_);
lean_inc(v_a_2857_);
v___x_2867_ = lean_apply_2(v_r_2856_, v_a_2857_, v_head_2862_);
v___x_2868_ = lean_unbox(v___x_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2870_; 
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v_a_2859_);
lean_ctor_set(v___x_2865_, 0, v_a_2857_);
v___x_2870_ = v___x_2865_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2857_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_a_2859_);
v___x_2870_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
v_a_2857_ = v_head_2862_;
v_a_2858_ = v_tail_2863_;
v_a_2859_ = v___x_2870_;
goto _start;
}
}
else
{
lean_del_object(v___x_2865_);
lean_dec(v_head_2862_);
v_a_2858_ = v_tail_2863_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop(lean_object* v_00_u03b1_2875_, lean_object* v_r_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_List_eraseRepsBy_loop___redArg(v_r_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy___redArg(lean_object* v_r_2881_, lean_object* v_x_2882_){
_start:
{
if (lean_obj_tag(v_x_2882_) == 0)
{
lean_dec_ref(v_r_2881_);
return v_x_2882_;
}
else
{
lean_object* v_head_2883_; lean_object* v_tail_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_head_2883_ = lean_ctor_get(v_x_2882_, 0);
lean_inc(v_head_2883_);
v_tail_2884_ = lean_ctor_get(v_x_2882_, 1);
lean_inc(v_tail_2884_);
lean_dec_ref(v_x_2882_);
v___x_2885_ = lean_box(0);
v___x_2886_ = l_List_eraseRepsBy_loop___redArg(v_r_2881_, v_head_2883_, v_tail_2884_, v___x_2885_);
return v___x_2886_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy(lean_object* v_00_u03b1_2887_, lean_object* v_r_2888_, lean_object* v_x_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_List_eraseRepsBy___redArg(v_r_2888_, v_x_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___redArg(lean_object* v_inst_2891_, lean_object* v_as_2892_){
_start:
{
lean_object* v___f_2893_; lean_object* v___x_2894_; 
v___f_2893_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2893_, 0, v_inst_2891_);
v___x_2894_ = l_List_eraseRepsBy___redArg(v___f_2893_, v_as_2892_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object* v_00_u03b1_2895_, lean_object* v_inst_2896_, lean_object* v_as_2897_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_List_eraseReps___redArg(v_inst_2896_, v_as_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___redArg(lean_object* v_p_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
if (lean_obj_tag(v_a_2900_) == 0)
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
lean_dec_ref(v_p_2899_);
v___x_2902_ = l_List_reverse___redArg(v_a_2901_);
v___x_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
lean_ctor_set(v___x_2903_, 1, v_a_2900_);
return v___x_2903_;
}
else
{
lean_object* v_head_2904_; lean_object* v_tail_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v_head_2904_ = lean_ctor_get(v_a_2900_, 0);
v_tail_2905_ = lean_ctor_get(v_a_2900_, 1);
lean_inc_ref(v_p_2899_);
lean_inc(v_head_2904_);
v___x_2906_ = lean_apply_1(v_p_2899_, v_head_2904_);
v___x_2907_ = lean_unbox(v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_dec_ref(v_p_2899_);
v___x_2908_ = l_List_reverse___redArg(v_a_2901_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v_a_2900_);
return v___x_2909_;
}
else
{
lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2917_; 
lean_inc(v_tail_2905_);
lean_inc(v_head_2904_);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_a_2900_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; lean_object* v_unused_2919_; 
v_unused_2918_ = lean_ctor_get(v_a_2900_, 1);
lean_dec(v_unused_2918_);
v_unused_2919_ = lean_ctor_get(v_a_2900_, 0);
lean_dec(v_unused_2919_);
v___x_2911_ = v_a_2900_;
v_isShared_2912_ = v_isSharedCheck_2917_;
goto v_resetjp_2910_;
}
else
{
lean_dec(v_a_2900_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2917_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v_a_2901_);
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_head_2904_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_a_2901_);
v___x_2914_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
v_a_2900_ = v_tail_2905_;
v_a_2901_ = v___x_2914_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop(lean_object* v_00_u03b1_2920_, lean_object* v_p_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_List_span_loop___redArg(v_p_2921_, v_a_2922_, v_a_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_List_span___redArg(lean_object* v_p_2925_, lean_object* v_as_2926_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_box(0);
v___x_2928_ = l_List_span_loop___redArg(v_p_2925_, v_as_2926_, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_List_span(lean_object* v_00_u03b1_2929_, lean_object* v_p_2930_, lean_object* v_as_2931_){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = lean_box(0);
v___x_2933_ = l_List_span_loop___redArg(v_p_2930_, v_as_2931_, v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___redArg(lean_object* v_R_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
if (lean_obj_tag(v_a_2935_) == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref(v_R_2934_);
v___x_2939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2936_);
lean_ctor_set(v___x_2939_, 1, v_a_2937_);
v___x_2940_ = l_List_reverse___redArg(v___x_2939_);
v___x_2941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v_a_2938_);
v___x_2942_ = l_List_reverse___redArg(v___x_2941_);
return v___x_2942_;
}
else
{
lean_object* v_head_2943_; lean_object* v_tail_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2961_; 
v_head_2943_ = lean_ctor_get(v_a_2935_, 0);
v_tail_2944_ = lean_ctor_get(v_a_2935_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_a_2935_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2946_ = v_a_2935_;
v_isShared_2947_ = v_isSharedCheck_2961_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_tail_2944_);
lean_inc(v_head_2943_);
lean_dec(v_a_2935_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2961_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; uint8_t v___x_2949_; 
lean_inc_ref(v_R_2934_);
lean_inc(v_head_2943_);
lean_inc(v_a_2936_);
v___x_2948_ = lean_apply_2(v_R_2934_, v_a_2936_, v_head_2943_);
v___x_2949_ = lean_unbox(v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_box(0);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v_a_2937_);
lean_ctor_set(v___x_2946_, 0, v_a_2936_);
v___x_2952_ = v___x_2946_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2936_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_a_2937_);
v___x_2952_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = l_List_reverse___redArg(v___x_2952_);
v___x_2954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set(v___x_2954_, 1, v_a_2938_);
v_a_2935_ = v_tail_2944_;
v_a_2936_ = v_head_2943_;
v_a_2937_ = v___x_2950_;
v_a_2938_ = v___x_2954_;
goto _start;
}
}
else
{
lean_object* v___x_2958_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v_a_2937_);
lean_ctor_set(v___x_2946_, 0, v_a_2936_);
v___x_2958_ = v___x_2946_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2936_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_a_2937_);
v___x_2958_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
v_a_2935_ = v_tail_2944_;
v_a_2936_ = v_head_2943_;
v_a_2937_ = v___x_2958_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop(lean_object* v_00_u03b1_2962_, lean_object* v_R_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_List_splitBy_loop___redArg(v_R_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___redArg(lean_object* v_R_2969_, lean_object* v_x_2970_){
_start:
{
if (lean_obj_tag(v_x_2970_) == 0)
{
lean_object* v___x_2971_; 
lean_dec_ref(v_R_2969_);
v___x_2971_ = lean_box(0);
return v___x_2971_;
}
else
{
lean_object* v_head_2972_; lean_object* v_tail_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_head_2972_ = lean_ctor_get(v_x_2970_, 0);
lean_inc(v_head_2972_);
v_tail_2973_ = lean_ctor_get(v_x_2970_, 1);
lean_inc(v_tail_2973_);
lean_dec_ref(v_x_2970_);
v___x_2974_ = lean_box(0);
v___x_2975_ = l_List_splitBy_loop___redArg(v_R_2969_, v_tail_2973_, v_head_2972_, v___x_2974_, v___x_2974_);
return v___x_2975_;
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy(lean_object* v_00_u03b1_2976_, lean_object* v_R_2977_, lean_object* v_x_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_List_splitBy___redArg(v_R_2977_, v_x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___redArg___lam__0(lean_object* v_inst_2980_, lean_object* v_ys_2981_, lean_object* v_x_2982_){
_start:
{
uint8_t v___x_2983_; 
v___x_2983_ = l_List_elem___redArg(v_inst_2980_, v_x_2982_, v_ys_2981_);
if (v___x_2983_ == 0)
{
uint8_t v___x_2984_; 
v___x_2984_ = 1;
return v___x_2984_;
}
else
{
uint8_t v___x_2985_; 
v___x_2985_ = 0;
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg___lam__0___boxed(lean_object* v_inst_2986_, lean_object* v_ys_2987_, lean_object* v_x_2988_){
_start:
{
uint8_t v_res_2989_; lean_object* v_r_2990_; 
v_res_2989_ = l_List_removeAll___redArg___lam__0(v_inst_2986_, v_ys_2987_, v_x_2988_);
v_r_2990_ = lean_box(v_res_2989_);
return v_r_2990_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg(lean_object* v_inst_2991_, lean_object* v_xs_2992_, lean_object* v_ys_2993_){
_start:
{
lean_object* v___f_2994_; lean_object* v___x_2995_; 
v___f_2994_ = lean_alloc_closure((void*)(l_List_removeAll___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2994_, 0, v_inst_2991_);
lean_closure_set(v___f_2994_, 1, v_ys_2993_);
v___x_2995_ = l_List_filter___redArg(v___f_2994_, v_xs_2992_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll(lean_object* v_00_u03b1_2996_, lean_object* v_inst_2997_, lean_object* v_xs_2998_, lean_object* v_ys_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_List_removeAll___redArg(v_inst_2997_, v_xs_2998_, v_ys_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_3001_, lean_object* v_h__1_3002_, lean_object* v_h__2_3003_){
_start:
{
if (lean_obj_tag(v_ys_3001_) == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_dec(v_h__2_3003_);
v___x_3004_ = lean_box(0);
v___x_3005_ = lean_apply_1(v_h__1_3002_, v___x_3004_);
return v___x_3005_;
}
else
{
lean_object* v_head_3006_; lean_object* v_tail_3007_; lean_object* v___x_3008_; 
lean_dec(v_h__1_3002_);
v_head_3006_ = lean_ctor_get(v_ys_3001_, 0);
lean_inc(v_head_3006_);
v_tail_3007_ = lean_ctor_get(v_ys_3001_, 1);
lean_inc(v_tail_3007_);
lean_dec_ref(v_ys_3001_);
v___x_3008_ = lean_apply_2(v_h__2_3003_, v_head_3006_, v_tail_3007_);
return v___x_3008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_3009_, lean_object* v_motive_3010_, lean_object* v_ys_3011_, lean_object* v_h__1_3012_, lean_object* v_h__2_3013_){
_start:
{
if (lean_obj_tag(v_ys_3011_) == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_dec(v_h__2_3013_);
v___x_3014_ = lean_box(0);
v___x_3015_ = lean_apply_1(v_h__1_3012_, v___x_3014_);
return v___x_3015_;
}
else
{
lean_object* v_head_3016_; lean_object* v_tail_3017_; lean_object* v___x_3018_; 
lean_dec(v_h__1_3012_);
v_head_3016_ = lean_ctor_get(v_ys_3011_, 0);
lean_inc(v_head_3016_);
v_tail_3017_ = lean_ctor_get(v_ys_3011_, 1);
lean_inc(v_tail_3017_);
lean_dec_ref(v_ys_3011_);
v___x_3018_ = lean_apply_2(v_h__2_3013_, v_head_3016_, v_tail_3017_);
return v___x_3018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(lean_object* v_x_3019_, lean_object* v_x_3020_, lean_object* v_h__1_3021_, lean_object* v_h__2_3022_){
_start:
{
if (lean_obj_tag(v_x_3019_) == 0)
{
lean_object* v___x_3023_; 
lean_dec(v_h__2_3022_);
v___x_3023_ = lean_apply_1(v_h__1_3021_, v_x_3020_);
return v___x_3023_;
}
else
{
lean_object* v_head_3024_; lean_object* v_tail_3025_; lean_object* v___x_3026_; 
lean_dec(v_h__1_3021_);
v_head_3024_ = lean_ctor_get(v_x_3019_, 0);
lean_inc(v_head_3024_);
v_tail_3025_ = lean_ctor_get(v_x_3019_, 1);
lean_inc(v_tail_3025_);
lean_dec_ref(v_x_3019_);
v___x_3026_ = lean_apply_3(v_h__2_3022_, v_head_3024_, v_tail_3025_, v_x_3020_);
return v___x_3026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(lean_object* v_00_u03b1_3027_, lean_object* v_motive_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_, lean_object* v_h__1_3031_, lean_object* v_h__2_3032_){
_start:
{
if (lean_obj_tag(v_x_3029_) == 0)
{
lean_object* v___x_3033_; 
lean_dec(v_h__2_3032_);
v___x_3033_ = lean_apply_1(v_h__1_3031_, v_x_3030_);
return v___x_3033_;
}
else
{
lean_object* v_head_3034_; lean_object* v_tail_3035_; lean_object* v___x_3036_; 
lean_dec(v_h__1_3031_);
v_head_3034_ = lean_ctor_get(v_x_3029_, 0);
lean_inc(v_head_3034_);
v_tail_3035_ = lean_ctor_get(v_x_3029_, 1);
lean_inc(v_tail_3035_);
lean_dec_ref(v_x_3029_);
v___x_3036_ = lean_apply_3(v_h__2_3032_, v_head_3034_, v_tail_3035_, v_x_3030_);
return v___x_3036_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object* v_f_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
if (lean_obj_tag(v_a_3038_) == 0)
{
lean_object* v___x_3040_; 
lean_dec(v_f_3037_);
v___x_3040_ = l_List_reverse___redArg(v_a_3039_);
return v___x_3040_;
}
else
{
lean_object* v_head_3041_; lean_object* v_tail_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3051_; 
v_head_3041_ = lean_ctor_get(v_a_3038_, 0);
v_tail_3042_ = lean_ctor_get(v_a_3038_, 1);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_a_3038_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3044_ = v_a_3038_;
v_isShared_3045_ = v_isSharedCheck_3051_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_tail_3042_);
lean_inc(v_head_3041_);
lean_dec(v_a_3038_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3051_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
lean_inc(v_f_3037_);
v___x_3046_ = lean_apply_1(v_f_3037_, v_head_3041_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 1, v_a_3039_);
lean_ctor_set(v___x_3044_, 0, v___x_3046_);
v___x_3048_ = v___x_3044_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_a_3039_);
v___x_3048_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
v_a_3038_ = v_tail_3042_;
v_a_3039_ = v___x_3048_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object* v_00_u03b1_3052_, lean_object* v_00_u03b2_3053_, lean_object* v_f_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_List_mapTR_loop___redArg(v_f_3054_, v_a_3055_, v_a_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object* v_f_3058_, lean_object* v_as_3059_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = lean_box(0);
v___x_3061_ = l_List_mapTR_loop___redArg(v_f_3058_, v_as_3059_, v___x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR(lean_object* v_00_u03b1_3062_, lean_object* v_00_u03b2_3063_, lean_object* v_f_3064_, lean_object* v_as_3065_){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_box(0);
v___x_3067_ = l_List_mapTR_loop___redArg(v_f_3064_, v_as_3065_, v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(lean_object* v_x_3068_, lean_object* v_x_3069_, lean_object* v_h__1_3070_, lean_object* v_h__2_3071_){
_start:
{
if (lean_obj_tag(v_x_3068_) == 0)
{
lean_object* v___x_3072_; 
lean_dec(v_h__2_3071_);
v___x_3072_ = lean_apply_1(v_h__1_3070_, v_x_3069_);
return v___x_3072_;
}
else
{
lean_object* v_head_3073_; lean_object* v_tail_3074_; lean_object* v___x_3075_; 
lean_dec(v_h__1_3070_);
v_head_3073_ = lean_ctor_get(v_x_3068_, 0);
lean_inc(v_head_3073_);
v_tail_3074_ = lean_ctor_get(v_x_3068_, 1);
lean_inc(v_tail_3074_);
lean_dec_ref(v_x_3068_);
v___x_3075_ = lean_apply_3(v_h__2_3071_, v_head_3073_, v_tail_3074_, v_x_3069_);
return v___x_3075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(lean_object* v_00_u03b1_3076_, lean_object* v_00_u03b2_3077_, lean_object* v_motive_3078_, lean_object* v_x_3079_, lean_object* v_x_3080_, lean_object* v_h__1_3081_, lean_object* v_h__2_3082_){
_start:
{
if (lean_obj_tag(v_x_3079_) == 0)
{
lean_object* v___x_3083_; 
lean_dec(v_h__2_3082_);
v___x_3083_ = lean_apply_1(v_h__1_3081_, v_x_3080_);
return v___x_3083_;
}
else
{
lean_object* v_head_3084_; lean_object* v_tail_3085_; lean_object* v___x_3086_; 
lean_dec(v_h__1_3081_);
v_head_3084_ = lean_ctor_get(v_x_3079_, 0);
lean_inc(v_head_3084_);
v_tail_3085_ = lean_ctor_get(v_x_3079_, 1);
lean_inc(v_tail_3085_);
lean_dec_ref(v_x_3079_);
v___x_3086_ = lean_apply_3(v_h__2_3082_, v_head_3084_, v_tail_3085_, v_x_3080_);
return v___x_3086_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object* v_p_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
if (lean_obj_tag(v_a_3088_) == 0)
{
lean_object* v___x_3090_; 
lean_dec_ref(v_p_3087_);
v___x_3090_ = l_List_reverse___redArg(v_a_3089_);
return v___x_3090_;
}
else
{
lean_object* v_head_3091_; lean_object* v_tail_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3103_; 
v_head_3091_ = lean_ctor_get(v_a_3088_, 0);
v_tail_3092_ = lean_ctor_get(v_a_3088_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_a_3088_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3094_ = v_a_3088_;
v_isShared_3095_ = v_isSharedCheck_3103_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_tail_3092_);
lean_inc(v_head_3091_);
lean_dec(v_a_3088_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3103_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; uint8_t v___x_3097_; 
lean_inc_ref(v_p_3087_);
lean_inc(v_head_3091_);
v___x_3096_ = lean_apply_1(v_p_3087_, v_head_3091_);
v___x_3097_ = lean_unbox(v___x_3096_);
if (v___x_3097_ == 0)
{
lean_del_object(v___x_3094_);
lean_dec(v_head_3091_);
v_a_3088_ = v_tail_3092_;
goto _start;
}
else
{
lean_object* v___x_3100_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 1, v_a_3089_);
v___x_3100_ = v___x_3094_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_head_3091_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_a_3089_);
v___x_3100_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
v_a_3088_ = v_tail_3092_;
v_a_3089_ = v___x_3100_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object* v_00_u03b1_3104_, lean_object* v_p_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_List_filterTR_loop___redArg(v_p_3105_, v_a_3106_, v_a_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object* v_p_3109_, lean_object* v_as_3110_){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = lean_box(0);
v___x_3112_ = l_List_filterTR_loop___redArg(v_p_3109_, v_as_3110_, v___x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR(lean_object* v_00_u03b1_3113_, lean_object* v_p_3114_, lean_object* v_as_3115_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_box(0);
v___x_3117_ = l_List_filterTR_loop___redArg(v_p_3114_, v_as_3115_, v___x_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v_zero_3121_; uint8_t v_isZero_3122_; 
v_zero_3121_ = lean_unsigned_to_nat(0u);
v_isZero_3122_ = lean_nat_dec_eq(v_a_3119_, v_zero_3121_);
if (v_isZero_3122_ == 1)
{
lean_dec(v_a_3119_);
lean_dec(v_a_3118_);
return v_a_3120_;
}
else
{
lean_object* v_one_3123_; lean_object* v_n_3124_; lean_object* v___x_3125_; 
v_one_3123_ = lean_unsigned_to_nat(1u);
v_n_3124_ = lean_nat_sub(v_a_3119_, v_one_3123_);
lean_dec(v_a_3119_);
lean_inc(v_a_3118_);
v___x_3125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_a_3118_);
lean_ctor_set(v___x_3125_, 1, v_a_3120_);
v_a_3119_ = v_n_3124_;
v_a_3120_ = v___x_3125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object* v_00_u03b1_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_List_replicateTR_loop___redArg(v_a_3128_, v_a_3129_, v_a_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object* v_n_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_box(0);
v___x_3135_ = l_List_replicateTR_loop___redArg(v_a_3133_, v_n_3132_, v___x_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object* v_00_u03b1_3136_, lean_object* v_n_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_List_replicateTR___redArg(v_n_3137_, v_a_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(lean_object* v_x_3140_, lean_object* v_x_3141_, lean_object* v_h__1_3142_, lean_object* v_h__2_3143_){
_start:
{
lean_object* v_zero_3144_; uint8_t v_isZero_3145_; 
v_zero_3144_ = lean_unsigned_to_nat(0u);
v_isZero_3145_ = lean_nat_dec_eq(v_x_3140_, v_zero_3144_);
if (v_isZero_3145_ == 1)
{
lean_object* v___x_3146_; 
lean_dec(v_h__2_3143_);
v___x_3146_ = lean_apply_1(v_h__1_3142_, v_x_3141_);
return v___x_3146_;
}
else
{
lean_object* v_one_3147_; lean_object* v_n_3148_; lean_object* v___x_3149_; 
lean_dec(v_h__1_3142_);
v_one_3147_ = lean_unsigned_to_nat(1u);
v_n_3148_ = lean_nat_sub(v_x_3140_, v_one_3147_);
v___x_3149_ = lean_apply_2(v_h__2_3143_, v_n_3148_, v_x_3141_);
return v___x_3149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_3150_, lean_object* v_x_3151_, lean_object* v_h__1_3152_, lean_object* v_h__2_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(v_x_3150_, v_x_3151_, v_h__1_3152_, v_h__2_3153_);
lean_dec(v_x_3150_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(lean_object* v_00_u03b1_3155_, lean_object* v_motive_3156_, lean_object* v_x_3157_, lean_object* v_x_3158_, lean_object* v_h__1_3159_, lean_object* v_h__2_3160_){
_start:
{
lean_object* v_zero_3161_; uint8_t v_isZero_3162_; 
v_zero_3161_ = lean_unsigned_to_nat(0u);
v_isZero_3162_ = lean_nat_dec_eq(v_x_3157_, v_zero_3161_);
if (v_isZero_3162_ == 1)
{
lean_object* v___x_3163_; 
lean_dec(v_h__2_3160_);
v___x_3163_ = lean_apply_1(v_h__1_3159_, v_x_3158_);
return v___x_3163_;
}
else
{
lean_object* v_one_3164_; lean_object* v_n_3165_; lean_object* v___x_3166_; 
lean_dec(v_h__1_3159_);
v_one_3164_ = lean_unsigned_to_nat(1u);
v_n_3165_ = lean_nat_sub(v_x_3157_, v_one_3164_);
v___x_3166_ = lean_apply_2(v_h__2_3160_, v_n_3165_, v_x_3158_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_3167_, lean_object* v_motive_3168_, lean_object* v_x_3169_, lean_object* v_x_3170_, lean_object* v_h__1_3171_, lean_object* v_h__2_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(v_00_u03b1_3167_, v_motive_3168_, v_x_3169_, v_x_3170_, v_h__1_3171_, v_h__2_3172_);
lean_dec(v_x_3169_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(lean_object* v_x_3174_, lean_object* v_x_3175_, lean_object* v_h__1_3176_, lean_object* v_h__2_3177_){
_start:
{
lean_object* v_zero_3178_; uint8_t v_isZero_3179_; 
v_zero_3178_ = lean_unsigned_to_nat(0u);
v_isZero_3179_ = lean_nat_dec_eq(v_x_3174_, v_zero_3178_);
if (v_isZero_3179_ == 1)
{
lean_object* v___x_3180_; 
lean_dec(v_h__2_3177_);
v___x_3180_ = lean_apply_1(v_h__1_3176_, v_x_3175_);
return v___x_3180_;
}
else
{
lean_object* v_one_3181_; lean_object* v_n_3182_; lean_object* v___x_3183_; 
lean_dec(v_h__1_3176_);
v_one_3181_ = lean_unsigned_to_nat(1u);
v_n_3182_ = lean_nat_sub(v_x_3174_, v_one_3181_);
v___x_3183_ = lean_apply_2(v_h__2_3177_, v_n_3182_, v_x_3175_);
return v___x_3183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_3184_, lean_object* v_x_3185_, lean_object* v_h__1_3186_, lean_object* v_h__2_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(v_x_3184_, v_x_3185_, v_h__1_3186_, v_h__2_3187_);
lean_dec(v_x_3184_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(lean_object* v_00_u03b1_3189_, lean_object* v_motive_3190_, lean_object* v_x_3191_, lean_object* v_x_3192_, lean_object* v_h__1_3193_, lean_object* v_h__2_3194_){
_start:
{
lean_object* v_zero_3195_; uint8_t v_isZero_3196_; 
v_zero_3195_ = lean_unsigned_to_nat(0u);
v_isZero_3196_ = lean_nat_dec_eq(v_x_3191_, v_zero_3195_);
if (v_isZero_3196_ == 1)
{
lean_object* v___x_3197_; 
lean_dec(v_h__2_3194_);
v___x_3197_ = lean_apply_1(v_h__1_3193_, v_x_3192_);
return v___x_3197_;
}
else
{
lean_object* v_one_3198_; lean_object* v_n_3199_; lean_object* v___x_3200_; 
lean_dec(v_h__1_3193_);
v_one_3198_ = lean_unsigned_to_nat(1u);
v_n_3199_ = lean_nat_sub(v_x_3191_, v_one_3198_);
v___x_3200_ = lean_apply_2(v_h__2_3194_, v_n_3199_, v_x_3192_);
return v___x_3200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___boxed(lean_object* v_00_u03b1_3201_, lean_object* v_motive_3202_, lean_object* v_x_3203_, lean_object* v_x_3204_, lean_object* v_h__1_3205_, lean_object* v_h__2_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(v_00_u03b1_3201_, v_motive_3202_, v_x_3203_, v_x_3204_, v_h__1_3205_, v_h__2_3206_);
lean_dec(v_x_3203_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg(lean_object* v_n_3208_, lean_object* v_a_3209_, lean_object* v_l_3210_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = l_List_lengthTR___redArg(v_l_3210_);
v___x_3212_ = lean_nat_sub(v_n_3208_, v___x_3211_);
lean_dec(v___x_3211_);
v___x_3213_ = l_List_replicateTR_loop___redArg(v_a_3209_, v___x_3212_, v_l_3210_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg___boxed(lean_object* v_n_3214_, lean_object* v_a_3215_, lean_object* v_l_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_List_leftpadTR___redArg(v_n_3214_, v_a_3215_, v_l_3216_);
lean_dec(v_n_3214_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object* v_00_u03b1_3218_, lean_object* v_n_3219_, lean_object* v_a_3220_, lean_object* v_l_3221_){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3222_ = l_List_lengthTR___redArg(v_l_3221_);
v___x_3223_ = lean_nat_sub(v_n_3219_, v___x_3222_);
lean_dec(v___x_3222_);
v___x_3224_ = l_List_replicateTR_loop___redArg(v_a_3220_, v___x_3223_, v_l_3221_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___boxed(lean_object* v_00_u03b1_3225_, lean_object* v_n_3226_, lean_object* v_a_3227_, lean_object* v_l_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_List_leftpadTR(v_00_u03b1_3225_, v_n_3226_, v_a_3227_, v_l_3228_);
lean_dec(v_n_3226_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg(lean_object* v_init_3230_, lean_object* v_x_3231_){
_start:
{
if (lean_obj_tag(v_x_3231_) == 0)
{
lean_inc_ref(v_init_3230_);
return v_init_3230_;
}
else
{
lean_object* v_head_3232_; lean_object* v_tail_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3259_; 
v_head_3232_ = lean_ctor_get(v_x_3231_, 0);
v_tail_3233_ = lean_ctor_get(v_x_3231_, 1);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_x_3231_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3235_ = v_x_3231_;
v_isShared_3236_ = v_isSharedCheck_3259_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_tail_3233_);
lean_inc(v_head_3232_);
lean_dec(v_x_3231_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3259_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v_fst_3237_; lean_object* v_snd_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3258_; 
v_fst_3237_ = lean_ctor_get(v_head_3232_, 0);
v_snd_3238_ = lean_ctor_get(v_head_3232_, 1);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_head_3232_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3240_ = v_head_3232_;
v_isShared_3241_ = v_isSharedCheck_3258_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_snd_3238_);
lean_inc(v_fst_3237_);
lean_dec(v_head_3232_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3258_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; lean_object* v_fst_3243_; lean_object* v_snd_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3257_; 
v___x_3242_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3230_, v_tail_3233_);
v_fst_3243_ = lean_ctor_get(v___x_3242_, 0);
v_snd_3244_ = lean_ctor_get(v___x_3242_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3246_ = v___x_3242_;
v_isShared_3247_ = v_isSharedCheck_3257_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_snd_3244_);
lean_inc(v_fst_3243_);
lean_dec(v___x_3242_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3257_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 1, v_fst_3243_);
lean_ctor_set(v___x_3235_, 0, v_fst_3237_);
v___x_3249_ = v___x_3235_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_fst_3237_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_fst_3243_);
v___x_3249_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3251_; 
if (v_isShared_3241_ == 0)
{
lean_ctor_set_tag(v___x_3240_, 1);
lean_ctor_set(v___x_3240_, 1, v_snd_3244_);
lean_ctor_set(v___x_3240_, 0, v_snd_3238_);
v___x_3251_ = v___x_3240_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_snd_3238_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_snd_3244_);
v___x_3251_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
lean_object* v___x_3253_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 1, v___x_3251_);
lean_ctor_set(v___x_3246_, 0, v___x_3249_);
v___x_3253_ = v___x_3246_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg___boxed(lean_object* v_init_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3260_, v_x_3261_);
lean_dec_ref(v_init_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object* v_l_3263_){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_3265_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v___x_3264_, v_l_3263_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object* v_00_u03b1_3266_, lean_object* v_00_u03b2_3267_, lean_object* v_l_3268_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_List_unzipTR___redArg(v_l_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0(lean_object* v_00_u03b1_3270_, lean_object* v_00_u03b2_3271_, lean_object* v_init_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3272_, v_x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___boxed(lean_object* v_00_u03b1_3275_, lean_object* v_00_u03b2_3276_, lean_object* v_init_3277_, lean_object* v_x_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_List_foldr___at___00List_unzipTR_spec__0(v_00_u03b1_3275_, v_00_u03b2_3276_, v_init_3277_, v_x_3278_);
lean_dec_ref(v_init_3277_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object* v_step_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v_zero_3284_; uint8_t v_isZero_3285_; 
v_zero_3284_ = lean_unsigned_to_nat(0u);
v_isZero_3285_ = lean_nat_dec_eq(v_a_3281_, v_zero_3284_);
if (v_isZero_3285_ == 1)
{
lean_dec(v_a_3282_);
lean_dec(v_a_3281_);
return v_a_3283_;
}
else
{
lean_object* v_one_3286_; lean_object* v_n_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_one_3286_ = lean_unsigned_to_nat(1u);
v_n_3287_ = lean_nat_sub(v_a_3281_, v_one_3286_);
lean_dec(v_a_3281_);
v___x_3288_ = lean_nat_sub(v_a_3282_, v_step_3280_);
lean_dec(v_a_3282_);
lean_inc(v___x_3288_);
v___x_3289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
lean_ctor_set(v___x_3289_, 1, v_a_3283_);
v_a_3281_ = v_n_3287_;
v_a_3282_ = v___x_3288_;
v_a_3283_ = v___x_3289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object* v_step_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_List_range_x27TR_go(v_step_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
lean_dec(v_step_3291_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object* v_s_3296_, lean_object* v_n_3297_, lean_object* v_step_3298_){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3299_ = lean_nat_mul(v_step_3298_, v_n_3297_);
v___x_3300_ = lean_nat_add(v_s_3296_, v___x_3299_);
lean_dec(v___x_3299_);
v___x_3301_ = lean_box(0);
v___x_3302_ = l_List_range_x27TR_go(v_step_3298_, v_n_3297_, v___x_3300_, v___x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object* v_s_3303_, lean_object* v_n_3304_, lean_object* v_step_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_List_range_x27TR(v_s_3303_, v_n_3304_, v_step_3305_);
lean_dec(v_step_3305_);
lean_dec(v_s_3303_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(lean_object* v_x_3307_, lean_object* v_x_3308_, lean_object* v_x_3309_, lean_object* v_h__1_3310_, lean_object* v_h__2_3311_){
_start:
{
lean_object* v_zero_3312_; uint8_t v_isZero_3313_; 
v_zero_3312_ = lean_unsigned_to_nat(0u);
v_isZero_3313_ = lean_nat_dec_eq(v_x_3307_, v_zero_3312_);
if (v_isZero_3313_ == 1)
{
lean_object* v___x_3314_; 
lean_dec(v_h__2_3311_);
v___x_3314_ = lean_apply_2(v_h__1_3310_, v_x_3308_, v_x_3309_);
return v___x_3314_;
}
else
{
lean_object* v_one_3315_; lean_object* v_n_3316_; lean_object* v___x_3317_; 
lean_dec(v_h__1_3310_);
v_one_3315_ = lean_unsigned_to_nat(1u);
v_n_3316_ = lean_nat_sub(v_x_3307_, v_one_3315_);
v___x_3317_ = lean_apply_3(v_h__2_3311_, v_n_3316_, v_x_3308_, v_x_3309_);
return v___x_3317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(lean_object* v_x_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_, lean_object* v_h__1_3321_, lean_object* v_h__2_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(v_x_3318_, v_x_3319_, v_x_3320_, v_h__1_3321_, v_h__2_3322_);
lean_dec(v_x_3318_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object* v_motive_3324_, lean_object* v_x_3325_, lean_object* v_x_3326_, lean_object* v_x_3327_, lean_object* v_h__1_3328_, lean_object* v_h__2_3329_){
_start:
{
lean_object* v_zero_3330_; uint8_t v_isZero_3331_; 
v_zero_3330_ = lean_unsigned_to_nat(0u);
v_isZero_3331_ = lean_nat_dec_eq(v_x_3325_, v_zero_3330_);
if (v_isZero_3331_ == 1)
{
lean_object* v___x_3332_; 
lean_dec(v_h__2_3329_);
v___x_3332_ = lean_apply_2(v_h__1_3328_, v_x_3326_, v_x_3327_);
return v___x_3332_;
}
else
{
lean_object* v_one_3333_; lean_object* v_n_3334_; lean_object* v___x_3335_; 
lean_dec(v_h__1_3328_);
v_one_3333_ = lean_unsigned_to_nat(1u);
v_n_3334_ = lean_nat_sub(v_x_3325_, v_one_3333_);
v___x_3335_ = lean_apply_3(v_h__2_3329_, v_n_3334_, v_x_3326_, v_x_3327_);
return v___x_3335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(lean_object* v_motive_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_, lean_object* v_x_3339_, lean_object* v_h__1_3340_, lean_object* v_h__2_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(v_motive_3336_, v_x_3337_, v_x_3338_, v_x_3339_, v_h__1_3340_, v_h__2_3341_);
lean_dec(v_x_3337_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg(lean_object* v_sep_3343_, lean_object* v_init_3344_, lean_object* v_x_3345_){
_start:
{
if (lean_obj_tag(v_x_3345_) == 0)
{
lean_dec(v_sep_3343_);
lean_inc(v_init_3344_);
return v_init_3344_;
}
else
{
lean_object* v_head_3346_; lean_object* v_tail_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3356_; 
v_head_3346_ = lean_ctor_get(v_x_3345_, 0);
v_tail_3347_ = lean_ctor_get(v_x_3345_, 1);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_x_3345_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3349_ = v_x_3345_;
v_isShared_3350_ = v_isSharedCheck_3356_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_tail_3347_);
lean_inc(v_head_3346_);
lean_dec(v_x_3345_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3356_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
lean_inc(v_sep_3343_);
v___x_3351_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3343_, v_init_3344_, v_tail_3347_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v___x_3351_);
v___x_3353_ = v___x_3349_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_head_3346_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3354_, 0, v_sep_3343_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
return v___x_3354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(lean_object* v_sep_3357_, lean_object* v_init_3358_, lean_object* v_x_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3357_, v_init_3358_, v_x_3359_);
lean_dec(v_init_3358_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object* v_sep_3361_, lean_object* v_x_3362_){
_start:
{
if (lean_obj_tag(v_x_3362_) == 0)
{
lean_dec(v_sep_3361_);
return v_x_3362_;
}
else
{
lean_object* v_tail_3363_; 
v_tail_3363_ = lean_ctor_get(v_x_3362_, 1);
lean_inc(v_tail_3363_);
if (lean_obj_tag(v_tail_3363_) == 0)
{
lean_dec(v_sep_3361_);
return v_x_3362_;
}
else
{
lean_object* v_head_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3383_; 
v_head_3364_ = lean_ctor_get(v_x_3362_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_x_3362_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; 
v_unused_3384_ = lean_ctor_get(v_x_3362_, 1);
lean_dec(v_unused_3384_);
v___x_3366_ = v_x_3362_;
v_isShared_3367_ = v_isSharedCheck_3383_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_head_3364_);
lean_dec(v_x_3362_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3383_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_head_3368_; lean_object* v_tail_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3382_; 
v_head_3368_ = lean_ctor_get(v_tail_3363_, 0);
v_tail_3369_ = lean_ctor_get(v_tail_3363_, 1);
v_isSharedCheck_3382_ = !lean_is_exclusive(v_tail_3363_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3371_ = v_tail_3363_;
v_isShared_3372_ = v_isSharedCheck_3382_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_tail_3369_);
lean_inc(v_head_3368_);
lean_dec(v_tail_3363_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3382_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3376_; 
v___x_3373_ = lean_box(0);
lean_inc(v_sep_3361_);
v___x_3374_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3361_, v___x_3373_, v_tail_3369_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 1, v___x_3374_);
v___x_3376_ = v___x_3371_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_head_3368_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3378_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 1, v___x_3376_);
lean_ctor_set(v___x_3366_, 0, v_sep_3361_);
v___x_3378_ = v___x_3366_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_sep_3361_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3379_, 0, v_head_3364_);
lean_ctor_set(v___x_3379_, 1, v___x_3378_);
return v___x_3379_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object* v_00_u03b1_3385_, lean_object* v_sep_3386_, lean_object* v_x_3387_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_List_intersperseTR___redArg(v_sep_3386_, v_x_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0(lean_object* v_00_u03b1_3389_, lean_object* v_sep_3390_, lean_object* v_init_3391_, lean_object* v_x_3392_){
_start:
{
lean_object* v___x_3393_; 
v___x_3393_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3390_, v_init_3391_, v_x_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___boxed(lean_object* v_00_u03b1_3394_, lean_object* v_sep_3395_, lean_object* v_init_3396_, lean_object* v_x_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_List_foldr___at___00List_intersperseTR_spec__0(v_00_u03b1_3394_, v_sep_3395_, v_init_3396_, v_x_3397_);
lean_dec(v_init_3396_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(lean_object* v_x_3399_, lean_object* v_h__1_3400_, lean_object* v_h__2_3401_, lean_object* v_h__3_3402_){
_start:
{
if (lean_obj_tag(v_x_3399_) == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec(v_h__3_3402_);
lean_dec(v_h__2_3401_);
v___x_3403_ = lean_box(0);
v___x_3404_ = lean_apply_1(v_h__1_3400_, v___x_3403_);
return v___x_3404_;
}
else
{
lean_object* v_tail_3405_; 
lean_dec(v_h__1_3400_);
v_tail_3405_ = lean_ctor_get(v_x_3399_, 1);
if (lean_obj_tag(v_tail_3405_) == 0)
{
lean_object* v_head_3406_; lean_object* v___x_3407_; 
lean_dec(v_h__3_3402_);
v_head_3406_ = lean_ctor_get(v_x_3399_, 0);
lean_inc(v_head_3406_);
lean_dec_ref(v_x_3399_);
v___x_3407_ = lean_apply_1(v_h__2_3401_, v_head_3406_);
return v___x_3407_;
}
else
{
lean_object* v_head_3408_; lean_object* v_head_3409_; lean_object* v_tail_3410_; lean_object* v___x_3411_; 
lean_inc_ref(v_tail_3405_);
lean_dec(v_h__2_3401_);
v_head_3408_ = lean_ctor_get(v_x_3399_, 0);
lean_inc(v_head_3408_);
lean_dec_ref(v_x_3399_);
v_head_3409_ = lean_ctor_get(v_tail_3405_, 0);
lean_inc(v_head_3409_);
v_tail_3410_ = lean_ctor_get(v_tail_3405_, 1);
lean_inc(v_tail_3410_);
lean_dec_ref(v_tail_3405_);
v___x_3411_ = lean_apply_3(v_h__3_3402_, v_head_3408_, v_head_3409_, v_tail_3410_);
return v___x_3411_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object* v_00_u03b1_3412_, lean_object* v_motive_3413_, lean_object* v_x_3414_, lean_object* v_h__1_3415_, lean_object* v_h__2_3416_, lean_object* v_h__3_3417_){
_start:
{
if (lean_obj_tag(v_x_3414_) == 0)
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec(v_h__3_3417_);
lean_dec(v_h__2_3416_);
v___x_3418_ = lean_box(0);
v___x_3419_ = lean_apply_1(v_h__1_3415_, v___x_3418_);
return v___x_3419_;
}
else
{
lean_object* v_tail_3420_; 
lean_dec(v_h__1_3415_);
v_tail_3420_ = lean_ctor_get(v_x_3414_, 1);
if (lean_obj_tag(v_tail_3420_) == 0)
{
lean_object* v_head_3421_; lean_object* v___x_3422_; 
lean_dec(v_h__3_3417_);
v_head_3421_ = lean_ctor_get(v_x_3414_, 0);
lean_inc(v_head_3421_);
lean_dec_ref(v_x_3414_);
v___x_3422_ = lean_apply_1(v_h__2_3416_, v_head_3421_);
return v___x_3422_;
}
else
{
lean_object* v_head_3423_; lean_object* v_head_3424_; lean_object* v_tail_3425_; lean_object* v___x_3426_; 
lean_inc_ref(v_tail_3420_);
lean_dec(v_h__2_3416_);
v_head_3423_ = lean_ctor_get(v_x_3414_, 0);
lean_inc(v_head_3423_);
lean_dec_ref(v_x_3414_);
v_head_3424_ = lean_ctor_get(v_tail_3420_, 0);
lean_inc(v_head_3424_);
v_tail_3425_ = lean_ctor_get(v_tail_3420_, 1);
lean_inc(v_tail_3425_);
lean_dec_ref(v_tail_3420_);
v___x_3426_ = lean_apply_3(v_h__3_3417_, v_head_3423_, v_head_3424_, v_tail_3425_);
return v___x_3426_;
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
