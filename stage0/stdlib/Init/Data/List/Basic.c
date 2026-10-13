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
LEAN_EXPORT lean_object* l_List_instLT___redArg();
LEAN_EXPORT lean_object* l_List_instLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instLT(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLE___redArg();
LEAN_EXPORT lean_object* l_List_instLE___redArg___boxed(lean_object*);
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
static const lean_ctor_object l_List_lex___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l_List_lex___auto__1___closed__25 = (const lean_object*)&l_List_lex___auto__1___closed__25_value;
static const lean_ctor_object l_List_lex___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_lex___auto__1___closed__26 = (const lean_object*)&l_List_lex___auto__1___closed__26_value;
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
static const lean_string_object l_List_lex___auto__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l_List_lex___auto__1___closed__32 = (const lean_object*)&l_List_lex___auto__1___closed__32_value;
static const lean_ctor_object l_List_lex___auto__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l_List_lex___auto__1___closed__33 = (const lean_object*)&l_List_lex___auto__1___closed__33_value;
static const lean_string_object l_List_lex___auto__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l_List_lex___auto__1___closed__34 = (const lean_object*)&l_List_lex___auto__1___closed__34_value;
static const lean_ctor_object l_List_lex___auto__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_lex___auto__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__35_value_aux_0),((lean_object*)&l_List_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_lex___auto__1___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__35_value_aux_1),((lean_object*)&l_List_lex___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_lex___auto__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_lex___auto__1___closed__35_value_aux_2),((lean_object*)&l_List_lex___auto__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l_List_lex___auto__1___closed__35 = (const lean_object*)&l_List_lex___auto__1___closed__35_value;
static const lean_string_object l_List_lex___auto__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l_List_lex___auto__1___closed__36 = (const lean_object*)&l_List_lex___auto__1___closed__36_value;
static lean_once_cell_t l_List_lex___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__37;
static lean_once_cell_t l_List_lex___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__38;
static lean_once_cell_t l_List_lex___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__39;
static lean_once_cell_t l_List_lex___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__40;
static lean_once_cell_t l_List_lex___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__41;
static const lean_string_object l_List_lex___auto__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_List_lex___auto__1___closed__42 = (const lean_object*)&l_List_lex___auto__1___closed__42_value;
static lean_once_cell_t l_List_lex___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__43;
static lean_once_cell_t l_List_lex___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__44;
static lean_once_cell_t l_List_lex___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__45;
static lean_once_cell_t l_List_lex___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__46;
static lean_once_cell_t l_List_lex___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__47;
static const lean_string_object l_List_lex___auto__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_List_lex___auto__1___closed__48 = (const lean_object*)&l_List_lex___auto__1___closed__48_value;
static lean_once_cell_t l_List_lex___auto__1___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_lex___auto__1___closed__49;
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
static const lean_closure_object l_List_instAppend___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_appendTR, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_List_instAppend___redArg___closed__0 = (const lean_object*)&l_List_instAppend___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_instAppend___redArg();
LEAN_EXPORT lean_object* l_List_instAppend___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_List_instMembership___redArg();
LEAN_EXPORT lean_object* l_List_instMembership___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg();
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg___boxed(lean_object*);
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
lean_object* v_head_133_; lean_object* v_tail_134_; lean_object* v_head_135_; lean_object* v_tail_136_; lean_object* v_decide_137_; uint8_t v___x_138_; 
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
lean_inc_ref(v_h_127_);
v_decide_137_ = lean_apply_2(v_h_127_, v_head_133_, v_head_135_);
v___x_138_ = lean_unbox(v_decide_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; uint8_t v___x_140_; 
lean_inc_ref(v_inst_126_);
v___x_139_ = lean_apply_2(v_inst_126_, v_head_133_, v_head_135_);
v___x_140_ = lean_unbox(v___x_139_);
if (v___x_140_ == 0)
{
uint8_t v___x_141_; 
lean_dec(v_tail_136_);
lean_dec(v_tail_134_);
lean_dec_ref(v_h_127_);
lean_dec_ref(v_inst_126_);
v___x_141_ = lean_unbox(v___x_139_);
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
v___x_143_ = lean_unbox(v___x_139_);
return v___x_143_;
}
}
}
else
{
uint8_t v___x_144_; 
lean_dec(v_tail_136_);
lean_dec(v_head_135_);
lean_dec(v_tail_134_);
lean_dec(v_head_133_);
lean_dec_ref(v_h_127_);
lean_dec_ref(v_inst_126_);
v___x_144_ = lean_unbox(v_decide_137_);
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
LEAN_EXPORT lean_object* l_List_instLT___redArg(){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_List_instLT___redArg___boxed(lean_object* v___dummy_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_List_instLT___redArg();
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_List_instLT(lean_object* v_00_u03b1_170_, lean_object* v_inst_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLT___redArg(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_l_u2081_175_, lean_object* v_l_u2082_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = l_List_decidableLex___redArg(v_inst_173_, v_inst_174_, v_l_u2081_175_, v_l_u2082_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLT___redArg___boxed(lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_l_u2081_180_, lean_object* v_l_u2082_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_List_decidableLT___redArg(v_inst_178_, v_inst_179_, v_l_u2081_180_, v_l_u2082_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLT(lean_object* v_00_u03b1_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_l_u2081_188_, lean_object* v_l_u2082_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = l_List_decidableLex___redArg(v_inst_185_, v_inst_187_, v_l_u2081_188_, v_l_u2082_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLT___boxed(lean_object* v_00_u03b1_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_l_u2081_195_, lean_object* v_l_u2082_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_List_decidableLT(v_00_u03b1_191_, v_inst_192_, v_inst_193_, v_inst_194_, v_l_u2081_195_, v_l_u2082_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT lean_object* l_List_instLE___redArg(){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_List_instLE___redArg___boxed(lean_object* v___dummy_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_List_instLE___redArg();
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_List_instLE(lean_object* v_00_u03b1_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLE___redArg(lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_l_u2081_208_, lean_object* v_l_u2082_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = l_List_decidableLex___redArg(v_inst_206_, v_inst_207_, v_l_u2082_209_, v_l_u2081_208_);
if (v___x_210_ == 0)
{
uint8_t v___x_211_; 
v___x_211_ = 1;
return v___x_211_;
}
else
{
uint8_t v___x_212_; 
v___x_212_ = 0;
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_List_decidableLE___redArg___boxed(lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_l_u2081_215_, lean_object* v_l_u2082_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_List_decidableLE___redArg(v_inst_213_, v_inst_214_, v_l_u2081_215_, v_l_u2082_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLE(lean_object* v_00_u03b1_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_l_u2081_223_, lean_object* v_l_u2082_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = l_List_decidableLE___redArg(v_inst_220_, v_inst_222_, v_l_u2081_223_, v_l_u2082_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLE___boxed(lean_object* v_00_u03b1_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_l_u2081_230_, lean_object* v_l_u2082_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_List_decidableLE(v_00_u03b1_226_, v_inst_227_, v_inst_228_, v_inst_229_, v_l_u2081_230_, v_l_u2082_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__12(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_List_lex___auto__1___closed__10));
v___x_261_ = l_Lean_mkAtom(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l_List_lex___auto__1___closed__12, &l_List_lex___auto__1___closed__12_once, _init_l_List_lex___auto__1___closed__12);
v___x_263_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_264_ = lean_array_push(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_List_lex___auto__1___closed__19));
v___x_280_ = l_Lean_mkAtom(v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__21(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_obj_once(&l_List_lex___auto__1___closed__20, &l_List_lex___auto__1___closed__20_once, _init_l_List_lex___auto__1___closed__20);
v___x_282_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_283_ = lean_array_push(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = ((lean_object*)(l_List_lex___auto__1___closed__26));
v___x_298_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_299_ = lean_array_push(v___x_298_, v___x_297_);
return v___x_299_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_300_ = lean_obj_once(&l_List_lex___auto__1___closed__27, &l_List_lex___auto__1___closed__27_once, _init_l_List_lex___auto__1___closed__27);
v___x_301_ = ((lean_object*)(l_List_lex___auto__1___closed__23));
v___x_302_ = lean_box(2);
v___x_303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_301_);
lean_ctor_set(v___x_303_, 2, v___x_300_);
return v___x_303_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_List_lex___auto__1___closed__28, &l_List_lex___auto__1___closed__28_once, _init_l_List_lex___auto__1___closed__28);
v___x_305_ = lean_obj_once(&l_List_lex___auto__1___closed__21, &l_List_lex___auto__1___closed__21_once, _init_l_List_lex___auto__1___closed__21);
v___x_306_ = lean_array_push(v___x_305_, v___x_304_);
return v___x_306_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_308_ = ((lean_object*)(l_List_lex___auto__1___closed__18));
v___x_309_ = lean_box(2);
v___x_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_308_);
lean_ctor_set(v___x_310_, 2, v___x_307_);
return v___x_310_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_obj_once(&l_List_lex___auto__1___closed__30, &l_List_lex___auto__1___closed__30_once, _init_l_List_lex___auto__1___closed__30);
v___x_312_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_313_ = lean_array_push(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l_List_lex___auto__1___closed__36));
v___x_325_ = l_Lean_mkAtom(v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_obj_once(&l_List_lex___auto__1___closed__37, &l_List_lex___auto__1___closed__37_once, _init_l_List_lex___auto__1___closed__37);
v___x_327_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_328_ = lean_array_push(v___x_327_, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_obj_once(&l_List_lex___auto__1___closed__28, &l_List_lex___auto__1___closed__28_once, _init_l_List_lex___auto__1___closed__28);
v___x_330_ = lean_obj_once(&l_List_lex___auto__1___closed__38, &l_List_lex___auto__1___closed__38_once, _init_l_List_lex___auto__1___closed__38);
v___x_331_ = lean_array_push(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_332_ = lean_obj_once(&l_List_lex___auto__1___closed__39, &l_List_lex___auto__1___closed__39_once, _init_l_List_lex___auto__1___closed__39);
v___x_333_ = ((lean_object*)(l_List_lex___auto__1___closed__35));
v___x_334_ = lean_box(2);
v___x_335_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
lean_ctor_set(v___x_335_, 2, v___x_332_);
return v___x_335_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_obj_once(&l_List_lex___auto__1___closed__40, &l_List_lex___auto__1___closed__40_once, _init_l_List_lex___auto__1___closed__40);
v___x_337_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_338_ = lean_array_push(v___x_337_, v___x_336_);
return v___x_338_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_List_lex___auto__1___closed__42));
v___x_341_ = l_Lean_mkAtom(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_obj_once(&l_List_lex___auto__1___closed__43, &l_List_lex___auto__1___closed__43_once, _init_l_List_lex___auto__1___closed__43);
v___x_343_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_344_ = lean_array_push(v___x_343_, v___x_342_);
return v___x_344_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_obj_once(&l_List_lex___auto__1___closed__40, &l_List_lex___auto__1___closed__40_once, _init_l_List_lex___auto__1___closed__40);
v___x_346_ = lean_obj_once(&l_List_lex___auto__1___closed__44, &l_List_lex___auto__1___closed__44_once, _init_l_List_lex___auto__1___closed__44);
v___x_347_ = lean_array_push(v___x_346_, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_348_ = lean_obj_once(&l_List_lex___auto__1___closed__45, &l_List_lex___auto__1___closed__45_once, _init_l_List_lex___auto__1___closed__45);
v___x_349_ = ((lean_object*)(l_List_lex___auto__1___closed__33));
v___x_350_ = lean_box(2);
v___x_351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
lean_ctor_set(v___x_351_, 2, v___x_348_);
return v___x_351_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&l_List_lex___auto__1___closed__46, &l_List_lex___auto__1___closed__46_once, _init_l_List_lex___auto__1___closed__46);
v___x_353_ = lean_obj_once(&l_List_lex___auto__1___closed__31, &l_List_lex___auto__1___closed__31_once, _init_l_List_lex___auto__1___closed__31);
v___x_354_ = lean_array_push(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__49(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_List_lex___auto__1___closed__48));
v___x_357_ = l_Lean_mkAtom(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__50(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_obj_once(&l_List_lex___auto__1___closed__49, &l_List_lex___auto__1___closed__49_once, _init_l_List_lex___auto__1___closed__49);
v___x_359_ = lean_obj_once(&l_List_lex___auto__1___closed__47, &l_List_lex___auto__1___closed__47_once, _init_l_List_lex___auto__1___closed__47);
v___x_360_ = lean_array_push(v___x_359_, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__51(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_361_ = lean_obj_once(&l_List_lex___auto__1___closed__50, &l_List_lex___auto__1___closed__50_once, _init_l_List_lex___auto__1___closed__50);
v___x_362_ = ((lean_object*)(l_List_lex___auto__1___closed__16));
v___x_363_ = lean_box(2);
v___x_364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
lean_ctor_set(v___x_364_, 2, v___x_361_);
return v___x_364_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__52(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = lean_obj_once(&l_List_lex___auto__1___closed__51, &l_List_lex___auto__1___closed__51_once, _init_l_List_lex___auto__1___closed__51);
v___x_366_ = lean_obj_once(&l_List_lex___auto__1___closed__13, &l_List_lex___auto__1___closed__13_once, _init_l_List_lex___auto__1___closed__13);
v___x_367_ = lean_array_push(v___x_366_, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__53(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_368_ = lean_obj_once(&l_List_lex___auto__1___closed__52, &l_List_lex___auto__1___closed__52_once, _init_l_List_lex___auto__1___closed__52);
v___x_369_ = ((lean_object*)(l_List_lex___auto__1___closed__11));
v___x_370_ = lean_box(2);
v___x_371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_369_);
lean_ctor_set(v___x_371_, 2, v___x_368_);
return v___x_371_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__54(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_List_lex___auto__1___closed__53, &l_List_lex___auto__1___closed__53_once, _init_l_List_lex___auto__1___closed__53);
v___x_373_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_374_ = lean_array_push(v___x_373_, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__55(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_375_ = lean_obj_once(&l_List_lex___auto__1___closed__54, &l_List_lex___auto__1___closed__54_once, _init_l_List_lex___auto__1___closed__54);
v___x_376_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_377_ = lean_box(2);
v___x_378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v___x_376_);
lean_ctor_set(v___x_378_, 2, v___x_375_);
return v___x_378_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__56(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l_List_lex___auto__1___closed__55, &l_List_lex___auto__1___closed__55_once, _init_l_List_lex___auto__1___closed__55);
v___x_380_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_381_ = lean_array_push(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__57(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_382_ = lean_obj_once(&l_List_lex___auto__1___closed__56, &l_List_lex___auto__1___closed__56_once, _init_l_List_lex___auto__1___closed__56);
v___x_383_ = ((lean_object*)(l_List_lex___auto__1___closed__7));
v___x_384_ = lean_box(2);
v___x_385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___x_383_);
lean_ctor_set(v___x_385_, 2, v___x_382_);
return v___x_385_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__58(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = lean_obj_once(&l_List_lex___auto__1___closed__57, &l_List_lex___auto__1___closed__57_once, _init_l_List_lex___auto__1___closed__57);
v___x_387_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_388_ = lean_array_push(v___x_387_, v___x_386_);
return v___x_388_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__59(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_389_ = lean_obj_once(&l_List_lex___auto__1___closed__58, &l_List_lex___auto__1___closed__58_once, _init_l_List_lex___auto__1___closed__58);
v___x_390_ = ((lean_object*)(l_List_lex___auto__1___closed__4));
v___x_391_ = lean_box(2);
v___x_392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_390_);
lean_ctor_set(v___x_392_, 2, v___x_389_);
return v___x_392_;
}
}
static lean_object* _init_l_List_lex___auto__1(void){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_obj_once(&l_List_lex___auto__1___closed__59, &l_List_lex___auto__1___closed__59_once, _init_l_List_lex___auto__1___closed__59);
return v___x_393_;
}
}
LEAN_EXPORT uint8_t l_List_lex___redArg(lean_object* v_inst_394_, lean_object* v_l_u2081_395_, lean_object* v_l_u2082_396_, lean_object* v_lt_397_){
_start:
{
if (lean_obj_tag(v_l_u2081_395_) == 0)
{
lean_dec_ref(v_lt_397_);
lean_dec_ref(v_inst_394_);
if (lean_obj_tag(v_l_u2082_396_) == 0)
{
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
else
{
uint8_t v___x_399_; 
lean_dec_ref_known(v_l_u2082_396_, 2);
v___x_399_ = 1;
return v___x_399_;
}
}
else
{
if (lean_obj_tag(v_l_u2082_396_) == 0)
{
uint8_t v___x_400_; 
lean_dec_ref_known(v_l_u2081_395_, 2);
lean_dec_ref(v_lt_397_);
lean_dec_ref(v_inst_394_);
v___x_400_ = 0;
return v___x_400_;
}
else
{
lean_object* v_head_401_; lean_object* v_tail_402_; lean_object* v_head_403_; lean_object* v_tail_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_head_401_ = lean_ctor_get(v_l_u2081_395_, 0);
lean_inc_n(v_head_401_, 2);
v_tail_402_ = lean_ctor_get(v_l_u2081_395_, 1);
lean_inc(v_tail_402_);
lean_dec_ref_known(v_l_u2081_395_, 2);
v_head_403_ = lean_ctor_get(v_l_u2082_396_, 0);
lean_inc_n(v_head_403_, 2);
v_tail_404_ = lean_ctor_get(v_l_u2082_396_, 1);
lean_inc(v_tail_404_);
lean_dec_ref_known(v_l_u2082_396_, 2);
lean_inc_ref(v_lt_397_);
v___x_405_ = lean_apply_2(v_lt_397_, v_head_401_, v_head_403_);
v___x_406_ = lean_unbox(v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; uint8_t v___x_408_; 
lean_inc_ref(v_inst_394_);
v___x_407_ = lean_apply_2(v_inst_394_, v_head_401_, v_head_403_);
v___x_408_ = lean_unbox(v___x_407_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; 
lean_dec(v_tail_404_);
lean_dec(v_tail_402_);
lean_dec_ref(v_lt_397_);
lean_dec_ref(v_inst_394_);
v___x_409_ = lean_unbox(v___x_407_);
return v___x_409_;
}
else
{
v_l_u2081_395_ = v_tail_402_;
v_l_u2082_396_ = v_tail_404_;
goto _start;
}
}
else
{
uint8_t v___x_411_; 
lean_dec(v_tail_404_);
lean_dec(v_head_403_);
lean_dec(v_tail_402_);
lean_dec(v_head_401_);
lean_dec_ref(v_lt_397_);
lean_dec_ref(v_inst_394_);
v___x_411_ = lean_unbox(v___x_405_);
return v___x_411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_lex___redArg___boxed(lean_object* v_inst_412_, lean_object* v_l_u2081_413_, lean_object* v_l_u2082_414_, lean_object* v_lt_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_List_lex___redArg(v_inst_412_, v_l_u2081_413_, v_l_u2082_414_, v_lt_415_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l_List_lex(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_, lean_object* v_l_u2081_420_, lean_object* v_l_u2082_421_, lean_object* v_lt_422_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = l_List_lex___redArg(v_inst_419_, v_l_u2081_420_, v_l_u2082_421_, v_lt_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_List_lex___boxed(lean_object* v_00_u03b1_424_, lean_object* v_inst_425_, lean_object* v_l_u2081_426_, lean_object* v_l_u2082_427_, lean_object* v_lt_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l_List_lex(v_00_u03b1_424_, v_inst_425_, v_l_u2081_426_, v_l_u2082_427_, v_lt_428_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg(lean_object* v_x_431_){
_start:
{
lean_object* v_tail_432_; 
v_tail_432_ = lean_ctor_get(v_x_431_, 1);
if (lean_obj_tag(v_tail_432_) == 0)
{
lean_object* v_head_433_; 
v_head_433_ = lean_ctor_get(v_x_431_, 0);
lean_inc(v_head_433_);
return v_head_433_;
}
else
{
v_x_431_ = v_tail_432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg___boxed(lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_List_getLast___redArg(v_x_435_);
lean_dec(v_x_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_List_getLast(lean_object* v_00_u03b1_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_List_getLast___redArg(v_x_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___boxed(lean_object* v_00_u03b1_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_List_getLast(v_00_u03b1_441_, v_x_442_, v_x_443_);
lean_dec(v_x_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg(lean_object* v_x_445_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v___x_446_; 
v___x_446_ = lean_box(0);
return v___x_446_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = l_List_getLast___redArg(v_x_445_);
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg___boxed(lean_object* v_x_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_List_getLast_x3f___redArg(v_x_449_);
lean_dec(v_x_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f(lean_object* v_00_u03b1_451_, lean_object* v_x_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_List_getLast_x3f___redArg(v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___boxed(lean_object* v_00_u03b1_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_List_getLast_x3f(v_00_u03b1_454_, v_x_455_);
lean_dec(v_x_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg(lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_inc(v_x_458_);
return v_x_458_;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l_List_getLast___redArg(v_x_457_);
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg___boxed(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_List_getLastD___redArg(v_x_460_, v_x_461_);
lean_dec(v_x_461_);
lean_dec(v_x_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD(lean_object* v_00_u03b1_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_List_getLastD___redArg(v_x_464_, v_x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___boxed(lean_object* v_00_u03b1_467_, lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_List_getLastD(v_00_u03b1_467_, v_x_468_, v_x_469_);
lean_dec(v_x_469_);
lean_dec(v_x_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg(lean_object* v_x_471_){
_start:
{
lean_object* v_head_472_; 
v_head_472_ = lean_ctor_get(v_x_471_, 0);
lean_inc(v_head_472_);
return v_head_472_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg___boxed(lean_object* v_x_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_List_head___redArg(v_x_473_);
lean_dec(v_x_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_List_head(lean_object* v_00_u03b1_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
lean_object* v_head_478_; 
v_head_478_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_head_478_);
return v_head_478_;
}
}
LEAN_EXPORT lean_object* l_List_head___boxed(lean_object* v_00_u03b1_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_List_head(v_00_u03b1_479_, v_x_480_, v_x_481_);
lean_dec(v_x_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg(lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_box(0);
return v___x_484_;
}
else
{
lean_object* v_head_485_; lean_object* v___x_486_; 
v_head_485_ = lean_ctor_get(v_x_483_, 0);
lean_inc(v_head_485_);
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v_head_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg___boxed(lean_object* v_x_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_List_head_x3f___redArg(v_x_487_);
lean_dec(v_x_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f(lean_object* v_00_u03b1_489_, lean_object* v_x_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_List_head_x3f___redArg(v_x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___boxed(lean_object* v_00_u03b1_492_, lean_object* v_x_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_List_head_x3f(v_00_u03b1_492_, v_x_493_);
lean_dec(v_x_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg(lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_inc(v_x_496_);
return v_x_496_;
}
else
{
lean_object* v_head_497_; 
v_head_497_ = lean_ctor_get(v_x_495_, 0);
lean_inc(v_head_497_);
return v_head_497_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg___boxed(lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_List_headD___redArg(v_x_498_, v_x_499_);
lean_dec(v_x_499_);
lean_dec(v_x_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_List_headD(lean_object* v_00_u03b1_501_, lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_502_) == 0)
{
lean_inc(v_x_503_);
return v_x_503_;
}
else
{
lean_object* v_head_504_; 
v_head_504_ = lean_ctor_get(v_x_502_, 0);
lean_inc(v_head_504_);
return v_head_504_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___boxed(lean_object* v_00_u03b1_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_List_headD(v_00_u03b1_505_, v_x_506_, v_x_507_);
lean_dec(v_x_507_);
lean_dec(v_x_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg(lean_object* v_x_509_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
return v_x_509_;
}
else
{
lean_object* v_tail_510_; 
v_tail_510_ = lean_ctor_get(v_x_509_, 1);
lean_inc(v_tail_510_);
return v_tail_510_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg___boxed(lean_object* v_x_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_List_tail___redArg(v_x_511_);
lean_dec(v_x_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_List_tail(lean_object* v_00_u03b1_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
return v_x_514_;
}
else
{
lean_object* v_tail_515_; 
v_tail_515_ = lean_ctor_get(v_x_514_, 1);
lean_inc(v_tail_515_);
return v_tail_515_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___boxed(lean_object* v_00_u03b1_516_, lean_object* v_x_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_List_tail(v_00_u03b1_516_, v_x_517_);
lean_dec(v_x_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg(lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
else
{
lean_object* v_tail_521_; lean_object* v___x_522_; 
v_tail_521_ = lean_ctor_get(v_x_519_, 1);
lean_inc(v_tail_521_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v_tail_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg___boxed(lean_object* v_x_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_List_tail_x3f___redArg(v_x_523_);
lean_dec(v_x_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f(lean_object* v_00_u03b1_525_, lean_object* v_x_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_List_tail_x3f___redArg(v_x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___boxed(lean_object* v_00_u03b1_528_, lean_object* v_x_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_List_tail_x3f(v_00_u03b1_528_, v_x_529_);
lean_dec(v_x_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg(lean_object* v_l_531_, lean_object* v_fallback_532_){
_start:
{
if (lean_obj_tag(v_l_531_) == 0)
{
lean_inc(v_fallback_532_);
return v_fallback_532_;
}
else
{
lean_object* v_tail_533_; 
v_tail_533_ = lean_ctor_get(v_l_531_, 1);
lean_inc(v_tail_533_);
return v_tail_533_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg___boxed(lean_object* v_l_534_, lean_object* v_fallback_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_List_tailD___redArg(v_l_534_, v_fallback_535_);
lean_dec(v_fallback_535_);
lean_dec(v_l_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_List_tailD(lean_object* v_00_u03b1_537_, lean_object* v_l_538_, lean_object* v_fallback_539_){
_start:
{
if (lean_obj_tag(v_l_538_) == 0)
{
lean_inc(v_fallback_539_);
return v_fallback_539_;
}
else
{
lean_object* v_tail_540_; 
v_tail_540_ = lean_ctor_get(v_l_538_, 1);
lean_inc(v_tail_540_);
return v_tail_540_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___boxed(lean_object* v_00_u03b1_541_, lean_object* v_l_542_, lean_object* v_fallback_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_List_tailD(v_00_u03b1_541_, v_l_542_, v_fallback_543_);
lean_dec(v_fallback_543_);
lean_dec(v_l_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_List_filter___redArg(lean_object* v_p_545_, lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
lean_dec_ref(v_p_545_);
return v_x_546_;
}
else
{
lean_object* v_head_547_; lean_object* v_tail_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_559_; 
v_head_547_ = lean_ctor_get(v_x_546_, 0);
v_tail_548_ = lean_ctor_get(v_x_546_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_546_);
if (v_isSharedCheck_559_ == 0)
{
v___x_550_ = v_x_546_;
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_tail_548_);
lean_inc(v_head_547_);
lean_dec(v_x_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; uint8_t v___x_553_; 
lean_inc_ref(v_p_545_);
lean_inc(v_head_547_);
v___x_552_ = lean_apply_1(v_p_545_, v_head_547_);
v___x_553_ = lean_unbox(v___x_552_);
if (v___x_553_ == 0)
{
lean_del_object(v___x_550_);
lean_dec(v_head_547_);
v_x_546_ = v_tail_548_;
goto _start;
}
else
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = l_List_filter___redArg(v_p_545_, v_tail_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_555_);
v___x_557_ = v___x_550_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_head_547_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filter(lean_object* v_00_u03b1_560_, lean_object* v_p_561_, lean_object* v_x_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_List_filter___redArg(v_p_561_, v_x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg(lean_object* v_f_564_, lean_object* v_init_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_dec(v_f_564_);
lean_inc(v_init_565_);
return v_init_565_;
}
else
{
lean_object* v_head_567_; lean_object* v_tail_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_head_567_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_head_567_);
v_tail_568_ = lean_ctor_get(v_x_566_, 1);
lean_inc(v_tail_568_);
lean_dec_ref_known(v_x_566_, 2);
lean_inc(v_f_564_);
v___x_569_ = l_List_foldr___redArg(v_f_564_, v_init_565_, v_tail_568_);
v___x_570_ = lean_apply_2(v_f_564_, v_head_567_, v___x_569_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg___boxed(lean_object* v_f_571_, lean_object* v_init_572_, lean_object* v_x_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_List_foldr___redArg(v_f_571_, v_init_572_, v_x_573_);
lean_dec(v_init_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_List_foldr(lean_object* v_00_u03b1_575_, lean_object* v_00_u03b2_576_, lean_object* v_f_577_, lean_object* v_init_578_, lean_object* v_x_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_List_foldr___redArg(v_f_577_, v_init_578_, v_x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___boxed(lean_object* v_00_u03b1_581_, lean_object* v_00_u03b2_582_, lean_object* v_f_583_, lean_object* v_init_584_, lean_object* v_x_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_List_foldr(v_00_u03b1_581_, v_00_u03b2_582_, v_f_583_, v_init_584_, v_x_585_);
lean_dec(v_init_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_List_reverseAux___redArg(lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
return v_x_588_;
}
else
{
lean_object* v_head_589_; lean_object* v_tail_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
v_head_589_ = lean_ctor_get(v_x_587_, 0);
v_tail_590_ = lean_ctor_get(v_x_587_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_598_ == 0)
{
v___x_592_ = v_x_587_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_tail_590_);
lean_inc(v_head_589_);
lean_dec(v_x_587_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v_x_588_);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_head_589_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_x_588_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v_x_587_ = v_tail_590_;
v_x_588_ = v___x_595_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object* v_00_u03b1_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_List_reverseAux___redArg(v_x_600_, v_x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_List_reverse___redArg(lean_object* v_as_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_box(0);
v___x_605_ = l_List_reverseAux___redArg(v_as_603_, v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_List_reverse(lean_object* v_00_u03b1_606_, lean_object* v_as_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_List_reverse___redArg(v_as_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_h__1_611_, lean_object* v_h__2_612_){
_start:
{
if (lean_obj_tag(v_x_609_) == 0)
{
lean_object* v___x_613_; 
lean_dec(v_h__2_612_);
v___x_613_ = lean_apply_1(v_h__1_611_, v_x_610_);
return v___x_613_;
}
else
{
lean_object* v_head_614_; lean_object* v_tail_615_; lean_object* v___x_616_; 
lean_dec(v_h__1_611_);
v_head_614_ = lean_ctor_get(v_x_609_, 0);
lean_inc(v_head_614_);
v_tail_615_ = lean_ctor_get(v_x_609_, 1);
lean_inc(v_tail_615_);
lean_dec_ref_known(v_x_609_, 2);
v___x_616_ = lean_apply_3(v_h__2_612_, v_head_614_, v_tail_615_, v_x_610_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_617_, lean_object* v_motive_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_h__1_621_, lean_object* v_h__2_622_){
_start:
{
if (lean_obj_tag(v_x_619_) == 0)
{
lean_object* v___x_623_; 
lean_dec(v_h__2_622_);
v___x_623_ = lean_apply_1(v_h__1_621_, v_x_620_);
return v___x_623_;
}
else
{
lean_object* v_head_624_; lean_object* v_tail_625_; lean_object* v___x_626_; 
lean_dec(v_h__1_621_);
v_head_624_ = lean_ctor_get(v_x_619_, 0);
lean_inc(v_head_624_);
v_tail_625_ = lean_ctor_get(v_x_619_, 1);
lean_inc(v_tail_625_);
lean_dec_ref_known(v_x_619_, 2);
v___x_626_ = lean_apply_3(v_h__2_622_, v_head_624_, v_tail_625_, v_x_620_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_List_appendTR___redArg(lean_object* v_as_627_, lean_object* v_bs_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = l_List_reverse___redArg(v_as_627_);
v___x_630_ = l_List_reverseAux___redArg(v___x_629_, v_bs_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR(lean_object* v_00_u03b1_631_, lean_object* v_as_632_, lean_object* v_bs_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_List_appendTR___redArg(v_as_632_, v_bs_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter___redArg(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_h__1_637_, lean_object* v_h__2_638_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
lean_object* v___x_639_; 
lean_dec(v_h__2_638_);
v___x_639_ = lean_apply_1(v_h__1_637_, v_x_636_);
return v___x_639_;
}
else
{
lean_object* v_head_640_; lean_object* v_tail_641_; lean_object* v___x_642_; 
lean_dec(v_h__1_637_);
v_head_640_ = lean_ctor_get(v_x_635_, 0);
lean_inc(v_head_640_);
v_tail_641_ = lean_ctor_get(v_x_635_, 1);
lean_inc(v_tail_641_);
lean_dec_ref_known(v_x_635_, 2);
v___x_642_ = lean_apply_3(v_h__2_638_, v_head_640_, v_tail_641_, v_x_636_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter(lean_object* v_00_u03b1_643_, lean_object* v_motive_644_, lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_h__1_647_, lean_object* v_h__2_648_){
_start:
{
if (lean_obj_tag(v_x_645_) == 0)
{
lean_object* v___x_649_; 
lean_dec(v_h__2_648_);
v___x_649_ = lean_apply_1(v_h__1_647_, v_x_646_);
return v___x_649_;
}
else
{
lean_object* v_head_650_; lean_object* v_tail_651_; lean_object* v___x_652_; 
lean_dec(v_h__1_647_);
v_head_650_ = lean_ctor_get(v_x_645_, 0);
lean_inc(v_head_650_);
v_tail_651_ = lean_ctor_get(v_x_645_, 1);
lean_inc(v_tail_651_);
lean_dec_ref_known(v_x_645_, 2);
v___x_652_ = lean_apply_3(v_h__2_648_, v_head_650_, v_tail_651_, v_x_646_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_List_instAppend___redArg(){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = ((lean_object*)(l_List_instAppend___redArg___closed__0));
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend___redArg___boxed(lean_object* v___dummy_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_List_instAppend___redArg();
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend(lean_object* v_00_u03b1_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = ((lean_object*)(l_List_instAppend___redArg___closed__0));
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_List_singleton___redArg(lean_object* v_a_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_662_, 0, v_a_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_List_singleton(lean_object* v_00_u03b1_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_box(0);
v___x_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_666_, 0, v_a_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg(lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
lean_object* v_zero_669_; uint8_t v_isZero_670_; 
v_zero_669_ = lean_unsigned_to_nat(0u);
v_isZero_670_ = lean_nat_dec_eq(v_x_667_, v_zero_669_);
if (v_isZero_670_ == 1)
{
lean_object* v___x_671_; 
lean_dec(v_x_668_);
v___x_671_ = lean_box(0);
return v___x_671_;
}
else
{
lean_object* v_one_672_; lean_object* v_n_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_one_672_ = lean_unsigned_to_nat(1u);
v_n_673_ = lean_nat_sub(v_x_667_, v_one_672_);
lean_inc(v_x_668_);
v___x_674_ = l_List_replicate___redArg(v_n_673_, v_x_668_);
lean_dec(v_n_673_);
v___x_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_675_, 0, v_x_668_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg___boxed(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_List_replicate___redArg(v_x_676_, v_x_677_);
lean_dec(v_x_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_List_replicate(lean_object* v_00_u03b1_679_, lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_List_replicate___redArg(v_x_680_, v_x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___boxed(lean_object* v_00_u03b1_683_, lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_List_replicate(v_00_u03b1_683_, v_x_684_, v_x_685_);
lean_dec(v_x_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg(lean_object* v_n_687_, lean_object* v_a_688_, lean_object* v_l_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = l_List_length___redArg(v_l_689_);
v___x_691_ = lean_nat_sub(v_n_687_, v___x_690_);
lean_dec(v___x_690_);
v___x_692_ = l_List_replicate___redArg(v___x_691_, v_a_688_);
lean_dec(v___x_691_);
v___x_693_ = l_List_appendTR___redArg(v___x_692_, v_l_689_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg___boxed(lean_object* v_n_694_, lean_object* v_a_695_, lean_object* v_l_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_List_leftpad___redArg(v_n_694_, v_a_695_, v_l_696_);
lean_dec(v_n_694_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad(lean_object* v_00_u03b1_698_, lean_object* v_n_699_, lean_object* v_a_700_, lean_object* v_l_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_List_leftpad___redArg(v_n_699_, v_a_700_, v_l_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___boxed(lean_object* v_00_u03b1_703_, lean_object* v_n_704_, lean_object* v_a_705_, lean_object* v_l_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_List_leftpad(v_00_u03b1_703_, v_n_704_, v_a_705_, v_l_706_);
lean_dec(v_n_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg(lean_object* v_n_708_, lean_object* v_a_709_, lean_object* v_l_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_711_ = l_List_length___redArg(v_l_710_);
v___x_712_ = lean_nat_sub(v_n_708_, v___x_711_);
lean_dec(v___x_711_);
v___x_713_ = l_List_replicate___redArg(v___x_712_, v_a_709_);
lean_dec(v___x_712_);
v___x_714_ = l_List_appendTR___redArg(v_l_710_, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg___boxed(lean_object* v_n_715_, lean_object* v_a_716_, lean_object* v_l_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_List_rightpad___redArg(v_n_715_, v_a_716_, v_l_717_);
lean_dec(v_n_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad(lean_object* v_00_u03b1_719_, lean_object* v_n_720_, lean_object* v_a_721_, lean_object* v_l_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_List_rightpad___redArg(v_n_720_, v_a_721_, v_l_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___boxed(lean_object* v_00_u03b1_724_, lean_object* v_n_725_, lean_object* v_a_726_, lean_object* v_l_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_List_rightpad(v_00_u03b1_724_, v_n_725_, v_a_726_, v_l_727_);
lean_dec(v_n_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_box(0);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg___boxed(lean_object* v___dummy_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_List_instEmptyCollection___redArg();
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object* v_00_u03b1_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_box(0);
return v___x_734_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty___redArg(lean_object* v_x_735_){
_start:
{
if (lean_obj_tag(v_x_735_) == 0)
{
uint8_t v___x_736_; 
v___x_736_ = 1;
return v___x_736_;
}
else
{
uint8_t v___x_737_; 
v___x_737_ = 0;
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___redArg___boxed(lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_List_isEmpty___redArg(v_x_738_);
lean_dec(v_x_738_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty(lean_object* v_00_u03b1_741_, lean_object* v_x_742_){
_start:
{
uint8_t v___x_743_; 
v___x_743_ = l_List_isEmpty___redArg(v_x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___boxed(lean_object* v_00_u03b1_744_, lean_object* v_x_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l_List_isEmpty(v_00_u03b1_744_, v_x_745_);
lean_dec(v_x_745_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT uint8_t l_List_elem___redArg(lean_object* v_inst_748_, lean_object* v_a_749_, lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
uint8_t v___x_751_; 
lean_dec(v_a_749_);
lean_dec_ref(v_inst_748_);
v___x_751_ = 0;
return v___x_751_;
}
else
{
lean_object* v_head_752_; lean_object* v_tail_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_head_752_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_head_752_);
v_tail_753_ = lean_ctor_get(v_x_750_, 1);
lean_inc(v_tail_753_);
lean_dec_ref_known(v_x_750_, 2);
lean_inc_ref(v_inst_748_);
lean_inc(v_a_749_);
v___x_754_ = lean_apply_2(v_inst_748_, v_a_749_, v_head_752_);
v___x_755_ = lean_unbox(v___x_754_);
if (v___x_755_ == 0)
{
v_x_750_ = v_tail_753_;
goto _start;
}
else
{
uint8_t v___x_757_; 
lean_dec(v_tail_753_);
lean_dec(v_a_749_);
lean_dec_ref(v_inst_748_);
v___x_757_ = lean_unbox(v___x_754_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___redArg___boxed(lean_object* v_inst_758_, lean_object* v_a_759_, lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_List_elem___redArg(v_inst_758_, v_a_759_, v_x_760_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT uint8_t l_List_elem(lean_object* v_00_u03b1_763_, lean_object* v_inst_764_, lean_object* v_a_765_, lean_object* v_x_766_){
_start:
{
uint8_t v___x_767_; 
v___x_767_ = l_List_elem___redArg(v_inst_764_, v_a_765_, v_x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_List_elem___boxed(lean_object* v_00_u03b1_768_, lean_object* v_inst_769_, lean_object* v_a_770_, lean_object* v_x_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_List_elem(v_00_u03b1_768_, v_inst_769_, v_a_770_, v_x_771_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT uint8_t l_List_contains___redArg(lean_object* v_inst_774_, lean_object* v_as_775_, lean_object* v_a_776_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = l_List_elem___redArg(v_inst_774_, v_a_776_, v_as_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_List_contains___redArg___boxed(lean_object* v_inst_778_, lean_object* v_as_779_, lean_object* v_a_780_){
_start:
{
uint8_t v_res_781_; lean_object* v_r_782_; 
v_res_781_ = l_List_contains___redArg(v_inst_778_, v_as_779_, v_a_780_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT uint8_t l_List_contains(lean_object* v_00_u03b1_783_, lean_object* v_inst_784_, lean_object* v_as_785_, lean_object* v_a_786_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = l_List_elem___redArg(v_inst_784_, v_a_786_, v_as_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_List_contains___boxed(lean_object* v_00_u03b1_788_, lean_object* v_inst_789_, lean_object* v_as_790_, lean_object* v_a_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l_List_contains(v_00_u03b1_788_, v_inst_789_, v_as_790_, v_a_791_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership___redArg(){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = lean_box(0);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership___redArg___boxed(lean_object* v___dummy_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_List_instMembership___redArg();
return v_res_797_;
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
lean_dec_ref_known(v_x_800_, 2);
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
lean_dec_ref_known(v_x_810_, 2);
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
uint8_t v_x_24__boxed_828_; lean_object* v_res_829_; 
v_x_24__boxed_828_ = lean_unbox(v_x_825_);
v_res_829_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_828_, v_h__1_826_, v_h__2_827_);
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
uint8_t v_x_35__boxed_842_; lean_object* v_res_843_; 
v_x_35__boxed_842_ = lean_unbox(v_x_839_);
v_res_843_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(v_motive_838_, v_x_35__boxed_842_, v_h__1_840_, v_h__2_841_);
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
lean_dec_ref_known(v_x_867_, 2);
lean_inc_ref(v_inst_866_);
v___x_871_ = lean_apply_1(v_inst_866_, v_head_869_);
v___x_872_ = lean_unbox(v___x_871_);
if (v___x_872_ == 0)
{
uint8_t v_decide_873_; 
v_decide_873_ = l_List_decidableBEx___redArg(v_inst_866_, v_tail_870_);
if (v_decide_873_ == 0)
{
uint8_t v___x_874_; 
v___x_874_ = lean_unbox(v___x_871_);
return v___x_874_;
}
else
{
return v_decide_873_;
}
}
else
{
uint8_t v___x_875_; 
lean_dec(v_tail_870_);
lean_dec_ref(v_inst_866_);
v___x_875_ = lean_unbox(v___x_871_);
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___redArg___boxed(lean_object* v_inst_876_, lean_object* v_x_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_List_decidableBEx___redArg(v_inst_876_, v_x_877_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx(lean_object* v_00_u03b1_880_, lean_object* v_p_881_, lean_object* v_inst_882_, lean_object* v_x_883_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = l_List_decidableBEx___redArg(v_inst_882_, v_x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___boxed(lean_object* v_00_u03b1_885_, lean_object* v_p_886_, lean_object* v_inst_887_, lean_object* v_x_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_List_decidableBEx(v_00_u03b1_885_, v_p_886_, v_inst_887_, v_x_888_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll___redArg(lean_object* v_inst_891_, lean_object* v_x_892_){
_start:
{
if (lean_obj_tag(v_x_892_) == 0)
{
uint8_t v___x_893_; 
lean_dec_ref(v_inst_891_);
v___x_893_ = 1;
return v___x_893_;
}
else
{
lean_object* v_head_894_; lean_object* v_tail_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_head_894_ = lean_ctor_get(v_x_892_, 0);
lean_inc(v_head_894_);
v_tail_895_ = lean_ctor_get(v_x_892_, 1);
lean_inc(v_tail_895_);
lean_dec_ref_known(v_x_892_, 2);
lean_inc_ref(v_inst_891_);
v___x_896_ = lean_apply_1(v_inst_891_, v_head_894_);
v___x_897_ = lean_unbox(v___x_896_);
if (v___x_897_ == 0)
{
uint8_t v___x_898_; 
lean_dec(v_tail_895_);
lean_dec_ref(v_inst_891_);
v___x_898_ = lean_unbox(v___x_896_);
return v___x_898_;
}
else
{
uint8_t v_decide_899_; 
v_decide_899_ = l_List_decidableBAll___redArg(v_inst_891_, v_tail_895_);
if (v_decide_899_ == 0)
{
return v_decide_899_;
}
else
{
uint8_t v___x_900_; 
v___x_900_ = lean_unbox(v___x_896_);
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___redArg___boxed(lean_object* v_inst_901_, lean_object* v_x_902_){
_start:
{
uint8_t v_res_903_; lean_object* v_r_904_; 
v_res_903_ = l_List_decidableBAll___redArg(v_inst_901_, v_x_902_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll(lean_object* v_00_u03b1_905_, lean_object* v_p_906_, lean_object* v_inst_907_, lean_object* v_x_908_){
_start:
{
uint8_t v___x_909_; 
v___x_909_ = l_List_decidableBAll___redArg(v_inst_907_, v_x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___boxed(lean_object* v_00_u03b1_910_, lean_object* v_p_911_, lean_object* v_inst_912_, lean_object* v_x_913_){
_start:
{
uint8_t v_res_914_; lean_object* v_r_915_; 
v_res_914_ = l_List_decidableBAll(v_00_u03b1_910_, v_p_911_, v_inst_912_, v_x_913_);
v_r_915_ = lean_box(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT lean_object* l_List_take___redArg(lean_object* v_x_916_, lean_object* v_x_917_){
_start:
{
lean_object* v_zero_918_; uint8_t v_isZero_919_; 
v_zero_918_ = lean_unsigned_to_nat(0u);
v_isZero_919_ = lean_nat_dec_eq(v_x_916_, v_zero_918_);
if (v_isZero_919_ == 1)
{
lean_object* v___x_920_; 
lean_dec(v_x_917_);
v___x_920_ = lean_box(0);
return v___x_920_;
}
else
{
if (lean_obj_tag(v_x_917_) == 0)
{
return v_x_917_;
}
else
{
lean_object* v_head_921_; lean_object* v_tail_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_932_; 
v_head_921_ = lean_ctor_get(v_x_917_, 0);
v_tail_922_ = lean_ctor_get(v_x_917_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_x_917_);
if (v_isSharedCheck_932_ == 0)
{
v___x_924_ = v_x_917_;
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_tail_922_);
lean_inc(v_head_921_);
lean_dec(v_x_917_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_one_926_; lean_object* v_n_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v_one_926_ = lean_unsigned_to_nat(1u);
v_n_927_ = lean_nat_sub(v_x_916_, v_one_926_);
v___x_928_ = l_List_take___redArg(v_n_927_, v_tail_922_);
lean_dec(v_n_927_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v___x_928_);
v___x_930_ = v___x_924_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_head_921_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_take___redArg___boxed(lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_List_take___redArg(v_x_933_, v_x_934_);
lean_dec(v_x_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_List_take(lean_object* v_00_u03b1_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_List_take___redArg(v_x_937_, v_x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_List_take___boxed(lean_object* v_00_u03b1_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_List_take(v_00_u03b1_940_, v_x_941_, v_x_942_);
lean_dec(v_x_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg(lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
lean_object* v_zero_946_; uint8_t v_isZero_947_; 
v_zero_946_ = lean_unsigned_to_nat(0u);
v_isZero_947_ = lean_nat_dec_eq(v_x_944_, v_zero_946_);
if (v_isZero_947_ == 1)
{
lean_dec(v_x_944_);
lean_inc(v_x_945_);
return v_x_945_;
}
else
{
if (lean_obj_tag(v_x_945_) == 0)
{
lean_dec(v_x_944_);
return v_x_945_;
}
else
{
lean_object* v_tail_948_; lean_object* v_one_949_; lean_object* v_n_950_; 
v_tail_948_ = lean_ctor_get(v_x_945_, 1);
v_one_949_ = lean_unsigned_to_nat(1u);
v_n_950_ = lean_nat_sub(v_x_944_, v_one_949_);
lean_dec(v_x_944_);
v_x_944_ = v_n_950_;
v_x_945_ = v_tail_948_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg___boxed(lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_List_drop___redArg(v_x_952_, v_x_953_);
lean_dec(v_x_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_List_drop(lean_object* v_00_u03b1_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_List_drop___redArg(v_x_956_, v_x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_List_drop___boxed(lean_object* v_00_u03b1_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_List_drop(v_00_u03b1_959_, v_x_960_, v_x_961_);
lean_dec(v_x_961_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg(lean_object* v_l_963_, lean_object* v_start_964_, lean_object* v_stop_965_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = lean_nat_sub(v_stop_965_, v_start_964_);
v___x_967_ = l_List_drop___redArg(v_start_964_, v_l_963_);
v___x_968_ = l_List_take___redArg(v___x_966_, v___x_967_);
lean_dec(v___x_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg___boxed(lean_object* v_l_969_, lean_object* v_start_970_, lean_object* v_stop_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_List_extract___redArg(v_l_969_, v_start_970_, v_stop_971_);
lean_dec(v_stop_971_);
lean_dec(v_l_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_List_extract(lean_object* v_00_u03b1_973_, lean_object* v_l_974_, lean_object* v_start_975_, lean_object* v_stop_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_nat_sub(v_stop_976_, v_start_975_);
v___x_978_ = l_List_drop___redArg(v_start_975_, v_l_974_);
v___x_979_ = l_List_take___redArg(v___x_977_, v___x_978_);
lean_dec(v___x_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_List_extract___boxed(lean_object* v_00_u03b1_980_, lean_object* v_l_981_, lean_object* v_start_982_, lean_object* v_stop_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_List_extract(v_00_u03b1_980_, v_l_981_, v_start_982_, v_stop_983_);
lean_dec(v_stop_983_);
lean_dec(v_l_981_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhile___redArg(lean_object* v_p_985_, lean_object* v_x_986_){
_start:
{
if (lean_obj_tag(v_x_986_) == 0)
{
lean_dec_ref(v_p_985_);
return v_x_986_;
}
else
{
lean_object* v_head_987_; lean_object* v_tail_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_999_; 
v_head_987_ = lean_ctor_get(v_x_986_, 0);
v_tail_988_ = lean_ctor_get(v_x_986_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_x_986_);
if (v_isSharedCheck_999_ == 0)
{
v___x_990_ = v_x_986_;
v_isShared_991_ = v_isSharedCheck_999_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_tail_988_);
lean_inc(v_head_987_);
lean_dec(v_x_986_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_999_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; uint8_t v___x_993_; 
lean_inc_ref(v_p_985_);
lean_inc(v_head_987_);
v___x_992_ = lean_apply_1(v_p_985_, v_head_987_);
v___x_993_ = lean_unbox(v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
lean_del_object(v___x_990_);
lean_dec(v_tail_988_);
lean_dec(v_head_987_);
lean_dec_ref(v_p_985_);
v___x_994_ = lean_box(0);
return v___x_994_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = l_List_takeWhile___redArg(v_p_985_, v_tail_988_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v___x_995_);
v___x_997_ = v___x_990_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_head_987_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_takeWhile(lean_object* v_00_u03b1_1000_, lean_object* v_p_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_List_takeWhile___redArg(v_p_1001_, v_x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___redArg(lean_object* v_p_1004_, lean_object* v_x_1005_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_dec_ref(v_p_1004_);
return v_x_1005_;
}
else
{
lean_object* v_head_1006_; lean_object* v_tail_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_head_1006_ = lean_ctor_get(v_x_1005_, 0);
v_tail_1007_ = lean_ctor_get(v_x_1005_, 1);
lean_inc_ref(v_p_1004_);
lean_inc(v_head_1006_);
v___x_1008_ = lean_apply_1(v_p_1004_, v_head_1006_);
v___x_1009_ = lean_unbox(v___x_1008_);
if (v___x_1009_ == 0)
{
lean_dec_ref(v_p_1004_);
return v_x_1005_;
}
else
{
lean_inc(v_tail_1007_);
lean_dec_ref_known(v_x_1005_, 2);
v_x_1005_ = v_tail_1007_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object* v_00_u03b1_1011_, lean_object* v_p_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_List_dropWhile___redArg(v_p_1012_, v_x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___redArg(lean_object* v_p_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
if (lean_obj_tag(v_a_1016_) == 0)
{
lean_object* v_fst_1018_; lean_object* v_snd_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref(v_p_1015_);
v_fst_1018_ = lean_ctor_get(v_a_1017_, 0);
v_snd_1019_ = lean_ctor_get(v_a_1017_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_a_1017_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1021_ = v_a_1017_;
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_snd_1019_);
lean_inc(v_fst_1018_);
lean_dec(v_a_1017_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1023_ = l_List_reverse___redArg(v_fst_1018_);
v___x_1024_ = l_List_reverse___redArg(v_snd_1019_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v___x_1024_);
lean_ctor_set(v___x_1021_, 0, v___x_1023_);
v___x_1026_ = v___x_1021_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
lean_object* v_head_1029_; lean_object* v_tail_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1056_; 
v_head_1029_ = lean_ctor_get(v_a_1016_, 0);
v_tail_1030_ = lean_ctor_get(v_a_1016_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_a_1016_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1032_ = v_a_1016_;
v_isShared_1033_ = v_isSharedCheck_1056_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_tail_1030_);
lean_inc(v_head_1029_);
lean_dec(v_a_1016_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1056_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1055_; 
v_fst_1034_ = lean_ctor_get(v_a_1017_, 0);
v_snd_1035_ = lean_ctor_get(v_a_1017_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_a_1017_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1037_ = v_a_1017_;
v_isShared_1038_ = v_isSharedCheck_1055_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snd_1035_);
lean_inc(v_fst_1034_);
lean_dec(v_a_1017_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1055_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
lean_inc_ref(v_p_1015_);
lean_inc(v_head_1029_);
v___x_1039_ = lean_apply_1(v_p_1015_, v_head_1029_);
v___x_1040_ = lean_unbox(v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1042_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v_snd_1035_);
v___x_1042_ = v___x_1032_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_head_1029_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_snd_1035_);
v___x_1042_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1044_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1042_);
v___x_1044_ = v___x_1037_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_fst_1034_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
v_a_1016_ = v_tail_1030_;
v_a_1017_ = v___x_1044_;
goto _start;
}
}
}
else
{
lean_object* v___x_1049_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v_fst_1034_);
v___x_1049_ = v___x_1032_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_head_1029_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_fst_1034_);
v___x_1049_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1049_);
v___x_1051_ = v___x_1037_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_snd_1035_);
v___x_1051_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
v_a_1016_ = v_tail_1030_;
v_a_1017_ = v___x_1051_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object* v_00_u03b1_1057_, lean_object* v_p_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_List_partition_loop___redArg(v_p_1058_, v_a_1059_, v_a_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_List_partition___redArg(lean_object* v_p_1064_, lean_object* v_as_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1067_ = l_List_partition_loop___redArg(v_p_1064_, v_as_1065_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_List_partition(lean_object* v_00_u03b1_1068_, lean_object* v_p_1069_, lean_object* v_as_1070_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1072_ = l_List_partition_loop___redArg(v_p_1069_, v_as_1070_, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_List_dropLast___redArg(lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
return v_x_1073_;
}
else
{
lean_object* v_tail_1074_; 
v_tail_1074_ = lean_ctor_get(v_x_1073_, 1);
lean_inc(v_tail_1074_);
if (lean_obj_tag(v_tail_1074_) == 0)
{
lean_dec_ref_known(v_x_1073_, 2);
return v_tail_1074_;
}
else
{
lean_object* v_head_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_head_1075_ = lean_ctor_get(v_x_1073_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_x_1073_, 1);
lean_dec(v_unused_1084_);
v___x_1077_ = v_x_1073_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_head_1075_);
lean_dec(v_x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = l_List_dropLast___redArg(v_tail_1074_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_head_1075_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropLast(lean_object* v_00_u03b1_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_List_dropLast___redArg(v_x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_1088_, lean_object* v_h__1_1089_, lean_object* v_h__2_1090_, lean_object* v_h__3_1091_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec(v_h__3_1091_);
lean_dec(v_h__2_1090_);
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_apply_1(v_h__1_1089_, v___x_1092_);
return v___x_1093_;
}
else
{
lean_object* v_tail_1094_; 
lean_dec(v_h__1_1089_);
v_tail_1094_ = lean_ctor_get(v_x_1088_, 1);
if (lean_obj_tag(v_tail_1094_) == 0)
{
lean_object* v_head_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__3_1091_);
v_head_1095_ = lean_ctor_get(v_x_1088_, 0);
lean_inc(v_head_1095_);
lean_dec_ref_known(v_x_1088_, 2);
v___x_1096_ = lean_apply_1(v_h__2_1090_, v_head_1095_);
return v___x_1096_;
}
else
{
lean_object* v_head_1097_; lean_object* v___x_1098_; 
lean_inc_ref(v_tail_1094_);
lean_dec(v_h__2_1090_);
v_head_1097_ = lean_ctor_get(v_x_1088_, 0);
lean_inc(v_head_1097_);
lean_dec_ref_known(v_x_1088_, 2);
v___x_1098_ = lean_apply_3(v_h__3_1091_, v_head_1097_, v_tail_1094_, lean_box(0));
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_1099_, lean_object* v_motive_1100_, lean_object* v_x_1101_, lean_object* v_h__1_1102_, lean_object* v_h__2_1103_, lean_object* v_h__3_1104_){
_start:
{
if (lean_obj_tag(v_x_1101_) == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v_h__3_1104_);
lean_dec(v_h__2_1103_);
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_apply_1(v_h__1_1102_, v___x_1105_);
return v___x_1106_;
}
else
{
lean_object* v_tail_1107_; 
lean_dec(v_h__1_1102_);
v_tail_1107_ = lean_ctor_get(v_x_1101_, 1);
if (lean_obj_tag(v_tail_1107_) == 0)
{
lean_object* v_head_1108_; lean_object* v___x_1109_; 
lean_dec(v_h__3_1104_);
v_head_1108_ = lean_ctor_get(v_x_1101_, 0);
lean_inc(v_head_1108_);
lean_dec_ref_known(v_x_1101_, 2);
v___x_1109_ = lean_apply_1(v_h__2_1103_, v_head_1108_);
return v___x_1109_;
}
else
{
lean_object* v_head_1110_; lean_object* v___x_1111_; 
lean_inc_ref(v_tail_1107_);
lean_dec(v_h__2_1103_);
v_head_1110_ = lean_ctor_get(v_x_1101_, 0);
lean_inc(v_head_1110_);
lean_dec_ref_known(v_x_1101_, 2);
v___x_1111_ = lean_apply_3(v_h__3_1104_, v_head_1110_, v_tail_1107_, lean_box(0));
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg(){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_box(0);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg___boxed(lean_object* v___dummy_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_List_instHasSubset___redArg();
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object* v_00_u03b1_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_box(0);
return v___x_1117_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(lean_object* v___f_1118_, lean_object* v_x_1119_, lean_object* v_a_1120_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = l_List_elem___redArg(v___f_1118_, v_a_1120_, v_x_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(lean_object* v___f_1122_, lean_object* v_x_1123_, lean_object* v_a_1124_){
_start:
{
uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_res_1125_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(v___f_1122_, v_x_1123_, v_a_1124_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg(lean_object* v_inst_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v___f_1130_; lean_object* v___f_1131_; uint8_t v___x_1132_; 
v___f_1130_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1130_, 0, v_inst_1127_);
v___f_1131_ = lean_alloc_closure((void*)(l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1131_, 0, v___f_1130_);
lean_closure_set(v___f_1131_, 1, v_x_1129_);
v___x_1132_ = l_List_decidableBAll___redArg(v___f_1131_, v_x_1128_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(lean_object* v_inst_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_res_1136_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1133_, v_x_1134_, v_x_1135_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq(lean_object* v_00_u03b1_1138_, lean_object* v_inst_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1139_, v_x_1140_, v_x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_inst_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_){
_start:
{
uint8_t v_res_1147_; lean_object* v_r_1148_; 
v_res_1147_ = l_List_instDecidableRelSubsetOfDecidableEq(v_00_u03b1_1143_, v_inst_1144_, v_x_1145_, v_x_1146_);
v_r_1148_ = lean_box(v_res_1147_);
return v_r_1148_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2));
v___x_1183_ = l_String_toRawSubstring_x27(v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object* v_x_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
lean_inc(v_x_1203_);
v___x_1207_ = l_Lean_Syntax_isOfKind(v_x_1203_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_x_1203_);
v___x_1208_ = lean_box(1);
v___x_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v_a_1205_);
return v___x_1209_;
}
else
{
lean_object* v_quotContext_1210_; lean_object* v_currMacroScope_1211_; lean_object* v_ref_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_quotContext_1210_ = lean_ctor_get(v_a_1204_, 1);
v_currMacroScope_1211_ = lean_ctor_get(v_a_1204_, 2);
v_ref_1212_ = lean_ctor_get(v_a_1204_, 5);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = l_Lean_Syntax_getArg(v_x_1203_, v___x_1213_);
v___x_1215_ = lean_unsigned_to_nat(2u);
v___x_1216_ = l_Lean_Syntax_getArg(v_x_1203_, v___x_1215_);
lean_dec(v_x_1203_);
v___x_1217_ = 0;
v___x_1218_ = l_Lean_SourceInfo_fromRef(v_ref_1212_, v___x_1217_);
v___x_1219_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1220_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
v___x_1221_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4));
lean_inc(v_currMacroScope_1211_);
lean_inc(v_quotContext_1210_);
v___x_1222_ = l_Lean_addMacroScope(v_quotContext_1210_, v___x_1221_, v_currMacroScope_1211_);
v___x_1223_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10));
lean_inc_n(v___x_1218_, 2);
v___x_1224_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1218_);
lean_ctor_set(v___x_1224_, 1, v___x_1220_);
lean_ctor_set(v___x_1224_, 2, v___x_1222_);
lean_ctor_set(v___x_1224_, 3, v___x_1223_);
v___x_1225_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1226_ = l_Lean_Syntax_node2(v___x_1218_, v___x_1225_, v___x_1214_, v___x_1216_);
v___x_1227_ = l_Lean_Syntax_node2(v___x_1218_, v___x_1219_, v___x_1224_, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v_a_1205_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___boxed(lean_object* v_x_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(v_x_1229_, v_a_1230_, v_a_1231_);
lean_dec_ref(v_a_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object* v_x_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1236_);
v___x_1240_ = l_Lean_Syntax_isOfKind(v_x_1236_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec(v_x_1236_);
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_a_1238_);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = l_Lean_Syntax_getArg(v_x_1236_, v___x_1243_);
v___x_1245_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1244_);
v___x_1246_ = l_Lean_Syntax_isOfKind(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec(v___x_1244_);
lean_dec(v_x_1236_);
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v_a_1238_);
return v___x_1248_;
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = l_Lean_Syntax_getArg(v_x_1236_, v___x_1249_);
lean_dec(v_x_1236_);
v___x_1251_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1250_);
v___x_1252_ = l_Lean_Syntax_matchesNull(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v___x_1250_);
lean_dec(v___x_1244_);
v___x_1253_ = lean_box(0);
v___x_1254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v_a_1238_);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_ref_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1255_ = l_Lean_Syntax_getArg(v___x_1250_, v___x_1243_);
v___x_1256_ = l_Lean_Syntax_getArg(v___x_1250_, v___x_1249_);
lean_dec(v___x_1250_);
v_ref_1257_ = l_Lean_replaceRef(v___x_1244_, v_a_1237_);
lean_dec(v___x_1244_);
v___x_1258_ = 0;
v___x_1259_ = l_Lean_SourceInfo_fromRef(v_ref_1257_, v___x_1258_);
lean_dec(v_ref_1257_);
v___x_1260_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
v___x_1261_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__5));
lean_inc(v___x_1259_);
v___x_1262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = l_Lean_Syntax_node3(v___x_1259_, v___x_1260_, v___x_1255_, v___x_1262_, v___x_1256_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v_a_1238_);
return v___x_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object* v_x_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(v_x_1265_, v_a_1266_, v_a_1267_);
lean_dec(v_a_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist___redArg(lean_object* v_inst_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
if (lean_obj_tag(v_x_1270_) == 0)
{
uint8_t v___x_1272_; 
lean_dec(v_x_1271_);
lean_dec_ref(v_inst_1269_);
v___x_1272_ = 1;
return v___x_1272_;
}
else
{
if (lean_obj_tag(v_x_1271_) == 0)
{
uint8_t v___x_1273_; 
lean_dec_ref_known(v_x_1270_, 2);
lean_dec_ref(v_inst_1269_);
v___x_1273_ = 0;
return v___x_1273_;
}
else
{
lean_object* v_head_1274_; lean_object* v_tail_1275_; lean_object* v_head_1276_; lean_object* v_tail_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_head_1274_ = lean_ctor_get(v_x_1270_, 0);
v_tail_1275_ = lean_ctor_get(v_x_1270_, 1);
v_head_1276_ = lean_ctor_get(v_x_1271_, 0);
lean_inc(v_head_1276_);
v_tail_1277_ = lean_ctor_get(v_x_1271_, 1);
lean_inc(v_tail_1277_);
lean_dec_ref_known(v_x_1271_, 2);
lean_inc_ref(v_inst_1269_);
lean_inc(v_head_1274_);
v___x_1278_ = lean_apply_2(v_inst_1269_, v_head_1274_, v_head_1276_);
v___x_1279_ = lean_unbox(v___x_1278_);
if (v___x_1279_ == 0)
{
v_x_1271_ = v_tail_1277_;
goto _start;
}
else
{
lean_inc(v_tail_1275_);
lean_dec_ref_known(v_x_1270_, 2);
v_x_1270_ = v_tail_1275_;
v_x_1271_ = v_tail_1277_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSublist___redArg___boxed(lean_object* v_inst_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
uint8_t v_res_1285_; lean_object* v_r_1286_; 
v_res_1285_ = l_List_isSublist___redArg(v_inst_1282_, v_x_1283_, v_x_1284_);
v_r_1286_ = lean_box(v_res_1285_);
return v_r_1286_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist(lean_object* v_00_u03b1_1287_, lean_object* v_inst_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
uint8_t v___x_1291_; 
v___x_1291_ = l_List_isSublist___redArg(v_inst_1288_, v_x_1289_, v_x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_List_isSublist___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_inst_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_){
_start:
{
uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_res_1296_ = l_List_isSublist(v_00_u03b1_1292_, v_inst_1293_, v_x_1294_, v_x_1295_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0));
v___x_1316_ = l_String_toRawSubstring_x27(v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object* v_x_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
lean_inc(v_x_1328_);
v___x_1332_ = l_Lean_Syntax_isOfKind(v_x_1328_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec(v_x_1328_);
v___x_1333_ = lean_box(1);
v___x_1334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v_a_1330_);
return v___x_1334_;
}
else
{
lean_object* v_quotContext_1335_; lean_object* v_currMacroScope_1336_; lean_object* v_ref_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_quotContext_1335_ = lean_ctor_get(v_a_1329_, 1);
v_currMacroScope_1336_ = lean_ctor_get(v_a_1329_, 2);
v_ref_1337_ = lean_ctor_get(v_a_1329_, 5);
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = l_Lean_Syntax_getArg(v_x_1328_, v___x_1338_);
v___x_1340_ = lean_unsigned_to_nat(2u);
v___x_1341_ = l_Lean_Syntax_getArg(v_x_1328_, v___x_1340_);
lean_dec(v_x_1328_);
v___x_1342_ = 0;
v___x_1343_ = l_Lean_SourceInfo_fromRef(v_ref_1337_, v___x_1342_);
v___x_1344_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1345_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
v___x_1346_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1336_);
lean_inc(v_quotContext_1335_);
v___x_1347_ = l_Lean_addMacroScope(v_quotContext_1335_, v___x_1346_, v_currMacroScope_1336_);
v___x_1348_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1343_, 2);
v___x_1349_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1343_);
lean_ctor_set(v___x_1349_, 1, v___x_1345_);
lean_ctor_set(v___x_1349_, 2, v___x_1347_);
lean_ctor_set(v___x_1349_, 3, v___x_1348_);
v___x_1350_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1351_ = l_Lean_Syntax_node2(v___x_1343_, v___x_1350_, v___x_1339_, v___x_1341_);
v___x_1352_ = l_Lean_Syntax_node2(v___x_1343_, v___x_1344_, v___x_1349_, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v_a_1330_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___boxed(lean_object* v_x_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(v_x_1354_, v_a_1355_, v_a_1356_);
lean_dec_ref(v_a_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object* v_x_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1358_);
v___x_1362_ = l_Lean_Syntax_isOfKind(v_x_1358_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec(v_x_1358_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v_a_1360_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = l_Lean_Syntax_getArg(v_x_1358_, v___x_1365_);
v___x_1367_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1366_);
v___x_1368_ = l_Lean_Syntax_isOfKind(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v___x_1366_);
lean_dec(v_x_1358_);
v___x_1369_ = lean_box(0);
v___x_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v_a_1360_);
return v___x_1370_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = l_Lean_Syntax_getArg(v_x_1358_, v___x_1371_);
lean_dec(v_x_1358_);
v___x_1373_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1372_);
v___x_1374_ = l_Lean_Syntax_matchesNull(v___x_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v___x_1372_);
lean_dec(v___x_1366_);
v___x_1375_ = lean_box(0);
v___x_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v_a_1360_);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_ref_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1377_ = l_Lean_Syntax_getArg(v___x_1372_, v___x_1365_);
v___x_1378_ = l_Lean_Syntax_getArg(v___x_1372_, v___x_1371_);
lean_dec(v___x_1372_);
v_ref_1379_ = l_Lean_replaceRef(v___x_1366_, v_a_1359_);
lean_dec(v___x_1366_);
v___x_1380_ = 0;
v___x_1381_ = l_Lean_SourceInfo_fromRef(v_ref_1379_, v___x_1380_);
lean_dec(v_ref_1379_);
v___x_1382_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
v___x_1383_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__2));
lean_inc(v___x_1381_);
v___x_1384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1381_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = l_Lean_Syntax_node3(v___x_1381_, v___x_1382_, v___x_1377_, v___x_1384_, v___x_1378_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v_a_1360_);
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object* v_x_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(v_x_1387_, v_a_1388_, v_a_1389_);
lean_dec(v_a_1388_);
return v_res_1390_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf___redArg(lean_object* v_inst_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
if (lean_obj_tag(v_x_1392_) == 0)
{
uint8_t v___x_1394_; 
lean_dec(v_x_1393_);
lean_dec_ref(v_inst_1391_);
v___x_1394_ = 1;
return v___x_1394_;
}
else
{
if (lean_obj_tag(v_x_1393_) == 0)
{
uint8_t v___x_1395_; 
lean_dec_ref_known(v_x_1392_, 2);
lean_dec_ref(v_inst_1391_);
v___x_1395_ = 0;
return v___x_1395_;
}
else
{
lean_object* v_head_1396_; lean_object* v_tail_1397_; lean_object* v_head_1398_; lean_object* v_tail_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_head_1396_ = lean_ctor_get(v_x_1392_, 0);
lean_inc(v_head_1396_);
v_tail_1397_ = lean_ctor_get(v_x_1392_, 1);
lean_inc(v_tail_1397_);
lean_dec_ref_known(v_x_1392_, 2);
v_head_1398_ = lean_ctor_get(v_x_1393_, 0);
lean_inc(v_head_1398_);
v_tail_1399_ = lean_ctor_get(v_x_1393_, 1);
lean_inc(v_tail_1399_);
lean_dec_ref_known(v_x_1393_, 2);
lean_inc_ref(v_inst_1391_);
v___x_1400_ = lean_apply_2(v_inst_1391_, v_head_1396_, v_head_1398_);
v___x_1401_ = lean_unbox(v___x_1400_);
if (v___x_1401_ == 0)
{
uint8_t v___x_1402_; 
lean_dec(v_tail_1399_);
lean_dec(v_tail_1397_);
lean_dec_ref(v_inst_1391_);
v___x_1402_ = lean_unbox(v___x_1400_);
return v___x_1402_;
}
else
{
v_x_1392_ = v_tail_1397_;
v_x_1393_ = v_tail_1399_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___redArg___boxed(lean_object* v_inst_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
uint8_t v_res_1407_; lean_object* v_r_1408_; 
v_res_1407_ = l_List_isPrefixOf___redArg(v_inst_1404_, v_x_1405_, v_x_1406_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf(lean_object* v_00_u03b1_1409_, lean_object* v_inst_1410_, lean_object* v_x_1411_, lean_object* v_x_1412_){
_start:
{
uint8_t v___x_1413_; 
v___x_1413_ = l_List_isPrefixOf___redArg(v_inst_1410_, v_x_1411_, v_x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___boxed(lean_object* v_00_u03b1_1414_, lean_object* v_inst_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_){
_start:
{
uint8_t v_res_1418_; lean_object* v_r_1419_; 
v_res_1418_ = l_List_isPrefixOf(v_00_u03b1_1414_, v_inst_1415_, v_x_1416_, v_x_1417_);
v_r_1419_ = lean_box(v_res_1418_);
return v_r_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_1420_, lean_object* v_x_1421_, lean_object* v_h__1_1422_, lean_object* v_h__2_1423_, lean_object* v_h__3_1424_){
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
lean_dec_ref_known(v_x_1420_, 2);
v_head_1429_ = lean_ctor_get(v_x_1421_, 0);
lean_inc(v_head_1429_);
v_tail_1430_ = lean_ctor_get(v_x_1421_, 1);
lean_inc(v_tail_1430_);
lean_dec_ref_known(v_x_1421_, 2);
v___x_1431_ = lean_apply_4(v_h__3_1424_, v_head_1427_, v_tail_1428_, v_head_1429_, v_tail_1430_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object* v_00_u03b1_1432_, lean_object* v_motive_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v_h__1_1436_, lean_object* v_h__2_1437_, lean_object* v_h__3_1438_){
_start:
{
if (lean_obj_tag(v_x_1434_) == 0)
{
lean_object* v___x_1439_; 
lean_dec(v_h__3_1438_);
lean_dec(v_h__2_1437_);
v___x_1439_ = lean_apply_1(v_h__1_1436_, v_x_1435_);
return v___x_1439_;
}
else
{
lean_dec(v_h__1_1436_);
if (lean_obj_tag(v_x_1435_) == 0)
{
lean_object* v___x_1440_; 
lean_dec(v_h__3_1438_);
v___x_1440_ = lean_apply_2(v_h__2_1437_, v_x_1434_, lean_box(0));
return v___x_1440_;
}
else
{
lean_object* v_head_1441_; lean_object* v_tail_1442_; lean_object* v_head_1443_; lean_object* v_tail_1444_; lean_object* v___x_1445_; 
lean_dec(v_h__2_1437_);
v_head_1441_ = lean_ctor_get(v_x_1434_, 0);
lean_inc(v_head_1441_);
v_tail_1442_ = lean_ctor_get(v_x_1434_, 1);
lean_inc(v_tail_1442_);
lean_dec_ref_known(v_x_1434_, 2);
v_head_1443_ = lean_ctor_get(v_x_1435_, 0);
lean_inc(v_head_1443_);
v_tail_1444_ = lean_ctor_get(v_x_1435_, 1);
lean_inc(v_tail_1444_);
lean_dec_ref_known(v_x_1435_, 2);
v___x_1445_ = lean_apply_4(v_h__3_1438_, v_head_1441_, v_tail_1442_, v_head_1443_, v_tail_1444_);
return v___x_1445_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___redArg(lean_object* v_inst_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_object* v___x_1449_; 
lean_dec_ref(v_inst_1446_);
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_x_1448_);
return v___x_1449_;
}
else
{
if (lean_obj_tag(v_x_1448_) == 0)
{
lean_object* v___x_1450_; 
lean_dec_ref_known(v_x_1447_, 2);
lean_dec_ref(v_inst_1446_);
v___x_1450_ = lean_box(0);
return v___x_1450_;
}
else
{
lean_object* v_head_1451_; lean_object* v_tail_1452_; lean_object* v_head_1453_; lean_object* v_tail_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_head_1451_ = lean_ctor_get(v_x_1447_, 0);
lean_inc(v_head_1451_);
v_tail_1452_ = lean_ctor_get(v_x_1447_, 1);
lean_inc(v_tail_1452_);
lean_dec_ref_known(v_x_1447_, 2);
v_head_1453_ = lean_ctor_get(v_x_1448_, 0);
lean_inc(v_head_1453_);
v_tail_1454_ = lean_ctor_get(v_x_1448_, 1);
lean_inc(v_tail_1454_);
lean_dec_ref_known(v_x_1448_, 2);
lean_inc_ref(v_inst_1446_);
v___x_1455_ = lean_apply_2(v_inst_1446_, v_head_1451_, v_head_1453_);
v___x_1456_ = lean_unbox(v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_dec(v_tail_1454_);
lean_dec(v_tail_1452_);
lean_dec_ref(v_inst_1446_);
v___x_1457_ = lean_box(0);
return v___x_1457_;
}
else
{
v_x_1447_ = v_tail_1452_;
v_x_1448_ = v_tail_1454_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object* v_00_u03b1_1459_, lean_object* v_inst_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_List_isPrefixOf_x3f___redArg(v_inst_1460_, v_x_1461_, v_x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf___redArg(lean_object* v_inst_1464_, lean_object* v_l_u2081_1465_, lean_object* v_l_u2082_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = l_List_reverse___redArg(v_l_u2081_1465_);
v___x_1468_ = l_List_reverse___redArg(v_l_u2082_1466_);
v___x_1469_ = l_List_isPrefixOf___redArg(v_inst_1464_, v___x_1467_, v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___redArg___boxed(lean_object* v_inst_1470_, lean_object* v_l_u2081_1471_, lean_object* v_l_u2082_1472_){
_start:
{
uint8_t v_res_1473_; lean_object* v_r_1474_; 
v_res_1473_ = l_List_isSuffixOf___redArg(v_inst_1470_, v_l_u2081_1471_, v_l_u2082_1472_);
v_r_1474_ = lean_box(v_res_1473_);
return v_r_1474_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf(lean_object* v_00_u03b1_1475_, lean_object* v_inst_1476_, lean_object* v_l_u2081_1477_, lean_object* v_l_u2082_1478_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = l_List_isSuffixOf___redArg(v_inst_1476_, v_l_u2081_1477_, v_l_u2082_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_inst_1481_, lean_object* v_l_u2081_1482_, lean_object* v_l_u2082_1483_){
_start:
{
uint8_t v_res_1484_; lean_object* v_r_1485_; 
v_res_1484_ = l_List_isSuffixOf(v_00_u03b1_1480_, v_inst_1481_, v_l_u2081_1482_, v_l_u2082_1483_);
v_r_1485_ = lean_box(v_res_1484_);
return v_r_1485_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___redArg(lean_object* v_inst_1486_, lean_object* v_l_u2081_1487_, lean_object* v_l_u2082_1488_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = l_List_reverse___redArg(v_l_u2081_1487_);
v___x_1490_ = l_List_reverse___redArg(v_l_u2082_1488_);
v___x_1491_ = l_List_isPrefixOf_x3f___redArg(v_inst_1486_, v___x_1489_, v___x_1490_);
if (lean_obj_tag(v___x_1491_) == 0)
{
return v___x_1491_;
}
else
{
lean_object* v_val_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1500_; 
v_val_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1500_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_val_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1500_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = l_List_reverse___redArg(v_val_1492_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1496_);
v___x_1498_ = v___x_1494_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object* v_00_u03b1_1501_, lean_object* v_inst_1502_, lean_object* v_l_u2081_1503_, lean_object* v_l_u2082_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_List_isSuffixOf_x3f___redArg(v_inst_1502_, v_l_u2081_1503_, v_l_u2082_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0));
v___x_1524_ = l_String_toRawSubstring_x27(v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object* v_x_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
lean_inc(v_x_1536_);
v___x_1540_ = l_Lean_Syntax_isOfKind(v_x_1536_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_dec(v_x_1536_);
v___x_1541_ = lean_box(1);
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v_a_1538_);
return v___x_1542_;
}
else
{
lean_object* v_quotContext_1543_; lean_object* v_currMacroScope_1544_; lean_object* v_ref_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_quotContext_1543_ = lean_ctor_get(v_a_1537_, 1);
v_currMacroScope_1544_ = lean_ctor_get(v_a_1537_, 2);
v_ref_1545_ = lean_ctor_get(v_a_1537_, 5);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = l_Lean_Syntax_getArg(v_x_1536_, v___x_1546_);
v___x_1548_ = lean_unsigned_to_nat(2u);
v___x_1549_ = l_Lean_Syntax_getArg(v_x_1536_, v___x_1548_);
lean_dec(v_x_1536_);
v___x_1550_ = 0;
v___x_1551_ = l_Lean_SourceInfo_fromRef(v_ref_1545_, v___x_1550_);
v___x_1552_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1553_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
v___x_1554_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2));
lean_inc(v_currMacroScope_1544_);
lean_inc(v_quotContext_1543_);
v___x_1555_ = l_Lean_addMacroScope(v_quotContext_1543_, v___x_1554_, v_currMacroScope_1544_);
v___x_1556_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5));
lean_inc_n(v___x_1551_, 2);
v___x_1557_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1551_);
lean_ctor_set(v___x_1557_, 1, v___x_1553_);
lean_ctor_set(v___x_1557_, 2, v___x_1555_);
lean_ctor_set(v___x_1557_, 3, v___x_1556_);
v___x_1558_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1559_ = l_Lean_Syntax_node2(v___x_1551_, v___x_1558_, v___x_1547_, v___x_1549_);
v___x_1560_ = l_Lean_Syntax_node2(v___x_1551_, v___x_1552_, v___x_1557_, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v_a_1538_);
return v___x_1561_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___boxed(lean_object* v_x_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(v_x_1562_, v_a_1563_, v_a_1564_);
lean_dec_ref(v_a_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object* v_x_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1566_);
v___x_1570_ = l_Lean_Syntax_isOfKind(v_x_1566_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec(v_x_1566_);
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_a_1568_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = l_Lean_Syntax_getArg(v_x_1566_, v___x_1573_);
v___x_1575_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1574_);
v___x_1576_ = l_Lean_Syntax_isOfKind(v___x_1574_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec(v___x_1574_);
lean_dec(v_x_1566_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v_a_1568_);
return v___x_1578_;
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1579_ = lean_unsigned_to_nat(1u);
v___x_1580_ = l_Lean_Syntax_getArg(v_x_1566_, v___x_1579_);
lean_dec(v_x_1566_);
v___x_1581_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1580_);
v___x_1582_ = l_Lean_Syntax_matchesNull(v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v___x_1580_);
lean_dec(v___x_1574_);
v___x_1583_ = lean_box(0);
v___x_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_a_1568_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v_ref_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1585_ = l_Lean_Syntax_getArg(v___x_1580_, v___x_1573_);
v___x_1586_ = l_Lean_Syntax_getArg(v___x_1580_, v___x_1579_);
lean_dec(v___x_1580_);
v_ref_1587_ = l_Lean_replaceRef(v___x_1574_, v_a_1567_);
lean_dec(v___x_1574_);
v___x_1588_ = 0;
v___x_1589_ = l_Lean_SourceInfo_fromRef(v_ref_1587_, v___x_1588_);
lean_dec(v_ref_1587_);
v___x_1590_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
v___x_1591_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__2));
lean_inc(v___x_1589_);
v___x_1592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1589_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_Syntax_node3(v___x_1589_, v___x_1590_, v___x_1585_, v___x_1592_, v___x_1586_);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v_a_1568_);
return v___x_1594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object* v_x_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(v_x_1595_, v_a_1596_, v_a_1597_);
lean_dec(v_a_1596_);
return v_res_1598_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0));
v___x_1617_ = l_String_toRawSubstring_x27(v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object* v_x_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
lean_inc(v_x_1629_);
v___x_1633_ = l_Lean_Syntax_isOfKind(v_x_1629_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec(v_x_1629_);
v___x_1634_ = lean_box(1);
v___x_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
lean_ctor_set(v___x_1635_, 1, v_a_1631_);
return v___x_1635_;
}
else
{
lean_object* v_quotContext_1636_; lean_object* v_currMacroScope_1637_; lean_object* v_ref_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_quotContext_1636_ = lean_ctor_get(v_a_1630_, 1);
v_currMacroScope_1637_ = lean_ctor_get(v_a_1630_, 2);
v_ref_1638_ = lean_ctor_get(v_a_1630_, 5);
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = l_Lean_Syntax_getArg(v_x_1629_, v___x_1639_);
v___x_1641_ = lean_unsigned_to_nat(2u);
v___x_1642_ = l_Lean_Syntax_getArg(v_x_1629_, v___x_1641_);
lean_dec(v_x_1629_);
v___x_1643_ = 0;
v___x_1644_ = l_Lean_SourceInfo_fromRef(v_ref_1638_, v___x_1643_);
v___x_1645_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1646_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
v___x_1647_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1637_);
lean_inc(v_quotContext_1636_);
v___x_1648_ = l_Lean_addMacroScope(v_quotContext_1636_, v___x_1647_, v_currMacroScope_1637_);
v___x_1649_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1644_, 2);
v___x_1650_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1644_);
lean_ctor_set(v___x_1650_, 1, v___x_1646_);
lean_ctor_set(v___x_1650_, 2, v___x_1648_);
lean_ctor_set(v___x_1650_, 3, v___x_1649_);
v___x_1651_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1652_ = l_Lean_Syntax_node2(v___x_1644_, v___x_1651_, v___x_1640_, v___x_1642_);
v___x_1653_ = l_Lean_Syntax_node2(v___x_1644_, v___x_1645_, v___x_1650_, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_a_1631_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___boxed(lean_object* v_x_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(v_x_1655_, v_a_1656_, v_a_1657_);
lean_dec_ref(v_a_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object* v_x_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1659_);
v___x_1663_ = l_Lean_Syntax_isOfKind(v_x_1659_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v_x_1659_);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v_a_1661_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
v___x_1667_ = l_Lean_Syntax_getArg(v_x_1659_, v___x_1666_);
v___x_1668_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1667_);
v___x_1669_ = l_Lean_Syntax_isOfKind(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec(v___x_1667_);
lean_dec(v_x_1659_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v_a_1661_);
return v___x_1671_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1672_ = lean_unsigned_to_nat(1u);
v___x_1673_ = l_Lean_Syntax_getArg(v_x_1659_, v___x_1672_);
lean_dec(v_x_1659_);
v___x_1674_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1673_);
v___x_1675_ = l_Lean_Syntax_matchesNull(v___x_1673_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v___x_1673_);
lean_dec(v___x_1667_);
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_a_1661_);
return v___x_1677_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_ref_1680_; uint8_t v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1678_ = l_Lean_Syntax_getArg(v___x_1673_, v___x_1666_);
v___x_1679_ = l_Lean_Syntax_getArg(v___x_1673_, v___x_1672_);
lean_dec(v___x_1673_);
v_ref_1680_ = l_Lean_replaceRef(v___x_1667_, v_a_1660_);
lean_dec(v___x_1667_);
v___x_1681_ = 0;
v___x_1682_ = l_Lean_SourceInfo_fromRef(v_ref_1680_, v___x_1681_);
lean_dec(v_ref_1680_);
v___x_1683_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
v___x_1684_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__2));
lean_inc(v___x_1682_);
v___x_1685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1682_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = l_Lean_Syntax_node3(v___x_1682_, v___x_1683_, v___x_1678_, v___x_1685_, v___x_1679_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v_a_1661_);
return v___x_1687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object* v_x_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(v_x_1688_, v_a_1689_, v_a_1690_);
lean_dec(v_a_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal___redArg(lean_object* v_inst_1692_, lean_object* v_l_u2081_1693_, lean_object* v_l_u2082_1694_){
_start:
{
uint8_t v___x_1695_; 
lean_inc(v_l_u2082_1694_);
lean_inc(v_l_u2081_1693_);
lean_inc_ref(v_inst_1692_);
v___x_1695_ = l_List_isPrefixOf___redArg(v_inst_1692_, v_l_u2081_1693_, v_l_u2082_1694_);
if (v___x_1695_ == 0)
{
if (lean_obj_tag(v_l_u2082_1694_) == 0)
{
lean_dec(v_l_u2081_1693_);
lean_dec_ref(v_inst_1692_);
return v___x_1695_;
}
else
{
lean_object* v_tail_1696_; 
v_tail_1696_ = lean_ctor_get(v_l_u2082_1694_, 1);
lean_inc(v_tail_1696_);
lean_dec_ref_known(v_l_u2082_1694_, 2);
v_l_u2082_1694_ = v_tail_1696_;
goto _start;
}
}
else
{
lean_dec(v_l_u2082_1694_);
lean_dec(v_l_u2081_1693_);
lean_dec_ref(v_inst_1692_);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___redArg___boxed(lean_object* v_inst_1698_, lean_object* v_l_u2081_1699_, lean_object* v_l_u2082_1700_){
_start:
{
uint8_t v_res_1701_; lean_object* v_r_1702_; 
v_res_1701_ = l_List_isInfixOf__internal___redArg(v_inst_1698_, v_l_u2081_1699_, v_l_u2082_1700_);
v_r_1702_ = lean_box(v_res_1701_);
return v_r_1702_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal(lean_object* v_00_u03b1_1703_, lean_object* v_inst_1704_, lean_object* v_l_u2081_1705_, lean_object* v_l_u2082_1706_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = l_List_isInfixOf__internal___redArg(v_inst_1704_, v_l_u2081_1705_, v_l_u2082_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_inst_1709_, lean_object* v_l_u2081_1710_, lean_object* v_l_u2082_1711_){
_start:
{
uint8_t v_res_1712_; lean_object* v_r_1713_; 
v_res_1712_ = l_List_isInfixOf__internal(v_00_u03b1_1708_, v_inst_1709_, v_l_u2081_1710_, v_l_u2082_1711_);
v_r_1713_ = lean_box(v_res_1712_);
return v_r_1713_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go___redArg(lean_object* v_l_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
if (lean_obj_tag(v_a_1715_) == 0)
{
lean_object* v___x_1718_; 
lean_dec(v_a_1717_);
lean_dec(v_a_1716_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_l_1714_);
lean_ctor_set(v___x_1718_, 1, v_a_1715_);
return v___x_1718_;
}
else
{
lean_object* v_head_1719_; lean_object* v_tail_1720_; lean_object* v_zero_1721_; uint8_t v_isZero_1722_; 
v_head_1719_ = lean_ctor_get(v_a_1715_, 0);
v_tail_1720_ = lean_ctor_get(v_a_1715_, 1);
v_zero_1721_ = lean_unsigned_to_nat(0u);
v_isZero_1722_ = lean_nat_dec_eq(v_a_1716_, v_zero_1721_);
if (v_isZero_1722_ == 1)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v_a_1716_);
lean_dec(v_l_1714_);
v___x_1723_ = l_List_reverse___redArg(v_a_1717_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v_a_1715_);
return v___x_1724_;
}
else
{
lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1734_; 
lean_inc(v_tail_1720_);
lean_inc(v_head_1719_);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_a_1715_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; lean_object* v_unused_1736_; 
v_unused_1735_ = lean_ctor_get(v_a_1715_, 1);
lean_dec(v_unused_1735_);
v_unused_1736_ = lean_ctor_get(v_a_1715_, 0);
lean_dec(v_unused_1736_);
v___x_1726_ = v_a_1715_;
v_isShared_1727_ = v_isSharedCheck_1734_;
goto v_resetjp_1725_;
}
else
{
lean_dec(v_a_1715_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1734_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_one_1728_; lean_object* v_n_1729_; lean_object* v___x_1731_; 
v_one_1728_ = lean_unsigned_to_nat(1u);
v_n_1729_ = lean_nat_sub(v_a_1716_, v_one_1728_);
lean_dec(v_a_1716_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v_a_1717_);
v___x_1731_ = v___x_1726_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_head_1719_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_a_1717_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
v_a_1715_ = v_tail_1720_;
v_a_1716_ = v_n_1729_;
v_a_1717_ = v___x_1731_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object* v_00_u03b1_1737_, lean_object* v_l_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_List_splitAt_go___redArg(v_l_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt___redArg(lean_object* v_n_1743_, lean_object* v_l_1744_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_box(0);
lean_inc(v_l_1744_);
v___x_1746_ = l_List_splitAt_go___redArg(v_l_1744_, v_l_1744_, v_n_1743_, v___x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt(lean_object* v_00_u03b1_1747_, lean_object* v_n_1748_, lean_object* v_l_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_List_splitAt___redArg(v_n_1748_, v_l_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg(lean_object* v_xs_1751_, lean_object* v_i_1752_){
_start:
{
lean_object* v_len_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v_len_1753_ = l_List_length___redArg(v_xs_1751_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = lean_nat_dec_le(v_len_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v_i_1756_; lean_object* v_ys_1757_; lean_object* v_zs_1758_; lean_object* v___x_1759_; 
v_i_1756_ = lean_nat_mod(v_i_1752_, v_len_1753_);
lean_dec(v_len_1753_);
lean_inc(v_xs_1751_);
v_ys_1757_ = l_List_take___redArg(v_i_1756_, v_xs_1751_);
v_zs_1758_ = l_List_drop___redArg(v_i_1756_, v_xs_1751_);
lean_dec(v_xs_1751_);
v___x_1759_ = l_List_appendTR___redArg(v_zs_1758_, v_ys_1757_);
return v___x_1759_;
}
else
{
lean_dec(v_len_1753_);
return v_xs_1751_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg___boxed(lean_object* v_xs_1760_, lean_object* v_i_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_List_rotateLeft___redArg(v_xs_1760_, v_i_1761_);
lean_dec(v_i_1761_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft(lean_object* v_00_u03b1_1763_, lean_object* v_xs_1764_, lean_object* v_i_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_List_rotateLeft___redArg(v_xs_1764_, v_i_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___boxed(lean_object* v_00_u03b1_1767_, lean_object* v_xs_1768_, lean_object* v_i_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_List_rotateLeft(v_00_u03b1_1767_, v_xs_1768_, v_i_1769_);
lean_dec(v_i_1769_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg(lean_object* v_xs_1771_, lean_object* v_i_1772_){
_start:
{
lean_object* v_len_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_len_1773_ = l_List_length___redArg(v_xs_1771_);
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = lean_nat_dec_le(v_len_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v_i_1777_; lean_object* v_ys_1778_; lean_object* v_zs_1779_; lean_object* v___x_1780_; 
v___x_1776_ = lean_nat_mod(v_i_1772_, v_len_1773_);
v_i_1777_ = lean_nat_sub(v_len_1773_, v___x_1776_);
lean_dec(v___x_1776_);
lean_dec(v_len_1773_);
lean_inc(v_xs_1771_);
v_ys_1778_ = l_List_take___redArg(v_i_1777_, v_xs_1771_);
v_zs_1779_ = l_List_drop___redArg(v_i_1777_, v_xs_1771_);
lean_dec(v_xs_1771_);
v___x_1780_ = l_List_appendTR___redArg(v_zs_1779_, v_ys_1778_);
return v___x_1780_;
}
else
{
lean_dec(v_len_1773_);
return v_xs_1771_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg___boxed(lean_object* v_xs_1781_, lean_object* v_i_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_List_rotateRight___redArg(v_xs_1781_, v_i_1782_);
lean_dec(v_i_1782_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight(lean_object* v_00_u03b1_1784_, lean_object* v_xs_1785_, lean_object* v_i_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_List_rotateRight___redArg(v_xs_1785_, v_i_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___boxed(lean_object* v_00_u03b1_1788_, lean_object* v_xs_1789_, lean_object* v_i_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_List_rotateRight(v_00_u03b1_1788_, v_xs_1789_, v_i_1790_);
lean_dec(v_i_1790_);
return v_res_1791_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise___redArg(lean_object* v_inst_1792_, lean_object* v_x_1793_){
_start:
{
if (lean_obj_tag(v_x_1793_) == 0)
{
uint8_t v___x_1794_; 
lean_dec_ref(v_inst_1792_);
v___x_1794_ = 1;
return v___x_1794_;
}
else
{
lean_object* v_head_1795_; lean_object* v_tail_1796_; uint8_t v_decide_1797_; 
v_head_1795_ = lean_ctor_get(v_x_1793_, 0);
lean_inc(v_head_1795_);
v_tail_1796_ = lean_ctor_get(v_x_1793_, 1);
lean_inc_n(v_tail_1796_, 2);
lean_dec_ref_known(v_x_1793_, 2);
lean_inc_ref(v_inst_1792_);
v_decide_1797_ = l_List_instDecidablePairwise___redArg(v_inst_1792_, v_tail_1796_);
if (v_decide_1797_ == 0)
{
lean_dec(v_tail_1796_);
lean_dec(v_head_1795_);
lean_dec_ref(v_inst_1792_);
return v_decide_1797_;
}
else
{
lean_object* v___x_1798_; uint8_t v_decide_1799_; 
v___x_1798_ = lean_apply_1(v_inst_1792_, v_head_1795_);
v_decide_1799_ = l_List_decidableBAll___redArg(v___x_1798_, v_tail_1796_);
return v_decide_1799_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___redArg___boxed(lean_object* v_inst_1800_, lean_object* v_x_1801_){
_start:
{
uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_res_1802_ = l_List_instDecidablePairwise___redArg(v_inst_1800_, v_x_1801_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise(lean_object* v_00_u03b1_1804_, lean_object* v_R_1805_, lean_object* v_inst_1806_, lean_object* v_x_1807_){
_start:
{
uint8_t v___x_1808_; 
v___x_1808_ = l_List_instDecidablePairwise___redArg(v_inst_1806_, v_x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___boxed(lean_object* v_00_u03b1_1809_, lean_object* v_R_1810_, lean_object* v_inst_1811_, lean_object* v_x_1812_){
_start:
{
uint8_t v_res_1813_; lean_object* v_r_1814_; 
v_res_1813_ = l_List_instDecidablePairwise(v_00_u03b1_1809_, v_R_1810_, v_inst_1811_, v_x_1812_);
v_r_1814_ = lean_box(v_res_1813_);
return v_r_1814_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg___lam__0(lean_object* v_inst_1815_, lean_object* v_a_1816_, lean_object* v_b_1817_){
_start:
{
lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = lean_apply_2(v_inst_1815_, v_a_1816_, v_b_1817_);
v___x_1819_ = lean_unbox(v___x_1818_);
if (v___x_1819_ == 0)
{
uint8_t v___x_1820_; 
v___x_1820_ = 1;
return v___x_1820_;
}
else
{
uint8_t v___x_1821_; 
v___x_1821_ = 0;
return v___x_1821_;
}
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___lam__0___boxed(lean_object* v_inst_1822_, lean_object* v_a_1823_, lean_object* v_b_1824_){
_start:
{
uint8_t v_res_1825_; lean_object* v_r_1826_; 
v_res_1825_ = l_List_nodupDecidable___redArg___lam__0(v_inst_1822_, v_a_1823_, v_b_1824_);
v_r_1826_ = lean_box(v_res_1825_);
return v_r_1826_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg(lean_object* v_inst_1827_, lean_object* v_l_1828_){
_start:
{
lean_object* v___f_1829_; uint8_t v___x_1830_; 
v___f_1829_ = lean_alloc_closure((void*)(l_List_nodupDecidable___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1829_, 0, v_inst_1827_);
v___x_1830_ = l_List_instDecidablePairwise___redArg(v___f_1829_, v_l_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___boxed(lean_object* v_inst_1831_, lean_object* v_l_1832_){
_start:
{
uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_res_1833_ = l_List_nodupDecidable___redArg(v_inst_1831_, v_l_1832_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable(lean_object* v_00_u03b1_1835_, lean_object* v_inst_1836_, lean_object* v_l_1837_){
_start:
{
uint8_t v___x_1838_; 
v___x_1838_ = l_List_nodupDecidable___redArg(v_inst_1836_, v_l_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___boxed(lean_object* v_00_u03b1_1839_, lean_object* v_inst_1840_, lean_object* v_l_1841_){
_start:
{
uint8_t v_res_1842_; lean_object* v_r_1843_; 
v_res_1842_ = l_List_nodupDecidable(v_00_u03b1_1839_, v_inst_1840_, v_l_1841_);
v_r_1843_ = lean_box(v_res_1842_);
return v_r_1843_;
}
}
LEAN_EXPORT lean_object* l_List_replace___redArg(lean_object* v_inst_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
if (lean_obj_tag(v_x_1845_) == 0)
{
lean_dec(v_x_1847_);
lean_dec(v_x_1846_);
lean_dec_ref(v_inst_1844_);
return v_x_1845_;
}
else
{
lean_object* v_head_1848_; lean_object* v_tail_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1862_; 
v_head_1848_ = lean_ctor_get(v_x_1845_, 0);
v_tail_1849_ = lean_ctor_get(v_x_1845_, 1);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_x_1845_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1851_ = v_x_1845_;
v_isShared_1852_ = v_isSharedCheck_1862_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_tail_1849_);
lean_inc(v_head_1848_);
lean_dec(v_x_1845_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1862_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; uint8_t v___x_1854_; 
lean_inc_ref(v_inst_1844_);
lean_inc(v_head_1848_);
lean_inc(v_x_1846_);
v___x_1853_ = lean_apply_2(v_inst_1844_, v_x_1846_, v_head_1848_);
v___x_1854_ = lean_unbox(v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = l_List_replace___redArg(v_inst_1844_, v_tail_1849_, v_x_1846_, v_x_1847_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v___x_1855_);
v___x_1857_ = v___x_1851_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_head_1848_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
else
{
lean_object* v___x_1860_; 
lean_dec(v_head_1848_);
lean_dec(v_x_1846_);
lean_dec_ref(v_inst_1844_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v_x_1847_);
v___x_1860_ = v___x_1851_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_x_1847_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_tail_1849_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_replace(lean_object* v_00_u03b1_1863_, lean_object* v_inst_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_List_replace___redArg(v_inst_1864_, v_x_1865_, v_x_1866_, v_x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg(lean_object* v_f_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_zero_1872_; uint8_t v_isZero_1873_; 
v_zero_1872_ = lean_unsigned_to_nat(0u);
v_isZero_1873_ = lean_nat_dec_eq(v_a_1870_, v_zero_1872_);
if (v_isZero_1873_ == 1)
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_apply_1(v_f_1869_, v_a_1871_);
return v___x_1874_;
}
else
{
if (lean_obj_tag(v_a_1871_) == 0)
{
lean_dec_ref(v_f_1869_);
return v_a_1871_;
}
else
{
lean_object* v_head_1875_; lean_object* v_tail_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1886_; 
v_head_1875_ = lean_ctor_get(v_a_1871_, 0);
v_tail_1876_ = lean_ctor_get(v_a_1871_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_a_1871_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1878_ = v_a_1871_;
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_tail_1876_);
lean_inc(v_head_1875_);
lean_dec(v_a_1871_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_one_1880_; lean_object* v_n_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v_one_1880_ = lean_unsigned_to_nat(1u);
v_n_1881_ = lean_nat_sub(v_a_1870_, v_one_1880_);
v___x_1882_ = l_List_modifyTailIdx_go___redArg(v_f_1869_, v_n_1881_, v_tail_1876_);
lean_dec(v_n_1881_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___x_1882_);
v___x_1884_ = v___x_1878_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_head_1875_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg___boxed(lean_object* v_f_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_List_modifyTailIdx_go___redArg(v_f_1887_, v_a_1888_, v_a_1889_);
lean_dec(v_a_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go(lean_object* v_00_u03b1_1891_, lean_object* v_f_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_List_modifyTailIdx_go___redArg(v_f_1892_, v_a_1893_, v_a_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___boxed(lean_object* v_00_u03b1_1896_, lean_object* v_f_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_List_modifyTailIdx_go(v_00_u03b1_1896_, v_f_1897_, v_a_1898_, v_a_1899_);
lean_dec(v_a_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg(lean_object* v_l_1901_, lean_object* v_i_1902_, lean_object* v_f_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_List_modifyTailIdx_go___redArg(v_f_1903_, v_i_1902_, v_l_1901_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg___boxed(lean_object* v_l_1905_, lean_object* v_i_1906_, lean_object* v_f_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_List_modifyTailIdx___redArg(v_l_1905_, v_i_1906_, v_f_1907_);
lean_dec(v_i_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx(lean_object* v_00_u03b1_1909_, lean_object* v_l_1910_, lean_object* v_i_1911_, lean_object* v_f_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_List_modifyTailIdx_go___redArg(v_f_1912_, v_i_1911_, v_l_1910_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___boxed(lean_object* v_00_u03b1_1914_, lean_object* v_l_1915_, lean_object* v_i_1916_, lean_object* v_f_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_List_modifyTailIdx(v_00_u03b1_1914_, v_l_1915_, v_i_1916_, v_f_1917_);
lean_dec(v_i_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_List_modifyHead___redArg(lean_object* v_f_1919_, lean_object* v_x_1920_){
_start:
{
if (lean_obj_tag(v_x_1920_) == 0)
{
lean_dec(v_f_1919_);
return v_x_1920_;
}
else
{
lean_object* v_head_1921_; lean_object* v_tail_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1930_; 
v_head_1921_ = lean_ctor_get(v_x_1920_, 0);
v_tail_1922_ = lean_ctor_get(v_x_1920_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_x_1920_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1924_ = v_x_1920_;
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_tail_1922_);
lean_inc(v_head_1921_);
lean_dec(v_x_1920_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = lean_apply_1(v_f_1919_, v_head_1921_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1926_);
v___x_1928_ = v___x_1924_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_tail_1922_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyHead(lean_object* v_00_u03b1_1931_, lean_object* v_f_1932_, lean_object* v_x_1933_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 0)
{
lean_dec(v_f_1932_);
return v_x_1933_;
}
else
{
lean_object* v_head_1934_; lean_object* v_tail_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1943_; 
v_head_1934_ = lean_ctor_get(v_x_1933_, 0);
v_tail_1935_ = lean_ctor_get(v_x_1933_, 1);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_x_1933_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1937_ = v_x_1933_;
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_tail_1935_);
lean_inc(v_head_1934_);
lean_dec(v_x_1933_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = lean_apply_1(v_f_1932_, v_head_1934_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1939_);
v___x_1941_ = v___x_1937_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_tail_1935_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg(lean_object* v_l_1944_, lean_object* v_i_1945_, lean_object* v_f_1946_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1947_, 0, lean_box(0));
lean_closure_set(v___x_1947_, 1, v_f_1946_);
v___x_1948_ = l_List_modifyTailIdx_go___redArg(v___x_1947_, v_i_1945_, v_l_1944_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg___boxed(lean_object* v_l_1949_, lean_object* v_i_1950_, lean_object* v_f_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_List_modify___redArg(v_l_1949_, v_i_1950_, v_f_1951_);
lean_dec(v_i_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_List_modify(lean_object* v_00_u03b1_1953_, lean_object* v_l_1954_, lean_object* v_i_1955_, lean_object* v_f_1956_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1957_, 0, lean_box(0));
lean_closure_set(v___x_1957_, 1, v_f_1956_);
v___x_1958_ = l_List_modifyTailIdx_go___redArg(v___x_1957_, v_i_1955_, v_l_1954_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_List_modify___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_l_1960_, lean_object* v_i_1961_, lean_object* v_f_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_List_modify(v_00_u03b1_1959_, v_l_1960_, v_i_1961_, v_f_1962_);
lean_dec(v_i_1961_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object* v_inst_1964_, lean_object* v_a_1965_, lean_object* v_l_1966_){
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
LEAN_EXPORT lean_object* l_List_insert(lean_object* v_00_u03b1_1969_, lean_object* v_inst_1970_, lean_object* v_a_1971_, lean_object* v_l_1972_){
_start:
{
uint8_t v___x_1973_; 
lean_inc(v_l_1972_);
lean_inc(v_a_1971_);
v___x_1973_ = l_List_elem___redArg(v_inst_1970_, v_a_1971_, v_l_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_a_1971_);
lean_ctor_set(v___x_1974_, 1, v_l_1972_);
return v___x_1974_;
}
else
{
lean_dec(v_a_1971_);
return v_l_1972_;
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_zero_1978_; uint8_t v_isZero_1979_; 
v_zero_1978_ = lean_unsigned_to_nat(0u);
v_isZero_1979_ = lean_nat_dec_eq(v_a_1976_, v_zero_1978_);
if (v_isZero_1979_ == 1)
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_a_1975_);
lean_ctor_set(v___x_1980_, 1, v_a_1977_);
return v___x_1980_;
}
else
{
if (lean_obj_tag(v_a_1977_) == 0)
{
lean_dec(v_a_1975_);
return v_a_1977_;
}
else
{
lean_object* v_head_1981_; lean_object* v_tail_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1992_; 
v_head_1981_ = lean_ctor_get(v_a_1977_, 0);
v_tail_1982_ = lean_ctor_get(v_a_1977_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1984_ = v_a_1977_;
v_isShared_1985_ = v_isSharedCheck_1992_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_tail_1982_);
lean_inc(v_head_1981_);
lean_dec(v_a_1977_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1992_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_one_1986_; lean_object* v_n_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v_one_1986_ = lean_unsigned_to_nat(1u);
v_n_1987_ = lean_nat_sub(v_a_1976_, v_one_1986_);
v___x_1988_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1975_, v_n_1987_, v_tail_1982_);
lean_dec(v_n_1987_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 1, v___x_1988_);
v___x_1990_ = v___x_1984_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_head_1981_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg___boxed(lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1993_, v_a_1994_, v_a_1995_);
lean_dec(v_a_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg(lean_object* v_xs_1997_, lean_object* v_i_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1999_, v_i_1998_, v_xs_1997_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___boxed(lean_object* v_xs_2001_, lean_object* v_i_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_List_insertIdx___redArg(v_xs_2001_, v_i_2002_, v_a_2003_);
lean_dec(v_i_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx(lean_object* v_00_u03b1_2005_, lean_object* v_xs_2006_, lean_object* v_i_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_2008_, v_i_2007_, v_xs_2006_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___boxed(lean_object* v_00_u03b1_2010_, lean_object* v_xs_2011_, lean_object* v_i_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_List_insertIdx(v_00_u03b1_2010_, v_xs_2011_, v_i_2012_, v_a_2013_);
lean_dec(v_i_2012_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(lean_object* v_00_u03b1_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_2016_, v_a_2017_, v_a_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(v_00_u03b1_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
lean_dec(v_a_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_List_erase___redArg(lean_object* v_inst_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_){
_start:
{
if (lean_obj_tag(v_x_2026_) == 0)
{
lean_dec(v_x_2027_);
lean_dec_ref(v_inst_2025_);
return v_x_2026_;
}
else
{
lean_object* v_head_2028_; lean_object* v_tail_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2039_; 
v_head_2028_ = lean_ctor_get(v_x_2026_, 0);
v_tail_2029_ = lean_ctor_get(v_x_2026_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_x_2026_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2031_ = v_x_2026_;
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_tail_2029_);
lean_inc(v_head_2028_);
lean_dec(v_x_2026_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
lean_inc_ref(v_inst_2025_);
lean_inc(v_x_2027_);
lean_inc(v_head_2028_);
v___x_2033_ = lean_apply_2(v_inst_2025_, v_head_2028_, v_x_2027_);
v___x_2034_ = lean_unbox(v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2035_ = l_List_erase___redArg(v_inst_2025_, v_tail_2029_, v_x_2027_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v___x_2035_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_head_2028_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
else
{
lean_del_object(v___x_2031_);
lean_dec(v_head_2028_);
lean_dec(v_x_2027_);
lean_dec_ref(v_inst_2025_);
return v_tail_2029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_erase(lean_object* v_00_u03b1_2040_, lean_object* v_inst_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_List_erase___redArg(v_inst_2041_, v_x_2042_, v_x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(lean_object* v_x_2045_, lean_object* v_x_2046_, lean_object* v_h__1_2047_, lean_object* v_h__2_2048_){
_start:
{
if (lean_obj_tag(v_x_2045_) == 0)
{
lean_object* v___x_2049_; 
lean_dec(v_h__2_2048_);
v___x_2049_ = lean_apply_1(v_h__1_2047_, v_x_2046_);
return v___x_2049_;
}
else
{
lean_object* v_head_2050_; lean_object* v_tail_2051_; lean_object* v___x_2052_; 
lean_dec(v_h__1_2047_);
v_head_2050_ = lean_ctor_get(v_x_2045_, 0);
lean_inc(v_head_2050_);
v_tail_2051_ = lean_ctor_get(v_x_2045_, 1);
lean_inc(v_tail_2051_);
lean_dec_ref_known(v_x_2045_, 2);
v___x_2052_ = lean_apply_3(v_h__2_2048_, v_head_2050_, v_tail_2051_, v_x_2046_);
return v___x_2052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object* v_00_u03b1_2053_, lean_object* v_motive_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_h__1_2057_, lean_object* v_h__2_2058_){
_start:
{
if (lean_obj_tag(v_x_2055_) == 0)
{
lean_object* v___x_2059_; 
lean_dec(v_h__2_2058_);
v___x_2059_ = lean_apply_1(v_h__1_2057_, v_x_2056_);
return v___x_2059_;
}
else
{
lean_object* v_head_2060_; lean_object* v_tail_2061_; lean_object* v___x_2062_; 
lean_dec(v_h__1_2057_);
v_head_2060_ = lean_ctor_get(v_x_2055_, 0);
lean_inc(v_head_2060_);
v_tail_2061_ = lean_ctor_get(v_x_2055_, 1);
lean_inc(v_tail_2061_);
lean_dec_ref_known(v_x_2055_, 2);
v___x_2062_ = lean_apply_3(v_h__2_2058_, v_head_2060_, v_tail_2061_, v_x_2056_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP___redArg(lean_object* v_p_2063_, lean_object* v_x_2064_){
_start:
{
if (lean_obj_tag(v_x_2064_) == 0)
{
lean_dec_ref(v_p_2063_);
return v_x_2064_;
}
else
{
lean_object* v_head_2065_; lean_object* v_tail_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2076_; 
v_head_2065_ = lean_ctor_get(v_x_2064_, 0);
v_tail_2066_ = lean_ctor_get(v_x_2064_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_x_2064_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2068_ = v_x_2064_;
v_isShared_2069_ = v_isSharedCheck_2076_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_tail_2066_);
lean_inc(v_head_2065_);
lean_dec(v_x_2064_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2076_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; uint8_t v___x_2071_; 
lean_inc_ref(v_p_2063_);
lean_inc(v_head_2065_);
v___x_2070_ = lean_apply_1(v_p_2063_, v_head_2065_);
v___x_2071_ = lean_unbox(v___x_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = l_List_eraseP___redArg(v_p_2063_, v_tail_2066_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v___x_2072_);
v___x_2074_ = v___x_2068_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_head_2065_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
else
{
lean_del_object(v___x_2068_);
lean_dec(v_head_2065_);
lean_dec_ref(v_p_2063_);
return v_tail_2066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP(lean_object* v_00_u03b1_2077_, lean_object* v_p_2078_, lean_object* v_x_2079_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_List_eraseP___redArg(v_p_2078_, v_x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg(lean_object* v_x_2081_, lean_object* v_x_2082_){
_start:
{
if (lean_obj_tag(v_x_2081_) == 0)
{
return v_x_2081_;
}
else
{
lean_object* v_head_2083_; lean_object* v_tail_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2096_; 
v_head_2083_ = lean_ctor_get(v_x_2081_, 0);
v_tail_2084_ = lean_ctor_get(v_x_2081_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_x_2081_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2086_ = v_x_2081_;
v_isShared_2087_ = v_isSharedCheck_2096_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_tail_2084_);
lean_inc(v_head_2083_);
lean_dec(v_x_2081_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2096_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_zero_2088_; uint8_t v_isZero_2089_; 
v_zero_2088_ = lean_unsigned_to_nat(0u);
v_isZero_2089_ = lean_nat_dec_eq(v_x_2082_, v_zero_2088_);
if (v_isZero_2089_ == 1)
{
lean_del_object(v___x_2086_);
lean_dec(v_head_2083_);
return v_tail_2084_;
}
else
{
lean_object* v_one_2090_; lean_object* v_n_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v_one_2090_ = lean_unsigned_to_nat(1u);
v_n_2091_ = lean_nat_sub(v_x_2082_, v_one_2090_);
v___x_2092_ = l_List_eraseIdx___redArg(v_tail_2084_, v_n_2091_);
lean_dec(v_n_2091_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v___x_2092_);
v___x_2094_ = v___x_2086_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_head_2083_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg___boxed(lean_object* v_x_2097_, lean_object* v_x_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_List_eraseIdx___redArg(v_x_2097_, v_x_2098_);
lean_dec(v_x_2098_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object* v_00_u03b1_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_List_eraseIdx___redArg(v_x_2101_, v_x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___boxed(lean_object* v_00_u03b1_2104_, lean_object* v_x_2105_, lean_object* v_x_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_List_eraseIdx(v_00_u03b1_2104_, v_x_2105_, v_x_2106_);
lean_dec(v_x_2106_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object* v_p_2108_, lean_object* v_x_2109_){
_start:
{
if (lean_obj_tag(v_x_2109_) == 0)
{
lean_object* v___x_2110_; 
lean_dec_ref(v_p_2108_);
v___x_2110_ = lean_box(0);
return v___x_2110_;
}
else
{
lean_object* v_head_2111_; lean_object* v_tail_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v_head_2111_ = lean_ctor_get(v_x_2109_, 0);
lean_inc_n(v_head_2111_, 2);
v_tail_2112_ = lean_ctor_get(v_x_2109_, 1);
lean_inc(v_tail_2112_);
lean_dec_ref_known(v_x_2109_, 2);
lean_inc_ref(v_p_2108_);
v___x_2113_ = lean_apply_1(v_p_2108_, v_head_2111_);
v___x_2114_ = lean_unbox(v___x_2113_);
if (v___x_2114_ == 0)
{
lean_dec(v_head_2111_);
v_x_2109_ = v_tail_2112_;
goto _start;
}
else
{
lean_object* v___x_2116_; 
lean_dec(v_tail_2112_);
lean_dec_ref(v_p_2108_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v_head_2111_);
return v___x_2116_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object* v_00_u03b1_2117_, lean_object* v_p_2118_, lean_object* v_x_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_List_find_x3f___redArg(v_p_2118_, v_x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object* v_f_2121_, lean_object* v_x_2122_){
_start:
{
if (lean_obj_tag(v_x_2122_) == 0)
{
lean_object* v___x_2123_; 
lean_dec_ref(v_f_2121_);
v___x_2123_ = lean_box(0);
return v___x_2123_;
}
else
{
lean_object* v_head_2124_; lean_object* v_tail_2125_; lean_object* v___x_2126_; 
v_head_2124_ = lean_ctor_get(v_x_2122_, 0);
lean_inc(v_head_2124_);
v_tail_2125_ = lean_ctor_get(v_x_2122_, 1);
lean_inc(v_tail_2125_);
lean_dec_ref_known(v_x_2122_, 2);
lean_inc_ref(v_f_2121_);
v___x_2126_ = lean_apply_1(v_f_2121_, v_head_2124_);
if (lean_obj_tag(v___x_2126_) == 0)
{
v_x_2122_ = v_tail_2125_;
goto _start;
}
else
{
lean_dec(v_tail_2125_);
lean_dec_ref(v_f_2121_);
return v___x_2126_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object* v_00_u03b1_2128_, lean_object* v_00_u03b2_2129_, lean_object* v_f_2130_, lean_object* v_x_2131_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_List_findSome_x3f___redArg(v_f_2130_, v_x_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f___redArg(lean_object* v_p_2133_, lean_object* v_x_2134_){
_start:
{
if (lean_obj_tag(v_x_2134_) == 0)
{
lean_object* v___x_2135_; 
lean_dec_ref(v_p_2133_);
v___x_2135_ = lean_box(0);
return v___x_2135_;
}
else
{
lean_object* v_head_2136_; lean_object* v_tail_2137_; lean_object* v___x_2138_; 
v_head_2136_ = lean_ctor_get(v_x_2134_, 0);
lean_inc(v_head_2136_);
v_tail_2137_ = lean_ctor_get(v_x_2134_, 1);
lean_inc(v_tail_2137_);
lean_dec_ref_known(v_x_2134_, 2);
lean_inc_ref(v_p_2133_);
v___x_2138_ = l_List_findRev_x3f___redArg(v_p_2133_, v_tail_2137_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
lean_inc(v_head_2136_);
v___x_2139_ = lean_apply_1(v_p_2133_, v_head_2136_);
v___x_2140_ = lean_unbox(v___x_2139_);
if (v___x_2140_ == 0)
{
lean_dec(v_head_2136_);
return v___x_2138_;
}
else
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2141_, 0, v_head_2136_);
return v___x_2141_;
}
}
else
{
lean_dec(v_head_2136_);
lean_dec_ref(v_p_2133_);
return v___x_2138_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f(lean_object* v_00_u03b1_2142_, lean_object* v_p_2143_, lean_object* v_x_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_List_findRev_x3f___redArg(v_p_2143_, v_x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f___redArg(lean_object* v_f_2146_, lean_object* v_x_2147_){
_start:
{
if (lean_obj_tag(v_x_2147_) == 0)
{
lean_object* v___x_2148_; 
lean_dec_ref(v_f_2146_);
v___x_2148_ = lean_box(0);
return v___x_2148_;
}
else
{
lean_object* v_head_2149_; lean_object* v_tail_2150_; lean_object* v___x_2151_; 
v_head_2149_ = lean_ctor_get(v_x_2147_, 0);
lean_inc(v_head_2149_);
v_tail_2150_ = lean_ctor_get(v_x_2147_, 1);
lean_inc(v_tail_2150_);
lean_dec_ref_known(v_x_2147_, 2);
lean_inc_ref(v_f_2146_);
v___x_2151_ = l_List_findSomeRev_x3f___redArg(v_f_2146_, v_tail_2150_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_apply_1(v_f_2146_, v_head_2149_);
return v___x_2152_;
}
else
{
lean_dec(v_head_2149_);
lean_dec_ref(v_f_2146_);
return v___x_2151_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f(lean_object* v_00_u03b1_2153_, lean_object* v_00_u03b2_2154_, lean_object* v_f_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_List_findSomeRev_x3f___redArg(v_f_2155_, v_x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___redArg(lean_object* v_p_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
if (lean_obj_tag(v_a_2159_) == 0)
{
lean_dec_ref(v_p_2158_);
return v_a_2160_;
}
else
{
lean_object* v_head_2161_; lean_object* v_tail_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_head_2161_ = lean_ctor_get(v_a_2159_, 0);
lean_inc(v_head_2161_);
v_tail_2162_ = lean_ctor_get(v_a_2159_, 1);
lean_inc(v_tail_2162_);
lean_dec_ref_known(v_a_2159_, 2);
lean_inc_ref(v_p_2158_);
v___x_2163_ = lean_apply_1(v_p_2158_, v_head_2161_);
v___x_2164_ = lean_unbox(v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_unsigned_to_nat(1u);
v___x_2166_ = lean_nat_add(v_a_2160_, v___x_2165_);
lean_dec(v_a_2160_);
v_a_2159_ = v_tail_2162_;
v_a_2160_ = v___x_2166_;
goto _start;
}
else
{
lean_dec(v_tail_2162_);
lean_dec_ref(v_p_2158_);
return v_a_2160_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object* v_00_u03b1_2168_, lean_object* v_p_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_List_findIdx_go___redArg(v_p_2169_, v_a_2170_, v_a_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx___redArg(lean_object* v_p_2173_, lean_object* v_l_2174_){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = l_List_findIdx_go___redArg(v_p_2173_, v_l_2174_, v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx(lean_object* v_00_u03b1_2177_, lean_object* v_p_2178_, lean_object* v_l_2179_){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = l_List_findIdx_go___redArg(v_p_2178_, v_l_2179_, v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT uint8_t l_List_idxOf___redArg___lam__0(lean_object* v_inst_2182_, lean_object* v_a_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = lean_apply_2(v_inst_2182_, v_x_2184_, v_a_2183_);
v___x_2186_ = lean_unbox(v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg___lam__0___boxed(lean_object* v_inst_2187_, lean_object* v_a_2188_, lean_object* v_x_2189_){
_start:
{
uint8_t v_res_2190_; lean_object* v_r_2191_; 
v_res_2190_ = l_List_idxOf___redArg___lam__0(v_inst_2187_, v_a_2188_, v_x_2189_);
v_r_2191_ = lean_box(v_res_2190_);
return v_r_2191_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg(lean_object* v_inst_2192_, lean_object* v_a_2193_, lean_object* v_l_2194_){
_start:
{
lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___f_2195_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2195_, 0, v_inst_2192_);
lean_closure_set(v___f_2195_, 1, v_a_2193_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = l_List_findIdx_go___redArg(v___f_2195_, v_l_2194_, v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf(lean_object* v_00_u03b1_2198_, lean_object* v_inst_2199_, lean_object* v_a_2200_, lean_object* v_l_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_List_idxOf___redArg(v_inst_2199_, v_a_2200_, v_l_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___redArg(lean_object* v_p_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
if (lean_obj_tag(v_a_2204_) == 0)
{
lean_object* v___x_2206_; 
lean_dec(v_a_2205_);
lean_dec_ref(v_p_2203_);
v___x_2206_ = lean_box(0);
return v___x_2206_;
}
else
{
lean_object* v_head_2207_; lean_object* v_tail_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v_head_2207_ = lean_ctor_get(v_a_2204_, 0);
lean_inc(v_head_2207_);
v_tail_2208_ = lean_ctor_get(v_a_2204_, 1);
lean_inc(v_tail_2208_);
lean_dec_ref_known(v_a_2204_, 2);
lean_inc_ref(v_p_2203_);
v___x_2209_ = lean_apply_1(v_p_2203_, v_head_2207_);
v___x_2210_ = lean_unbox(v___x_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_unsigned_to_nat(1u);
v___x_2212_ = lean_nat_add(v_a_2205_, v___x_2211_);
lean_dec(v_a_2205_);
v_a_2204_ = v_tail_2208_;
v_a_2205_ = v___x_2212_;
goto _start;
}
else
{
lean_object* v___x_2214_; 
lean_dec(v_tail_2208_);
lean_dec_ref(v_p_2203_);
v___x_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_a_2205_);
return v___x_2214_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go(lean_object* v_00_u03b1_2215_, lean_object* v_p_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_List_findIdx_x3f_go___redArg(v_p_2216_, v_a_2217_, v_a_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f___redArg(lean_object* v_p_2220_, lean_object* v_l_2221_){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = l_List_findIdx_x3f_go___redArg(v_p_2220_, v_l_2221_, v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object* v_00_u03b1_2224_, lean_object* v_p_2225_, lean_object* v_l_2226_){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = l_List_findIdx_x3f_go___redArg(v_p_2225_, v_l_2226_, v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f___redArg(lean_object* v_inst_2229_, lean_object* v_a_2230_, lean_object* v_l_2231_){
_start:
{
lean_object* v___f_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___f_2232_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2232_, 0, v_inst_2229_);
lean_closure_set(v___f_2232_, 1, v_a_2230_);
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = l_List_findIdx_x3f_go___redArg(v___f_2232_, v_l_2231_, v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f(lean_object* v_00_u03b1_2235_, lean_object* v_inst_2236_, lean_object* v_a_2237_, lean_object* v_l_2238_){
_start:
{
lean_object* v___f_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___f_2239_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2239_, 0, v_inst_2236_);
lean_closure_set(v___f_2239_, 1, v_a_2237_);
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = l_List_findIdx_x3f_go___redArg(v___f_2239_, v_l_2238_, v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___redArg(lean_object* v_p_2242_, lean_object* v_l_x27_2243_, lean_object* v_i_2244_){
_start:
{
if (lean_obj_tag(v_l_x27_2243_) == 0)
{
lean_object* v___x_2245_; 
lean_dec(v_i_2244_);
lean_dec_ref(v_p_2242_);
v___x_2245_ = lean_box(0);
return v___x_2245_;
}
else
{
lean_object* v_head_2246_; lean_object* v_tail_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v_head_2246_ = lean_ctor_get(v_l_x27_2243_, 0);
lean_inc(v_head_2246_);
v_tail_2247_ = lean_ctor_get(v_l_x27_2243_, 1);
lean_inc(v_tail_2247_);
lean_dec_ref_known(v_l_x27_2243_, 2);
lean_inc_ref(v_p_2242_);
v___x_2248_ = lean_apply_1(v_p_2242_, v_head_2246_);
v___x_2249_ = lean_unbox(v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_unsigned_to_nat(1u);
v___x_2251_ = lean_nat_add(v_i_2244_, v___x_2250_);
lean_dec(v_i_2244_);
v_l_x27_2243_ = v_tail_2247_;
v_i_2244_ = v___x_2251_;
goto _start;
}
else
{
lean_object* v___x_2253_; 
lean_dec(v_tail_2247_);
lean_dec_ref(v_p_2242_);
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_i_2244_);
return v___x_2253_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go(lean_object* v_00_u03b1_2254_, lean_object* v_p_2255_, lean_object* v_l_2256_, lean_object* v_l_x27_2257_, lean_object* v_i_2258_, lean_object* v_h_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_List_findFinIdx_x3f_go___redArg(v_p_2255_, v_l_x27_2257_, v_i_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___boxed(lean_object* v_00_u03b1_2261_, lean_object* v_p_2262_, lean_object* v_l_2263_, lean_object* v_l_x27_2264_, lean_object* v_i_2265_, lean_object* v_h_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_List_findFinIdx_x3f_go(v_00_u03b1_2261_, v_p_2262_, v_l_2263_, v_l_x27_2264_, v_i_2265_, v_h_2266_);
lean_dec(v_l_2263_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f___redArg(lean_object* v_p_2268_, lean_object* v_l_2269_){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = l_List_findFinIdx_x3f_go___redArg(v_p_2268_, v_l_2269_, v___x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f(lean_object* v_00_u03b1_2272_, lean_object* v_p_2273_, lean_object* v_l_2274_){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = l_List_findFinIdx_x3f_go___redArg(v_p_2273_, v_l_2274_, v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f___redArg(lean_object* v_inst_2277_, lean_object* v_a_2278_, lean_object* v_l_2279_){
_start:
{
lean_object* v___f_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___f_2280_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2280_, 0, v_inst_2277_);
lean_closure_set(v___f_2280_, 1, v_a_2278_);
v___x_2281_ = lean_unsigned_to_nat(0u);
v___x_2282_ = l_List_findFinIdx_x3f_go___redArg(v___f_2280_, v_l_2279_, v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f(lean_object* v_00_u03b1_2283_, lean_object* v_inst_2284_, lean_object* v_a_2285_, lean_object* v_l_2286_){
_start:
{
lean_object* v___f_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___f_2287_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2287_, 0, v_inst_2284_);
lean_closure_set(v___f_2287_, 1, v_a_2285_);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = l_List_findFinIdx_x3f_go___redArg(v___f_2287_, v_l_2286_, v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___redArg(lean_object* v_p_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
if (lean_obj_tag(v_a_2291_) == 0)
{
lean_dec_ref(v_p_2290_);
return v_a_2292_;
}
else
{
lean_object* v_head_2293_; lean_object* v_tail_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v_head_2293_ = lean_ctor_get(v_a_2291_, 0);
lean_inc(v_head_2293_);
v_tail_2294_ = lean_ctor_get(v_a_2291_, 1);
lean_inc(v_tail_2294_);
lean_dec_ref_known(v_a_2291_, 2);
lean_inc_ref(v_p_2290_);
v___x_2295_ = lean_apply_1(v_p_2290_, v_head_2293_);
v___x_2296_ = lean_unbox(v___x_2295_);
if (v___x_2296_ == 0)
{
v_a_2291_ = v_tail_2294_;
goto _start;
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_add(v_a_2292_, v___x_2298_);
lean_dec(v_a_2292_);
v_a_2291_ = v_tail_2294_;
v_a_2292_ = v___x_2299_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go(lean_object* v_00_u03b1_2301_, lean_object* v_p_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_List_countP_go___redArg(v_p_2302_, v_a_2303_, v_a_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_List_countP___redArg(lean_object* v_p_2306_, lean_object* v_l_2307_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = l_List_countP_go___redArg(v_p_2306_, v_l_2307_, v___x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_List_countP(lean_object* v_00_u03b1_2310_, lean_object* v_p_2311_, lean_object* v_l_2312_){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = l_List_countP_go___redArg(v_p_2311_, v_l_2312_, v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_List_count___redArg(lean_object* v_inst_2315_, lean_object* v_a_2316_, lean_object* v_l_2317_){
_start:
{
lean_object* v___f_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___f_2318_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2318_, 0, v_inst_2315_);
lean_closure_set(v___f_2318_, 1, v_a_2316_);
v___x_2319_ = lean_unsigned_to_nat(0u);
v___x_2320_ = l_List_countP_go___redArg(v___f_2318_, v_l_2317_, v___x_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_List_count(lean_object* v_00_u03b1_2321_, lean_object* v_inst_2322_, lean_object* v_a_2323_, lean_object* v_l_2324_){
_start:
{
lean_object* v___f_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___f_2325_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2325_, 0, v_inst_2322_);
lean_closure_set(v___f_2325_, 1, v_a_2323_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = l_List_countP_go___redArg(v___f_2325_, v_l_2324_, v___x_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___redArg(lean_object* v_inst_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_){
_start:
{
if (lean_obj_tag(v_x_2330_) == 0)
{
lean_object* v___x_2331_; 
lean_dec(v_x_2329_);
lean_dec_ref(v_inst_2328_);
v___x_2331_ = lean_box(0);
return v___x_2331_;
}
else
{
lean_object* v_head_2332_; lean_object* v_tail_2333_; lean_object* v_fst_2334_; lean_object* v_snd_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v_head_2332_ = lean_ctor_get(v_x_2330_, 0);
lean_inc(v_head_2332_);
v_tail_2333_ = lean_ctor_get(v_x_2330_, 1);
lean_inc(v_tail_2333_);
lean_dec_ref_known(v_x_2330_, 2);
v_fst_2334_ = lean_ctor_get(v_head_2332_, 0);
lean_inc(v_fst_2334_);
v_snd_2335_ = lean_ctor_get(v_head_2332_, 1);
lean_inc(v_snd_2335_);
lean_dec(v_head_2332_);
lean_inc_ref(v_inst_2328_);
lean_inc(v_x_2329_);
v___x_2336_ = lean_apply_2(v_inst_2328_, v_x_2329_, v_fst_2334_);
v___x_2337_ = lean_unbox(v___x_2336_);
if (v___x_2337_ == 0)
{
lean_dec(v_snd_2335_);
v_x_2330_ = v_tail_2333_;
goto _start;
}
else
{
lean_object* v___x_2339_; 
lean_dec(v_tail_2333_);
lean_dec(v_x_2329_);
lean_dec_ref(v_inst_2328_);
v___x_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2339_, 0, v_snd_2335_);
return v___x_2339_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup(lean_object* v_00_u03b1_2340_, lean_object* v_00_u03b2_2341_, lean_object* v_inst_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_List_lookup___redArg(v_inst_2342_, v_x_2343_, v_x_2344_);
return v___x_2345_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0));
v___x_2364_ = l_String_toRawSubstring_x27(v___x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object* v_x_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
lean_inc(v_x_2384_);
v___x_2388_ = l_Lean_Syntax_isOfKind(v_x_2384_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_dec(v_x_2384_);
v___x_2389_ = lean_box(1);
v___x_2390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v_a_2386_);
return v___x_2390_;
}
else
{
lean_object* v_quotContext_2391_; lean_object* v_currMacroScope_2392_; lean_object* v_ref_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_quotContext_2391_ = lean_ctor_get(v_a_2385_, 1);
v_currMacroScope_2392_ = lean_ctor_get(v_a_2385_, 2);
v_ref_2393_ = lean_ctor_get(v_a_2385_, 5);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = l_Lean_Syntax_getArg(v_x_2384_, v___x_2394_);
v___x_2396_ = lean_unsigned_to_nat(2u);
v___x_2397_ = l_Lean_Syntax_getArg(v_x_2384_, v___x_2396_);
lean_dec(v_x_2384_);
v___x_2398_ = 0;
v___x_2399_ = l_Lean_SourceInfo_fromRef(v_ref_2393_, v___x_2398_);
v___x_2400_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_2401_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
v___x_2402_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2));
lean_inc(v_currMacroScope_2392_);
lean_inc(v_quotContext_2391_);
v___x_2403_ = l_Lean_addMacroScope(v_quotContext_2391_, v___x_2402_, v_currMacroScope_2392_);
v___x_2404_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8));
lean_inc_n(v___x_2399_, 2);
v___x_2405_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2399_);
lean_ctor_set(v___x_2405_, 1, v___x_2401_);
lean_ctor_set(v___x_2405_, 2, v___x_2403_);
lean_ctor_set(v___x_2405_, 3, v___x_2404_);
v___x_2406_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_2407_ = l_Lean_Syntax_node2(v___x_2399_, v___x_2406_, v___x_2395_, v___x_2397_);
v___x_2408_ = l_Lean_Syntax_node2(v___x_2399_, v___x_2400_, v___x_2405_, v___x_2407_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v_a_2386_);
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___boxed(lean_object* v_x_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(v_x_2410_, v_a_2411_, v_a_2412_);
lean_dec_ref(v_a_2411_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object* v_x_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_2414_);
v___x_2418_ = l_Lean_Syntax_isOfKind(v_x_2414_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
lean_dec(v_x_2414_);
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v_a_2416_);
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = l_Lean_Syntax_getArg(v_x_2414_, v___x_2421_);
v___x_2423_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_2422_);
v___x_2424_ = l_Lean_Syntax_isOfKind(v___x_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec(v___x_2422_);
lean_dec(v_x_2414_);
v___x_2425_ = lean_box(0);
v___x_2426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set(v___x_2426_, 1, v_a_2416_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2427_ = lean_unsigned_to_nat(1u);
v___x_2428_ = l_Lean_Syntax_getArg(v_x_2414_, v___x_2427_);
lean_dec(v_x_2414_);
v___x_2429_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2428_);
v___x_2430_ = l_Lean_Syntax_matchesNull(v___x_2428_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
lean_dec(v___x_2428_);
lean_dec(v___x_2422_);
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
lean_ctor_set(v___x_2432_, 1, v_a_2416_);
return v___x_2432_;
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_ref_2435_; uint8_t v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2433_ = l_Lean_Syntax_getArg(v___x_2428_, v___x_2421_);
v___x_2434_ = l_Lean_Syntax_getArg(v___x_2428_, v___x_2427_);
lean_dec(v___x_2428_);
v_ref_2435_ = l_Lean_replaceRef(v___x_2422_, v_a_2415_);
lean_dec(v___x_2422_);
v___x_2436_ = 0;
v___x_2437_ = l_Lean_SourceInfo_fromRef(v_ref_2435_, v___x_2436_);
lean_dec(v_ref_2435_);
v___x_2438_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
v___x_2439_ = ((lean_object*)(l_List_term___x7e___00__closed__2));
lean_inc(v___x_2437_);
v___x_2440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2437_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = l_Lean_Syntax_node3(v___x_2437_, v___x_2438_, v___x_2433_, v___x_2440_, v___x_2434_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v_a_2416_);
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object* v_x_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(v_x_2443_, v_a_2444_, v_a_2445_);
lean_dec(v_a_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm___redArg(lean_object* v_inst_2447_, lean_object* v_x_2448_, lean_object* v_x_2449_){
_start:
{
if (lean_obj_tag(v_x_2448_) == 0)
{
uint8_t v___x_2450_; 
lean_dec_ref(v_inst_2447_);
v___x_2450_ = l_List_isEmpty___redArg(v_x_2449_);
lean_dec(v_x_2449_);
return v___x_2450_;
}
else
{
lean_object* v_head_2451_; lean_object* v_tail_2452_; uint8_t v___x_2453_; 
v_head_2451_ = lean_ctor_get(v_x_2448_, 0);
lean_inc_n(v_head_2451_, 2);
v_tail_2452_ = lean_ctor_get(v_x_2448_, 1);
lean_inc(v_tail_2452_);
lean_dec_ref_known(v_x_2448_, 2);
lean_inc(v_x_2449_);
lean_inc_ref(v_inst_2447_);
v___x_2453_ = l_List_elem___redArg(v_inst_2447_, v_head_2451_, v_x_2449_);
if (v___x_2453_ == 0)
{
lean_dec(v_tail_2452_);
lean_dec(v_head_2451_);
lean_dec(v_x_2449_);
lean_dec_ref(v_inst_2447_);
return v___x_2453_;
}
else
{
lean_object* v___x_2454_; 
lean_inc_ref(v_inst_2447_);
v___x_2454_ = l_List_erase___redArg(v_inst_2447_, v_x_2449_, v_head_2451_);
v_x_2448_ = v_tail_2452_;
v_x_2449_ = v___x_2454_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPerm___redArg___boxed(lean_object* v_inst_2456_, lean_object* v_x_2457_, lean_object* v_x_2458_){
_start:
{
uint8_t v_res_2459_; lean_object* v_r_2460_; 
v_res_2459_ = l_List_isPerm___redArg(v_inst_2456_, v_x_2457_, v_x_2458_);
v_r_2460_ = lean_box(v_res_2459_);
return v_r_2460_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm(lean_object* v_00_u03b1_2461_, lean_object* v_inst_2462_, lean_object* v_x_2463_, lean_object* v_x_2464_){
_start:
{
uint8_t v___x_2465_; 
v___x_2465_ = l_List_isPerm___redArg(v_inst_2462_, v_x_2463_, v_x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_List_isPerm___boxed(lean_object* v_00_u03b1_2466_, lean_object* v_inst_2467_, lean_object* v_x_2468_, lean_object* v_x_2469_){
_start:
{
uint8_t v_res_2470_; lean_object* v_r_2471_; 
v_res_2470_ = l_List_isPerm(v_00_u03b1_2466_, v_inst_2467_, v_x_2468_, v_x_2469_);
v_r_2471_ = lean_box(v_res_2470_);
return v_r_2471_;
}
}
LEAN_EXPORT uint8_t l_List_any___redArg(lean_object* v_x_2472_, lean_object* v_x_2473_){
_start:
{
if (lean_obj_tag(v_x_2472_) == 0)
{
uint8_t v___x_2474_; 
lean_dec_ref(v_x_2473_);
v___x_2474_ = 0;
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
v_x_2472_ = v_tail_2476_;
goto _start;
}
else
{
uint8_t v___x_2480_; 
lean_dec(v_tail_2476_);
lean_dec_ref(v_x_2473_);
v___x_2480_ = lean_unbox(v___x_2477_);
return v___x_2480_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___redArg___boxed(lean_object* v_x_2481_, lean_object* v_x_2482_){
_start:
{
uint8_t v_res_2483_; lean_object* v_r_2484_; 
v_res_2483_ = l_List_any___redArg(v_x_2481_, v_x_2482_);
v_r_2484_ = lean_box(v_res_2483_);
return v_r_2484_;
}
}
LEAN_EXPORT uint8_t l_List_any(lean_object* v_00_u03b1_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_){
_start:
{
uint8_t v___x_2488_; 
v___x_2488_ = l_List_any___redArg(v_x_2486_, v_x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_List_any___boxed(lean_object* v_00_u03b1_2489_, lean_object* v_x_2490_, lean_object* v_x_2491_){
_start:
{
uint8_t v_res_2492_; lean_object* v_r_2493_; 
v_res_2492_ = l_List_any(v_00_u03b1_2489_, v_x_2490_, v_x_2491_);
v_r_2493_ = lean_box(v_res_2492_);
return v_r_2493_;
}
}
LEAN_EXPORT uint8_t l_List_all___redArg(lean_object* v_x_2494_, lean_object* v_x_2495_){
_start:
{
if (lean_obj_tag(v_x_2494_) == 0)
{
uint8_t v___x_2496_; 
lean_dec_ref(v_x_2495_);
v___x_2496_ = 1;
return v___x_2496_;
}
else
{
lean_object* v_head_2497_; lean_object* v_tail_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v_head_2497_ = lean_ctor_get(v_x_2494_, 0);
lean_inc(v_head_2497_);
v_tail_2498_ = lean_ctor_get(v_x_2494_, 1);
lean_inc(v_tail_2498_);
lean_dec_ref_known(v_x_2494_, 2);
lean_inc_ref(v_x_2495_);
v___x_2499_ = lean_apply_1(v_x_2495_, v_head_2497_);
v___x_2500_ = lean_unbox(v___x_2499_);
if (v___x_2500_ == 0)
{
uint8_t v___x_2501_; 
lean_dec(v_tail_2498_);
lean_dec_ref(v_x_2495_);
v___x_2501_ = lean_unbox(v___x_2499_);
return v___x_2501_;
}
else
{
v_x_2494_ = v_tail_2498_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___redArg___boxed(lean_object* v_x_2503_, lean_object* v_x_2504_){
_start:
{
uint8_t v_res_2505_; lean_object* v_r_2506_; 
v_res_2505_ = l_List_all___redArg(v_x_2503_, v_x_2504_);
v_r_2506_ = lean_box(v_res_2505_);
return v_r_2506_;
}
}
LEAN_EXPORT uint8_t l_List_all(lean_object* v_00_u03b1_2507_, lean_object* v_x_2508_, lean_object* v_x_2509_){
_start:
{
uint8_t v___x_2510_; 
v___x_2510_ = l_List_all___redArg(v_x_2508_, v_x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_List_all___boxed(lean_object* v_00_u03b1_2511_, lean_object* v_x_2512_, lean_object* v_x_2513_){
_start:
{
uint8_t v_res_2514_; lean_object* v_r_2515_; 
v_res_2514_ = l_List_all(v_00_u03b1_2511_, v_x_2512_, v_x_2513_);
v_r_2515_ = lean_box(v_res_2514_);
return v_r_2515_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_or_spec__0(lean_object* v_x_2516_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
uint8_t v___x_2517_; 
v___x_2517_ = 0;
return v___x_2517_;
}
else
{
lean_object* v_head_2518_; uint8_t v___x_2519_; 
v_head_2518_ = lean_ctor_get(v_x_2516_, 0);
v___x_2519_ = lean_unbox(v_head_2518_);
if (v___x_2519_ == 0)
{
lean_object* v_tail_2520_; 
v_tail_2520_ = lean_ctor_get(v_x_2516_, 1);
v_x_2516_ = v_tail_2520_;
goto _start;
}
else
{
uint8_t v___x_2522_; 
v___x_2522_ = lean_unbox(v_head_2518_);
return v___x_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_or_spec__0___boxed(lean_object* v_x_2523_){
_start:
{
uint8_t v_res_2524_; lean_object* v_r_2525_; 
v_res_2524_ = l_List_any___at___00List_or_spec__0(v_x_2523_);
lean_dec(v_x_2523_);
v_r_2525_ = lean_box(v_res_2524_);
return v_r_2525_;
}
}
LEAN_EXPORT uint8_t l_List_or(lean_object* v_bs_2526_){
_start:
{
uint8_t v___x_2527_; 
v___x_2527_ = l_List_any___at___00List_or_spec__0(v_bs_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object* v_bs_2528_){
_start:
{
uint8_t v_res_2529_; lean_object* v_r_2530_; 
v_res_2529_ = l_List_or(v_bs_2528_);
lean_dec(v_bs_2528_);
v_r_2530_ = lean_box(v_res_2529_);
return v_r_2530_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00List_and_spec__0(lean_object* v_x_2531_){
_start:
{
if (lean_obj_tag(v_x_2531_) == 0)
{
uint8_t v___x_2532_; 
v___x_2532_ = 1;
return v___x_2532_;
}
else
{
lean_object* v_head_2533_; uint8_t v___x_2534_; 
v_head_2533_ = lean_ctor_get(v_x_2531_, 0);
v___x_2534_ = lean_unbox(v_head_2533_);
if (v___x_2534_ == 0)
{
uint8_t v___x_2535_; 
v___x_2535_ = lean_unbox(v_head_2533_);
return v___x_2535_;
}
else
{
lean_object* v_tail_2536_; 
v_tail_2536_ = lean_ctor_get(v_x_2531_, 1);
v_x_2531_ = v_tail_2536_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00List_and_spec__0___boxed(lean_object* v_x_2538_){
_start:
{
uint8_t v_res_2539_; lean_object* v_r_2540_; 
v_res_2539_ = l_List_all___at___00List_and_spec__0(v_x_2538_);
lean_dec(v_x_2538_);
v_r_2540_ = lean_box(v_res_2539_);
return v_r_2540_;
}
}
LEAN_EXPORT uint8_t l_List_and(lean_object* v_bs_2541_){
_start:
{
uint8_t v___x_2542_; 
v___x_2542_ = l_List_all___at___00List_and_spec__0(v_bs_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object* v_bs_2543_){
_start:
{
uint8_t v_res_2544_; lean_object* v_r_2545_; 
v_res_2544_ = l_List_and(v_bs_2543_);
lean_dec(v_bs_2543_);
v_r_2545_ = lean_box(v_res_2544_);
return v_r_2545_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___redArg(lean_object* v_f_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_){
_start:
{
if (lean_obj_tag(v_x_2547_) == 0)
{
lean_object* v___x_2549_; 
lean_dec(v_x_2548_);
lean_dec(v_f_2546_);
v___x_2549_ = lean_box(0);
return v___x_2549_;
}
else
{
if (lean_obj_tag(v_x_2548_) == 0)
{
lean_object* v___x_2550_; 
lean_dec_ref_known(v_x_2547_, 2);
lean_dec(v_f_2546_);
v___x_2550_ = lean_box(0);
return v___x_2550_;
}
else
{
lean_object* v_head_2551_; lean_object* v_tail_2552_; lean_object* v_head_2553_; lean_object* v_tail_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2563_; 
v_head_2551_ = lean_ctor_get(v_x_2547_, 0);
lean_inc(v_head_2551_);
v_tail_2552_ = lean_ctor_get(v_x_2547_, 1);
lean_inc(v_tail_2552_);
lean_dec_ref_known(v_x_2547_, 2);
v_head_2553_ = lean_ctor_get(v_x_2548_, 0);
v_tail_2554_ = lean_ctor_get(v_x_2548_, 1);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_x_2548_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2556_ = v_x_2548_;
v_isShared_2557_ = v_isSharedCheck_2563_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_tail_2554_);
lean_inc(v_head_2553_);
lean_dec(v_x_2548_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2563_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
lean_inc(v_f_2546_);
v___x_2558_ = lean_apply_2(v_f_2546_, v_head_2551_, v_head_2553_);
v___x_2559_ = l_List_zipWith___redArg(v_f_2546_, v_tail_2552_, v_tail_2554_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 1, v___x_2559_);
lean_ctor_set(v___x_2556_, 0, v___x_2558_);
v___x_2561_ = v___x_2556_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith(lean_object* v_00_u03b1_2564_, lean_object* v_00_u03b2_2565_, lean_object* v_00_u03b3_2566_, lean_object* v_f_2567_, lean_object* v_x_2568_, lean_object* v_x_2569_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_List_zipWith___redArg(v_f_2567_, v_x_2568_, v_x_2569_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object* v_x_2571_, lean_object* v_x_2572_, lean_object* v_h__1_2573_, lean_object* v_h__2_2574_){
_start:
{
if (lean_obj_tag(v_x_2571_) == 0)
{
lean_object* v___x_2575_; 
lean_dec(v_h__1_2573_);
v___x_2575_ = lean_apply_3(v_h__2_2574_, v_x_2571_, v_x_2572_, lean_box(0));
return v___x_2575_;
}
else
{
if (lean_obj_tag(v_x_2572_) == 0)
{
lean_object* v___x_2576_; 
lean_dec(v_h__1_2573_);
v___x_2576_ = lean_apply_3(v_h__2_2574_, v_x_2571_, v_x_2572_, lean_box(0));
return v___x_2576_;
}
else
{
lean_object* v_head_2577_; lean_object* v_tail_2578_; lean_object* v_head_2579_; lean_object* v_tail_2580_; lean_object* v___x_2581_; 
lean_dec(v_h__2_2574_);
v_head_2577_ = lean_ctor_get(v_x_2571_, 0);
lean_inc(v_head_2577_);
v_tail_2578_ = lean_ctor_get(v_x_2571_, 1);
lean_inc(v_tail_2578_);
lean_dec_ref_known(v_x_2571_, 2);
v_head_2579_ = lean_ctor_get(v_x_2572_, 0);
lean_inc(v_head_2579_);
v_tail_2580_ = lean_ctor_get(v_x_2572_, 1);
lean_inc(v_tail_2580_);
lean_dec_ref_known(v_x_2572_, 2);
v___x_2581_ = lean_apply_4(v_h__1_2573_, v_head_2577_, v_tail_2578_, v_head_2579_, v_tail_2580_);
return v___x_2581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object* v_00_u03b1_2582_, lean_object* v_00_u03b2_2583_, lean_object* v_motive_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_, lean_object* v_h__1_2587_, lean_object* v_h__2_2588_){
_start:
{
if (lean_obj_tag(v_x_2585_) == 0)
{
lean_object* v___x_2589_; 
lean_dec(v_h__1_2587_);
v___x_2589_ = lean_apply_3(v_h__2_2588_, v_x_2585_, v_x_2586_, lean_box(0));
return v___x_2589_;
}
else
{
if (lean_obj_tag(v_x_2586_) == 0)
{
lean_object* v___x_2590_; 
lean_dec(v_h__1_2587_);
v___x_2590_ = lean_apply_3(v_h__2_2588_, v_x_2585_, v_x_2586_, lean_box(0));
return v___x_2590_;
}
else
{
lean_object* v_head_2591_; lean_object* v_tail_2592_; lean_object* v_head_2593_; lean_object* v_tail_2594_; lean_object* v___x_2595_; 
lean_dec(v_h__2_2588_);
v_head_2591_ = lean_ctor_get(v_x_2585_, 0);
lean_inc(v_head_2591_);
v_tail_2592_ = lean_ctor_get(v_x_2585_, 1);
lean_inc(v_tail_2592_);
lean_dec_ref_known(v_x_2585_, 2);
v_head_2593_ = lean_ctor_get(v_x_2586_, 0);
lean_inc(v_head_2593_);
v_tail_2594_ = lean_ctor_get(v_x_2586_, 1);
lean_inc(v_tail_2594_);
lean_dec_ref_known(v_x_2586_, 2);
v___x_2595_ = lean_apply_4(v_h__1_2587_, v_head_2591_, v_tail_2592_, v_head_2593_, v_tail_2594_);
return v___x_2595_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object* v_x_2596_, lean_object* v_x_2597_){
_start:
{
if (lean_obj_tag(v_x_2596_) == 0)
{
lean_object* v___x_2598_; 
lean_dec(v_x_2597_);
v___x_2598_ = lean_box(0);
return v___x_2598_;
}
else
{
if (lean_obj_tag(v_x_2597_) == 0)
{
lean_object* v___x_2599_; 
lean_dec_ref_known(v_x_2596_, 2);
v___x_2599_ = lean_box(0);
return v___x_2599_;
}
else
{
lean_object* v_head_2600_; lean_object* v_tail_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2618_; 
v_head_2600_ = lean_ctor_get(v_x_2596_, 0);
v_tail_2601_ = lean_ctor_get(v_x_2596_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_x_2596_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2603_ = v_x_2596_;
v_isShared_2604_ = v_isSharedCheck_2618_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_tail_2601_);
lean_inc(v_head_2600_);
lean_dec(v_x_2596_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2618_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v_head_2605_; lean_object* v_tail_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2617_; 
v_head_2605_ = lean_ctor_get(v_x_2597_, 0);
v_tail_2606_ = lean_ctor_get(v_x_2597_, 1);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_x_2597_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2608_ = v_x_2597_;
v_isShared_2609_ = v_isSharedCheck_2617_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_tail_2606_);
lean_inc(v_head_2605_);
lean_dec(v_x_2597_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2617_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 0);
lean_ctor_set(v___x_2603_, 1, v_head_2605_);
v___x_2611_ = v___x_2603_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_head_2600_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_head_2605_);
v___x_2611_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_tail_2601_, v_tail_2606_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 1, v___x_2612_);
lean_ctor_set(v___x_2608_, 0, v___x_2611_);
v___x_2614_ = v___x_2608_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zip___redArg(lean_object* v_xs_2619_, lean_object* v_ys_2620_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2619_, v_ys_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_List_zip(lean_object* v_00_u03b1_2622_, lean_object* v_00_u03b2_2623_, lean_object* v_xs_2624_, lean_object* v_ys_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2624_, v_ys_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object* v_00_u03b1_2627_, lean_object* v_00_u03b2_2628_, lean_object* v_x_2629_, lean_object* v_x_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_x_2629_, v_x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__0(lean_object* v_f_2632_, lean_object* v_b_2633_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_box(0);
v___x_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2635_, 0, v_b_2633_);
v___x_2636_ = lean_apply_2(v_f_2632_, v___x_2634_, v___x_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__1(lean_object* v_f_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2639_, 0, v_a_2638_);
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_apply_2(v_f_2637_, v___x_2639_, v___x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object* v_f_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_){
_start:
{
if (lean_obj_tag(v_x_2643_) == 0)
{
lean_object* v___f_2645_; lean_object* v___x_2646_; 
v___f_2645_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2645_, 0, v_f_2642_);
v___x_2646_ = l_List_map___redArg(v___f_2645_, v_x_2644_);
return v___x_2646_;
}
else
{
if (lean_obj_tag(v_x_2644_) == 0)
{
lean_object* v___f_2647_; lean_object* v___x_2648_; 
v___f_2647_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2647_, 0, v_f_2642_);
v___x_2648_ = l_List_map___redArg(v___f_2647_, v_x_2643_);
return v___x_2648_;
}
else
{
lean_object* v_head_2649_; lean_object* v_tail_2650_; lean_object* v_head_2651_; lean_object* v_tail_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2663_; 
v_head_2649_ = lean_ctor_get(v_x_2643_, 0);
lean_inc(v_head_2649_);
v_tail_2650_ = lean_ctor_get(v_x_2643_, 1);
lean_inc(v_tail_2650_);
lean_dec_ref_known(v_x_2643_, 2);
v_head_2651_ = lean_ctor_get(v_x_2644_, 0);
v_tail_2652_ = lean_ctor_get(v_x_2644_, 1);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2654_ = v_x_2644_;
v_isShared_2655_ = v_isSharedCheck_2663_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_tail_2652_);
lean_inc(v_head_2651_);
lean_dec(v_x_2644_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2663_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_head_2649_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_head_2651_);
lean_inc(v_f_2642_);
v___x_2658_ = lean_apply_2(v_f_2642_, v___x_2656_, v___x_2657_);
v___x_2659_ = l_List_zipWithAll___redArg(v_f_2642_, v_tail_2650_, v_tail_2652_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 1, v___x_2659_);
lean_ctor_set(v___x_2654_, 0, v___x_2658_);
v___x_2661_ = v___x_2654_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object* v_00_u03b1_2664_, lean_object* v_00_u03b2_2665_, lean_object* v_00_u03b3_2666_, lean_object* v_f_2667_, lean_object* v_x_2668_, lean_object* v_x_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_List_zipWithAll___redArg(v_f_2667_, v_x_2668_, v_x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_List_unzip___redArg(lean_object* v_x_2671_){
_start:
{
if (lean_obj_tag(v_x_2671_) == 0)
{
lean_object* v___x_2672_; 
v___x_2672_ = ((lean_object*)(l_List_partition___redArg___closed__0));
return v___x_2672_;
}
else
{
lean_object* v_head_2673_; lean_object* v_tail_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2700_; 
v_head_2673_ = lean_ctor_get(v_x_2671_, 0);
v_tail_2674_ = lean_ctor_get(v_x_2671_, 1);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_x_2671_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2676_ = v_x_2671_;
v_isShared_2677_ = v_isSharedCheck_2700_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_tail_2674_);
lean_inc(v_head_2673_);
lean_dec(v_x_2671_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2700_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v_fst_2678_; lean_object* v_snd_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2699_; 
v_fst_2678_ = lean_ctor_get(v_head_2673_, 0);
v_snd_2679_ = lean_ctor_get(v_head_2673_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_head_2673_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2681_ = v_head_2673_;
v_isShared_2682_ = v_isSharedCheck_2699_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_snd_2679_);
lean_inc(v_fst_2678_);
lean_dec(v_head_2673_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2699_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v_fst_2684_; lean_object* v_snd_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2698_; 
v___x_2683_ = l_List_unzip___redArg(v_tail_2674_);
v_fst_2684_ = lean_ctor_get(v___x_2683_, 0);
v_snd_2685_ = lean_ctor_get(v___x_2683_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2687_ = v___x_2683_;
v_isShared_2688_ = v_isSharedCheck_2698_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_snd_2685_);
lean_inc(v_fst_2684_);
lean_dec(v___x_2683_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2698_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 1, v_fst_2684_);
lean_ctor_set(v___x_2676_, 0, v_fst_2678_);
v___x_2690_ = v___x_2676_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_fst_2678_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_fst_2684_);
v___x_2690_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2692_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set_tag(v___x_2681_, 1);
lean_ctor_set(v___x_2681_, 1, v_snd_2685_);
lean_ctor_set(v___x_2681_, 0, v_snd_2679_);
v___x_2692_ = v___x_2681_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_snd_2679_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_snd_2685_);
v___x_2692_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2694_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v___x_2692_);
lean_ctor_set(v___x_2687_, 0, v___x_2690_);
v___x_2694_ = v___x_2687_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_unzip(lean_object* v_00_u03b1_2701_, lean_object* v_00_u03b2_2702_, lean_object* v_x_2703_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_List_unzip___redArg(v_x_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___lam__0(lean_object* v_inst_2705_, lean_object* v_x1_2706_, lean_object* v_x2_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_apply_2(v_inst_2705_, v_x1_2706_, v_x2_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg(lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_l_2711_){
_start:
{
lean_object* v___f_2712_; lean_object* v___x_2713_; 
v___f_2712_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2712_, 0, v_inst_2709_);
v___x_2713_ = l_List_foldr___redArg(v___f_2712_, v_inst_2710_, v_l_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___boxed(lean_object* v_inst_2714_, lean_object* v_inst_2715_, lean_object* v_l_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_List_sum___redArg(v_inst_2714_, v_inst_2715_, v_l_2716_);
lean_dec(v_inst_2715_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_List_sum(lean_object* v_00_u03b1_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_l_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_List_sum___redArg(v_inst_2719_, v_inst_2720_, v_l_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_List_sum___boxed(lean_object* v_00_u03b1_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_l_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_List_sum(v_00_u03b1_2723_, v_inst_2724_, v_inst_2725_, v_l_2726_);
lean_dec(v_inst_2725_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg(lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v_l_2730_){
_start:
{
lean_object* v___f_2731_; lean_object* v___x_2732_; 
v___f_2731_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2731_, 0, v_inst_2728_);
v___x_2732_ = l_List_foldr___redArg(v___f_2731_, v_inst_2729_, v_l_2730_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg___boxed(lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_l_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_List_prod___redArg(v_inst_2733_, v_inst_2734_, v_l_2735_);
lean_dec(v_inst_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_List_prod(lean_object* v_00_u03b1_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_l_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_List_prod___redArg(v_inst_2738_, v_inst_2739_, v_l_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_List_prod___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_l_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_List_prod(v_00_u03b1_2742_, v_inst_2743_, v_inst_2744_, v_l_2745_);
lean_dec(v_inst_2744_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_List_range_loop(lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_zero_2749_; uint8_t v_isZero_2750_; 
v_zero_2749_ = lean_unsigned_to_nat(0u);
v_isZero_2750_ = lean_nat_dec_eq(v_a_2747_, v_zero_2749_);
if (v_isZero_2750_ == 1)
{
lean_dec(v_a_2747_);
return v_a_2748_;
}
else
{
lean_object* v_one_2751_; lean_object* v_n_2752_; lean_object* v___x_2753_; 
v_one_2751_ = lean_unsigned_to_nat(1u);
v_n_2752_ = lean_nat_sub(v_a_2747_, v_one_2751_);
lean_dec(v_a_2747_);
lean_inc(v_n_2752_);
v___x_2753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2753_, 0, v_n_2752_);
lean_ctor_set(v___x_2753_, 1, v_a_2748_);
v_a_2747_ = v_n_2752_;
v_a_2748_ = v___x_2753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range(lean_object* v_n_2755_){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = lean_box(0);
v___x_2757_ = l_List_range_loop(v_n_2755_, v___x_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27(lean_object* v_x_2758_, lean_object* v_x_2759_, lean_object* v_x_2760_){
_start:
{
lean_object* v_zero_2761_; uint8_t v_isZero_2762_; 
v_zero_2761_ = lean_unsigned_to_nat(0u);
v_isZero_2762_ = lean_nat_dec_eq(v_x_2759_, v_zero_2761_);
if (v_isZero_2762_ == 1)
{
lean_object* v___x_2763_; 
lean_dec(v_x_2758_);
v___x_2763_ = lean_box(0);
return v___x_2763_;
}
else
{
lean_object* v_one_2764_; lean_object* v_n_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_one_2764_ = lean_unsigned_to_nat(1u);
v_n_2765_ = lean_nat_sub(v_x_2759_, v_one_2764_);
v___x_2766_ = lean_nat_add(v_x_2758_, v_x_2760_);
v___x_2767_ = l_List_range_x27(v___x_2766_, v_n_2765_, v_x_2760_);
lean_dec(v_n_2765_);
v___x_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_x_2758_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
return v___x_2768_;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object* v_x_2769_, lean_object* v_x_2770_, lean_object* v_x_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_List_range_x27(v_x_2769_, v_x_2770_, v_x_2771_);
lean_dec(v_x_2771_);
lean_dec(v_x_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdx___redArg(lean_object* v_x_2773_, lean_object* v_x_2774_){
_start:
{
if (lean_obj_tag(v_x_2773_) == 0)
{
lean_object* v___x_2775_; 
lean_dec(v_x_2774_);
v___x_2775_ = lean_box(0);
return v___x_2775_;
}
else
{
lean_object* v_head_2776_; lean_object* v_tail_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2788_; 
v_head_2776_ = lean_ctor_get(v_x_2773_, 0);
v_tail_2777_ = lean_ctor_get(v_x_2773_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_x_2773_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2779_ = v_x_2773_;
v_isShared_2780_ = v_isSharedCheck_2788_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_tail_2777_);
lean_inc(v_head_2776_);
lean_dec(v_x_2773_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2788_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
lean_inc(v_x_2774_);
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v_head_2776_);
lean_ctor_set(v___x_2781_, 1, v_x_2774_);
v___x_2782_ = lean_unsigned_to_nat(1u);
v___x_2783_ = lean_nat_add(v_x_2774_, v___x_2782_);
lean_dec(v_x_2774_);
v___x_2784_ = l_List_zipIdx___redArg(v_tail_2777_, v___x_2783_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 1, v___x_2784_);
lean_ctor_set(v___x_2779_, 0, v___x_2781_);
v___x_2786_ = v___x_2779_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdx(lean_object* v_00_u03b1_2789_, lean_object* v_x_2790_, lean_object* v_x_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_List_zipIdx___redArg(v_x_2790_, v_x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object* v_inst_2793_, lean_object* v_x_2794_){
_start:
{
if (lean_obj_tag(v_x_2794_) == 0)
{
lean_object* v___x_2795_; 
lean_dec(v_inst_2793_);
v___x_2795_ = lean_box(0);
return v___x_2795_;
}
else
{
lean_object* v_head_2796_; lean_object* v_tail_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_head_2796_ = lean_ctor_get(v_x_2794_, 0);
lean_inc(v_head_2796_);
v_tail_2797_ = lean_ctor_get(v_x_2794_, 1);
lean_inc(v_tail_2797_);
lean_dec_ref_known(v_x_2794_, 2);
v___x_2798_ = l_List_foldl___redArg(v_inst_2793_, v_head_2796_, v_tail_2797_);
v___x_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
return v___x_2799_;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object* v_00_u03b1_2800_, lean_object* v_inst_2801_, lean_object* v_x_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_List_min_x3f___redArg(v_inst_2801_, v_x_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object* v_inst_2804_, lean_object* v_x_2805_){
_start:
{
lean_object* v_head_2806_; lean_object* v_tail_2807_; lean_object* v___x_2808_; 
v_head_2806_ = lean_ctor_get(v_x_2805_, 0);
lean_inc(v_head_2806_);
v_tail_2807_ = lean_ctor_get(v_x_2805_, 1);
lean_inc(v_tail_2807_);
lean_dec(v_x_2805_);
v___x_2808_ = l_List_foldl___redArg(v_inst_2804_, v_head_2806_, v_tail_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_List_min(lean_object* v_00_u03b1_2809_, lean_object* v_inst_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_List_min___redArg(v_inst_2810_, v_x_2811_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object* v_inst_2814_, lean_object* v_x_2815_){
_start:
{
if (lean_obj_tag(v_x_2815_) == 0)
{
lean_object* v___x_2816_; 
lean_dec(v_inst_2814_);
v___x_2816_ = lean_box(0);
return v___x_2816_;
}
else
{
lean_object* v_head_2817_; lean_object* v_tail_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_head_2817_ = lean_ctor_get(v_x_2815_, 0);
lean_inc(v_head_2817_);
v_tail_2818_ = lean_ctor_get(v_x_2815_, 1);
lean_inc(v_tail_2818_);
lean_dec_ref_known(v_x_2815_, 2);
v___x_2819_ = l_List_foldl___redArg(v_inst_2814_, v_head_2817_, v_tail_2818_);
v___x_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
return v___x_2820_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object* v_00_u03b1_2821_, lean_object* v_inst_2822_, lean_object* v_x_2823_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_List_max_x3f___redArg(v_inst_2822_, v_x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object* v_inst_2825_, lean_object* v_x_2826_){
_start:
{
lean_object* v_head_2827_; lean_object* v_tail_2828_; lean_object* v___x_2829_; 
v_head_2827_ = lean_ctor_get(v_x_2826_, 0);
lean_inc(v_head_2827_);
v_tail_2828_ = lean_ctor_get(v_x_2826_, 1);
lean_inc(v_tail_2828_);
lean_dec(v_x_2826_);
v___x_2829_ = l_List_foldl___redArg(v_inst_2825_, v_head_2827_, v_tail_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_List_max(lean_object* v_00_u03b1_2830_, lean_object* v_inst_2831_, lean_object* v_x_2832_, lean_object* v_x_2833_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_List_max___redArg(v_inst_2831_, v_x_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_List_intersperse___redArg(lean_object* v_sep_2835_, lean_object* v_x_2836_){
_start:
{
if (lean_obj_tag(v_x_2836_) == 0)
{
lean_dec(v_sep_2835_);
return v_x_2836_;
}
else
{
lean_object* v_tail_2837_; 
v_tail_2837_ = lean_ctor_get(v_x_2836_, 1);
if (lean_obj_tag(v_tail_2837_) == 0)
{
lean_dec(v_sep_2835_);
return v_x_2836_;
}
else
{
lean_object* v_head_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2847_; 
lean_inc_ref(v_tail_2837_);
v_head_2838_ = lean_ctor_get(v_x_2836_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_x_2836_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v_x_2836_, 1);
lean_dec(v_unused_2848_);
v___x_2840_ = v_x_2836_;
v_isShared_2841_ = v_isSharedCheck_2847_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_head_2838_);
lean_dec(v_x_2836_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2847_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
lean_inc(v_sep_2835_);
v___x_2842_ = l_List_intersperse___redArg(v_sep_2835_, v_tail_2837_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 1, v___x_2842_);
lean_ctor_set(v___x_2840_, 0, v_sep_2835_);
v___x_2844_ = v___x_2840_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_sep_2835_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2845_, 0, v_head_2838_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
return v___x_2845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperse(lean_object* v_00_u03b1_2849_, lean_object* v_sep_2850_, lean_object* v_x_2851_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_List_intersperse___redArg(v_sep_2850_, v_x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(lean_object* v___x_2853_, lean_object* v_x_2854_){
_start:
{
if (lean_obj_tag(v_x_2854_) == 0)
{
uint8_t v___x_2855_; 
lean_dec_ref(v___x_2853_);
v___x_2855_ = 0;
return v___x_2855_;
}
else
{
lean_object* v_head_2856_; lean_object* v_tail_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_head_2856_ = lean_ctor_get(v_x_2854_, 0);
lean_inc(v_head_2856_);
v_tail_2857_ = lean_ctor_get(v_x_2854_, 1);
lean_inc(v_tail_2857_);
lean_dec_ref_known(v_x_2854_, 2);
lean_inc_ref(v___x_2853_);
v___x_2858_ = lean_apply_1(v___x_2853_, v_head_2856_);
v___x_2859_ = lean_unbox(v___x_2858_);
if (v___x_2859_ == 0)
{
v_x_2854_ = v_tail_2857_;
goto _start;
}
else
{
uint8_t v___x_2861_; 
lean_dec(v_tail_2857_);
lean_dec_ref(v___x_2853_);
v___x_2861_ = lean_unbox(v___x_2858_);
return v___x_2861_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg___boxed(lean_object* v___x_2862_, lean_object* v_x_2863_){
_start:
{
uint8_t v_res_2864_; lean_object* v_r_2865_; 
v_res_2864_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2862_, v_x_2863_);
v_r_2865_ = lean_box(v_res_2864_);
return v_r_2865_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object* v_r_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
if (lean_obj_tag(v_a_2867_) == 0)
{
lean_object* v___x_2869_; 
lean_dec_ref(v_r_2866_);
v___x_2869_ = l_List_reverse___redArg(v_a_2868_);
return v___x_2869_;
}
else
{
lean_object* v_head_2870_; lean_object* v_tail_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2882_; 
v_head_2870_ = lean_ctor_get(v_a_2867_, 0);
v_tail_2871_ = lean_ctor_get(v_a_2867_, 1);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_a_2867_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2873_ = v_a_2867_;
v_isShared_2874_ = v_isSharedCheck_2882_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_tail_2871_);
lean_inc(v_head_2870_);
lean_dec(v_a_2867_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2882_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; uint8_t v___x_2876_; 
lean_inc_ref(v_r_2866_);
lean_inc(v_head_2870_);
v___x_2875_ = lean_apply_1(v_r_2866_, v_head_2870_);
lean_inc(v_a_2868_);
v___x_2876_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2875_, v_a_2868_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2878_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 1, v_a_2868_);
v___x_2878_ = v___x_2873_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_head_2870_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_a_2868_);
v___x_2878_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
v_a_2867_ = v_tail_2871_;
v_a_2868_ = v___x_2878_;
goto _start;
}
}
else
{
lean_del_object(v___x_2873_);
lean_dec(v_head_2870_);
v_a_2867_ = v_tail_2871_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object* v_00_u03b1_2883_, lean_object* v_r_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_List_eraseDupsBy_loop___redArg(v_r_2884_, v_a_2885_, v_a_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0(lean_object* v_00_u03b1_2888_, lean_object* v___x_2889_, lean_object* v_x_2890_){
_start:
{
uint8_t v___x_2891_; 
v___x_2891_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2889_, v_x_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___boxed(lean_object* v_00_u03b1_2892_, lean_object* v___x_2893_, lean_object* v_x_2894_){
_start:
{
uint8_t v_res_2895_; lean_object* v_r_2896_; 
v_res_2895_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0(v_00_u03b1_2892_, v___x_2893_, v_x_2894_);
v_r_2896_ = lean_box(v_res_2895_);
return v_r_2896_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy___redArg(lean_object* v_r_2897_, lean_object* v_as_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_box(0);
v___x_2900_ = l_List_eraseDupsBy_loop___redArg(v_r_2897_, v_as_2898_, v___x_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy(lean_object* v_00_u03b1_2901_, lean_object* v_r_2902_, lean_object* v_as_2903_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_List_eraseDupsBy___redArg(v_r_2902_, v_as_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT uint8_t l_List_eraseDups___redArg___lam__0(lean_object* v_inst_2905_, lean_object* v_x1_2906_, lean_object* v_x2_2907_){
_start:
{
lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = lean_apply_2(v_inst_2905_, v_x1_2906_, v_x2_2907_);
v___x_2909_ = lean_unbox(v___x_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg___lam__0___boxed(lean_object* v_inst_2910_, lean_object* v_x1_2911_, lean_object* v_x2_2912_){
_start:
{
uint8_t v_res_2913_; lean_object* v_r_2914_; 
v_res_2913_ = l_List_eraseDups___redArg___lam__0(v_inst_2910_, v_x1_2911_, v_x2_2912_);
v_r_2914_ = lean_box(v_res_2913_);
return v_r_2914_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg(lean_object* v_inst_2915_, lean_object* v_as_2916_){
_start:
{
lean_object* v___f_2917_; lean_object* v___x_2918_; 
v___f_2917_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2917_, 0, v_inst_2915_);
v___x_2918_ = l_List_eraseDupsBy___redArg(v___f_2917_, v_as_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object* v_00_u03b1_2919_, lean_object* v_inst_2920_, lean_object* v_as_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_List_eraseDups___redArg(v_inst_2920_, v_as_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop___redArg(lean_object* v_r_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
if (lean_obj_tag(v_a_2925_) == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_dec_ref(v_r_2923_);
v___x_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2927_, 0, v_a_2924_);
lean_ctor_set(v___x_2927_, 1, v_a_2926_);
v___x_2928_ = l_List_reverse___redArg(v___x_2927_);
return v___x_2928_;
}
else
{
lean_object* v_head_2929_; lean_object* v_tail_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2941_; 
v_head_2929_ = lean_ctor_get(v_a_2925_, 0);
v_tail_2930_ = lean_ctor_get(v_a_2925_, 1);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_a_2925_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2932_ = v_a_2925_;
v_isShared_2933_ = v_isSharedCheck_2941_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_tail_2930_);
lean_inc(v_head_2929_);
lean_dec(v_a_2925_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2941_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; uint8_t v___x_2935_; 
lean_inc_ref(v_r_2923_);
lean_inc(v_head_2929_);
lean_inc(v_a_2924_);
v___x_2934_ = lean_apply_2(v_r_2923_, v_a_2924_, v_head_2929_);
v___x_2935_ = lean_unbox(v___x_2934_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2937_; 
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 1, v_a_2926_);
lean_ctor_set(v___x_2932_, 0, v_a_2924_);
v___x_2937_ = v___x_2932_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2924_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_a_2926_);
v___x_2937_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
v_a_2924_ = v_head_2929_;
v_a_2925_ = v_tail_2930_;
v_a_2926_ = v___x_2937_;
goto _start;
}
}
else
{
lean_del_object(v___x_2932_);
lean_dec(v_head_2929_);
v_a_2925_ = v_tail_2930_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop(lean_object* v_00_u03b1_2942_, lean_object* v_r_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l_List_eraseRepsBy_loop___redArg(v_r_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy___redArg(lean_object* v_r_2948_, lean_object* v_x_2949_){
_start:
{
if (lean_obj_tag(v_x_2949_) == 0)
{
lean_dec_ref(v_r_2948_);
return v_x_2949_;
}
else
{
lean_object* v_head_2950_; lean_object* v_tail_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_head_2950_ = lean_ctor_get(v_x_2949_, 0);
lean_inc(v_head_2950_);
v_tail_2951_ = lean_ctor_get(v_x_2949_, 1);
lean_inc(v_tail_2951_);
lean_dec_ref_known(v_x_2949_, 2);
v___x_2952_ = lean_box(0);
v___x_2953_ = l_List_eraseRepsBy_loop___redArg(v_r_2948_, v_head_2950_, v_tail_2951_, v___x_2952_);
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy(lean_object* v_00_u03b1_2954_, lean_object* v_r_2955_, lean_object* v_x_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_List_eraseRepsBy___redArg(v_r_2955_, v_x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___redArg(lean_object* v_inst_2958_, lean_object* v_as_2959_){
_start:
{
lean_object* v___f_2960_; lean_object* v___x_2961_; 
v___f_2960_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2960_, 0, v_inst_2958_);
v___x_2961_ = l_List_eraseRepsBy___redArg(v___f_2960_, v_as_2959_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object* v_00_u03b1_2962_, lean_object* v_inst_2963_, lean_object* v_as_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_List_eraseReps___redArg(v_inst_2963_, v_as_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___redArg(lean_object* v_p_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
if (lean_obj_tag(v_a_2967_) == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec_ref(v_p_2966_);
v___x_2969_ = l_List_reverse___redArg(v_a_2968_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v_a_2967_);
return v___x_2970_;
}
else
{
lean_object* v_head_2971_; lean_object* v_tail_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v_head_2971_ = lean_ctor_get(v_a_2967_, 0);
v_tail_2972_ = lean_ctor_get(v_a_2967_, 1);
lean_inc_ref(v_p_2966_);
lean_inc(v_head_2971_);
v___x_2973_ = lean_apply_1(v_p_2966_, v_head_2971_);
v___x_2974_ = lean_unbox(v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_dec_ref(v_p_2966_);
v___x_2975_ = l_List_reverse___redArg(v_a_2968_);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v_a_2967_);
return v___x_2976_;
}
else
{
lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2984_; 
lean_inc(v_tail_2972_);
lean_inc(v_head_2971_);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_a_2967_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; lean_object* v_unused_2986_; 
v_unused_2985_ = lean_ctor_get(v_a_2967_, 1);
lean_dec(v_unused_2985_);
v_unused_2986_ = lean_ctor_get(v_a_2967_, 0);
lean_dec(v_unused_2986_);
v___x_2978_ = v_a_2967_;
v_isShared_2979_ = v_isSharedCheck_2984_;
goto v_resetjp_2977_;
}
else
{
lean_dec(v_a_2967_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2984_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 1, v_a_2968_);
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_head_2971_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_a_2968_);
v___x_2981_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
v_a_2967_ = v_tail_2972_;
v_a_2968_ = v___x_2981_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop(lean_object* v_00_u03b1_2987_, lean_object* v_p_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_List_span_loop___redArg(v_p_2988_, v_a_2989_, v_a_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_List_span___redArg(lean_object* v_p_2992_, lean_object* v_as_2993_){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_box(0);
v___x_2995_ = l_List_span_loop___redArg(v_p_2992_, v_as_2993_, v___x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_List_span(lean_object* v_00_u03b1_2996_, lean_object* v_p_2997_, lean_object* v_as_2998_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_box(0);
v___x_3000_ = l_List_span_loop___redArg(v_p_2997_, v_as_2998_, v___x_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___redArg(lean_object* v_R_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
if (lean_obj_tag(v_a_3002_) == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec_ref(v_R_3001_);
v___x_3006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3006_, 0, v_a_3003_);
lean_ctor_set(v___x_3006_, 1, v_a_3004_);
v___x_3007_ = l_List_reverse___redArg(v___x_3006_);
v___x_3008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v_a_3005_);
v___x_3009_ = l_List_reverse___redArg(v___x_3008_);
return v___x_3009_;
}
else
{
lean_object* v_head_3010_; lean_object* v_tail_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3028_; 
v_head_3010_ = lean_ctor_get(v_a_3002_, 0);
v_tail_3011_ = lean_ctor_get(v_a_3002_, 1);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_a_3002_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3013_ = v_a_3002_;
v_isShared_3014_ = v_isSharedCheck_3028_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_tail_3011_);
lean_inc(v_head_3010_);
lean_dec(v_a_3002_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3028_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; uint8_t v___x_3016_; 
lean_inc_ref(v_R_3001_);
lean_inc(v_head_3010_);
lean_inc(v_a_3003_);
v___x_3015_ = lean_apply_2(v_R_3001_, v_a_3003_, v_head_3010_);
v___x_3016_ = lean_unbox(v___x_3015_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3017_ = lean_box(0);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 1, v_a_3004_);
lean_ctor_set(v___x_3013_, 0, v_a_3003_);
v___x_3019_ = v___x_3013_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3003_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_a_3004_);
v___x_3019_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = l_List_reverse___redArg(v___x_3019_);
v___x_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
lean_ctor_set(v___x_3021_, 1, v_a_3005_);
v_a_3002_ = v_tail_3011_;
v_a_3003_ = v_head_3010_;
v_a_3004_ = v___x_3017_;
v_a_3005_ = v___x_3021_;
goto _start;
}
}
else
{
lean_object* v___x_3025_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 1, v_a_3004_);
lean_ctor_set(v___x_3013_, 0, v_a_3003_);
v___x_3025_ = v___x_3013_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3003_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_a_3004_);
v___x_3025_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
v_a_3002_ = v_tail_3011_;
v_a_3003_ = v_head_3010_;
v_a_3004_ = v___x_3025_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop(lean_object* v_00_u03b1_3029_, lean_object* v_R_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_List_splitBy_loop___redArg(v_R_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___redArg(lean_object* v_R_3036_, lean_object* v_x_3037_){
_start:
{
if (lean_obj_tag(v_x_3037_) == 0)
{
lean_object* v___x_3038_; 
lean_dec_ref(v_R_3036_);
v___x_3038_ = lean_box(0);
return v___x_3038_;
}
else
{
lean_object* v_head_3039_; lean_object* v_tail_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_head_3039_ = lean_ctor_get(v_x_3037_, 0);
lean_inc(v_head_3039_);
v_tail_3040_ = lean_ctor_get(v_x_3037_, 1);
lean_inc(v_tail_3040_);
lean_dec_ref_known(v_x_3037_, 2);
v___x_3041_ = lean_box(0);
v___x_3042_ = l_List_splitBy_loop___redArg(v_R_3036_, v_tail_3040_, v_head_3039_, v___x_3041_, v___x_3041_);
return v___x_3042_;
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy(lean_object* v_00_u03b1_3043_, lean_object* v_R_3044_, lean_object* v_x_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_List_splitBy___redArg(v_R_3044_, v_x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___redArg___lam__0(lean_object* v_inst_3047_, lean_object* v_ys_3048_, lean_object* v_x_3049_){
_start:
{
uint8_t v___x_3050_; 
v___x_3050_ = l_List_elem___redArg(v_inst_3047_, v_x_3049_, v_ys_3048_);
if (v___x_3050_ == 0)
{
uint8_t v___x_3051_; 
v___x_3051_ = 1;
return v___x_3051_;
}
else
{
uint8_t v___x_3052_; 
v___x_3052_ = 0;
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg___lam__0___boxed(lean_object* v_inst_3053_, lean_object* v_ys_3054_, lean_object* v_x_3055_){
_start:
{
uint8_t v_res_3056_; lean_object* v_r_3057_; 
v_res_3056_ = l_List_removeAll___redArg___lam__0(v_inst_3053_, v_ys_3054_, v_x_3055_);
v_r_3057_ = lean_box(v_res_3056_);
return v_r_3057_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg(lean_object* v_inst_3058_, lean_object* v_xs_3059_, lean_object* v_ys_3060_){
_start:
{
lean_object* v___f_3061_; lean_object* v___x_3062_; 
v___f_3061_ = lean_alloc_closure((void*)(l_List_removeAll___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3061_, 0, v_inst_3058_);
lean_closure_set(v___f_3061_, 1, v_ys_3060_);
v___x_3062_ = l_List_filter___redArg(v___f_3061_, v_xs_3059_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll(lean_object* v_00_u03b1_3063_, lean_object* v_inst_3064_, lean_object* v_xs_3065_, lean_object* v_ys_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_List_removeAll___redArg(v_inst_3064_, v_xs_3065_, v_ys_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_3068_, lean_object* v_h__1_3069_, lean_object* v_h__2_3070_){
_start:
{
if (lean_obj_tag(v_ys_3068_) == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_dec(v_h__2_3070_);
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_apply_1(v_h__1_3069_, v___x_3071_);
return v___x_3072_;
}
else
{
lean_object* v_head_3073_; lean_object* v_tail_3074_; lean_object* v___x_3075_; 
lean_dec(v_h__1_3069_);
v_head_3073_ = lean_ctor_get(v_ys_3068_, 0);
lean_inc(v_head_3073_);
v_tail_3074_ = lean_ctor_get(v_ys_3068_, 1);
lean_inc(v_tail_3074_);
lean_dec_ref_known(v_ys_3068_, 2);
v___x_3075_ = lean_apply_2(v_h__2_3070_, v_head_3073_, v_tail_3074_);
return v___x_3075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_3076_, lean_object* v_motive_3077_, lean_object* v_ys_3078_, lean_object* v_h__1_3079_, lean_object* v_h__2_3080_){
_start:
{
if (lean_obj_tag(v_ys_3078_) == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
lean_dec(v_h__2_3080_);
v___x_3081_ = lean_box(0);
v___x_3082_ = lean_apply_1(v_h__1_3079_, v___x_3081_);
return v___x_3082_;
}
else
{
lean_object* v_head_3083_; lean_object* v_tail_3084_; lean_object* v___x_3085_; 
lean_dec(v_h__1_3079_);
v_head_3083_ = lean_ctor_get(v_ys_3078_, 0);
lean_inc(v_head_3083_);
v_tail_3084_ = lean_ctor_get(v_ys_3078_, 1);
lean_inc(v_tail_3084_);
lean_dec_ref_known(v_ys_3078_, 2);
v___x_3085_ = lean_apply_2(v_h__2_3080_, v_head_3083_, v_tail_3084_);
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(lean_object* v_x_3086_, lean_object* v_x_3087_, lean_object* v_h__1_3088_, lean_object* v_h__2_3089_){
_start:
{
if (lean_obj_tag(v_x_3086_) == 0)
{
lean_object* v___x_3090_; 
lean_dec(v_h__2_3089_);
v___x_3090_ = lean_apply_1(v_h__1_3088_, v_x_3087_);
return v___x_3090_;
}
else
{
lean_object* v_head_3091_; lean_object* v_tail_3092_; lean_object* v___x_3093_; 
lean_dec(v_h__1_3088_);
v_head_3091_ = lean_ctor_get(v_x_3086_, 0);
lean_inc(v_head_3091_);
v_tail_3092_ = lean_ctor_get(v_x_3086_, 1);
lean_inc(v_tail_3092_);
lean_dec_ref_known(v_x_3086_, 2);
v___x_3093_ = lean_apply_3(v_h__2_3089_, v_head_3091_, v_tail_3092_, v_x_3087_);
return v___x_3093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(lean_object* v_00_u03b1_3094_, lean_object* v_motive_3095_, lean_object* v_x_3096_, lean_object* v_x_3097_, lean_object* v_h__1_3098_, lean_object* v_h__2_3099_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 0)
{
lean_object* v___x_3100_; 
lean_dec(v_h__2_3099_);
v___x_3100_ = lean_apply_1(v_h__1_3098_, v_x_3097_);
return v___x_3100_;
}
else
{
lean_object* v_head_3101_; lean_object* v_tail_3102_; lean_object* v___x_3103_; 
lean_dec(v_h__1_3098_);
v_head_3101_ = lean_ctor_get(v_x_3096_, 0);
lean_inc(v_head_3101_);
v_tail_3102_ = lean_ctor_get(v_x_3096_, 1);
lean_inc(v_tail_3102_);
lean_dec_ref_known(v_x_3096_, 2);
v___x_3103_ = lean_apply_3(v_h__2_3099_, v_head_3101_, v_tail_3102_, v_x_3097_);
return v___x_3103_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object* v_f_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
if (lean_obj_tag(v_a_3105_) == 0)
{
lean_object* v___x_3107_; 
lean_dec(v_f_3104_);
v___x_3107_ = l_List_reverse___redArg(v_a_3106_);
return v___x_3107_;
}
else
{
lean_object* v_head_3108_; lean_object* v_tail_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3118_; 
v_head_3108_ = lean_ctor_get(v_a_3105_, 0);
v_tail_3109_ = lean_ctor_get(v_a_3105_, 1);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_a_3105_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3111_ = v_a_3105_;
v_isShared_3112_ = v_isSharedCheck_3118_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_tail_3109_);
lean_inc(v_head_3108_);
lean_dec(v_a_3105_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3118_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v___x_3115_; 
lean_inc(v_f_3104_);
v___x_3113_ = lean_apply_1(v_f_3104_, v_head_3108_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v_a_3106_);
lean_ctor_set(v___x_3111_, 0, v___x_3113_);
v___x_3115_ = v___x_3111_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_a_3106_);
v___x_3115_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
v_a_3105_ = v_tail_3109_;
v_a_3106_ = v___x_3115_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object* v_00_u03b1_3119_, lean_object* v_00_u03b2_3120_, lean_object* v_f_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_List_mapTR_loop___redArg(v_f_3121_, v_a_3122_, v_a_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object* v_f_3125_, lean_object* v_as_3126_){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = lean_box(0);
v___x_3128_ = l_List_mapTR_loop___redArg(v_f_3125_, v_as_3126_, v___x_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR(lean_object* v_00_u03b1_3129_, lean_object* v_00_u03b2_3130_, lean_object* v_f_3131_, lean_object* v_as_3132_){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = lean_box(0);
v___x_3134_ = l_List_mapTR_loop___redArg(v_f_3131_, v_as_3132_, v___x_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(lean_object* v_x_3135_, lean_object* v_x_3136_, lean_object* v_h__1_3137_, lean_object* v_h__2_3138_){
_start:
{
if (lean_obj_tag(v_x_3135_) == 0)
{
lean_object* v___x_3139_; 
lean_dec(v_h__2_3138_);
v___x_3139_ = lean_apply_1(v_h__1_3137_, v_x_3136_);
return v___x_3139_;
}
else
{
lean_object* v_head_3140_; lean_object* v_tail_3141_; lean_object* v___x_3142_; 
lean_dec(v_h__1_3137_);
v_head_3140_ = lean_ctor_get(v_x_3135_, 0);
lean_inc(v_head_3140_);
v_tail_3141_ = lean_ctor_get(v_x_3135_, 1);
lean_inc(v_tail_3141_);
lean_dec_ref_known(v_x_3135_, 2);
v___x_3142_ = lean_apply_3(v_h__2_3138_, v_head_3140_, v_tail_3141_, v_x_3136_);
return v___x_3142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(lean_object* v_00_u03b1_3143_, lean_object* v_00_u03b2_3144_, lean_object* v_motive_3145_, lean_object* v_x_3146_, lean_object* v_x_3147_, lean_object* v_h__1_3148_, lean_object* v_h__2_3149_){
_start:
{
if (lean_obj_tag(v_x_3146_) == 0)
{
lean_object* v___x_3150_; 
lean_dec(v_h__2_3149_);
v___x_3150_ = lean_apply_1(v_h__1_3148_, v_x_3147_);
return v___x_3150_;
}
else
{
lean_object* v_head_3151_; lean_object* v_tail_3152_; lean_object* v___x_3153_; 
lean_dec(v_h__1_3148_);
v_head_3151_ = lean_ctor_get(v_x_3146_, 0);
lean_inc(v_head_3151_);
v_tail_3152_ = lean_ctor_get(v_x_3146_, 1);
lean_inc(v_tail_3152_);
lean_dec_ref_known(v_x_3146_, 2);
v___x_3153_ = lean_apply_3(v_h__2_3149_, v_head_3151_, v_tail_3152_, v_x_3147_);
return v___x_3153_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object* v_p_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_){
_start:
{
if (lean_obj_tag(v_a_3155_) == 0)
{
lean_object* v___x_3157_; 
lean_dec_ref(v_p_3154_);
v___x_3157_ = l_List_reverse___redArg(v_a_3156_);
return v___x_3157_;
}
else
{
lean_object* v_head_3158_; lean_object* v_tail_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3170_; 
v_head_3158_ = lean_ctor_get(v_a_3155_, 0);
v_tail_3159_ = lean_ctor_get(v_a_3155_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_a_3155_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3161_ = v_a_3155_;
v_isShared_3162_ = v_isSharedCheck_3170_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_tail_3159_);
lean_inc(v_head_3158_);
lean_dec(v_a_3155_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3170_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; uint8_t v___x_3164_; 
lean_inc_ref(v_p_3154_);
lean_inc(v_head_3158_);
v___x_3163_ = lean_apply_1(v_p_3154_, v_head_3158_);
v___x_3164_ = lean_unbox(v___x_3163_);
if (v___x_3164_ == 0)
{
lean_del_object(v___x_3161_);
lean_dec(v_head_3158_);
v_a_3155_ = v_tail_3159_;
goto _start;
}
else
{
lean_object* v___x_3167_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 1, v_a_3156_);
v___x_3167_ = v___x_3161_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_head_3158_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_a_3156_);
v___x_3167_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
v_a_3155_ = v_tail_3159_;
v_a_3156_ = v___x_3167_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object* v_00_u03b1_3171_, lean_object* v_p_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_List_filterTR_loop___redArg(v_p_3172_, v_a_3173_, v_a_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object* v_p_3176_, lean_object* v_as_3177_){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = lean_box(0);
v___x_3179_ = l_List_filterTR_loop___redArg(v_p_3176_, v_as_3177_, v___x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR(lean_object* v_00_u03b1_3180_, lean_object* v_p_3181_, lean_object* v_as_3182_){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = lean_box(0);
v___x_3184_ = l_List_filterTR_loop___redArg(v_p_3181_, v_as_3182_, v___x_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_zero_3188_; uint8_t v_isZero_3189_; 
v_zero_3188_ = lean_unsigned_to_nat(0u);
v_isZero_3189_ = lean_nat_dec_eq(v_a_3186_, v_zero_3188_);
if (v_isZero_3189_ == 1)
{
lean_dec(v_a_3186_);
lean_dec(v_a_3185_);
return v_a_3187_;
}
else
{
lean_object* v_one_3190_; lean_object* v_n_3191_; lean_object* v___x_3192_; 
v_one_3190_ = lean_unsigned_to_nat(1u);
v_n_3191_ = lean_nat_sub(v_a_3186_, v_one_3190_);
lean_dec(v_a_3186_);
lean_inc(v_a_3185_);
v___x_3192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3192_, 0, v_a_3185_);
lean_ctor_set(v___x_3192_, 1, v_a_3187_);
v_a_3186_ = v_n_3191_;
v_a_3187_ = v___x_3192_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object* v_00_u03b1_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_List_replicateTR_loop___redArg(v_a_3195_, v_a_3196_, v_a_3197_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object* v_n_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = lean_box(0);
v___x_3202_ = l_List_replicateTR_loop___redArg(v_a_3200_, v_n_3199_, v___x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object* v_00_u03b1_3203_, lean_object* v_n_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_List_replicateTR___redArg(v_n_3204_, v_a_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(lean_object* v_x_3207_, lean_object* v_x_3208_, lean_object* v_h__1_3209_, lean_object* v_h__2_3210_){
_start:
{
lean_object* v_zero_3211_; uint8_t v_isZero_3212_; 
v_zero_3211_ = lean_unsigned_to_nat(0u);
v_isZero_3212_ = lean_nat_dec_eq(v_x_3207_, v_zero_3211_);
if (v_isZero_3212_ == 1)
{
lean_object* v___x_3213_; 
lean_dec(v_h__2_3210_);
v___x_3213_ = lean_apply_1(v_h__1_3209_, v_x_3208_);
return v___x_3213_;
}
else
{
lean_object* v_one_3214_; lean_object* v_n_3215_; lean_object* v___x_3216_; 
lean_dec(v_h__1_3209_);
v_one_3214_ = lean_unsigned_to_nat(1u);
v_n_3215_ = lean_nat_sub(v_x_3207_, v_one_3214_);
v___x_3216_ = lean_apply_2(v_h__2_3210_, v_n_3215_, v_x_3208_);
return v___x_3216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_3217_, lean_object* v_x_3218_, lean_object* v_h__1_3219_, lean_object* v_h__2_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(v_x_3217_, v_x_3218_, v_h__1_3219_, v_h__2_3220_);
lean_dec(v_x_3217_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(lean_object* v_00_u03b1_3222_, lean_object* v_motive_3223_, lean_object* v_x_3224_, lean_object* v_x_3225_, lean_object* v_h__1_3226_, lean_object* v_h__2_3227_){
_start:
{
lean_object* v_zero_3228_; uint8_t v_isZero_3229_; 
v_zero_3228_ = lean_unsigned_to_nat(0u);
v_isZero_3229_ = lean_nat_dec_eq(v_x_3224_, v_zero_3228_);
if (v_isZero_3229_ == 1)
{
lean_object* v___x_3230_; 
lean_dec(v_h__2_3227_);
v___x_3230_ = lean_apply_1(v_h__1_3226_, v_x_3225_);
return v___x_3230_;
}
else
{
lean_object* v_one_3231_; lean_object* v_n_3232_; lean_object* v___x_3233_; 
lean_dec(v_h__1_3226_);
v_one_3231_ = lean_unsigned_to_nat(1u);
v_n_3232_ = lean_nat_sub(v_x_3224_, v_one_3231_);
v___x_3233_ = lean_apply_2(v_h__2_3227_, v_n_3232_, v_x_3225_);
return v___x_3233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_3234_, lean_object* v_motive_3235_, lean_object* v_x_3236_, lean_object* v_x_3237_, lean_object* v_h__1_3238_, lean_object* v_h__2_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(v_00_u03b1_3234_, v_motive_3235_, v_x_3236_, v_x_3237_, v_h__1_3238_, v_h__2_3239_);
lean_dec(v_x_3236_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(lean_object* v_x_3241_, lean_object* v_x_3242_, lean_object* v_h__1_3243_, lean_object* v_h__2_3244_){
_start:
{
lean_object* v_zero_3245_; uint8_t v_isZero_3246_; 
v_zero_3245_ = lean_unsigned_to_nat(0u);
v_isZero_3246_ = lean_nat_dec_eq(v_x_3241_, v_zero_3245_);
if (v_isZero_3246_ == 1)
{
lean_object* v___x_3247_; 
lean_dec(v_h__2_3244_);
v___x_3247_ = lean_apply_1(v_h__1_3243_, v_x_3242_);
return v___x_3247_;
}
else
{
lean_object* v_one_3248_; lean_object* v_n_3249_; lean_object* v___x_3250_; 
lean_dec(v_h__1_3243_);
v_one_3248_ = lean_unsigned_to_nat(1u);
v_n_3249_ = lean_nat_sub(v_x_3241_, v_one_3248_);
v___x_3250_ = lean_apply_2(v_h__2_3244_, v_n_3249_, v_x_3242_);
return v___x_3250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_3251_, lean_object* v_x_3252_, lean_object* v_h__1_3253_, lean_object* v_h__2_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(v_x_3251_, v_x_3252_, v_h__1_3253_, v_h__2_3254_);
lean_dec(v_x_3251_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(lean_object* v_00_u03b1_3256_, lean_object* v_motive_3257_, lean_object* v_x_3258_, lean_object* v_x_3259_, lean_object* v_h__1_3260_, lean_object* v_h__2_3261_){
_start:
{
lean_object* v_zero_3262_; uint8_t v_isZero_3263_; 
v_zero_3262_ = lean_unsigned_to_nat(0u);
v_isZero_3263_ = lean_nat_dec_eq(v_x_3258_, v_zero_3262_);
if (v_isZero_3263_ == 1)
{
lean_object* v___x_3264_; 
lean_dec(v_h__2_3261_);
v___x_3264_ = lean_apply_1(v_h__1_3260_, v_x_3259_);
return v___x_3264_;
}
else
{
lean_object* v_one_3265_; lean_object* v_n_3266_; lean_object* v___x_3267_; 
lean_dec(v_h__1_3260_);
v_one_3265_ = lean_unsigned_to_nat(1u);
v_n_3266_ = lean_nat_sub(v_x_3258_, v_one_3265_);
v___x_3267_ = lean_apply_2(v_h__2_3261_, v_n_3266_, v_x_3259_);
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___boxed(lean_object* v_00_u03b1_3268_, lean_object* v_motive_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_, lean_object* v_h__1_3272_, lean_object* v_h__2_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(v_00_u03b1_3268_, v_motive_3269_, v_x_3270_, v_x_3271_, v_h__1_3272_, v_h__2_3273_);
lean_dec(v_x_3270_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg(lean_object* v_n_3275_, lean_object* v_a_3276_, lean_object* v_l_3277_){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3278_ = l_List_lengthTR___redArg(v_l_3277_);
v___x_3279_ = lean_nat_sub(v_n_3275_, v___x_3278_);
lean_dec(v___x_3278_);
v___x_3280_ = l_List_replicateTR_loop___redArg(v_a_3276_, v___x_3279_, v_l_3277_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg___boxed(lean_object* v_n_3281_, lean_object* v_a_3282_, lean_object* v_l_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_List_leftpadTR___redArg(v_n_3281_, v_a_3282_, v_l_3283_);
lean_dec(v_n_3281_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object* v_00_u03b1_3285_, lean_object* v_n_3286_, lean_object* v_a_3287_, lean_object* v_l_3288_){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = l_List_lengthTR___redArg(v_l_3288_);
v___x_3290_ = lean_nat_sub(v_n_3286_, v___x_3289_);
lean_dec(v___x_3289_);
v___x_3291_ = l_List_replicateTR_loop___redArg(v_a_3287_, v___x_3290_, v_l_3288_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___boxed(lean_object* v_00_u03b1_3292_, lean_object* v_n_3293_, lean_object* v_a_3294_, lean_object* v_l_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_List_leftpadTR(v_00_u03b1_3292_, v_n_3293_, v_a_3294_, v_l_3295_);
lean_dec(v_n_3293_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg(lean_object* v_init_3297_, lean_object* v_x_3298_){
_start:
{
if (lean_obj_tag(v_x_3298_) == 0)
{
lean_inc_ref(v_init_3297_);
return v_init_3297_;
}
else
{
lean_object* v_head_3299_; lean_object* v_tail_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3326_; 
v_head_3299_ = lean_ctor_get(v_x_3298_, 0);
v_tail_3300_ = lean_ctor_get(v_x_3298_, 1);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_x_3298_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3302_ = v_x_3298_;
v_isShared_3303_ = v_isSharedCheck_3326_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_tail_3300_);
lean_inc(v_head_3299_);
lean_dec(v_x_3298_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3326_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v_fst_3304_; lean_object* v_snd_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3325_; 
v_fst_3304_ = lean_ctor_get(v_head_3299_, 0);
v_snd_3305_ = lean_ctor_get(v_head_3299_, 1);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_head_3299_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3307_ = v_head_3299_;
v_isShared_3308_ = v_isSharedCheck_3325_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_snd_3305_);
lean_inc(v_fst_3304_);
lean_dec(v_head_3299_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3325_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3309_; lean_object* v_fst_3310_; lean_object* v_snd_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3324_; 
v___x_3309_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3297_, v_tail_3300_);
v_fst_3310_ = lean_ctor_get(v___x_3309_, 0);
v_snd_3311_ = lean_ctor_get(v___x_3309_, 1);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3313_ = v___x_3309_;
v_isShared_3314_ = v_isSharedCheck_3324_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_snd_3311_);
lean_inc(v_fst_3310_);
lean_dec(v___x_3309_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3324_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 1, v_fst_3310_);
lean_ctor_set(v___x_3302_, 0, v_fst_3304_);
v___x_3316_ = v___x_3302_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_fst_3304_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v_fst_3310_);
v___x_3316_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3318_; 
if (v_isShared_3308_ == 0)
{
lean_ctor_set_tag(v___x_3307_, 1);
lean_ctor_set(v___x_3307_, 1, v_snd_3311_);
lean_ctor_set(v___x_3307_, 0, v_snd_3305_);
v___x_3318_ = v___x_3307_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_snd_3305_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_snd_3311_);
v___x_3318_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3320_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 1, v___x_3318_);
lean_ctor_set(v___x_3313_, 0, v___x_3316_);
v___x_3320_ = v___x_3313_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg___boxed(lean_object* v_init_3327_, lean_object* v_x_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3327_, v_x_3328_);
lean_dec_ref(v_init_3327_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object* v_l_3330_){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_3332_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v___x_3331_, v_l_3330_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object* v_00_u03b1_3333_, lean_object* v_00_u03b2_3334_, lean_object* v_l_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_List_unzipTR___redArg(v_l_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0(lean_object* v_00_u03b1_3337_, lean_object* v_00_u03b2_3338_, lean_object* v_init_3339_, lean_object* v_x_3340_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3339_, v_x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___boxed(lean_object* v_00_u03b1_3342_, lean_object* v_00_u03b2_3343_, lean_object* v_init_3344_, lean_object* v_x_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_List_foldr___at___00List_unzipTR_spec__0(v_00_u03b1_3342_, v_00_u03b2_3343_, v_init_3344_, v_x_3345_);
lean_dec_ref(v_init_3344_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object* v_step_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_){
_start:
{
lean_object* v_zero_3351_; uint8_t v_isZero_3352_; 
v_zero_3351_ = lean_unsigned_to_nat(0u);
v_isZero_3352_ = lean_nat_dec_eq(v_a_3348_, v_zero_3351_);
if (v_isZero_3352_ == 1)
{
lean_dec(v_a_3349_);
lean_dec(v_a_3348_);
return v_a_3350_;
}
else
{
lean_object* v_one_3353_; lean_object* v_n_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_one_3353_ = lean_unsigned_to_nat(1u);
v_n_3354_ = lean_nat_sub(v_a_3348_, v_one_3353_);
lean_dec(v_a_3348_);
v___x_3355_ = lean_nat_sub(v_a_3349_, v_step_3347_);
lean_dec(v_a_3349_);
lean_inc(v___x_3355_);
v___x_3356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
lean_ctor_set(v___x_3356_, 1, v_a_3350_);
v_a_3348_ = v_n_3354_;
v_a_3349_ = v___x_3355_;
v_a_3350_ = v___x_3356_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object* v_step_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_List_range_x27TR_go(v_step_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
lean_dec(v_step_3358_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object* v_s_3363_, lean_object* v_n_3364_, lean_object* v_step_3365_){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3366_ = lean_nat_mul(v_step_3365_, v_n_3364_);
v___x_3367_ = lean_nat_add(v_s_3363_, v___x_3366_);
lean_dec(v___x_3366_);
v___x_3368_ = lean_box(0);
v___x_3369_ = l_List_range_x27TR_go(v_step_3365_, v_n_3364_, v___x_3367_, v___x_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object* v_s_3370_, lean_object* v_n_3371_, lean_object* v_step_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_List_range_x27TR(v_s_3370_, v_n_3371_, v_step_3372_);
lean_dec(v_step_3372_);
lean_dec(v_s_3370_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(lean_object* v_x_3374_, lean_object* v_x_3375_, lean_object* v_x_3376_, lean_object* v_h__1_3377_, lean_object* v_h__2_3378_){
_start:
{
lean_object* v_zero_3379_; uint8_t v_isZero_3380_; 
v_zero_3379_ = lean_unsigned_to_nat(0u);
v_isZero_3380_ = lean_nat_dec_eq(v_x_3374_, v_zero_3379_);
if (v_isZero_3380_ == 1)
{
lean_object* v___x_3381_; 
lean_dec(v_h__2_3378_);
v___x_3381_ = lean_apply_2(v_h__1_3377_, v_x_3375_, v_x_3376_);
return v___x_3381_;
}
else
{
lean_object* v_one_3382_; lean_object* v_n_3383_; lean_object* v___x_3384_; 
lean_dec(v_h__1_3377_);
v_one_3382_ = lean_unsigned_to_nat(1u);
v_n_3383_ = lean_nat_sub(v_x_3374_, v_one_3382_);
v___x_3384_ = lean_apply_3(v_h__2_3378_, v_n_3383_, v_x_3375_, v_x_3376_);
return v___x_3384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(lean_object* v_x_3385_, lean_object* v_x_3386_, lean_object* v_x_3387_, lean_object* v_h__1_3388_, lean_object* v_h__2_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(v_x_3385_, v_x_3386_, v_x_3387_, v_h__1_3388_, v_h__2_3389_);
lean_dec(v_x_3385_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object* v_motive_3391_, lean_object* v_x_3392_, lean_object* v_x_3393_, lean_object* v_x_3394_, lean_object* v_h__1_3395_, lean_object* v_h__2_3396_){
_start:
{
lean_object* v_zero_3397_; uint8_t v_isZero_3398_; 
v_zero_3397_ = lean_unsigned_to_nat(0u);
v_isZero_3398_ = lean_nat_dec_eq(v_x_3392_, v_zero_3397_);
if (v_isZero_3398_ == 1)
{
lean_object* v___x_3399_; 
lean_dec(v_h__2_3396_);
v___x_3399_ = lean_apply_2(v_h__1_3395_, v_x_3393_, v_x_3394_);
return v___x_3399_;
}
else
{
lean_object* v_one_3400_; lean_object* v_n_3401_; lean_object* v___x_3402_; 
lean_dec(v_h__1_3395_);
v_one_3400_ = lean_unsigned_to_nat(1u);
v_n_3401_ = lean_nat_sub(v_x_3392_, v_one_3400_);
v___x_3402_ = lean_apply_3(v_h__2_3396_, v_n_3401_, v_x_3393_, v_x_3394_);
return v___x_3402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(lean_object* v_motive_3403_, lean_object* v_x_3404_, lean_object* v_x_3405_, lean_object* v_x_3406_, lean_object* v_h__1_3407_, lean_object* v_h__2_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(v_motive_3403_, v_x_3404_, v_x_3405_, v_x_3406_, v_h__1_3407_, v_h__2_3408_);
lean_dec(v_x_3404_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg(lean_object* v_sep_3410_, lean_object* v_init_3411_, lean_object* v_x_3412_){
_start:
{
if (lean_obj_tag(v_x_3412_) == 0)
{
lean_dec(v_sep_3410_);
lean_inc(v_init_3411_);
return v_init_3411_;
}
else
{
lean_object* v_head_3413_; lean_object* v_tail_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3423_; 
v_head_3413_ = lean_ctor_get(v_x_3412_, 0);
v_tail_3414_ = lean_ctor_get(v_x_3412_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_x_3412_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3416_ = v_x_3412_;
v_isShared_3417_ = v_isSharedCheck_3423_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_tail_3414_);
lean_inc(v_head_3413_);
lean_dec(v_x_3412_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3423_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
lean_inc(v_sep_3410_);
v___x_3418_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3410_, v_init_3411_, v_tail_3414_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 1, v___x_3418_);
v___x_3420_ = v___x_3416_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_head_3413_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3421_, 0, v_sep_3410_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
return v___x_3421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(lean_object* v_sep_3424_, lean_object* v_init_3425_, lean_object* v_x_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3424_, v_init_3425_, v_x_3426_);
lean_dec(v_init_3425_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object* v_sep_3428_, lean_object* v_x_3429_){
_start:
{
if (lean_obj_tag(v_x_3429_) == 0)
{
lean_dec(v_sep_3428_);
return v_x_3429_;
}
else
{
lean_object* v_tail_3430_; 
v_tail_3430_ = lean_ctor_get(v_x_3429_, 1);
lean_inc(v_tail_3430_);
if (lean_obj_tag(v_tail_3430_) == 0)
{
lean_dec(v_sep_3428_);
return v_x_3429_;
}
else
{
lean_object* v_head_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3450_; 
v_head_3431_ = lean_ctor_get(v_x_3429_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_x_3429_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; 
v_unused_3451_ = lean_ctor_get(v_x_3429_, 1);
lean_dec(v_unused_3451_);
v___x_3433_ = v_x_3429_;
v_isShared_3434_ = v_isSharedCheck_3450_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_head_3431_);
lean_dec(v_x_3429_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3450_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_head_3435_; lean_object* v_tail_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3449_; 
v_head_3435_ = lean_ctor_get(v_tail_3430_, 0);
v_tail_3436_ = lean_ctor_get(v_tail_3430_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_tail_3430_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3438_ = v_tail_3430_;
v_isShared_3439_ = v_isSharedCheck_3449_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_tail_3436_);
lean_inc(v_head_3435_);
lean_dec(v_tail_3430_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3449_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3440_ = lean_box(0);
lean_inc(v_sep_3428_);
v___x_3441_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3428_, v___x_3440_, v_tail_3436_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3441_);
v___x_3443_ = v___x_3438_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_head_3435_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3445_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3443_);
lean_ctor_set(v___x_3433_, 0, v_sep_3428_);
v___x_3445_ = v___x_3433_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_sep_3428_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_head_3431_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
return v___x_3446_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object* v_00_u03b1_3452_, lean_object* v_sep_3453_, lean_object* v_x_3454_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = l_List_intersperseTR___redArg(v_sep_3453_, v_x_3454_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0(lean_object* v_00_u03b1_3456_, lean_object* v_sep_3457_, lean_object* v_init_3458_, lean_object* v_x_3459_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3457_, v_init_3458_, v_x_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___boxed(lean_object* v_00_u03b1_3461_, lean_object* v_sep_3462_, lean_object* v_init_3463_, lean_object* v_x_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_List_foldr___at___00List_intersperseTR_spec__0(v_00_u03b1_3461_, v_sep_3462_, v_init_3463_, v_x_3464_);
lean_dec(v_init_3463_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(lean_object* v_x_3466_, lean_object* v_h__1_3467_, lean_object* v_h__2_3468_, lean_object* v_h__3_3469_){
_start:
{
if (lean_obj_tag(v_x_3466_) == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec(v_h__3_3469_);
lean_dec(v_h__2_3468_);
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_apply_1(v_h__1_3467_, v___x_3470_);
return v___x_3471_;
}
else
{
lean_object* v_tail_3472_; 
lean_dec(v_h__1_3467_);
v_tail_3472_ = lean_ctor_get(v_x_3466_, 1);
if (lean_obj_tag(v_tail_3472_) == 0)
{
lean_object* v_head_3473_; lean_object* v___x_3474_; 
lean_dec(v_h__3_3469_);
v_head_3473_ = lean_ctor_get(v_x_3466_, 0);
lean_inc(v_head_3473_);
lean_dec_ref_known(v_x_3466_, 2);
v___x_3474_ = lean_apply_1(v_h__2_3468_, v_head_3473_);
return v___x_3474_;
}
else
{
lean_object* v_head_3475_; lean_object* v_head_3476_; lean_object* v_tail_3477_; lean_object* v___x_3478_; 
lean_inc_ref(v_tail_3472_);
lean_dec(v_h__2_3468_);
v_head_3475_ = lean_ctor_get(v_x_3466_, 0);
lean_inc(v_head_3475_);
lean_dec_ref_known(v_x_3466_, 2);
v_head_3476_ = lean_ctor_get(v_tail_3472_, 0);
lean_inc(v_head_3476_);
v_tail_3477_ = lean_ctor_get(v_tail_3472_, 1);
lean_inc(v_tail_3477_);
lean_dec_ref_known(v_tail_3472_, 2);
v___x_3478_ = lean_apply_3(v_h__3_3469_, v_head_3475_, v_head_3476_, v_tail_3477_);
return v___x_3478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object* v_00_u03b1_3479_, lean_object* v_motive_3480_, lean_object* v_x_3481_, lean_object* v_h__1_3482_, lean_object* v_h__2_3483_, lean_object* v_h__3_3484_){
_start:
{
if (lean_obj_tag(v_x_3481_) == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
lean_dec(v_h__3_3484_);
lean_dec(v_h__2_3483_);
v___x_3485_ = lean_box(0);
v___x_3486_ = lean_apply_1(v_h__1_3482_, v___x_3485_);
return v___x_3486_;
}
else
{
lean_object* v_tail_3487_; 
lean_dec(v_h__1_3482_);
v_tail_3487_ = lean_ctor_get(v_x_3481_, 1);
if (lean_obj_tag(v_tail_3487_) == 0)
{
lean_object* v_head_3488_; lean_object* v___x_3489_; 
lean_dec(v_h__3_3484_);
v_head_3488_ = lean_ctor_get(v_x_3481_, 0);
lean_inc(v_head_3488_);
lean_dec_ref_known(v_x_3481_, 2);
v___x_3489_ = lean_apply_1(v_h__2_3483_, v_head_3488_);
return v___x_3489_;
}
else
{
lean_object* v_head_3490_; lean_object* v_head_3491_; lean_object* v_tail_3492_; lean_object* v___x_3493_; 
lean_inc_ref(v_tail_3487_);
lean_dec(v_h__2_3483_);
v_head_3490_ = lean_ctor_get(v_x_3481_, 0);
lean_inc(v_head_3490_);
lean_dec_ref_known(v_x_3481_, 2);
v_head_3491_ = lean_ctor_get(v_tail_3487_, 0);
lean_inc(v_head_3491_);
v_tail_3492_ = lean_ctor_get(v_tail_3487_, 1);
lean_inc(v_tail_3492_);
lean_dec_ref_known(v_tail_3487_, 2);
v___x_3493_ = lean_apply_3(v_h__3_3484_, v_head_3490_, v_head_3491_, v_tail_3492_);
return v___x_3493_;
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
