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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_drop___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_drop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_drop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dropWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_partition___redArg___closed__0 = (const lean_object*)&l_List_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_partition___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_min(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_reverseAux___redArg(lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
return v_x_546_;
}
else
{
lean_object* v_head_547_; lean_object* v_tail_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_556_; 
v_head_547_ = lean_ctor_get(v_x_545_, 0);
v_tail_548_ = lean_ctor_get(v_x_545_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_556_ == 0)
{
v___x_550_ = v_x_545_;
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_tail_548_);
lean_inc(v_head_547_);
lean_dec(v_x_545_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v_x_546_);
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_head_547_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_x_546_);
v___x_553_ = v_reuseFailAlloc_555_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
v_x_545_ = v_tail_548_;
v_x_546_ = v___x_553_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object* v_00_u03b1_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_List_reverseAux___redArg(v_x_558_, v_x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_List_reverse___redArg(lean_object* v_as_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_box(0);
v___x_563_ = l_List_reverseAux___redArg(v_as_561_, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_List_reverse(lean_object* v_00_u03b1_564_, lean_object* v_as_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_List_reverse___redArg(v_as_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_h__1_569_, lean_object* v_h__2_570_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_object* v___x_571_; 
lean_dec(v_h__2_570_);
v___x_571_ = lean_apply_1(v_h__1_569_, v_x_568_);
return v___x_571_;
}
else
{
lean_object* v_head_572_; lean_object* v_tail_573_; lean_object* v___x_574_; 
lean_dec(v_h__1_569_);
v_head_572_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_head_572_);
v_tail_573_ = lean_ctor_get(v_x_567_, 1);
lean_inc(v_tail_573_);
lean_dec_ref_known(v_x_567_, 2);
v___x_574_ = lean_apply_3(v_h__2_570_, v_head_572_, v_tail_573_, v_x_568_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_575_, lean_object* v_motive_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_h__1_579_, lean_object* v_h__2_580_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v___x_581_; 
lean_dec(v_h__2_580_);
v___x_581_ = lean_apply_1(v_h__1_579_, v_x_578_);
return v___x_581_;
}
else
{
lean_object* v_head_582_; lean_object* v_tail_583_; lean_object* v___x_584_; 
lean_dec(v_h__1_579_);
v_head_582_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_head_582_);
v_tail_583_ = lean_ctor_get(v_x_577_, 1);
lean_inc(v_tail_583_);
lean_dec_ref_known(v_x_577_, 2);
v___x_584_ = lean_apply_3(v_h__2_580_, v_head_582_, v_tail_583_, v_x_578_);
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_List_appendTR___redArg(lean_object* v_as_585_, lean_object* v_bs_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_List_reverse___redArg(v_as_585_);
v___x_588_ = l_List_reverseAux___redArg(v___x_587_, v_bs_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR(lean_object* v_00_u03b1_589_, lean_object* v_as_590_, lean_object* v_bs_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_List_appendTR___redArg(v_as_590_, v_bs_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter___redArg(lean_object* v_x_593_, lean_object* v_x_594_, lean_object* v_h__1_595_, lean_object* v_h__2_596_){
_start:
{
if (lean_obj_tag(v_x_593_) == 0)
{
lean_object* v___x_597_; 
lean_dec(v_h__2_596_);
v___x_597_ = lean_apply_1(v_h__1_595_, v_x_594_);
return v___x_597_;
}
else
{
lean_object* v_head_598_; lean_object* v_tail_599_; lean_object* v___x_600_; 
lean_dec(v_h__1_595_);
v_head_598_ = lean_ctor_get(v_x_593_, 0);
lean_inc(v_head_598_);
v_tail_599_ = lean_ctor_get(v_x_593_, 1);
lean_inc(v_tail_599_);
lean_dec_ref_known(v_x_593_, 2);
v___x_600_ = lean_apply_3(v_h__2_596_, v_head_598_, v_tail_599_, v_x_594_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter(lean_object* v_00_u03b1_601_, lean_object* v_motive_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
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
LEAN_EXPORT lean_object* l_List_instAppend___redArg(){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = ((lean_object*)(l_List_instAppend___redArg___closed__0));
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend___redArg___boxed(lean_object* v___dummy_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_List_instAppend___redArg();
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend(lean_object* v_00_u03b1_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = ((lean_object*)(l_List_instAppend___redArg___closed__0));
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_List_singleton___redArg(lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_box(0);
v___x_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_620_, 0, v_a_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_List_singleton(lean_object* v_00_u03b1_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_box(0);
v___x_624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_624_, 0, v_a_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_625_, lean_object* v_h__1_626_, lean_object* v_h__2_627_){
_start:
{
if (lean_obj_tag(v_ys_625_) == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v_h__2_627_);
v___x_628_ = lean_box(0);
v___x_629_ = lean_apply_1(v_h__1_626_, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v_head_630_; lean_object* v_tail_631_; lean_object* v___x_632_; 
lean_dec(v_h__1_626_);
v_head_630_ = lean_ctor_get(v_ys_625_, 0);
lean_inc(v_head_630_);
v_tail_631_ = lean_ctor_get(v_ys_625_, 1);
lean_inc(v_tail_631_);
lean_dec_ref_known(v_ys_625_, 2);
v___x_632_ = lean_apply_2(v_h__2_627_, v_head_630_, v_tail_631_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_633_, lean_object* v_motive_634_, lean_object* v_ys_635_, lean_object* v_h__1_636_, lean_object* v_h__2_637_){
_start:
{
if (lean_obj_tag(v_ys_635_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_h__2_637_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_apply_1(v_h__1_636_, v___x_638_);
return v___x_639_;
}
else
{
lean_object* v_head_640_; lean_object* v_tail_641_; lean_object* v___x_642_; 
lean_dec(v_h__1_636_);
v_head_640_ = lean_ctor_get(v_ys_635_, 0);
lean_inc(v_head_640_);
v_tail_641_ = lean_ctor_get(v_ys_635_, 1);
lean_inc(v_tail_641_);
lean_dec_ref_known(v_ys_635_, 2);
v___x_642_ = lean_apply_2(v_h__2_637_, v_head_640_, v_tail_641_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_h__1_645_, lean_object* v_h__2_646_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_object* v___x_647_; 
lean_dec(v_h__2_646_);
v___x_647_ = lean_apply_1(v_h__1_645_, v_x_644_);
return v___x_647_;
}
else
{
lean_object* v_head_648_; lean_object* v_tail_649_; lean_object* v___x_650_; 
lean_dec(v_h__1_645_);
v_head_648_ = lean_ctor_get(v_x_643_, 0);
lean_inc(v_head_648_);
v_tail_649_ = lean_ctor_get(v_x_643_, 1);
lean_inc(v_tail_649_);
lean_dec_ref_known(v_x_643_, 2);
v___x_650_ = lean_apply_3(v_h__2_646_, v_head_648_, v_tail_649_, v_x_644_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(lean_object* v_00_u03b1_651_, lean_object* v_motive_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_h__1_655_, lean_object* v_h__2_656_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
lean_object* v___x_657_; 
lean_dec(v_h__2_656_);
v___x_657_ = lean_apply_1(v_h__1_655_, v_x_654_);
return v___x_657_;
}
else
{
lean_object* v_head_658_; lean_object* v_tail_659_; lean_object* v___x_660_; 
lean_dec(v_h__1_655_);
v_head_658_ = lean_ctor_get(v_x_653_, 0);
lean_inc(v_head_658_);
v_tail_659_ = lean_ctor_get(v_x_653_, 1);
lean_inc(v_tail_659_);
lean_dec_ref_known(v_x_653_, 2);
v___x_660_ = lean_apply_3(v_h__2_656_, v_head_658_, v_tail_659_, v_x_654_);
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object* v_f_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
if (lean_obj_tag(v_a_662_) == 0)
{
lean_object* v___x_664_; 
lean_dec(v_f_661_);
v___x_664_ = l_List_reverse___redArg(v_a_663_);
return v___x_664_;
}
else
{
lean_object* v_head_665_; lean_object* v_tail_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_675_; 
v_head_665_ = lean_ctor_get(v_a_662_, 0);
v_tail_666_ = lean_ctor_get(v_a_662_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_a_662_);
if (v_isSharedCheck_675_ == 0)
{
v___x_668_ = v_a_662_;
v_isShared_669_ = v_isSharedCheck_675_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_tail_666_);
lean_inc(v_head_665_);
lean_dec(v_a_662_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_675_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
lean_inc(v_f_661_);
v___x_670_ = lean_apply_1(v_f_661_, v_head_665_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v_a_663_);
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_a_663_);
v___x_672_ = v_reuseFailAlloc_674_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
v_a_662_ = v_tail_666_;
v_a_663_ = v___x_672_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_f_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_List_mapTR_loop___redArg(v_f_678_, v_a_679_, v_a_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object* v_f_682_, lean_object* v_as_683_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_box(0);
v___x_685_ = l_List_mapTR_loop___redArg(v_f_682_, v_as_683_, v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR(lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_f_688_, lean_object* v_as_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_box(0);
v___x_691_ = l_List_mapTR_loop___redArg(v_f_688_, v_as_689_, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_h__1_694_, lean_object* v_h__2_695_){
_start:
{
if (lean_obj_tag(v_x_692_) == 0)
{
lean_object* v___x_696_; 
lean_dec(v_h__2_695_);
v___x_696_ = lean_apply_1(v_h__1_694_, v_x_693_);
return v___x_696_;
}
else
{
lean_object* v_head_697_; lean_object* v_tail_698_; lean_object* v___x_699_; 
lean_dec(v_h__1_694_);
v_head_697_ = lean_ctor_get(v_x_692_, 0);
lean_inc(v_head_697_);
v_tail_698_ = lean_ctor_get(v_x_692_, 1);
lean_inc(v_tail_698_);
lean_dec_ref_known(v_x_692_, 2);
v___x_699_ = lean_apply_3(v_h__2_695_, v_head_697_, v_tail_698_, v_x_693_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(lean_object* v_00_u03b1_700_, lean_object* v_00_u03b2_701_, lean_object* v_motive_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_h__1_705_, lean_object* v_h__2_706_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v___x_707_; 
lean_dec(v_h__2_706_);
v___x_707_ = lean_apply_1(v_h__1_705_, v_x_704_);
return v___x_707_;
}
else
{
lean_object* v_head_708_; lean_object* v_tail_709_; lean_object* v___x_710_; 
lean_dec(v_h__1_705_);
v_head_708_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_head_708_);
v_tail_709_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_tail_709_);
lean_dec_ref_known(v_x_703_, 2);
v___x_710_ = lean_apply_3(v_h__2_706_, v_head_708_, v_tail_709_, v_x_704_);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object* v_p_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
if (lean_obj_tag(v_a_712_) == 0)
{
lean_object* v___x_714_; 
lean_dec_ref(v_p_711_);
v___x_714_ = l_List_reverse___redArg(v_a_713_);
return v___x_714_;
}
else
{
lean_object* v_head_715_; lean_object* v_tail_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_727_; 
v_head_715_ = lean_ctor_get(v_a_712_, 0);
v_tail_716_ = lean_ctor_get(v_a_712_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_727_ == 0)
{
v___x_718_ = v_a_712_;
v_isShared_719_ = v_isSharedCheck_727_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_tail_716_);
lean_inc(v_head_715_);
lean_dec(v_a_712_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_727_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; uint8_t v___x_721_; 
lean_inc_ref(v_p_711_);
lean_inc(v_head_715_);
v___x_720_ = lean_apply_1(v_p_711_, v_head_715_);
v___x_721_ = lean_unbox(v___x_720_);
if (v___x_721_ == 0)
{
lean_del_object(v___x_718_);
lean_dec(v_head_715_);
v_a_712_ = v_tail_716_;
goto _start;
}
else
{
lean_object* v___x_724_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v_a_713_);
v___x_724_ = v___x_718_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_head_715_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_a_713_);
v___x_724_ = v_reuseFailAlloc_726_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
v_a_712_ = v_tail_716_;
v_a_713_ = v___x_724_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object* v_00_u03b1_728_, lean_object* v_p_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_List_filterTR_loop___redArg(v_p_729_, v_a_730_, v_a_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object* v_p_733_, lean_object* v_as_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_box(0);
v___x_736_ = l_List_filterTR_loop___redArg(v_p_733_, v_as_734_, v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR(lean_object* v_00_u03b1_737_, lean_object* v_p_738_, lean_object* v_as_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_box(0);
v___x_741_ = l_List_filterTR_loop___redArg(v_p_738_, v_as_739_, v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(uint8_t v_x_742_, lean_object* v_h__1_743_, lean_object* v_h__2_744_){
_start:
{
if (v_x_742_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec(v_h__1_743_);
v___x_745_ = lean_box(0);
v___x_746_ = lean_apply_1(v_h__2_744_, v___x_745_);
return v___x_746_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v_h__2_744_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_apply_1(v_h__1_743_, v___x_747_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_749_, lean_object* v_h__1_750_, lean_object* v_h__2_751_){
_start:
{
uint8_t v_x_24__boxed_752_; lean_object* v_res_753_; 
v_x_24__boxed_752_ = lean_unbox(v_x_749_);
v_res_753_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_752_, v_h__1_750_, v_h__2_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object* v_motive_754_, uint8_t v_x_755_, lean_object* v_h__1_756_, lean_object* v_h__2_757_){
_start:
{
if (v_x_755_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v_h__1_756_);
v___x_758_ = lean_box(0);
v___x_759_ = lean_apply_1(v_h__2_757_, v___x_758_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v_h__2_757_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_apply_1(v_h__1_756_, v___x_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_762_, lean_object* v_x_763_, lean_object* v_h__1_764_, lean_object* v_h__2_765_){
_start:
{
uint8_t v_x_35__boxed_766_; lean_object* v_res_767_; 
v_x_35__boxed_766_ = lean_unbox(v_x_763_);
v_res_767_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(v_motive_762_, v_x_35__boxed_766_, v_h__1_764_, v_h__2_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_768_, lean_object* v_h__1_769_, lean_object* v_h__2_770_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec(v_h__2_770_);
v___x_771_ = lean_box(0);
v___x_772_ = lean_apply_1(v_h__1_769_, v___x_771_);
return v___x_772_;
}
else
{
lean_object* v_head_773_; lean_object* v_tail_774_; lean_object* v___x_775_; 
lean_dec(v_h__1_769_);
v_head_773_ = lean_ctor_get(v_x_768_, 0);
lean_inc(v_head_773_);
v_tail_774_ = lean_ctor_get(v_x_768_, 1);
lean_inc(v_tail_774_);
lean_dec_ref_known(v_x_768_, 2);
v___x_775_ = lean_apply_2(v_h__2_770_, v_head_773_, v_tail_774_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_776_, lean_object* v_motive_777_, lean_object* v_x_778_, lean_object* v_h__1_779_, lean_object* v_h__2_780_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec(v_h__2_780_);
v___x_781_ = lean_box(0);
v___x_782_ = lean_apply_1(v_h__1_779_, v___x_781_);
return v___x_782_;
}
else
{
lean_object* v_head_783_; lean_object* v_tail_784_; lean_object* v___x_785_; 
lean_dec(v_h__1_779_);
v_head_783_ = lean_ctor_get(v_x_778_, 0);
lean_inc(v_head_783_);
v_tail_784_ = lean_ctor_get(v_x_778_, 1);
lean_inc(v_tail_784_);
lean_dec_ref_known(v_x_778_, 2);
v___x_785_ = lean_apply_2(v_h__2_780_, v_head_783_, v_tail_784_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_zero_789_; uint8_t v_isZero_790_; 
v_zero_789_ = lean_unsigned_to_nat(0u);
v_isZero_790_ = lean_nat_dec_eq(v_a_787_, v_zero_789_);
if (v_isZero_790_ == 1)
{
lean_dec(v_a_787_);
lean_dec(v_a_786_);
return v_a_788_;
}
else
{
lean_object* v_one_791_; lean_object* v_n_792_; lean_object* v___x_793_; 
v_one_791_ = lean_unsigned_to_nat(1u);
v_n_792_ = lean_nat_sub(v_a_787_, v_one_791_);
lean_dec(v_a_787_);
lean_inc(v_a_786_);
v___x_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_793_, 0, v_a_786_);
lean_ctor_set(v___x_793_, 1, v_a_788_);
v_a_787_ = v_n_792_;
v_a_788_ = v___x_793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object* v_00_u03b1_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_List_replicateTR_loop___redArg(v_a_796_, v_a_797_, v_a_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object* v_n_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_box(0);
v___x_803_ = l_List_replicateTR_loop___redArg(v_a_801_, v_n_800_, v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object* v_00_u03b1_804_, lean_object* v_n_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_List_replicateTR___redArg(v_n_805_, v_a_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_h__1_810_, lean_object* v_h__2_811_){
_start:
{
lean_object* v_zero_812_; uint8_t v_isZero_813_; 
v_zero_812_ = lean_unsigned_to_nat(0u);
v_isZero_813_ = lean_nat_dec_eq(v_x_808_, v_zero_812_);
if (v_isZero_813_ == 1)
{
lean_object* v___x_814_; 
lean_dec(v_h__2_811_);
v___x_814_ = lean_apply_1(v_h__1_810_, v_x_809_);
return v___x_814_;
}
else
{
lean_object* v_one_815_; lean_object* v_n_816_; lean_object* v___x_817_; 
lean_dec(v_h__1_810_);
v_one_815_ = lean_unsigned_to_nat(1u);
v_n_816_ = lean_nat_sub(v_x_808_, v_one_815_);
v___x_817_ = lean_apply_2(v_h__2_811_, v_n_816_, v_x_809_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_h__1_820_, lean_object* v_h__2_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(v_x_818_, v_x_819_, v_h__1_820_, v_h__2_821_);
lean_dec(v_x_818_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(lean_object* v_00_u03b1_823_, lean_object* v_motive_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_h__1_827_, lean_object* v_h__2_828_){
_start:
{
lean_object* v_zero_829_; uint8_t v_isZero_830_; 
v_zero_829_ = lean_unsigned_to_nat(0u);
v_isZero_830_ = lean_nat_dec_eq(v_x_825_, v_zero_829_);
if (v_isZero_830_ == 1)
{
lean_object* v___x_831_; 
lean_dec(v_h__2_828_);
v___x_831_ = lean_apply_1(v_h__1_827_, v_x_826_);
return v___x_831_;
}
else
{
lean_object* v_one_832_; lean_object* v_n_833_; lean_object* v___x_834_; 
lean_dec(v_h__1_827_);
v_one_832_ = lean_unsigned_to_nat(1u);
v_n_833_ = lean_nat_sub(v_x_825_, v_one_832_);
v___x_834_ = lean_apply_2(v_h__2_828_, v_n_833_, v_x_826_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_835_, lean_object* v_motive_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_h__1_839_, lean_object* v_h__2_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(v_00_u03b1_835_, v_motive_836_, v_x_837_, v_x_838_, v_h__1_839_, v_h__2_840_);
lean_dec(v_x_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_h__1_844_, lean_object* v_h__2_845_){
_start:
{
lean_object* v_zero_846_; uint8_t v_isZero_847_; 
v_zero_846_ = lean_unsigned_to_nat(0u);
v_isZero_847_ = lean_nat_dec_eq(v_x_842_, v_zero_846_);
if (v_isZero_847_ == 1)
{
lean_object* v___x_848_; 
lean_dec(v_h__2_845_);
v___x_848_ = lean_apply_1(v_h__1_844_, v_x_843_);
return v___x_848_;
}
else
{
lean_object* v_one_849_; lean_object* v_n_850_; lean_object* v___x_851_; 
lean_dec(v_h__1_844_);
v_one_849_ = lean_unsigned_to_nat(1u);
v_n_850_ = lean_nat_sub(v_x_842_, v_one_849_);
v___x_851_ = lean_apply_2(v_h__2_845_, v_n_850_, v_x_843_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_h__1_854_, lean_object* v_h__2_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(v_x_852_, v_x_853_, v_h__1_854_, v_h__2_855_);
lean_dec(v_x_852_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(lean_object* v_00_u03b1_857_, lean_object* v_motive_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_h__1_861_, lean_object* v_h__2_862_){
_start:
{
lean_object* v_zero_863_; uint8_t v_isZero_864_; 
v_zero_863_ = lean_unsigned_to_nat(0u);
v_isZero_864_ = lean_nat_dec_eq(v_x_859_, v_zero_863_);
if (v_isZero_864_ == 1)
{
lean_object* v___x_865_; 
lean_dec(v_h__2_862_);
v___x_865_ = lean_apply_1(v_h__1_861_, v_x_860_);
return v___x_865_;
}
else
{
lean_object* v_one_866_; lean_object* v_n_867_; lean_object* v___x_868_; 
lean_dec(v_h__1_861_);
v_one_866_ = lean_unsigned_to_nat(1u);
v_n_867_ = lean_nat_sub(v_x_859_, v_one_866_);
v___x_868_ = lean_apply_2(v_h__2_862_, v_n_867_, v_x_860_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___boxed(lean_object* v_00_u03b1_869_, lean_object* v_motive_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_h__1_873_, lean_object* v_h__2_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(v_00_u03b1_869_, v_motive_870_, v_x_871_, v_x_872_, v_h__1_873_, v_h__2_874_);
lean_dec(v_x_871_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg(lean_object* v_n_876_, lean_object* v_a_877_, lean_object* v_l_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = l_List_lengthTR___redArg(v_l_878_);
v___x_880_ = lean_nat_sub(v_n_876_, v___x_879_);
lean_dec(v___x_879_);
v___x_881_ = l_List_replicateTR_loop___redArg(v_a_877_, v___x_880_, v_l_878_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg___boxed(lean_object* v_n_882_, lean_object* v_a_883_, lean_object* v_l_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_List_leftpadTR___redArg(v_n_882_, v_a_883_, v_l_884_);
lean_dec(v_n_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object* v_00_u03b1_886_, lean_object* v_n_887_, lean_object* v_a_888_, lean_object* v_l_889_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = l_List_lengthTR___redArg(v_l_889_);
v___x_891_ = lean_nat_sub(v_n_887_, v___x_890_);
lean_dec(v___x_890_);
v___x_892_ = l_List_replicateTR_loop___redArg(v_a_888_, v___x_891_, v_l_889_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___boxed(lean_object* v_00_u03b1_893_, lean_object* v_n_894_, lean_object* v_a_895_, lean_object* v_l_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_List_leftpadTR(v_00_u03b1_893_, v_n_894_, v_a_895_, v_l_896_);
lean_dec(v_n_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg(lean_object* v_n_898_, lean_object* v_a_899_, lean_object* v_l_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_901_ = l_List_lengthTR___redArg(v_l_900_);
v___x_902_ = lean_nat_sub(v_n_898_, v___x_901_);
lean_dec(v___x_901_);
v___x_903_ = l_List_replicateTR___redArg(v___x_902_, v_a_899_);
v___x_904_ = l_List_appendTR___redArg(v_l_900_, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg___boxed(lean_object* v_n_905_, lean_object* v_a_906_, lean_object* v_l_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_List_rightpad___redArg(v_n_905_, v_a_906_, v_l_907_);
lean_dec(v_n_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad(lean_object* v_00_u03b1_909_, lean_object* v_n_910_, lean_object* v_a_911_, lean_object* v_l_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_List_rightpad___redArg(v_n_910_, v_a_911_, v_l_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___boxed(lean_object* v_00_u03b1_914_, lean_object* v_n_915_, lean_object* v_a_916_, lean_object* v_l_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_List_rightpad(v_00_u03b1_914_, v_n_915_, v_a_916_, v_l_917_);
lean_dec(v_n_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = lean_box(0);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg___boxed(lean_object* v___dummy_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_List_instEmptyCollection___redArg();
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object* v_00_u03b1_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_box(0);
return v___x_924_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty___redArg(lean_object* v_x_925_){
_start:
{
if (lean_obj_tag(v_x_925_) == 0)
{
uint8_t v___x_926_; 
v___x_926_ = 1;
return v___x_926_;
}
else
{
uint8_t v___x_927_; 
v___x_927_ = 0;
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___redArg___boxed(lean_object* v_x_928_){
_start:
{
uint8_t v_res_929_; lean_object* v_r_930_; 
v_res_929_ = l_List_isEmpty___redArg(v_x_928_);
lean_dec(v_x_928_);
v_r_930_ = lean_box(v_res_929_);
return v_r_930_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty(lean_object* v_00_u03b1_931_, lean_object* v_x_932_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = l_List_isEmpty___redArg(v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___boxed(lean_object* v_00_u03b1_934_, lean_object* v_x_935_){
_start:
{
uint8_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = l_List_isEmpty(v_00_u03b1_934_, v_x_935_);
lean_dec(v_x_935_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT uint8_t l_List_elem___redArg(lean_object* v_inst_938_, lean_object* v_a_939_, lean_object* v_x_940_){
_start:
{
if (lean_obj_tag(v_x_940_) == 0)
{
uint8_t v___x_941_; 
lean_dec(v_a_939_);
lean_dec_ref(v_inst_938_);
v___x_941_ = 0;
return v___x_941_;
}
else
{
lean_object* v_head_942_; lean_object* v_tail_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_head_942_ = lean_ctor_get(v_x_940_, 0);
lean_inc(v_head_942_);
v_tail_943_ = lean_ctor_get(v_x_940_, 1);
lean_inc(v_tail_943_);
lean_dec_ref_known(v_x_940_, 2);
lean_inc_ref(v_inst_938_);
lean_inc(v_a_939_);
v___x_944_ = lean_apply_2(v_inst_938_, v_a_939_, v_head_942_);
v___x_945_ = lean_unbox(v___x_944_);
if (v___x_945_ == 0)
{
v_x_940_ = v_tail_943_;
goto _start;
}
else
{
uint8_t v___x_947_; 
lean_dec(v_tail_943_);
lean_dec(v_a_939_);
lean_dec_ref(v_inst_938_);
v___x_947_ = lean_unbox(v___x_944_);
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___redArg___boxed(lean_object* v_inst_948_, lean_object* v_a_949_, lean_object* v_x_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_List_elem___redArg(v_inst_948_, v_a_949_, v_x_950_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT uint8_t l_List_elem(lean_object* v_00_u03b1_953_, lean_object* v_inst_954_, lean_object* v_a_955_, lean_object* v_x_956_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = l_List_elem___redArg(v_inst_954_, v_a_955_, v_x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_List_elem___boxed(lean_object* v_00_u03b1_958_, lean_object* v_inst_959_, lean_object* v_a_960_, lean_object* v_x_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l_List_elem(v_00_u03b1_958_, v_inst_959_, v_a_960_, v_x_961_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT uint8_t l_List_contains___redArg(lean_object* v_inst_964_, lean_object* v_as_965_, lean_object* v_a_966_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = l_List_elem___redArg(v_inst_964_, v_a_966_, v_as_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_List_contains___redArg___boxed(lean_object* v_inst_968_, lean_object* v_as_969_, lean_object* v_a_970_){
_start:
{
uint8_t v_res_971_; lean_object* v_r_972_; 
v_res_971_ = l_List_contains___redArg(v_inst_968_, v_as_969_, v_a_970_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
LEAN_EXPORT uint8_t l_List_contains(lean_object* v_00_u03b1_973_, lean_object* v_inst_974_, lean_object* v_as_975_, lean_object* v_a_976_){
_start:
{
uint8_t v___x_977_; 
v___x_977_ = l_List_elem___redArg(v_inst_974_, v_a_976_, v_as_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_List_contains___boxed(lean_object* v_00_u03b1_978_, lean_object* v_inst_979_, lean_object* v_as_980_, lean_object* v_a_981_){
_start:
{
uint8_t v_res_982_; lean_object* v_r_983_; 
v_res_982_ = l_List_contains(v_00_u03b1_978_, v_inst_979_, v_as_980_, v_a_981_);
v_r_983_ = lean_box(v_res_982_);
return v_r_983_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership___redArg(){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = lean_box(0);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership___redArg___boxed(lean_object* v___dummy_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_List_instMembership___redArg();
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership(lean_object* v_00_u03b1_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = lean_box(0);
return v___x_989_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_990_, lean_object* v_a_991_, lean_object* v_as_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = l_List_elem___redArg(v_inst_990_, v_a_991_, v_as_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_994_, lean_object* v_a_995_, lean_object* v_as_996_){
_start:
{
uint8_t v_res_997_; lean_object* v_r_998_; 
v_res_997_ = l_List_instDecidableMemOfLawfulBEq___redArg(v_inst_994_, v_a_995_, v_as_996_);
v_r_998_ = lean_box(v_res_997_);
return v_r_998_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_a_1002_, lean_object* v_as_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = l_List_elem___redArg(v_inst_1000_, v_a_1002_, v_as_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_a_1008_, lean_object* v_as_1009_){
_start:
{
uint8_t v_res_1010_; lean_object* v_r_1011_; 
v_res_1010_ = l_List_instDecidableMemOfLawfulBEq(v_00_u03b1_1005_, v_inst_1006_, v_inst_1007_, v_a_1008_, v_as_1009_);
v_r_1011_ = lean_box(v_res_1010_);
return v_r_1011_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx___redArg(lean_object* v_inst_1012_, lean_object* v_x_1013_){
_start:
{
if (lean_obj_tag(v_x_1013_) == 0)
{
uint8_t v___x_1014_; 
lean_dec_ref(v_inst_1012_);
v___x_1014_ = 0;
return v___x_1014_;
}
else
{
lean_object* v_head_1015_; lean_object* v_tail_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_head_1015_ = lean_ctor_get(v_x_1013_, 0);
lean_inc(v_head_1015_);
v_tail_1016_ = lean_ctor_get(v_x_1013_, 1);
lean_inc(v_tail_1016_);
lean_dec_ref_known(v_x_1013_, 2);
lean_inc_ref(v_inst_1012_);
v___x_1017_ = lean_apply_1(v_inst_1012_, v_head_1015_);
v___x_1018_ = lean_unbox(v___x_1017_);
if (v___x_1018_ == 0)
{
uint8_t v_decide_1019_; 
v_decide_1019_ = l_List_decidableBEx___redArg(v_inst_1012_, v_tail_1016_);
if (v_decide_1019_ == 0)
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_unbox(v___x_1017_);
return v___x_1020_;
}
else
{
return v_decide_1019_;
}
}
else
{
uint8_t v___x_1021_; 
lean_dec(v_tail_1016_);
lean_dec_ref(v_inst_1012_);
v___x_1021_ = lean_unbox(v___x_1017_);
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___redArg___boxed(lean_object* v_inst_1022_, lean_object* v_x_1023_){
_start:
{
uint8_t v_res_1024_; lean_object* v_r_1025_; 
v_res_1024_ = l_List_decidableBEx___redArg(v_inst_1022_, v_x_1023_);
v_r_1025_ = lean_box(v_res_1024_);
return v_r_1025_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx(lean_object* v_00_u03b1_1026_, lean_object* v_p_1027_, lean_object* v_inst_1028_, lean_object* v_x_1029_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = l_List_decidableBEx___redArg(v_inst_1028_, v_x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___boxed(lean_object* v_00_u03b1_1031_, lean_object* v_p_1032_, lean_object* v_inst_1033_, lean_object* v_x_1034_){
_start:
{
uint8_t v_res_1035_; lean_object* v_r_1036_; 
v_res_1035_ = l_List_decidableBEx(v_00_u03b1_1031_, v_p_1032_, v_inst_1033_, v_x_1034_);
v_r_1036_ = lean_box(v_res_1035_);
return v_r_1036_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll___redArg(lean_object* v_inst_1037_, lean_object* v_x_1038_){
_start:
{
if (lean_obj_tag(v_x_1038_) == 0)
{
uint8_t v___x_1039_; 
lean_dec_ref(v_inst_1037_);
v___x_1039_ = 1;
return v___x_1039_;
}
else
{
lean_object* v_head_1040_; lean_object* v_tail_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v_head_1040_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_head_1040_);
v_tail_1041_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_tail_1041_);
lean_dec_ref_known(v_x_1038_, 2);
lean_inc_ref(v_inst_1037_);
v___x_1042_ = lean_apply_1(v_inst_1037_, v_head_1040_);
v___x_1043_ = lean_unbox(v___x_1042_);
if (v___x_1043_ == 0)
{
uint8_t v___x_1044_; 
lean_dec(v_tail_1041_);
lean_dec_ref(v_inst_1037_);
v___x_1044_ = lean_unbox(v___x_1042_);
return v___x_1044_;
}
else
{
uint8_t v_decide_1045_; 
v_decide_1045_ = l_List_decidableBAll___redArg(v_inst_1037_, v_tail_1041_);
if (v_decide_1045_ == 0)
{
return v_decide_1045_;
}
else
{
uint8_t v___x_1046_; 
v___x_1046_ = lean_unbox(v___x_1042_);
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___redArg___boxed(lean_object* v_inst_1047_, lean_object* v_x_1048_){
_start:
{
uint8_t v_res_1049_; lean_object* v_r_1050_; 
v_res_1049_ = l_List_decidableBAll___redArg(v_inst_1047_, v_x_1048_);
v_r_1050_ = lean_box(v_res_1049_);
return v_r_1050_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll(lean_object* v_00_u03b1_1051_, lean_object* v_p_1052_, lean_object* v_inst_1053_, lean_object* v_x_1054_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = l_List_decidableBAll___redArg(v_inst_1053_, v_x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___boxed(lean_object* v_00_u03b1_1056_, lean_object* v_p_1057_, lean_object* v_inst_1058_, lean_object* v_x_1059_){
_start:
{
uint8_t v_res_1060_; lean_object* v_r_1061_; 
v_res_1060_ = l_List_decidableBAll(v_00_u03b1_1056_, v_p_1057_, v_inst_1058_, v_x_1059_);
v_r_1061_ = lean_box(v_res_1060_);
return v_r_1061_;
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg(lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
lean_object* v_zero_1064_; uint8_t v_isZero_1065_; 
v_zero_1064_ = lean_unsigned_to_nat(0u);
v_isZero_1065_ = lean_nat_dec_eq(v_x_1062_, v_zero_1064_);
if (v_isZero_1065_ == 1)
{
lean_dec(v_x_1062_);
lean_inc(v_x_1063_);
return v_x_1063_;
}
else
{
if (lean_obj_tag(v_x_1063_) == 0)
{
lean_dec(v_x_1062_);
return v_x_1063_;
}
else
{
lean_object* v_tail_1066_; lean_object* v_one_1067_; lean_object* v_n_1068_; 
v_tail_1066_ = lean_ctor_get(v_x_1063_, 1);
v_one_1067_ = lean_unsigned_to_nat(1u);
v_n_1068_ = lean_nat_sub(v_x_1062_, v_one_1067_);
lean_dec(v_x_1062_);
v_x_1062_ = v_n_1068_;
v_x_1063_ = v_tail_1066_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg___boxed(lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_List_drop___redArg(v_x_1070_, v_x_1071_);
lean_dec(v_x_1071_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_List_drop(lean_object* v_00_u03b1_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_List_drop___redArg(v_x_1074_, v_x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_List_drop___boxed(lean_object* v_00_u03b1_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_List_drop(v_00_u03b1_1077_, v_x_1078_, v_x_1079_);
lean_dec(v_x_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___redArg(lean_object* v_p_1081_, lean_object* v_x_1082_){
_start:
{
if (lean_obj_tag(v_x_1082_) == 0)
{
lean_dec_ref(v_p_1081_);
return v_x_1082_;
}
else
{
lean_object* v_head_1083_; lean_object* v_tail_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_head_1083_ = lean_ctor_get(v_x_1082_, 0);
v_tail_1084_ = lean_ctor_get(v_x_1082_, 1);
lean_inc_ref(v_p_1081_);
lean_inc(v_head_1083_);
v___x_1085_ = lean_apply_1(v_p_1081_, v_head_1083_);
v___x_1086_ = lean_unbox(v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec_ref(v_p_1081_);
return v_x_1082_;
}
else
{
lean_inc(v_tail_1084_);
lean_dec_ref_known(v_x_1082_, 2);
v_x_1082_ = v_tail_1084_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object* v_00_u03b1_1088_, lean_object* v_p_1089_, lean_object* v_x_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_List_dropWhile___redArg(v_p_1089_, v_x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___redArg(lean_object* v_p_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
if (lean_obj_tag(v_a_1093_) == 0)
{
lean_object* v_fst_1095_; lean_object* v_snd_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_p_1092_);
v_fst_1095_ = lean_ctor_get(v_a_1094_, 0);
v_snd_1096_ = lean_ctor_get(v_a_1094_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_a_1094_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1098_ = v_a_1094_;
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_snd_1096_);
lean_inc(v_fst_1095_);
lean_dec(v_a_1094_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1100_ = l_List_reverse___redArg(v_fst_1095_);
v___x_1101_ = l_List_reverse___redArg(v_snd_1096_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1101_);
lean_ctor_set(v___x_1098_, 0, v___x_1100_);
v___x_1103_ = v___x_1098_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
else
{
lean_object* v_head_1106_; lean_object* v_tail_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1133_; 
v_head_1106_ = lean_ctor_get(v_a_1093_, 0);
v_tail_1107_ = lean_ctor_get(v_a_1093_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_a_1093_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1109_ = v_a_1093_;
v_isShared_1110_ = v_isSharedCheck_1133_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_tail_1107_);
lean_inc(v_head_1106_);
lean_dec(v_a_1093_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1133_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_fst_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1132_; 
v_fst_1111_ = lean_ctor_get(v_a_1094_, 0);
v_snd_1112_ = lean_ctor_get(v_a_1094_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_a_1094_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1114_ = v_a_1094_;
v_isShared_1115_ = v_isSharedCheck_1132_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_inc(v_fst_1111_);
lean_dec(v_a_1094_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1132_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
lean_inc_ref(v_p_1092_);
lean_inc(v_head_1106_);
v___x_1116_ = lean_apply_1(v_p_1092_, v_head_1106_);
v___x_1117_ = lean_unbox(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1119_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v_snd_1112_);
v___x_1119_ = v___x_1109_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_head_1106_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_snd_1112_);
v___x_1119_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1119_);
v___x_1121_ = v___x_1114_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_fst_1111_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
v_a_1093_ = v_tail_1107_;
v_a_1094_ = v___x_1121_;
goto _start;
}
}
}
else
{
lean_object* v___x_1126_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v_fst_1111_);
v___x_1126_ = v___x_1109_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_head_1106_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_fst_1111_);
v___x_1126_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1128_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1126_);
v___x_1128_ = v___x_1114_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_snd_1112_);
v___x_1128_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
v_a_1093_ = v_tail_1107_;
v_a_1094_ = v___x_1128_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object* v_00_u03b1_1134_, lean_object* v_p_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_List_partition_loop___redArg(v_p_1135_, v_a_1136_, v_a_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_List_partition___redArg(lean_object* v_p_1141_, lean_object* v_as_1142_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1144_ = l_List_partition_loop___redArg(v_p_1141_, v_as_1142_, v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_List_partition(lean_object* v_00_u03b1_1145_, lean_object* v_p_1146_, lean_object* v_as_1147_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1149_ = l_List_partition_loop___redArg(v_p_1146_, v_as_1147_, v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_1150_, lean_object* v_h__1_1151_, lean_object* v_h__2_1152_, lean_object* v_h__3_1153_){
_start:
{
if (lean_obj_tag(v_x_1150_) == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_h__3_1153_);
lean_dec(v_h__2_1152_);
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_apply_1(v_h__1_1151_, v___x_1154_);
return v___x_1155_;
}
else
{
lean_object* v_tail_1156_; 
lean_dec(v_h__1_1151_);
v_tail_1156_ = lean_ctor_get(v_x_1150_, 1);
if (lean_obj_tag(v_tail_1156_) == 0)
{
lean_object* v_head_1157_; lean_object* v___x_1158_; 
lean_dec(v_h__3_1153_);
v_head_1157_ = lean_ctor_get(v_x_1150_, 0);
lean_inc(v_head_1157_);
lean_dec_ref_known(v_x_1150_, 2);
v___x_1158_ = lean_apply_1(v_h__2_1152_, v_head_1157_);
return v___x_1158_;
}
else
{
lean_object* v_head_1159_; lean_object* v___x_1160_; 
lean_inc_ref(v_tail_1156_);
lean_dec(v_h__2_1152_);
v_head_1159_ = lean_ctor_get(v_x_1150_, 0);
lean_inc(v_head_1159_);
lean_dec_ref_known(v_x_1150_, 2);
v___x_1160_ = lean_apply_3(v_h__3_1153_, v_head_1159_, v_tail_1156_, lean_box(0));
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_1161_, lean_object* v_motive_1162_, lean_object* v_x_1163_, lean_object* v_h__1_1164_, lean_object* v_h__2_1165_, lean_object* v_h__3_1166_){
_start:
{
if (lean_obj_tag(v_x_1163_) == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_h__3_1166_);
lean_dec(v_h__2_1165_);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_apply_1(v_h__1_1164_, v___x_1167_);
return v___x_1168_;
}
else
{
lean_object* v_tail_1169_; 
lean_dec(v_h__1_1164_);
v_tail_1169_ = lean_ctor_get(v_x_1163_, 1);
if (lean_obj_tag(v_tail_1169_) == 0)
{
lean_object* v_head_1170_; lean_object* v___x_1171_; 
lean_dec(v_h__3_1166_);
v_head_1170_ = lean_ctor_get(v_x_1163_, 0);
lean_inc(v_head_1170_);
lean_dec_ref_known(v_x_1163_, 2);
v___x_1171_ = lean_apply_1(v_h__2_1165_, v_head_1170_);
return v___x_1171_;
}
else
{
lean_object* v_head_1172_; lean_object* v___x_1173_; 
lean_inc_ref(v_tail_1169_);
lean_dec(v_h__2_1165_);
v_head_1172_ = lean_ctor_get(v_x_1163_, 0);
lean_inc(v_head_1172_);
lean_dec_ref_known(v_x_1163_, 2);
v___x_1173_ = lean_apply_3(v_h__3_1166_, v_head_1172_, v_tail_1169_, lean_box(0));
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg(){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_box(0);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg___boxed(lean_object* v___dummy_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_List_instHasSubset___redArg();
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object* v_00_u03b1_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_box(0);
return v___x_1179_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(lean_object* v___f_1180_, lean_object* v_x_1181_, lean_object* v_a_1182_){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = l_List_elem___redArg(v___f_1180_, v_a_1182_, v_x_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(lean_object* v___f_1184_, lean_object* v_x_1185_, lean_object* v_a_1186_){
_start:
{
uint8_t v_res_1187_; lean_object* v_r_1188_; 
v_res_1187_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(v___f_1184_, v_x_1185_, v_a_1186_);
v_r_1188_ = lean_box(v_res_1187_);
return v_r_1188_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg(lean_object* v_inst_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_){
_start:
{
lean_object* v___f_1192_; lean_object* v___f_1193_; uint8_t v___x_1194_; 
v___f_1192_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1192_, 0, v_inst_1189_);
v___f_1193_ = lean_alloc_closure((void*)(l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1193_, 0, v___f_1192_);
lean_closure_set(v___f_1193_, 1, v_x_1191_);
v___x_1194_ = l_List_decidableBAll___redArg(v___f_1193_, v_x_1190_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(lean_object* v_inst_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
uint8_t v_res_1198_; lean_object* v_r_1199_; 
v_res_1198_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1195_, v_x_1196_, v_x_1197_);
v_r_1199_ = lean_box(v_res_1198_);
return v_r_1199_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq(lean_object* v_00_u03b1_1200_, lean_object* v_inst_1201_, lean_object* v_x_1202_, lean_object* v_x_1203_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1201_, v_x_1202_, v_x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_inst_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
uint8_t v_res_1209_; lean_object* v_r_1210_; 
v_res_1209_ = l_List_instDecidableRelSubsetOfDecidableEq(v_00_u03b1_1205_, v_inst_1206_, v_x_1207_, v_x_1208_);
v_r_1210_ = lean_box(v_res_1209_);
return v_r_1210_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2));
v___x_1245_ = l_String_toRawSubstring_x27(v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object* v_x_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
lean_inc(v_x_1265_);
v___x_1269_ = l_Lean_Syntax_isOfKind(v_x_1265_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_x_1265_);
v___x_1270_ = lean_box(1);
v___x_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v_a_1267_);
return v___x_1271_;
}
else
{
lean_object* v_quotContext_1272_; lean_object* v_currMacroScope_1273_; lean_object* v_ref_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_quotContext_1272_ = lean_ctor_get(v_a_1266_, 1);
v_currMacroScope_1273_ = lean_ctor_get(v_a_1266_, 2);
v_ref_1274_ = lean_ctor_get(v_a_1266_, 5);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = l_Lean_Syntax_getArg(v_x_1265_, v___x_1275_);
v___x_1277_ = lean_unsigned_to_nat(2u);
v___x_1278_ = l_Lean_Syntax_getArg(v_x_1265_, v___x_1277_);
lean_dec(v_x_1265_);
v___x_1279_ = 0;
v___x_1280_ = l_Lean_SourceInfo_fromRef(v_ref_1274_, v___x_1279_);
v___x_1281_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1282_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
v___x_1283_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4));
lean_inc(v_currMacroScope_1273_);
lean_inc(v_quotContext_1272_);
v___x_1284_ = l_Lean_addMacroScope(v_quotContext_1272_, v___x_1283_, v_currMacroScope_1273_);
v___x_1285_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10));
lean_inc_n(v___x_1280_, 2);
v___x_1286_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1280_);
lean_ctor_set(v___x_1286_, 1, v___x_1282_);
lean_ctor_set(v___x_1286_, 2, v___x_1284_);
lean_ctor_set(v___x_1286_, 3, v___x_1285_);
v___x_1287_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1288_ = l_Lean_Syntax_node2(v___x_1280_, v___x_1287_, v___x_1276_, v___x_1278_);
v___x_1289_ = l_Lean_Syntax_node2(v___x_1280_, v___x_1281_, v___x_1286_, v___x_1288_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v_a_1267_);
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___boxed(lean_object* v_x_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(v_x_1291_, v_a_1292_, v_a_1293_);
lean_dec_ref(v_a_1292_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object* v_x_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1298_);
v___x_1302_ = l_Lean_Syntax_isOfKind(v_x_1298_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec(v_x_1298_);
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v_a_1300_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = l_Lean_Syntax_getArg(v_x_1298_, v___x_1305_);
v___x_1307_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1306_);
v___x_1308_ = l_Lean_Syntax_isOfKind(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec(v___x_1306_);
lean_dec(v_x_1298_);
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v_a_1300_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1311_ = lean_unsigned_to_nat(1u);
v___x_1312_ = l_Lean_Syntax_getArg(v_x_1298_, v___x_1311_);
lean_dec(v_x_1298_);
v___x_1313_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1312_);
v___x_1314_ = l_Lean_Syntax_matchesNull(v___x_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v___x_1312_);
lean_dec(v___x_1306_);
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v_a_1300_);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_ref_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1317_ = l_Lean_Syntax_getArg(v___x_1312_, v___x_1305_);
v___x_1318_ = l_Lean_Syntax_getArg(v___x_1312_, v___x_1311_);
lean_dec(v___x_1312_);
v_ref_1319_ = l_Lean_replaceRef(v___x_1306_, v_a_1299_);
lean_dec(v___x_1306_);
v___x_1320_ = 0;
v___x_1321_ = l_Lean_SourceInfo_fromRef(v_ref_1319_, v___x_1320_);
lean_dec(v_ref_1319_);
v___x_1322_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
v___x_1323_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__5));
lean_inc(v___x_1321_);
v___x_1324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1321_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = l_Lean_Syntax_node3(v___x_1321_, v___x_1322_, v___x_1317_, v___x_1324_, v___x_1318_);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v_a_1300_);
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object* v_x_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(v_x_1327_, v_a_1328_, v_a_1329_);
lean_dec(v_a_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist___redArg(lean_object* v_inst_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
if (lean_obj_tag(v_x_1332_) == 0)
{
uint8_t v___x_1334_; 
lean_dec(v_x_1333_);
lean_dec_ref(v_inst_1331_);
v___x_1334_ = 1;
return v___x_1334_;
}
else
{
if (lean_obj_tag(v_x_1333_) == 0)
{
uint8_t v___x_1335_; 
lean_dec_ref_known(v_x_1332_, 2);
lean_dec_ref(v_inst_1331_);
v___x_1335_ = 0;
return v___x_1335_;
}
else
{
lean_object* v_head_1336_; lean_object* v_tail_1337_; lean_object* v_head_1338_; lean_object* v_tail_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_head_1336_ = lean_ctor_get(v_x_1332_, 0);
v_tail_1337_ = lean_ctor_get(v_x_1332_, 1);
v_head_1338_ = lean_ctor_get(v_x_1333_, 0);
lean_inc(v_head_1338_);
v_tail_1339_ = lean_ctor_get(v_x_1333_, 1);
lean_inc(v_tail_1339_);
lean_dec_ref_known(v_x_1333_, 2);
lean_inc_ref(v_inst_1331_);
lean_inc(v_head_1336_);
v___x_1340_ = lean_apply_2(v_inst_1331_, v_head_1336_, v_head_1338_);
v___x_1341_ = lean_unbox(v___x_1340_);
if (v___x_1341_ == 0)
{
v_x_1333_ = v_tail_1339_;
goto _start;
}
else
{
lean_inc(v_tail_1337_);
lean_dec_ref_known(v_x_1332_, 2);
v_x_1332_ = v_tail_1337_;
v_x_1333_ = v_tail_1339_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSublist___redArg___boxed(lean_object* v_inst_1344_, lean_object* v_x_1345_, lean_object* v_x_1346_){
_start:
{
uint8_t v_res_1347_; lean_object* v_r_1348_; 
v_res_1347_ = l_List_isSublist___redArg(v_inst_1344_, v_x_1345_, v_x_1346_);
v_r_1348_ = lean_box(v_res_1347_);
return v_r_1348_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist(lean_object* v_00_u03b1_1349_, lean_object* v_inst_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = l_List_isSublist___redArg(v_inst_1350_, v_x_1351_, v_x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_List_isSublist___boxed(lean_object* v_00_u03b1_1354_, lean_object* v_inst_1355_, lean_object* v_x_1356_, lean_object* v_x_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = l_List_isSublist(v_00_u03b1_1354_, v_inst_1355_, v_x_1356_, v_x_1357_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0));
v___x_1378_ = l_String_toRawSubstring_x27(v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object* v_x_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
lean_inc(v_x_1390_);
v___x_1394_ = l_Lean_Syntax_isOfKind(v_x_1390_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec(v_x_1390_);
v___x_1395_ = lean_box(1);
v___x_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v_a_1392_);
return v___x_1396_;
}
else
{
lean_object* v_quotContext_1397_; lean_object* v_currMacroScope_1398_; lean_object* v_ref_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_quotContext_1397_ = lean_ctor_get(v_a_1391_, 1);
v_currMacroScope_1398_ = lean_ctor_get(v_a_1391_, 2);
v_ref_1399_ = lean_ctor_get(v_a_1391_, 5);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = l_Lean_Syntax_getArg(v_x_1390_, v___x_1400_);
v___x_1402_ = lean_unsigned_to_nat(2u);
v___x_1403_ = l_Lean_Syntax_getArg(v_x_1390_, v___x_1402_);
lean_dec(v_x_1390_);
v___x_1404_ = 0;
v___x_1405_ = l_Lean_SourceInfo_fromRef(v_ref_1399_, v___x_1404_);
v___x_1406_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1407_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
v___x_1408_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1398_);
lean_inc(v_quotContext_1397_);
v___x_1409_ = l_Lean_addMacroScope(v_quotContext_1397_, v___x_1408_, v_currMacroScope_1398_);
v___x_1410_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1405_, 2);
v___x_1411_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1405_);
lean_ctor_set(v___x_1411_, 1, v___x_1407_);
lean_ctor_set(v___x_1411_, 2, v___x_1409_);
lean_ctor_set(v___x_1411_, 3, v___x_1410_);
v___x_1412_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1413_ = l_Lean_Syntax_node2(v___x_1405_, v___x_1412_, v___x_1401_, v___x_1403_);
v___x_1414_ = l_Lean_Syntax_node2(v___x_1405_, v___x_1406_, v___x_1411_, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
lean_ctor_set(v___x_1415_, 1, v_a_1392_);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___boxed(lean_object* v_x_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(v_x_1416_, v_a_1417_, v_a_1418_);
lean_dec_ref(v_a_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object* v_x_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1420_);
v___x_1424_ = l_Lean_Syntax_isOfKind(v_x_1420_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec(v_x_1420_);
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v_a_1422_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = l_Lean_Syntax_getArg(v_x_1420_, v___x_1427_);
v___x_1429_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1428_);
v___x_1430_ = l_Lean_Syntax_isOfKind(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec(v___x_1428_);
lean_dec(v_x_1420_);
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_a_1422_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = l_Lean_Syntax_getArg(v_x_1420_, v___x_1433_);
lean_dec(v_x_1420_);
v___x_1435_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1434_);
v___x_1436_ = l_Lean_Syntax_matchesNull(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec(v___x_1434_);
lean_dec(v___x_1428_);
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v_a_1422_);
return v___x_1438_;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_ref_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1439_ = l_Lean_Syntax_getArg(v___x_1434_, v___x_1427_);
v___x_1440_ = l_Lean_Syntax_getArg(v___x_1434_, v___x_1433_);
lean_dec(v___x_1434_);
v_ref_1441_ = l_Lean_replaceRef(v___x_1428_, v_a_1421_);
lean_dec(v___x_1428_);
v___x_1442_ = 0;
v___x_1443_ = l_Lean_SourceInfo_fromRef(v_ref_1441_, v___x_1442_);
lean_dec(v_ref_1441_);
v___x_1444_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
v___x_1445_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__2));
lean_inc(v___x_1443_);
v___x_1446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1443_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l_Lean_Syntax_node3(v___x_1443_, v___x_1444_, v___x_1439_, v___x_1446_, v___x_1440_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
lean_ctor_set(v___x_1448_, 1, v_a_1422_);
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object* v_x_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(v_x_1449_, v_a_1450_, v_a_1451_);
lean_dec(v_a_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf___redArg(lean_object* v_inst_1453_, lean_object* v_x_1454_, lean_object* v_x_1455_){
_start:
{
if (lean_obj_tag(v_x_1454_) == 0)
{
uint8_t v___x_1456_; 
lean_dec(v_x_1455_);
lean_dec_ref(v_inst_1453_);
v___x_1456_ = 1;
return v___x_1456_;
}
else
{
if (lean_obj_tag(v_x_1455_) == 0)
{
uint8_t v___x_1457_; 
lean_dec_ref_known(v_x_1454_, 2);
lean_dec_ref(v_inst_1453_);
v___x_1457_ = 0;
return v___x_1457_;
}
else
{
lean_object* v_head_1458_; lean_object* v_tail_1459_; lean_object* v_head_1460_; lean_object* v_tail_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_head_1458_ = lean_ctor_get(v_x_1454_, 0);
lean_inc(v_head_1458_);
v_tail_1459_ = lean_ctor_get(v_x_1454_, 1);
lean_inc(v_tail_1459_);
lean_dec_ref_known(v_x_1454_, 2);
v_head_1460_ = lean_ctor_get(v_x_1455_, 0);
lean_inc(v_head_1460_);
v_tail_1461_ = lean_ctor_get(v_x_1455_, 1);
lean_inc(v_tail_1461_);
lean_dec_ref_known(v_x_1455_, 2);
lean_inc_ref(v_inst_1453_);
v___x_1462_ = lean_apply_2(v_inst_1453_, v_head_1458_, v_head_1460_);
v___x_1463_ = lean_unbox(v___x_1462_);
if (v___x_1463_ == 0)
{
uint8_t v___x_1464_; 
lean_dec(v_tail_1461_);
lean_dec(v_tail_1459_);
lean_dec_ref(v_inst_1453_);
v___x_1464_ = lean_unbox(v___x_1462_);
return v___x_1464_;
}
else
{
v_x_1454_ = v_tail_1459_;
v_x_1455_ = v_tail_1461_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___redArg___boxed(lean_object* v_inst_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_res_1469_ = l_List_isPrefixOf___redArg(v_inst_1466_, v_x_1467_, v_x_1468_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf(lean_object* v_00_u03b1_1471_, lean_object* v_inst_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_){
_start:
{
uint8_t v___x_1475_; 
v___x_1475_ = l_List_isPrefixOf___redArg(v_inst_1472_, v_x_1473_, v_x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___boxed(lean_object* v_00_u03b1_1476_, lean_object* v_inst_1477_, lean_object* v_x_1478_, lean_object* v_x_1479_){
_start:
{
uint8_t v_res_1480_; lean_object* v_r_1481_; 
v_res_1480_ = l_List_isPrefixOf(v_00_u03b1_1476_, v_inst_1477_, v_x_1478_, v_x_1479_);
v_r_1481_ = lean_box(v_res_1480_);
return v_r_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_1482_, lean_object* v_x_1483_, lean_object* v_h__1_1484_, lean_object* v_h__2_1485_, lean_object* v_h__3_1486_){
_start:
{
if (lean_obj_tag(v_x_1482_) == 0)
{
lean_object* v___x_1487_; 
lean_dec(v_h__3_1486_);
lean_dec(v_h__2_1485_);
v___x_1487_ = lean_apply_1(v_h__1_1484_, v_x_1483_);
return v___x_1487_;
}
else
{
lean_dec(v_h__1_1484_);
if (lean_obj_tag(v_x_1483_) == 0)
{
lean_object* v___x_1488_; 
lean_dec(v_h__3_1486_);
v___x_1488_ = lean_apply_2(v_h__2_1485_, v_x_1482_, lean_box(0));
return v___x_1488_;
}
else
{
lean_object* v_head_1489_; lean_object* v_tail_1490_; lean_object* v_head_1491_; lean_object* v_tail_1492_; lean_object* v___x_1493_; 
lean_dec(v_h__2_1485_);
v_head_1489_ = lean_ctor_get(v_x_1482_, 0);
lean_inc(v_head_1489_);
v_tail_1490_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_tail_1490_);
lean_dec_ref_known(v_x_1482_, 2);
v_head_1491_ = lean_ctor_get(v_x_1483_, 0);
lean_inc(v_head_1491_);
v_tail_1492_ = lean_ctor_get(v_x_1483_, 1);
lean_inc(v_tail_1492_);
lean_dec_ref_known(v_x_1483_, 2);
v___x_1493_ = lean_apply_4(v_h__3_1486_, v_head_1489_, v_tail_1490_, v_head_1491_, v_tail_1492_);
return v___x_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object* v_00_u03b1_1494_, lean_object* v_motive_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_h__1_1498_, lean_object* v_h__2_1499_, lean_object* v_h__3_1500_){
_start:
{
if (lean_obj_tag(v_x_1496_) == 0)
{
lean_object* v___x_1501_; 
lean_dec(v_h__3_1500_);
lean_dec(v_h__2_1499_);
v___x_1501_ = lean_apply_1(v_h__1_1498_, v_x_1497_);
return v___x_1501_;
}
else
{
lean_dec(v_h__1_1498_);
if (lean_obj_tag(v_x_1497_) == 0)
{
lean_object* v___x_1502_; 
lean_dec(v_h__3_1500_);
v___x_1502_ = lean_apply_2(v_h__2_1499_, v_x_1496_, lean_box(0));
return v___x_1502_;
}
else
{
lean_object* v_head_1503_; lean_object* v_tail_1504_; lean_object* v_head_1505_; lean_object* v_tail_1506_; lean_object* v___x_1507_; 
lean_dec(v_h__2_1499_);
v_head_1503_ = lean_ctor_get(v_x_1496_, 0);
lean_inc(v_head_1503_);
v_tail_1504_ = lean_ctor_get(v_x_1496_, 1);
lean_inc(v_tail_1504_);
lean_dec_ref_known(v_x_1496_, 2);
v_head_1505_ = lean_ctor_get(v_x_1497_, 0);
lean_inc(v_head_1505_);
v_tail_1506_ = lean_ctor_get(v_x_1497_, 1);
lean_inc(v_tail_1506_);
lean_dec_ref_known(v_x_1497_, 2);
v___x_1507_ = lean_apply_4(v_h__3_1500_, v_head_1503_, v_tail_1504_, v_head_1505_, v_tail_1506_);
return v___x_1507_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___redArg(lean_object* v_inst_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_){
_start:
{
if (lean_obj_tag(v_x_1509_) == 0)
{
lean_object* v___x_1511_; 
lean_dec_ref(v_inst_1508_);
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_x_1510_);
return v___x_1511_;
}
else
{
if (lean_obj_tag(v_x_1510_) == 0)
{
lean_object* v___x_1512_; 
lean_dec_ref_known(v_x_1509_, 2);
lean_dec_ref(v_inst_1508_);
v___x_1512_ = lean_box(0);
return v___x_1512_;
}
else
{
lean_object* v_head_1513_; lean_object* v_tail_1514_; lean_object* v_head_1515_; lean_object* v_tail_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_head_1513_ = lean_ctor_get(v_x_1509_, 0);
lean_inc(v_head_1513_);
v_tail_1514_ = lean_ctor_get(v_x_1509_, 1);
lean_inc(v_tail_1514_);
lean_dec_ref_known(v_x_1509_, 2);
v_head_1515_ = lean_ctor_get(v_x_1510_, 0);
lean_inc(v_head_1515_);
v_tail_1516_ = lean_ctor_get(v_x_1510_, 1);
lean_inc(v_tail_1516_);
lean_dec_ref_known(v_x_1510_, 2);
lean_inc_ref(v_inst_1508_);
v___x_1517_ = lean_apply_2(v_inst_1508_, v_head_1513_, v_head_1515_);
v___x_1518_ = lean_unbox(v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
lean_dec(v_tail_1516_);
lean_dec(v_tail_1514_);
lean_dec_ref(v_inst_1508_);
v___x_1519_ = lean_box(0);
return v___x_1519_;
}
else
{
v_x_1509_ = v_tail_1514_;
v_x_1510_ = v_tail_1516_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object* v_00_u03b1_1521_, lean_object* v_inst_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_List_isPrefixOf_x3f___redArg(v_inst_1522_, v_x_1523_, v_x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf___redArg(lean_object* v_inst_1526_, lean_object* v_l_u2081_1527_, lean_object* v_l_u2082_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = l_List_reverse___redArg(v_l_u2081_1527_);
v___x_1530_ = l_List_reverse___redArg(v_l_u2082_1528_);
v___x_1531_ = l_List_isPrefixOf___redArg(v_inst_1526_, v___x_1529_, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___redArg___boxed(lean_object* v_inst_1532_, lean_object* v_l_u2081_1533_, lean_object* v_l_u2082_1534_){
_start:
{
uint8_t v_res_1535_; lean_object* v_r_1536_; 
v_res_1535_ = l_List_isSuffixOf___redArg(v_inst_1532_, v_l_u2081_1533_, v_l_u2082_1534_);
v_r_1536_ = lean_box(v_res_1535_);
return v_r_1536_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf(lean_object* v_00_u03b1_1537_, lean_object* v_inst_1538_, lean_object* v_l_u2081_1539_, lean_object* v_l_u2082_1540_){
_start:
{
uint8_t v___x_1541_; 
v___x_1541_ = l_List_isSuffixOf___redArg(v_inst_1538_, v_l_u2081_1539_, v_l_u2082_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___boxed(lean_object* v_00_u03b1_1542_, lean_object* v_inst_1543_, lean_object* v_l_u2081_1544_, lean_object* v_l_u2082_1545_){
_start:
{
uint8_t v_res_1546_; lean_object* v_r_1547_; 
v_res_1546_ = l_List_isSuffixOf(v_00_u03b1_1542_, v_inst_1543_, v_l_u2081_1544_, v_l_u2082_1545_);
v_r_1547_ = lean_box(v_res_1546_);
return v_r_1547_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___redArg(lean_object* v_inst_1548_, lean_object* v_l_u2081_1549_, lean_object* v_l_u2082_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = l_List_reverse___redArg(v_l_u2081_1549_);
v___x_1552_ = l_List_reverse___redArg(v_l_u2082_1550_);
v___x_1553_ = l_List_isPrefixOf_x3f___redArg(v_inst_1548_, v___x_1551_, v___x_1552_);
if (lean_obj_tag(v___x_1553_) == 0)
{
return v___x_1553_;
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1562_; 
v_val_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_val_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = l_List_reverse___redArg(v_val_1554_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1558_);
v___x_1560_ = v___x_1556_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object* v_00_u03b1_1563_, lean_object* v_inst_1564_, lean_object* v_l_u2081_1565_, lean_object* v_l_u2082_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_List_isSuffixOf_x3f___redArg(v_inst_1564_, v_l_u2081_1565_, v_l_u2082_1566_);
return v___x_1567_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0));
v___x_1586_ = l_String_toRawSubstring_x27(v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object* v_x_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
lean_inc(v_x_1598_);
v___x_1602_ = l_Lean_Syntax_isOfKind(v_x_1598_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_x_1598_);
v___x_1603_ = lean_box(1);
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1600_);
return v___x_1604_;
}
else
{
lean_object* v_quotContext_1605_; lean_object* v_currMacroScope_1606_; lean_object* v_ref_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_quotContext_1605_ = lean_ctor_get(v_a_1599_, 1);
v_currMacroScope_1606_ = lean_ctor_get(v_a_1599_, 2);
v_ref_1607_ = lean_ctor_get(v_a_1599_, 5);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = l_Lean_Syntax_getArg(v_x_1598_, v___x_1608_);
v___x_1610_ = lean_unsigned_to_nat(2u);
v___x_1611_ = l_Lean_Syntax_getArg(v_x_1598_, v___x_1610_);
lean_dec(v_x_1598_);
v___x_1612_ = 0;
v___x_1613_ = l_Lean_SourceInfo_fromRef(v_ref_1607_, v___x_1612_);
v___x_1614_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1615_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
v___x_1616_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2));
lean_inc(v_currMacroScope_1606_);
lean_inc(v_quotContext_1605_);
v___x_1617_ = l_Lean_addMacroScope(v_quotContext_1605_, v___x_1616_, v_currMacroScope_1606_);
v___x_1618_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5));
lean_inc_n(v___x_1613_, 2);
v___x_1619_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1613_);
lean_ctor_set(v___x_1619_, 1, v___x_1615_);
lean_ctor_set(v___x_1619_, 2, v___x_1617_);
lean_ctor_set(v___x_1619_, 3, v___x_1618_);
v___x_1620_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1621_ = l_Lean_Syntax_node2(v___x_1613_, v___x_1620_, v___x_1609_, v___x_1611_);
v___x_1622_ = l_Lean_Syntax_node2(v___x_1613_, v___x_1614_, v___x_1619_, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v_a_1600_);
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___boxed(lean_object* v_x_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(v_x_1624_, v_a_1625_, v_a_1626_);
lean_dec_ref(v_a_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object* v_x_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1628_);
v___x_1632_ = l_Lean_Syntax_isOfKind(v_x_1628_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec(v_x_1628_);
v___x_1633_ = lean_box(0);
v___x_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
lean_ctor_set(v___x_1634_, 1, v_a_1630_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = l_Lean_Syntax_getArg(v_x_1628_, v___x_1635_);
v___x_1637_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1636_);
v___x_1638_ = l_Lean_Syntax_isOfKind(v___x_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec(v___x_1636_);
lean_dec(v_x_1628_);
v___x_1639_ = lean_box(0);
v___x_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v_a_1630_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = l_Lean_Syntax_getArg(v_x_1628_, v___x_1641_);
lean_dec(v_x_1628_);
v___x_1643_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1642_);
v___x_1644_ = l_Lean_Syntax_matchesNull(v___x_1642_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v___x_1642_);
lean_dec(v___x_1636_);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v_a_1630_);
return v___x_1646_;
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v_ref_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1647_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1635_);
v___x_1648_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1641_);
lean_dec(v___x_1642_);
v_ref_1649_ = l_Lean_replaceRef(v___x_1636_, v_a_1629_);
lean_dec(v___x_1636_);
v___x_1650_ = 0;
v___x_1651_ = l_Lean_SourceInfo_fromRef(v_ref_1649_, v___x_1650_);
lean_dec(v_ref_1649_);
v___x_1652_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
v___x_1653_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__2));
lean_inc(v___x_1651_);
v___x_1654_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1651_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_Syntax_node3(v___x_1651_, v___x_1652_, v___x_1647_, v___x_1654_, v___x_1648_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v_a_1630_);
return v___x_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object* v_x_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(v_x_1657_, v_a_1658_, v_a_1659_);
lean_dec(v_a_1658_);
return v_res_1660_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0));
v___x_1679_ = l_String_toRawSubstring_x27(v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object* v_x_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1694_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
lean_inc(v_x_1691_);
v___x_1695_ = l_Lean_Syntax_isOfKind(v_x_1691_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v_x_1691_);
v___x_1696_ = lean_box(1);
v___x_1697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v_a_1693_);
return v___x_1697_;
}
else
{
lean_object* v_quotContext_1698_; lean_object* v_currMacroScope_1699_; lean_object* v_ref_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_quotContext_1698_ = lean_ctor_get(v_a_1692_, 1);
v_currMacroScope_1699_ = lean_ctor_get(v_a_1692_, 2);
v_ref_1700_ = lean_ctor_get(v_a_1692_, 5);
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = l_Lean_Syntax_getArg(v_x_1691_, v___x_1701_);
v___x_1703_ = lean_unsigned_to_nat(2u);
v___x_1704_ = l_Lean_Syntax_getArg(v_x_1691_, v___x_1703_);
lean_dec(v_x_1691_);
v___x_1705_ = 0;
v___x_1706_ = l_Lean_SourceInfo_fromRef(v_ref_1700_, v___x_1705_);
v___x_1707_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1708_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
v___x_1709_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1699_);
lean_inc(v_quotContext_1698_);
v___x_1710_ = l_Lean_addMacroScope(v_quotContext_1698_, v___x_1709_, v_currMacroScope_1699_);
v___x_1711_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1706_, 2);
v___x_1712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1706_);
lean_ctor_set(v___x_1712_, 1, v___x_1708_);
lean_ctor_set(v___x_1712_, 2, v___x_1710_);
lean_ctor_set(v___x_1712_, 3, v___x_1711_);
v___x_1713_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1714_ = l_Lean_Syntax_node2(v___x_1706_, v___x_1713_, v___x_1702_, v___x_1704_);
v___x_1715_ = l_Lean_Syntax_node2(v___x_1706_, v___x_1707_, v___x_1712_, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v_a_1693_);
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___boxed(lean_object* v_x_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(v_x_1717_, v_a_1718_, v_a_1719_);
lean_dec_ref(v_a_1718_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object* v_x_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1721_);
v___x_1725_ = l_Lean_Syntax_isOfKind(v_x_1721_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec(v_x_1721_);
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v_a_1723_);
return v___x_1727_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1728_ = lean_unsigned_to_nat(0u);
v___x_1729_ = l_Lean_Syntax_getArg(v_x_1721_, v___x_1728_);
v___x_1730_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1729_);
v___x_1731_ = l_Lean_Syntax_isOfKind(v___x_1729_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v___x_1729_);
lean_dec(v_x_1721_);
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v_a_1723_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = l_Lean_Syntax_getArg(v_x_1721_, v___x_1734_);
lean_dec(v_x_1721_);
v___x_1736_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1735_);
v___x_1737_ = l_Lean_Syntax_matchesNull(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v___x_1735_);
lean_dec(v___x_1729_);
v___x_1738_ = lean_box(0);
v___x_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v_a_1723_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v_ref_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1740_ = l_Lean_Syntax_getArg(v___x_1735_, v___x_1728_);
v___x_1741_ = l_Lean_Syntax_getArg(v___x_1735_, v___x_1734_);
lean_dec(v___x_1735_);
v_ref_1742_ = l_Lean_replaceRef(v___x_1729_, v_a_1722_);
lean_dec(v___x_1729_);
v___x_1743_ = 0;
v___x_1744_ = l_Lean_SourceInfo_fromRef(v_ref_1742_, v___x_1743_);
lean_dec(v_ref_1742_);
v___x_1745_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
v___x_1746_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__2));
lean_inc(v___x_1744_);
v___x_1747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1744_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = l_Lean_Syntax_node3(v___x_1744_, v___x_1745_, v___x_1740_, v___x_1747_, v___x_1741_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
lean_ctor_set(v___x_1749_, 1, v_a_1723_);
return v___x_1749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object* v_x_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(v_x_1750_, v_a_1751_, v_a_1752_);
lean_dec(v_a_1751_);
return v_res_1753_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal___redArg(lean_object* v_inst_1754_, lean_object* v_l_u2081_1755_, lean_object* v_l_u2082_1756_){
_start:
{
uint8_t v___x_1757_; 
lean_inc(v_l_u2082_1756_);
lean_inc(v_l_u2081_1755_);
lean_inc_ref(v_inst_1754_);
v___x_1757_ = l_List_isPrefixOf___redArg(v_inst_1754_, v_l_u2081_1755_, v_l_u2082_1756_);
if (v___x_1757_ == 0)
{
if (lean_obj_tag(v_l_u2082_1756_) == 0)
{
lean_dec(v_l_u2081_1755_);
lean_dec_ref(v_inst_1754_);
return v___x_1757_;
}
else
{
lean_object* v_tail_1758_; 
v_tail_1758_ = lean_ctor_get(v_l_u2082_1756_, 1);
lean_inc(v_tail_1758_);
lean_dec_ref_known(v_l_u2082_1756_, 2);
v_l_u2082_1756_ = v_tail_1758_;
goto _start;
}
}
else
{
lean_dec(v_l_u2082_1756_);
lean_dec(v_l_u2081_1755_);
lean_dec_ref(v_inst_1754_);
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___redArg___boxed(lean_object* v_inst_1760_, lean_object* v_l_u2081_1761_, lean_object* v_l_u2082_1762_){
_start:
{
uint8_t v_res_1763_; lean_object* v_r_1764_; 
v_res_1763_ = l_List_isInfixOf__internal___redArg(v_inst_1760_, v_l_u2081_1761_, v_l_u2082_1762_);
v_r_1764_ = lean_box(v_res_1763_);
return v_r_1764_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal(lean_object* v_00_u03b1_1765_, lean_object* v_inst_1766_, lean_object* v_l_u2081_1767_, lean_object* v_l_u2082_1768_){
_start:
{
uint8_t v___x_1769_; 
v___x_1769_ = l_List_isInfixOf__internal___redArg(v_inst_1766_, v_l_u2081_1767_, v_l_u2082_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_inst_1771_, lean_object* v_l_u2081_1772_, lean_object* v_l_u2082_1773_){
_start:
{
uint8_t v_res_1774_; lean_object* v_r_1775_; 
v_res_1774_ = l_List_isInfixOf__internal(v_00_u03b1_1770_, v_inst_1771_, v_l_u2081_1772_, v_l_u2082_1773_);
v_r_1775_ = lean_box(v_res_1774_);
return v_r_1775_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go___redArg(lean_object* v_l_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
if (lean_obj_tag(v_a_1777_) == 0)
{
lean_object* v___x_1780_; 
lean_dec(v_a_1779_);
lean_dec(v_a_1778_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v_l_1776_);
lean_ctor_set(v___x_1780_, 1, v_a_1777_);
return v___x_1780_;
}
else
{
lean_object* v_head_1781_; lean_object* v_tail_1782_; lean_object* v_zero_1783_; uint8_t v_isZero_1784_; 
v_head_1781_ = lean_ctor_get(v_a_1777_, 0);
v_tail_1782_ = lean_ctor_get(v_a_1777_, 1);
v_zero_1783_ = lean_unsigned_to_nat(0u);
v_isZero_1784_ = lean_nat_dec_eq(v_a_1778_, v_zero_1783_);
if (v_isZero_1784_ == 1)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_dec(v_a_1778_);
lean_dec(v_l_1776_);
v___x_1785_ = l_List_reverse___redArg(v_a_1779_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
lean_ctor_set(v___x_1786_, 1, v_a_1777_);
return v___x_1786_;
}
else
{
lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1796_; 
lean_inc(v_tail_1782_);
lean_inc(v_head_1781_);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_a_1777_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; lean_object* v_unused_1798_; 
v_unused_1797_ = lean_ctor_get(v_a_1777_, 1);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_a_1777_, 0);
lean_dec(v_unused_1798_);
v___x_1788_ = v_a_1777_;
v_isShared_1789_ = v_isSharedCheck_1796_;
goto v_resetjp_1787_;
}
else
{
lean_dec(v_a_1777_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1796_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_one_1790_; lean_object* v_n_1791_; lean_object* v___x_1793_; 
v_one_1790_ = lean_unsigned_to_nat(1u);
v_n_1791_ = lean_nat_sub(v_a_1778_, v_one_1790_);
lean_dec(v_a_1778_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 1, v_a_1779_);
v___x_1793_ = v___x_1788_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_head_1781_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_a_1779_);
v___x_1793_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
v_a_1777_ = v_tail_1782_;
v_a_1778_ = v_n_1791_;
v_a_1779_ = v___x_1793_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object* v_00_u03b1_1799_, lean_object* v_l_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_List_splitAt_go___redArg(v_l_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt___redArg(lean_object* v_n_1805_, lean_object* v_l_1806_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = lean_box(0);
lean_inc(v_l_1806_);
v___x_1808_ = l_List_splitAt_go___redArg(v_l_1806_, v_l_1806_, v_n_1805_, v___x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt(lean_object* v_00_u03b1_1809_, lean_object* v_n_1810_, lean_object* v_l_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_List_splitAt___redArg(v_n_1810_, v_l_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise___redArg(lean_object* v_inst_1813_, lean_object* v_x_1814_){
_start:
{
if (lean_obj_tag(v_x_1814_) == 0)
{
uint8_t v___x_1815_; 
lean_dec_ref(v_inst_1813_);
v___x_1815_ = 1;
return v___x_1815_;
}
else
{
lean_object* v_head_1816_; lean_object* v_tail_1817_; uint8_t v_decide_1818_; 
v_head_1816_ = lean_ctor_get(v_x_1814_, 0);
lean_inc(v_head_1816_);
v_tail_1817_ = lean_ctor_get(v_x_1814_, 1);
lean_inc_n(v_tail_1817_, 2);
lean_dec_ref_known(v_x_1814_, 2);
lean_inc_ref(v_inst_1813_);
v_decide_1818_ = l_List_instDecidablePairwise___redArg(v_inst_1813_, v_tail_1817_);
if (v_decide_1818_ == 0)
{
lean_dec(v_tail_1817_);
lean_dec(v_head_1816_);
lean_dec_ref(v_inst_1813_);
return v_decide_1818_;
}
else
{
lean_object* v___x_1819_; uint8_t v_decide_1820_; 
v___x_1819_ = lean_apply_1(v_inst_1813_, v_head_1816_);
v_decide_1820_ = l_List_decidableBAll___redArg(v___x_1819_, v_tail_1817_);
return v_decide_1820_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___redArg___boxed(lean_object* v_inst_1821_, lean_object* v_x_1822_){
_start:
{
uint8_t v_res_1823_; lean_object* v_r_1824_; 
v_res_1823_ = l_List_instDecidablePairwise___redArg(v_inst_1821_, v_x_1822_);
v_r_1824_ = lean_box(v_res_1823_);
return v_r_1824_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise(lean_object* v_00_u03b1_1825_, lean_object* v_R_1826_, lean_object* v_inst_1827_, lean_object* v_x_1828_){
_start:
{
uint8_t v___x_1829_; 
v___x_1829_ = l_List_instDecidablePairwise___redArg(v_inst_1827_, v_x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___boxed(lean_object* v_00_u03b1_1830_, lean_object* v_R_1831_, lean_object* v_inst_1832_, lean_object* v_x_1833_){
_start:
{
uint8_t v_res_1834_; lean_object* v_r_1835_; 
v_res_1834_ = l_List_instDecidablePairwise(v_00_u03b1_1830_, v_R_1831_, v_inst_1832_, v_x_1833_);
v_r_1835_ = lean_box(v_res_1834_);
return v_r_1835_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg___lam__0(lean_object* v_inst_1836_, lean_object* v_a_1837_, lean_object* v_b_1838_){
_start:
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = lean_apply_2(v_inst_1836_, v_a_1837_, v_b_1838_);
v___x_1840_ = lean_unbox(v___x_1839_);
if (v___x_1840_ == 0)
{
uint8_t v___x_1841_; 
v___x_1841_ = 1;
return v___x_1841_;
}
else
{
uint8_t v___x_1842_; 
v___x_1842_ = 0;
return v___x_1842_;
}
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___lam__0___boxed(lean_object* v_inst_1843_, lean_object* v_a_1844_, lean_object* v_b_1845_){
_start:
{
uint8_t v_res_1846_; lean_object* v_r_1847_; 
v_res_1846_ = l_List_nodupDecidable___redArg___lam__0(v_inst_1843_, v_a_1844_, v_b_1845_);
v_r_1847_ = lean_box(v_res_1846_);
return v_r_1847_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg(lean_object* v_inst_1848_, lean_object* v_l_1849_){
_start:
{
lean_object* v___f_1850_; uint8_t v___x_1851_; 
v___f_1850_ = lean_alloc_closure((void*)(l_List_nodupDecidable___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1850_, 0, v_inst_1848_);
v___x_1851_ = l_List_instDecidablePairwise___redArg(v___f_1850_, v_l_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___boxed(lean_object* v_inst_1852_, lean_object* v_l_1853_){
_start:
{
uint8_t v_res_1854_; lean_object* v_r_1855_; 
v_res_1854_ = l_List_nodupDecidable___redArg(v_inst_1852_, v_l_1853_);
v_r_1855_ = lean_box(v_res_1854_);
return v_r_1855_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable(lean_object* v_00_u03b1_1856_, lean_object* v_inst_1857_, lean_object* v_l_1858_){
_start:
{
uint8_t v___x_1859_; 
v___x_1859_ = l_List_nodupDecidable___redArg(v_inst_1857_, v_l_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___boxed(lean_object* v_00_u03b1_1860_, lean_object* v_inst_1861_, lean_object* v_l_1862_){
_start:
{
uint8_t v_res_1863_; lean_object* v_r_1864_; 
v_res_1863_ = l_List_nodupDecidable(v_00_u03b1_1860_, v_inst_1861_, v_l_1862_);
v_r_1864_ = lean_box(v_res_1863_);
return v_r_1864_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg(lean_object* v_f_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_zero_1868_; uint8_t v_isZero_1869_; 
v_zero_1868_ = lean_unsigned_to_nat(0u);
v_isZero_1869_ = lean_nat_dec_eq(v_a_1866_, v_zero_1868_);
if (v_isZero_1869_ == 1)
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_apply_1(v_f_1865_, v_a_1867_);
return v___x_1870_;
}
else
{
if (lean_obj_tag(v_a_1867_) == 0)
{
lean_dec_ref(v_f_1865_);
return v_a_1867_;
}
else
{
lean_object* v_head_1871_; lean_object* v_tail_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1882_; 
v_head_1871_ = lean_ctor_get(v_a_1867_, 0);
v_tail_1872_ = lean_ctor_get(v_a_1867_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_a_1867_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1874_ = v_a_1867_;
v_isShared_1875_ = v_isSharedCheck_1882_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_tail_1872_);
lean_inc(v_head_1871_);
lean_dec(v_a_1867_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1882_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_one_1876_; lean_object* v_n_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v_one_1876_ = lean_unsigned_to_nat(1u);
v_n_1877_ = lean_nat_sub(v_a_1866_, v_one_1876_);
v___x_1878_ = l_List_modifyTailIdx_go___redArg(v_f_1865_, v_n_1877_, v_tail_1872_);
lean_dec(v_n_1877_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 1, v___x_1878_);
v___x_1880_ = v___x_1874_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_head_1871_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg___boxed(lean_object* v_f_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_List_modifyTailIdx_go___redArg(v_f_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go(lean_object* v_00_u03b1_1887_, lean_object* v_f_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_List_modifyTailIdx_go___redArg(v_f_1888_, v_a_1889_, v_a_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_f_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_List_modifyTailIdx_go(v_00_u03b1_1892_, v_f_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_a_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg(lean_object* v_l_1897_, lean_object* v_i_1898_, lean_object* v_f_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_List_modifyTailIdx_go___redArg(v_f_1899_, v_i_1898_, v_l_1897_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg___boxed(lean_object* v_l_1901_, lean_object* v_i_1902_, lean_object* v_f_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_List_modifyTailIdx___redArg(v_l_1901_, v_i_1902_, v_f_1903_);
lean_dec(v_i_1902_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx(lean_object* v_00_u03b1_1905_, lean_object* v_l_1906_, lean_object* v_i_1907_, lean_object* v_f_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_List_modifyTailIdx_go___redArg(v_f_1908_, v_i_1907_, v_l_1906_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___boxed(lean_object* v_00_u03b1_1910_, lean_object* v_l_1911_, lean_object* v_i_1912_, lean_object* v_f_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_List_modifyTailIdx(v_00_u03b1_1910_, v_l_1911_, v_i_1912_, v_f_1913_);
lean_dec(v_i_1912_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_List_modifyHead___redArg(lean_object* v_f_1915_, lean_object* v_x_1916_){
_start:
{
if (lean_obj_tag(v_x_1916_) == 0)
{
lean_dec(v_f_1915_);
return v_x_1916_;
}
else
{
lean_object* v_head_1917_; lean_object* v_tail_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1926_; 
v_head_1917_ = lean_ctor_get(v_x_1916_, 0);
v_tail_1918_ = lean_ctor_get(v_x_1916_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_x_1916_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1920_ = v_x_1916_;
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_tail_1918_);
lean_inc(v_head_1917_);
lean_dec(v_x_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_apply_1(v_f_1915_, v_head_1917_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_tail_1918_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyHead(lean_object* v_00_u03b1_1927_, lean_object* v_f_1928_, lean_object* v_x_1929_){
_start:
{
if (lean_obj_tag(v_x_1929_) == 0)
{
lean_dec(v_f_1928_);
return v_x_1929_;
}
else
{
lean_object* v_head_1930_; lean_object* v_tail_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1939_; 
v_head_1930_ = lean_ctor_get(v_x_1929_, 0);
v_tail_1931_ = lean_ctor_get(v_x_1929_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_x_1929_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1933_ = v_x_1929_;
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_tail_1931_);
lean_inc(v_head_1930_);
lean_dec(v_x_1929_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = lean_apply_1(v_f_1928_, v_head_1930_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1935_);
v___x_1937_ = v___x_1933_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_tail_1931_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object* v_inst_1940_, lean_object* v_a_1941_, lean_object* v_l_1942_){
_start:
{
uint8_t v___x_1943_; 
lean_inc(v_l_1942_);
lean_inc(v_a_1941_);
v___x_1943_ = l_List_elem___redArg(v_inst_1940_, v_a_1941_, v_l_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_a_1941_);
lean_ctor_set(v___x_1944_, 1, v_l_1942_);
return v___x_1944_;
}
else
{
lean_dec(v_a_1941_);
return v_l_1942_;
}
}
}
LEAN_EXPORT lean_object* l_List_insert(lean_object* v_00_u03b1_1945_, lean_object* v_inst_1946_, lean_object* v_a_1947_, lean_object* v_l_1948_){
_start:
{
uint8_t v___x_1949_; 
lean_inc(v_l_1948_);
lean_inc(v_a_1947_);
v___x_1949_ = l_List_elem___redArg(v_inst_1946_, v_a_1947_, v_l_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1950_, 0, v_a_1947_);
lean_ctor_set(v___x_1950_, 1, v_l_1948_);
return v___x_1950_;
}
else
{
lean_dec(v_a_1947_);
return v_l_1948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(lean_object* v_x_1951_, lean_object* v_x_1952_, lean_object* v_h__1_1953_, lean_object* v_h__2_1954_){
_start:
{
if (lean_obj_tag(v_x_1951_) == 0)
{
lean_object* v___x_1955_; 
lean_dec(v_h__2_1954_);
v___x_1955_ = lean_apply_1(v_h__1_1953_, v_x_1952_);
return v___x_1955_;
}
else
{
lean_object* v_head_1956_; lean_object* v_tail_1957_; lean_object* v___x_1958_; 
lean_dec(v_h__1_1953_);
v_head_1956_ = lean_ctor_get(v_x_1951_, 0);
lean_inc(v_head_1956_);
v_tail_1957_ = lean_ctor_get(v_x_1951_, 1);
lean_inc(v_tail_1957_);
lean_dec_ref_known(v_x_1951_, 2);
v___x_1958_ = lean_apply_3(v_h__2_1954_, v_head_1956_, v_tail_1957_, v_x_1952_);
return v___x_1958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object* v_00_u03b1_1959_, lean_object* v_motive_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_, lean_object* v_h__1_1963_, lean_object* v_h__2_1964_){
_start:
{
if (lean_obj_tag(v_x_1961_) == 0)
{
lean_object* v___x_1965_; 
lean_dec(v_h__2_1964_);
v___x_1965_ = lean_apply_1(v_h__1_1963_, v_x_1962_);
return v___x_1965_;
}
else
{
lean_object* v_head_1966_; lean_object* v_tail_1967_; lean_object* v___x_1968_; 
lean_dec(v_h__1_1963_);
v_head_1966_ = lean_ctor_get(v_x_1961_, 0);
lean_inc(v_head_1966_);
v_tail_1967_ = lean_ctor_get(v_x_1961_, 1);
lean_inc(v_tail_1967_);
lean_dec_ref_known(v_x_1961_, 2);
v___x_1968_ = lean_apply_3(v_h__2_1964_, v_head_1966_, v_tail_1967_, v_x_1962_);
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object* v_p_1969_, lean_object* v_x_1970_){
_start:
{
if (lean_obj_tag(v_x_1970_) == 0)
{
lean_object* v___x_1971_; 
lean_dec_ref(v_p_1969_);
v___x_1971_ = lean_box(0);
return v___x_1971_;
}
else
{
lean_object* v_head_1972_; lean_object* v_tail_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_head_1972_ = lean_ctor_get(v_x_1970_, 0);
lean_inc_n(v_head_1972_, 2);
v_tail_1973_ = lean_ctor_get(v_x_1970_, 1);
lean_inc(v_tail_1973_);
lean_dec_ref_known(v_x_1970_, 2);
lean_inc_ref(v_p_1969_);
v___x_1974_ = lean_apply_1(v_p_1969_, v_head_1972_);
v___x_1975_ = lean_unbox(v___x_1974_);
if (v___x_1975_ == 0)
{
lean_dec(v_head_1972_);
v_x_1970_ = v_tail_1973_;
goto _start;
}
else
{
lean_object* v___x_1977_; 
lean_dec(v_tail_1973_);
lean_dec_ref(v_p_1969_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_head_1972_);
return v___x_1977_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object* v_00_u03b1_1978_, lean_object* v_p_1979_, lean_object* v_x_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_List_find_x3f___redArg(v_p_1979_, v_x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object* v_f_1982_, lean_object* v_x_1983_){
_start:
{
if (lean_obj_tag(v_x_1983_) == 0)
{
lean_object* v___x_1984_; 
lean_dec_ref(v_f_1982_);
v___x_1984_ = lean_box(0);
return v___x_1984_;
}
else
{
lean_object* v_head_1985_; lean_object* v_tail_1986_; lean_object* v___x_1987_; 
v_head_1985_ = lean_ctor_get(v_x_1983_, 0);
lean_inc(v_head_1985_);
v_tail_1986_ = lean_ctor_get(v_x_1983_, 1);
lean_inc(v_tail_1986_);
lean_dec_ref_known(v_x_1983_, 2);
lean_inc_ref(v_f_1982_);
v___x_1987_ = lean_apply_1(v_f_1982_, v_head_1985_);
if (lean_obj_tag(v___x_1987_) == 0)
{
v_x_1983_ = v_tail_1986_;
goto _start;
}
else
{
lean_dec(v_tail_1986_);
lean_dec_ref(v_f_1982_);
return v___x_1987_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object* v_00_u03b1_1989_, lean_object* v_00_u03b2_1990_, lean_object* v_f_1991_, lean_object* v_x_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_List_findSome_x3f___redArg(v_f_1991_, v_x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___redArg(lean_object* v_p_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
if (lean_obj_tag(v_a_1995_) == 0)
{
lean_dec_ref(v_p_1994_);
return v_a_1996_;
}
else
{
lean_object* v_head_1997_; lean_object* v_tail_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_head_1997_ = lean_ctor_get(v_a_1995_, 0);
lean_inc(v_head_1997_);
v_tail_1998_ = lean_ctor_get(v_a_1995_, 1);
lean_inc(v_tail_1998_);
lean_dec_ref_known(v_a_1995_, 2);
lean_inc_ref(v_p_1994_);
v___x_1999_ = lean_apply_1(v_p_1994_, v_head_1997_);
v___x_2000_ = lean_unbox(v___x_1999_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = lean_nat_add(v_a_1996_, v___x_2001_);
lean_dec(v_a_1996_);
v_a_1995_ = v_tail_1998_;
v_a_1996_ = v___x_2002_;
goto _start;
}
else
{
lean_dec(v_tail_1998_);
lean_dec_ref(v_p_1994_);
return v_a_1996_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object* v_00_u03b1_2004_, lean_object* v_p_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_List_findIdx_go___redArg(v_p_2005_, v_a_2006_, v_a_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx___redArg(lean_object* v_p_2009_, lean_object* v_l_2010_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = l_List_findIdx_go___redArg(v_p_2009_, v_l_2010_, v___x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx(lean_object* v_00_u03b1_2013_, lean_object* v_p_2014_, lean_object* v_l_2015_){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_unsigned_to_nat(0u);
v___x_2017_ = l_List_findIdx_go___redArg(v_p_2014_, v_l_2015_, v___x_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT uint8_t l_List_idxOf___redArg___lam__0(lean_object* v_inst_2018_, lean_object* v_a_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = lean_apply_2(v_inst_2018_, v_x_2020_, v_a_2019_);
v___x_2022_ = lean_unbox(v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg___lam__0___boxed(lean_object* v_inst_2023_, lean_object* v_a_2024_, lean_object* v_x_2025_){
_start:
{
uint8_t v_res_2026_; lean_object* v_r_2027_; 
v_res_2026_ = l_List_idxOf___redArg___lam__0(v_inst_2023_, v_a_2024_, v_x_2025_);
v_r_2027_ = lean_box(v_res_2026_);
return v_r_2027_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg(lean_object* v_inst_2028_, lean_object* v_a_2029_, lean_object* v_l_2030_){
_start:
{
lean_object* v___f_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___f_2031_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2031_, 0, v_inst_2028_);
lean_closure_set(v___f_2031_, 1, v_a_2029_);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = l_List_findIdx_go___redArg(v___f_2031_, v_l_2030_, v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf(lean_object* v_00_u03b1_2034_, lean_object* v_inst_2035_, lean_object* v_a_2036_, lean_object* v_l_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_List_idxOf___redArg(v_inst_2035_, v_a_2036_, v_l_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___redArg(lean_object* v_p_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
if (lean_obj_tag(v_a_2040_) == 0)
{
lean_object* v___x_2042_; 
lean_dec(v_a_2041_);
lean_dec_ref(v_p_2039_);
v___x_2042_ = lean_box(0);
return v___x_2042_;
}
else
{
lean_object* v_head_2043_; lean_object* v_tail_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v_head_2043_ = lean_ctor_get(v_a_2040_, 0);
lean_inc(v_head_2043_);
v_tail_2044_ = lean_ctor_get(v_a_2040_, 1);
lean_inc(v_tail_2044_);
lean_dec_ref_known(v_a_2040_, 2);
lean_inc_ref(v_p_2039_);
v___x_2045_ = lean_apply_1(v_p_2039_, v_head_2043_);
v___x_2046_ = lean_unbox(v___x_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_unsigned_to_nat(1u);
v___x_2048_ = lean_nat_add(v_a_2041_, v___x_2047_);
lean_dec(v_a_2041_);
v_a_2040_ = v_tail_2044_;
v_a_2041_ = v___x_2048_;
goto _start;
}
else
{
lean_object* v___x_2050_; 
lean_dec(v_tail_2044_);
lean_dec_ref(v_p_2039_);
v___x_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_a_2041_);
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go(lean_object* v_00_u03b1_2051_, lean_object* v_p_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_List_findIdx_x3f_go___redArg(v_p_2052_, v_a_2053_, v_a_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f___redArg(lean_object* v_p_2056_, lean_object* v_l_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = l_List_findIdx_x3f_go___redArg(v_p_2056_, v_l_2057_, v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object* v_00_u03b1_2060_, lean_object* v_p_2061_, lean_object* v_l_2062_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = l_List_findIdx_x3f_go___redArg(v_p_2061_, v_l_2062_, v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f___redArg(lean_object* v_inst_2065_, lean_object* v_a_2066_, lean_object* v_l_2067_){
_start:
{
lean_object* v___f_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___f_2068_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2068_, 0, v_inst_2065_);
lean_closure_set(v___f_2068_, 1, v_a_2066_);
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2070_ = l_List_findIdx_x3f_go___redArg(v___f_2068_, v_l_2067_, v___x_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f(lean_object* v_00_u03b1_2071_, lean_object* v_inst_2072_, lean_object* v_a_2073_, lean_object* v_l_2074_){
_start:
{
lean_object* v___f_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___f_2075_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2075_, 0, v_inst_2072_);
lean_closure_set(v___f_2075_, 1, v_a_2073_);
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = l_List_findIdx_x3f_go___redArg(v___f_2075_, v_l_2074_, v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___redArg(lean_object* v_p_2078_, lean_object* v_l_x27_2079_, lean_object* v_i_2080_){
_start:
{
if (lean_obj_tag(v_l_x27_2079_) == 0)
{
lean_object* v___x_2081_; 
lean_dec(v_i_2080_);
lean_dec_ref(v_p_2078_);
v___x_2081_ = lean_box(0);
return v___x_2081_;
}
else
{
lean_object* v_head_2082_; lean_object* v_tail_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_head_2082_ = lean_ctor_get(v_l_x27_2079_, 0);
lean_inc(v_head_2082_);
v_tail_2083_ = lean_ctor_get(v_l_x27_2079_, 1);
lean_inc(v_tail_2083_);
lean_dec_ref_known(v_l_x27_2079_, 2);
lean_inc_ref(v_p_2078_);
v___x_2084_ = lean_apply_1(v_p_2078_, v_head_2082_);
v___x_2085_ = lean_unbox(v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_unsigned_to_nat(1u);
v___x_2087_ = lean_nat_add(v_i_2080_, v___x_2086_);
lean_dec(v_i_2080_);
v_l_x27_2079_ = v_tail_2083_;
v_i_2080_ = v___x_2087_;
goto _start;
}
else
{
lean_object* v___x_2089_; 
lean_dec(v_tail_2083_);
lean_dec_ref(v_p_2078_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_i_2080_);
return v___x_2089_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go(lean_object* v_00_u03b1_2090_, lean_object* v_p_2091_, lean_object* v_l_2092_, lean_object* v_l_x27_2093_, lean_object* v_i_2094_, lean_object* v_h_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_List_findFinIdx_x3f_go___redArg(v_p_2091_, v_l_x27_2093_, v_i_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___boxed(lean_object* v_00_u03b1_2097_, lean_object* v_p_2098_, lean_object* v_l_2099_, lean_object* v_l_x27_2100_, lean_object* v_i_2101_, lean_object* v_h_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_List_findFinIdx_x3f_go(v_00_u03b1_2097_, v_p_2098_, v_l_2099_, v_l_x27_2100_, v_i_2101_, v_h_2102_);
lean_dec(v_l_2099_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f___redArg(lean_object* v_p_2104_, lean_object* v_l_2105_){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = l_List_findFinIdx_x3f_go___redArg(v_p_2104_, v_l_2105_, v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f(lean_object* v_00_u03b1_2108_, lean_object* v_p_2109_, lean_object* v_l_2110_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = l_List_findFinIdx_x3f_go___redArg(v_p_2109_, v_l_2110_, v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f___redArg(lean_object* v_inst_2113_, lean_object* v_a_2114_, lean_object* v_l_2115_){
_start:
{
lean_object* v___f_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___f_2116_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2116_, 0, v_inst_2113_);
lean_closure_set(v___f_2116_, 1, v_a_2114_);
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = l_List_findFinIdx_x3f_go___redArg(v___f_2116_, v_l_2115_, v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f(lean_object* v_00_u03b1_2119_, lean_object* v_inst_2120_, lean_object* v_a_2121_, lean_object* v_l_2122_){
_start:
{
lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___f_2123_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2123_, 0, v_inst_2120_);
lean_closure_set(v___f_2123_, 1, v_a_2121_);
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = l_List_findFinIdx_x3f_go___redArg(v___f_2123_, v_l_2122_, v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___redArg(lean_object* v_p_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
if (lean_obj_tag(v_a_2127_) == 0)
{
lean_dec_ref(v_p_2126_);
return v_a_2128_;
}
else
{
lean_object* v_head_2129_; lean_object* v_tail_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v_head_2129_ = lean_ctor_get(v_a_2127_, 0);
lean_inc(v_head_2129_);
v_tail_2130_ = lean_ctor_get(v_a_2127_, 1);
lean_inc(v_tail_2130_);
lean_dec_ref_known(v_a_2127_, 2);
lean_inc_ref(v_p_2126_);
v___x_2131_ = lean_apply_1(v_p_2126_, v_head_2129_);
v___x_2132_ = lean_unbox(v___x_2131_);
if (v___x_2132_ == 0)
{
v_a_2127_ = v_tail_2130_;
goto _start;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_unsigned_to_nat(1u);
v___x_2135_ = lean_nat_add(v_a_2128_, v___x_2134_);
lean_dec(v_a_2128_);
v_a_2127_ = v_tail_2130_;
v_a_2128_ = v___x_2135_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go(lean_object* v_00_u03b1_2137_, lean_object* v_p_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_List_countP_go___redArg(v_p_2138_, v_a_2139_, v_a_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_List_countP___redArg(lean_object* v_p_2142_, lean_object* v_l_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = l_List_countP_go___redArg(v_p_2142_, v_l_2143_, v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_List_countP(lean_object* v_00_u03b1_2146_, lean_object* v_p_2147_, lean_object* v_l_2148_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = l_List_countP_go___redArg(v_p_2147_, v_l_2148_, v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_List_count___redArg(lean_object* v_inst_2151_, lean_object* v_a_2152_, lean_object* v_l_2153_){
_start:
{
lean_object* v___f_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___f_2154_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2154_, 0, v_inst_2151_);
lean_closure_set(v___f_2154_, 1, v_a_2152_);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = l_List_countP_go___redArg(v___f_2154_, v_l_2153_, v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_List_count(lean_object* v_00_u03b1_2157_, lean_object* v_inst_2158_, lean_object* v_a_2159_, lean_object* v_l_2160_){
_start:
{
lean_object* v___f_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___f_2161_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2161_, 0, v_inst_2158_);
lean_closure_set(v___f_2161_, 1, v_a_2159_);
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = l_List_countP_go___redArg(v___f_2161_, v_l_2160_, v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___redArg(lean_object* v_inst_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_){
_start:
{
if (lean_obj_tag(v_x_2166_) == 0)
{
lean_object* v___x_2167_; 
lean_dec(v_x_2165_);
lean_dec_ref(v_inst_2164_);
v___x_2167_ = lean_box(0);
return v___x_2167_;
}
else
{
lean_object* v_head_2168_; lean_object* v_tail_2169_; lean_object* v_fst_2170_; lean_object* v_snd_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v_head_2168_ = lean_ctor_get(v_x_2166_, 0);
lean_inc(v_head_2168_);
v_tail_2169_ = lean_ctor_get(v_x_2166_, 1);
lean_inc(v_tail_2169_);
lean_dec_ref_known(v_x_2166_, 2);
v_fst_2170_ = lean_ctor_get(v_head_2168_, 0);
lean_inc(v_fst_2170_);
v_snd_2171_ = lean_ctor_get(v_head_2168_, 1);
lean_inc(v_snd_2171_);
lean_dec(v_head_2168_);
lean_inc_ref(v_inst_2164_);
lean_inc(v_x_2165_);
v___x_2172_ = lean_apply_2(v_inst_2164_, v_x_2165_, v_fst_2170_);
v___x_2173_ = lean_unbox(v___x_2172_);
if (v___x_2173_ == 0)
{
lean_dec(v_snd_2171_);
v_x_2166_ = v_tail_2169_;
goto _start;
}
else
{
lean_object* v___x_2175_; 
lean_dec(v_tail_2169_);
lean_dec(v_x_2165_);
lean_dec_ref(v_inst_2164_);
v___x_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2175_, 0, v_snd_2171_);
return v___x_2175_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup(lean_object* v_00_u03b1_2176_, lean_object* v_00_u03b2_2177_, lean_object* v_inst_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_List_lookup___redArg(v_inst_2178_, v_x_2179_, v_x_2180_);
return v___x_2181_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0));
v___x_2200_ = l_String_toRawSubstring_x27(v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object* v_x_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
lean_inc(v_x_2220_);
v___x_2224_ = l_Lean_Syntax_isOfKind(v_x_2220_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v_x_2220_);
v___x_2225_ = lean_box(1);
v___x_2226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v_a_2222_);
return v___x_2226_;
}
else
{
lean_object* v_quotContext_2227_; lean_object* v_currMacroScope_2228_; lean_object* v_ref_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_quotContext_2227_ = lean_ctor_get(v_a_2221_, 1);
v_currMacroScope_2228_ = lean_ctor_get(v_a_2221_, 2);
v_ref_2229_ = lean_ctor_get(v_a_2221_, 5);
v___x_2230_ = lean_unsigned_to_nat(0u);
v___x_2231_ = l_Lean_Syntax_getArg(v_x_2220_, v___x_2230_);
v___x_2232_ = lean_unsigned_to_nat(2u);
v___x_2233_ = l_Lean_Syntax_getArg(v_x_2220_, v___x_2232_);
lean_dec(v_x_2220_);
v___x_2234_ = 0;
v___x_2235_ = l_Lean_SourceInfo_fromRef(v_ref_2229_, v___x_2234_);
v___x_2236_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_2237_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
v___x_2238_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2));
lean_inc(v_currMacroScope_2228_);
lean_inc(v_quotContext_2227_);
v___x_2239_ = l_Lean_addMacroScope(v_quotContext_2227_, v___x_2238_, v_currMacroScope_2228_);
v___x_2240_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8));
lean_inc_n(v___x_2235_, 2);
v___x_2241_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2235_);
lean_ctor_set(v___x_2241_, 1, v___x_2237_);
lean_ctor_set(v___x_2241_, 2, v___x_2239_);
lean_ctor_set(v___x_2241_, 3, v___x_2240_);
v___x_2242_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_2243_ = l_Lean_Syntax_node2(v___x_2235_, v___x_2242_, v___x_2231_, v___x_2233_);
v___x_2244_ = l_Lean_Syntax_node2(v___x_2235_, v___x_2236_, v___x_2241_, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v_a_2222_);
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___boxed(lean_object* v_x_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(v_x_2246_, v_a_2247_, v_a_2248_);
lean_dec_ref(v_a_2247_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object* v_x_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_2250_);
v___x_2254_ = l_Lean_Syntax_isOfKind(v_x_2250_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec(v_x_2250_);
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v_a_2252_);
return v___x_2256_;
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2257_ = lean_unsigned_to_nat(0u);
v___x_2258_ = l_Lean_Syntax_getArg(v_x_2250_, v___x_2257_);
v___x_2259_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_2258_);
v___x_2260_ = l_Lean_Syntax_isOfKind(v___x_2258_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec(v___x_2258_);
lean_dec(v_x_2250_);
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
lean_ctor_set(v___x_2262_, 1, v_a_2252_);
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2263_ = lean_unsigned_to_nat(1u);
v___x_2264_ = l_Lean_Syntax_getArg(v_x_2250_, v___x_2263_);
lean_dec(v_x_2250_);
v___x_2265_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2264_);
v___x_2266_ = l_Lean_Syntax_matchesNull(v___x_2264_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_dec(v___x_2264_);
lean_dec(v___x_2258_);
v___x_2267_ = lean_box(0);
v___x_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v_a_2252_);
return v___x_2268_;
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v_ref_2271_; uint8_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2269_ = l_Lean_Syntax_getArg(v___x_2264_, v___x_2257_);
v___x_2270_ = l_Lean_Syntax_getArg(v___x_2264_, v___x_2263_);
lean_dec(v___x_2264_);
v_ref_2271_ = l_Lean_replaceRef(v___x_2258_, v_a_2251_);
lean_dec(v___x_2258_);
v___x_2272_ = 0;
v___x_2273_ = l_Lean_SourceInfo_fromRef(v_ref_2271_, v___x_2272_);
lean_dec(v_ref_2271_);
v___x_2274_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
v___x_2275_ = ((lean_object*)(l_List_term___x7e___00__closed__2));
lean_inc(v___x_2273_);
v___x_2276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2273_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_Syntax_node3(v___x_2273_, v___x_2274_, v___x_2269_, v___x_2276_, v___x_2270_);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v_a_2252_);
return v___x_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object* v_x_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(v_x_2279_, v_a_2280_, v_a_2281_);
lean_dec(v_a_2280_);
return v_res_2282_;
}
}
LEAN_EXPORT uint8_t l_List_any___redArg(lean_object* v_x_2283_, lean_object* v_x_2284_){
_start:
{
if (lean_obj_tag(v_x_2283_) == 0)
{
uint8_t v___x_2285_; 
lean_dec_ref(v_x_2284_);
v___x_2285_ = 0;
return v___x_2285_;
}
else
{
lean_object* v_head_2286_; lean_object* v_tail_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_head_2286_ = lean_ctor_get(v_x_2283_, 0);
lean_inc(v_head_2286_);
v_tail_2287_ = lean_ctor_get(v_x_2283_, 1);
lean_inc(v_tail_2287_);
lean_dec_ref_known(v_x_2283_, 2);
lean_inc_ref(v_x_2284_);
v___x_2288_ = lean_apply_1(v_x_2284_, v_head_2286_);
v___x_2289_ = lean_unbox(v___x_2288_);
if (v___x_2289_ == 0)
{
v_x_2283_ = v_tail_2287_;
goto _start;
}
else
{
uint8_t v___x_2291_; 
lean_dec(v_tail_2287_);
lean_dec_ref(v_x_2284_);
v___x_2291_ = lean_unbox(v___x_2288_);
return v___x_2291_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___redArg___boxed(lean_object* v_x_2292_, lean_object* v_x_2293_){
_start:
{
uint8_t v_res_2294_; lean_object* v_r_2295_; 
v_res_2294_ = l_List_any___redArg(v_x_2292_, v_x_2293_);
v_r_2295_ = lean_box(v_res_2294_);
return v_r_2295_;
}
}
LEAN_EXPORT uint8_t l_List_any(lean_object* v_00_u03b1_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = l_List_any___redArg(v_x_2297_, v_x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_List_any___boxed(lean_object* v_00_u03b1_2300_, lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
uint8_t v_res_2303_; lean_object* v_r_2304_; 
v_res_2303_ = l_List_any(v_00_u03b1_2300_, v_x_2301_, v_x_2302_);
v_r_2304_ = lean_box(v_res_2303_);
return v_r_2304_;
}
}
LEAN_EXPORT uint8_t l_List_all___redArg(lean_object* v_x_2305_, lean_object* v_x_2306_){
_start:
{
if (lean_obj_tag(v_x_2305_) == 0)
{
uint8_t v___x_2307_; 
lean_dec_ref(v_x_2306_);
v___x_2307_ = 1;
return v___x_2307_;
}
else
{
lean_object* v_head_2308_; lean_object* v_tail_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v_head_2308_ = lean_ctor_get(v_x_2305_, 0);
lean_inc(v_head_2308_);
v_tail_2309_ = lean_ctor_get(v_x_2305_, 1);
lean_inc(v_tail_2309_);
lean_dec_ref_known(v_x_2305_, 2);
lean_inc_ref(v_x_2306_);
v___x_2310_ = lean_apply_1(v_x_2306_, v_head_2308_);
v___x_2311_ = lean_unbox(v___x_2310_);
if (v___x_2311_ == 0)
{
uint8_t v___x_2312_; 
lean_dec(v_tail_2309_);
lean_dec_ref(v_x_2306_);
v___x_2312_ = lean_unbox(v___x_2310_);
return v___x_2312_;
}
else
{
v_x_2305_ = v_tail_2309_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___redArg___boxed(lean_object* v_x_2314_, lean_object* v_x_2315_){
_start:
{
uint8_t v_res_2316_; lean_object* v_r_2317_; 
v_res_2316_ = l_List_all___redArg(v_x_2314_, v_x_2315_);
v_r_2317_ = lean_box(v_res_2316_);
return v_r_2317_;
}
}
LEAN_EXPORT uint8_t l_List_all(lean_object* v_00_u03b1_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = l_List_all___redArg(v_x_2319_, v_x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_List_all___boxed(lean_object* v_00_u03b1_2322_, lean_object* v_x_2323_, lean_object* v_x_2324_){
_start:
{
uint8_t v_res_2325_; lean_object* v_r_2326_; 
v_res_2325_ = l_List_all(v_00_u03b1_2322_, v_x_2323_, v_x_2324_);
v_r_2326_ = lean_box(v_res_2325_);
return v_r_2326_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_or_spec__0(lean_object* v_x_2327_){
_start:
{
if (lean_obj_tag(v_x_2327_) == 0)
{
uint8_t v___x_2328_; 
v___x_2328_ = 0;
return v___x_2328_;
}
else
{
lean_object* v_head_2329_; uint8_t v___x_2330_; 
v_head_2329_ = lean_ctor_get(v_x_2327_, 0);
v___x_2330_ = lean_unbox(v_head_2329_);
if (v___x_2330_ == 0)
{
lean_object* v_tail_2331_; 
v_tail_2331_ = lean_ctor_get(v_x_2327_, 1);
v_x_2327_ = v_tail_2331_;
goto _start;
}
else
{
uint8_t v___x_2333_; 
v___x_2333_ = lean_unbox(v_head_2329_);
return v___x_2333_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_or_spec__0___boxed(lean_object* v_x_2334_){
_start:
{
uint8_t v_res_2335_; lean_object* v_r_2336_; 
v_res_2335_ = l_List_any___at___00List_or_spec__0(v_x_2334_);
lean_dec(v_x_2334_);
v_r_2336_ = lean_box(v_res_2335_);
return v_r_2336_;
}
}
LEAN_EXPORT uint8_t l_List_or(lean_object* v_bs_2337_){
_start:
{
uint8_t v___x_2338_; 
v___x_2338_ = l_List_any___at___00List_or_spec__0(v_bs_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object* v_bs_2339_){
_start:
{
uint8_t v_res_2340_; lean_object* v_r_2341_; 
v_res_2340_ = l_List_or(v_bs_2339_);
lean_dec(v_bs_2339_);
v_r_2341_ = lean_box(v_res_2340_);
return v_r_2341_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00List_and_spec__0(lean_object* v_x_2342_){
_start:
{
if (lean_obj_tag(v_x_2342_) == 0)
{
uint8_t v___x_2343_; 
v___x_2343_ = 1;
return v___x_2343_;
}
else
{
lean_object* v_head_2344_; uint8_t v___x_2345_; 
v_head_2344_ = lean_ctor_get(v_x_2342_, 0);
v___x_2345_ = lean_unbox(v_head_2344_);
if (v___x_2345_ == 0)
{
uint8_t v___x_2346_; 
v___x_2346_ = lean_unbox(v_head_2344_);
return v___x_2346_;
}
else
{
lean_object* v_tail_2347_; 
v_tail_2347_ = lean_ctor_get(v_x_2342_, 1);
v_x_2342_ = v_tail_2347_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00List_and_spec__0___boxed(lean_object* v_x_2349_){
_start:
{
uint8_t v_res_2350_; lean_object* v_r_2351_; 
v_res_2350_ = l_List_all___at___00List_and_spec__0(v_x_2349_);
lean_dec(v_x_2349_);
v_r_2351_ = lean_box(v_res_2350_);
return v_r_2351_;
}
}
LEAN_EXPORT uint8_t l_List_and(lean_object* v_bs_2352_){
_start:
{
uint8_t v___x_2353_; 
v___x_2353_ = l_List_all___at___00List_and_spec__0(v_bs_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object* v_bs_2354_){
_start:
{
uint8_t v_res_2355_; lean_object* v_r_2356_; 
v_res_2355_ = l_List_and(v_bs_2354_);
lean_dec(v_bs_2354_);
v_r_2356_ = lean_box(v_res_2355_);
return v_r_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object* v_x_2357_, lean_object* v_x_2358_, lean_object* v_h__1_2359_, lean_object* v_h__2_2360_){
_start:
{
if (lean_obj_tag(v_x_2357_) == 0)
{
lean_object* v___x_2361_; 
lean_dec(v_h__1_2359_);
v___x_2361_ = lean_apply_3(v_h__2_2360_, v_x_2357_, v_x_2358_, lean_box(0));
return v___x_2361_;
}
else
{
if (lean_obj_tag(v_x_2358_) == 0)
{
lean_object* v___x_2362_; 
lean_dec(v_h__1_2359_);
v___x_2362_ = lean_apply_3(v_h__2_2360_, v_x_2357_, v_x_2358_, lean_box(0));
return v___x_2362_;
}
else
{
lean_object* v_head_2363_; lean_object* v_tail_2364_; lean_object* v_head_2365_; lean_object* v_tail_2366_; lean_object* v___x_2367_; 
lean_dec(v_h__2_2360_);
v_head_2363_ = lean_ctor_get(v_x_2357_, 0);
lean_inc(v_head_2363_);
v_tail_2364_ = lean_ctor_get(v_x_2357_, 1);
lean_inc(v_tail_2364_);
lean_dec_ref_known(v_x_2357_, 2);
v_head_2365_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_head_2365_);
v_tail_2366_ = lean_ctor_get(v_x_2358_, 1);
lean_inc(v_tail_2366_);
lean_dec_ref_known(v_x_2358_, 2);
v___x_2367_ = lean_apply_4(v_h__1_2359_, v_head_2363_, v_tail_2364_, v_head_2365_, v_tail_2366_);
return v___x_2367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object* v_00_u03b1_2368_, lean_object* v_00_u03b2_2369_, lean_object* v_motive_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_, lean_object* v_h__1_2373_, lean_object* v_h__2_2374_){
_start:
{
if (lean_obj_tag(v_x_2371_) == 0)
{
lean_object* v___x_2375_; 
lean_dec(v_h__1_2373_);
v___x_2375_ = lean_apply_3(v_h__2_2374_, v_x_2371_, v_x_2372_, lean_box(0));
return v___x_2375_;
}
else
{
if (lean_obj_tag(v_x_2372_) == 0)
{
lean_object* v___x_2376_; 
lean_dec(v_h__1_2373_);
v___x_2376_ = lean_apply_3(v_h__2_2374_, v_x_2371_, v_x_2372_, lean_box(0));
return v___x_2376_;
}
else
{
lean_object* v_head_2377_; lean_object* v_tail_2378_; lean_object* v_head_2379_; lean_object* v_tail_2380_; lean_object* v___x_2381_; 
lean_dec(v_h__2_2374_);
v_head_2377_ = lean_ctor_get(v_x_2371_, 0);
lean_inc(v_head_2377_);
v_tail_2378_ = lean_ctor_get(v_x_2371_, 1);
lean_inc(v_tail_2378_);
lean_dec_ref_known(v_x_2371_, 2);
v_head_2379_ = lean_ctor_get(v_x_2372_, 0);
lean_inc(v_head_2379_);
v_tail_2380_ = lean_ctor_get(v_x_2372_, 1);
lean_inc(v_tail_2380_);
lean_dec_ref_known(v_x_2372_, 2);
v___x_2381_ = lean_apply_4(v_h__1_2373_, v_head_2377_, v_tail_2378_, v_head_2379_, v_tail_2380_);
return v___x_2381_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__0(lean_object* v_f_2382_, lean_object* v_b_2383_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = lean_box(0);
v___x_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2385_, 0, v_b_2383_);
v___x_2386_ = lean_apply_2(v_f_2382_, v___x_2384_, v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__1(lean_object* v_f_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v_a_2388_);
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_apply_2(v_f_2387_, v___x_2389_, v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object* v_f_2392_, lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
if (lean_obj_tag(v_x_2393_) == 0)
{
lean_object* v___f_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___f_2395_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2395_, 0, v_f_2392_);
v___x_2396_ = lean_box(0);
v___x_2397_ = l_List_mapTR_loop___redArg(v___f_2395_, v_x_2394_, v___x_2396_);
return v___x_2397_;
}
else
{
if (lean_obj_tag(v_x_2394_) == 0)
{
lean_object* v___f_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___f_2398_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2398_, 0, v_f_2392_);
v___x_2399_ = lean_box(0);
v___x_2400_ = l_List_mapTR_loop___redArg(v___f_2398_, v_x_2393_, v___x_2399_);
return v___x_2400_;
}
else
{
lean_object* v_head_2401_; lean_object* v_tail_2402_; lean_object* v_head_2403_; lean_object* v_tail_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2415_; 
v_head_2401_ = lean_ctor_get(v_x_2393_, 0);
lean_inc(v_head_2401_);
v_tail_2402_ = lean_ctor_get(v_x_2393_, 1);
lean_inc(v_tail_2402_);
lean_dec_ref_known(v_x_2393_, 2);
v_head_2403_ = lean_ctor_get(v_x_2394_, 0);
v_tail_2404_ = lean_ctor_get(v_x_2394_, 1);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_x_2394_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2406_ = v_x_2394_;
v_isShared_2407_ = v_isSharedCheck_2415_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_tail_2404_);
lean_inc(v_head_2403_);
lean_dec(v_x_2394_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2415_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_head_2401_);
v___x_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2409_, 0, v_head_2403_);
lean_inc(v_f_2392_);
v___x_2410_ = lean_apply_2(v_f_2392_, v___x_2408_, v___x_2409_);
v___x_2411_ = l_List_zipWithAll___redArg(v_f_2392_, v_tail_2402_, v_tail_2404_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 1, v___x_2411_);
lean_ctor_set(v___x_2406_, 0, v___x_2410_);
v___x_2413_ = v___x_2406_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object* v_00_u03b1_2416_, lean_object* v_00_u03b2_2417_, lean_object* v_00_u03b3_2418_, lean_object* v_f_2419_, lean_object* v_x_2420_, lean_object* v_x_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_List_zipWithAll___redArg(v_f_2419_, v_x_2420_, v_x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_List_range_loop(lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_zero_2425_; uint8_t v_isZero_2426_; 
v_zero_2425_ = lean_unsigned_to_nat(0u);
v_isZero_2426_ = lean_nat_dec_eq(v_a_2423_, v_zero_2425_);
if (v_isZero_2426_ == 1)
{
lean_dec(v_a_2423_);
return v_a_2424_;
}
else
{
lean_object* v_one_2427_; lean_object* v_n_2428_; lean_object* v___x_2429_; 
v_one_2427_ = lean_unsigned_to_nat(1u);
v_n_2428_ = lean_nat_sub(v_a_2423_, v_one_2427_);
lean_dec(v_a_2423_);
lean_inc(v_n_2428_);
v___x_2429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_n_2428_);
lean_ctor_set(v___x_2429_, 1, v_a_2424_);
v_a_2423_ = v_n_2428_;
v_a_2424_ = v___x_2429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range(lean_object* v_n_2431_){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_box(0);
v___x_2433_ = l_List_range_loop(v_n_2431_, v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object* v_inst_2434_, lean_object* v_x_2435_){
_start:
{
if (lean_obj_tag(v_x_2435_) == 0)
{
lean_object* v___x_2436_; 
lean_dec(v_inst_2434_);
v___x_2436_ = lean_box(0);
return v___x_2436_;
}
else
{
lean_object* v_head_2437_; lean_object* v_tail_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_head_2437_ = lean_ctor_get(v_x_2435_, 0);
lean_inc(v_head_2437_);
v_tail_2438_ = lean_ctor_get(v_x_2435_, 1);
lean_inc(v_tail_2438_);
lean_dec_ref_known(v_x_2435_, 2);
v___x_2439_ = l_List_foldl___redArg(v_inst_2434_, v_head_2437_, v_tail_2438_);
v___x_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object* v_00_u03b1_2441_, lean_object* v_inst_2442_, lean_object* v_x_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_List_min_x3f___redArg(v_inst_2442_, v_x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object* v_inst_2445_, lean_object* v_x_2446_){
_start:
{
lean_object* v_head_2447_; lean_object* v_tail_2448_; lean_object* v___x_2449_; 
v_head_2447_ = lean_ctor_get(v_x_2446_, 0);
lean_inc(v_head_2447_);
v_tail_2448_ = lean_ctor_get(v_x_2446_, 1);
lean_inc(v_tail_2448_);
lean_dec(v_x_2446_);
v___x_2449_ = l_List_foldl___redArg(v_inst_2445_, v_head_2447_, v_tail_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_List_min(lean_object* v_00_u03b1_2450_, lean_object* v_inst_2451_, lean_object* v_x_2452_, lean_object* v_x_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_List_min___redArg(v_inst_2451_, v_x_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object* v_inst_2455_, lean_object* v_x_2456_){
_start:
{
if (lean_obj_tag(v_x_2456_) == 0)
{
lean_object* v___x_2457_; 
lean_dec(v_inst_2455_);
v___x_2457_ = lean_box(0);
return v___x_2457_;
}
else
{
lean_object* v_head_2458_; lean_object* v_tail_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_head_2458_ = lean_ctor_get(v_x_2456_, 0);
lean_inc(v_head_2458_);
v_tail_2459_ = lean_ctor_get(v_x_2456_, 1);
lean_inc(v_tail_2459_);
lean_dec_ref_known(v_x_2456_, 2);
v___x_2460_ = l_List_foldl___redArg(v_inst_2455_, v_head_2458_, v_tail_2459_);
v___x_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
return v___x_2461_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object* v_00_u03b1_2462_, lean_object* v_inst_2463_, lean_object* v_x_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_List_max_x3f___redArg(v_inst_2463_, v_x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object* v_inst_2466_, lean_object* v_x_2467_){
_start:
{
lean_object* v_head_2468_; lean_object* v_tail_2469_; lean_object* v___x_2470_; 
v_head_2468_ = lean_ctor_get(v_x_2467_, 0);
lean_inc(v_head_2468_);
v_tail_2469_ = lean_ctor_get(v_x_2467_, 1);
lean_inc(v_tail_2469_);
lean_dec(v_x_2467_);
v___x_2470_ = l_List_foldl___redArg(v_inst_2466_, v_head_2468_, v_tail_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_List_max(lean_object* v_00_u03b1_2471_, lean_object* v_inst_2472_, lean_object* v_x_2473_, lean_object* v_x_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_List_max___redArg(v_inst_2472_, v_x_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(lean_object* v___x_2476_, lean_object* v_x_2477_){
_start:
{
if (lean_obj_tag(v_x_2477_) == 0)
{
uint8_t v___x_2478_; 
lean_dec_ref(v___x_2476_);
v___x_2478_ = 0;
return v___x_2478_;
}
else
{
lean_object* v_head_2479_; lean_object* v_tail_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_head_2479_ = lean_ctor_get(v_x_2477_, 0);
lean_inc(v_head_2479_);
v_tail_2480_ = lean_ctor_get(v_x_2477_, 1);
lean_inc(v_tail_2480_);
lean_dec_ref_known(v_x_2477_, 2);
lean_inc_ref(v___x_2476_);
v___x_2481_ = lean_apply_1(v___x_2476_, v_head_2479_);
v___x_2482_ = lean_unbox(v___x_2481_);
if (v___x_2482_ == 0)
{
v_x_2477_ = v_tail_2480_;
goto _start;
}
else
{
uint8_t v___x_2484_; 
lean_dec(v_tail_2480_);
lean_dec_ref(v___x_2476_);
v___x_2484_ = lean_unbox(v___x_2481_);
return v___x_2484_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg___boxed(lean_object* v___x_2485_, lean_object* v_x_2486_){
_start:
{
uint8_t v_res_2487_; lean_object* v_r_2488_; 
v_res_2487_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2485_, v_x_2486_);
v_r_2488_ = lean_box(v_res_2487_);
return v_r_2488_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object* v_r_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
if (lean_obj_tag(v_a_2490_) == 0)
{
lean_object* v___x_2492_; 
lean_dec_ref(v_r_2489_);
v___x_2492_ = l_List_reverse___redArg(v_a_2491_);
return v___x_2492_;
}
else
{
lean_object* v_head_2493_; lean_object* v_tail_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2505_; 
v_head_2493_ = lean_ctor_get(v_a_2490_, 0);
v_tail_2494_ = lean_ctor_get(v_a_2490_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_a_2490_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2496_ = v_a_2490_;
v_isShared_2497_ = v_isSharedCheck_2505_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_tail_2494_);
lean_inc(v_head_2493_);
lean_dec(v_a_2490_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2505_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; uint8_t v___x_2499_; 
lean_inc_ref(v_r_2489_);
lean_inc(v_head_2493_);
v___x_2498_ = lean_apply_1(v_r_2489_, v_head_2493_);
lean_inc(v_a_2491_);
v___x_2499_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2498_, v_a_2491_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2501_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 1, v_a_2491_);
v___x_2501_ = v___x_2496_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_head_2493_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_a_2491_);
v___x_2501_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
v_a_2490_ = v_tail_2494_;
v_a_2491_ = v___x_2501_;
goto _start;
}
}
else
{
lean_del_object(v___x_2496_);
lean_dec(v_head_2493_);
v_a_2490_ = v_tail_2494_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object* v_00_u03b1_2506_, lean_object* v_r_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_List_eraseDupsBy_loop___redArg(v_r_2507_, v_a_2508_, v_a_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0(lean_object* v_00_u03b1_2511_, lean_object* v___x_2512_, lean_object* v_x_2513_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2512_, v_x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___boxed(lean_object* v_00_u03b1_2515_, lean_object* v___x_2516_, lean_object* v_x_2517_){
_start:
{
uint8_t v_res_2518_; lean_object* v_r_2519_; 
v_res_2518_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0(v_00_u03b1_2515_, v___x_2516_, v_x_2517_);
v_r_2519_ = lean_box(v_res_2518_);
return v_r_2519_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy___redArg(lean_object* v_r_2520_, lean_object* v_as_2521_){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_box(0);
v___x_2523_ = l_List_eraseDupsBy_loop___redArg(v_r_2520_, v_as_2521_, v___x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy(lean_object* v_00_u03b1_2524_, lean_object* v_r_2525_, lean_object* v_as_2526_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_List_eraseDupsBy___redArg(v_r_2525_, v_as_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT uint8_t l_List_eraseDups___redArg___lam__0(lean_object* v_inst_2528_, lean_object* v_x1_2529_, lean_object* v_x2_2530_){
_start:
{
lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2531_ = lean_apply_2(v_inst_2528_, v_x1_2529_, v_x2_2530_);
v___x_2532_ = lean_unbox(v___x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg___lam__0___boxed(lean_object* v_inst_2533_, lean_object* v_x1_2534_, lean_object* v_x2_2535_){
_start:
{
uint8_t v_res_2536_; lean_object* v_r_2537_; 
v_res_2536_ = l_List_eraseDups___redArg___lam__0(v_inst_2533_, v_x1_2534_, v_x2_2535_);
v_r_2537_ = lean_box(v_res_2536_);
return v_r_2537_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg(lean_object* v_inst_2538_, lean_object* v_as_2539_){
_start:
{
lean_object* v___f_2540_; lean_object* v___x_2541_; 
v___f_2540_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2540_, 0, v_inst_2538_);
v___x_2541_ = l_List_eraseDupsBy___redArg(v___f_2540_, v_as_2539_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object* v_00_u03b1_2542_, lean_object* v_inst_2543_, lean_object* v_as_2544_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_List_eraseDups___redArg(v_inst_2543_, v_as_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop___redArg(lean_object* v_r_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
if (lean_obj_tag(v_a_2548_) == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec_ref(v_r_2546_);
v___x_2550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2550_, 0, v_a_2547_);
lean_ctor_set(v___x_2550_, 1, v_a_2549_);
v___x_2551_ = l_List_reverse___redArg(v___x_2550_);
return v___x_2551_;
}
else
{
lean_object* v_head_2552_; lean_object* v_tail_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2564_; 
v_head_2552_ = lean_ctor_get(v_a_2548_, 0);
v_tail_2553_ = lean_ctor_get(v_a_2548_, 1);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_a_2548_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2555_ = v_a_2548_;
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_tail_2553_);
lean_inc(v_head_2552_);
lean_dec(v_a_2548_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; uint8_t v___x_2558_; 
lean_inc_ref(v_r_2546_);
lean_inc(v_head_2552_);
lean_inc(v_a_2547_);
v___x_2557_ = lean_apply_2(v_r_2546_, v_a_2547_, v_head_2552_);
v___x_2558_ = lean_unbox(v___x_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2560_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v_a_2549_);
lean_ctor_set(v___x_2555_, 0, v_a_2547_);
v___x_2560_ = v___x_2555_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_a_2549_);
v___x_2560_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
v_a_2547_ = v_head_2552_;
v_a_2548_ = v_tail_2553_;
v_a_2549_ = v___x_2560_;
goto _start;
}
}
else
{
lean_del_object(v___x_2555_);
lean_dec(v_head_2552_);
v_a_2548_ = v_tail_2553_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop(lean_object* v_00_u03b1_2565_, lean_object* v_r_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_List_eraseRepsBy_loop___redArg(v_r_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy___redArg(lean_object* v_r_2571_, lean_object* v_x_2572_){
_start:
{
if (lean_obj_tag(v_x_2572_) == 0)
{
lean_dec_ref(v_r_2571_);
return v_x_2572_;
}
else
{
lean_object* v_head_2573_; lean_object* v_tail_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_head_2573_ = lean_ctor_get(v_x_2572_, 0);
lean_inc(v_head_2573_);
v_tail_2574_ = lean_ctor_get(v_x_2572_, 1);
lean_inc(v_tail_2574_);
lean_dec_ref_known(v_x_2572_, 2);
v___x_2575_ = lean_box(0);
v___x_2576_ = l_List_eraseRepsBy_loop___redArg(v_r_2571_, v_head_2573_, v_tail_2574_, v___x_2575_);
return v___x_2576_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy(lean_object* v_00_u03b1_2577_, lean_object* v_r_2578_, lean_object* v_x_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_List_eraseRepsBy___redArg(v_r_2578_, v_x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___redArg(lean_object* v_inst_2581_, lean_object* v_as_2582_){
_start:
{
lean_object* v___f_2583_; lean_object* v___x_2584_; 
v___f_2583_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2583_, 0, v_inst_2581_);
v___x_2584_ = l_List_eraseRepsBy___redArg(v___f_2583_, v_as_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object* v_00_u03b1_2585_, lean_object* v_inst_2586_, lean_object* v_as_2587_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_List_eraseReps___redArg(v_inst_2586_, v_as_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___redArg(lean_object* v_p_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
if (lean_obj_tag(v_a_2590_) == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec_ref(v_p_2589_);
v___x_2592_ = l_List_reverse___redArg(v_a_2591_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v_a_2590_);
return v___x_2593_;
}
else
{
lean_object* v_head_2594_; lean_object* v_tail_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v_head_2594_ = lean_ctor_get(v_a_2590_, 0);
v_tail_2595_ = lean_ctor_get(v_a_2590_, 1);
lean_inc_ref(v_p_2589_);
lean_inc(v_head_2594_);
v___x_2596_ = lean_apply_1(v_p_2589_, v_head_2594_);
v___x_2597_ = lean_unbox(v___x_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec_ref(v_p_2589_);
v___x_2598_ = l_List_reverse___redArg(v_a_2591_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
lean_ctor_set(v___x_2599_, 1, v_a_2590_);
return v___x_2599_;
}
else
{
lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2607_; 
lean_inc(v_tail_2595_);
lean_inc(v_head_2594_);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_a_2590_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; lean_object* v_unused_2609_; 
v_unused_2608_ = lean_ctor_get(v_a_2590_, 1);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v_a_2590_, 0);
lean_dec(v_unused_2609_);
v___x_2601_ = v_a_2590_;
v_isShared_2602_ = v_isSharedCheck_2607_;
goto v_resetjp_2600_;
}
else
{
lean_dec(v_a_2590_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2607_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 1, v_a_2591_);
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_head_2594_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_a_2591_);
v___x_2604_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
v_a_2590_ = v_tail_2595_;
v_a_2591_ = v___x_2604_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop(lean_object* v_00_u03b1_2610_, lean_object* v_p_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_List_span_loop___redArg(v_p_2611_, v_a_2612_, v_a_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_List_span___redArg(lean_object* v_p_2615_, lean_object* v_as_2616_){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = lean_box(0);
v___x_2618_ = l_List_span_loop___redArg(v_p_2615_, v_as_2616_, v___x_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_List_span(lean_object* v_00_u03b1_2619_, lean_object* v_p_2620_, lean_object* v_as_2621_){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = lean_box(0);
v___x_2623_ = l_List_span_loop___redArg(v_p_2620_, v_as_2621_, v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___redArg(lean_object* v_R_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
if (lean_obj_tag(v_a_2625_) == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec_ref(v_R_2624_);
v___x_2629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2629_, 0, v_a_2626_);
lean_ctor_set(v___x_2629_, 1, v_a_2627_);
v___x_2630_ = l_List_reverse___redArg(v___x_2629_);
v___x_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
lean_ctor_set(v___x_2631_, 1, v_a_2628_);
v___x_2632_ = l_List_reverse___redArg(v___x_2631_);
return v___x_2632_;
}
else
{
lean_object* v_head_2633_; lean_object* v_tail_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2651_; 
v_head_2633_ = lean_ctor_get(v_a_2625_, 0);
v_tail_2634_ = lean_ctor_get(v_a_2625_, 1);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_a_2625_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2636_ = v_a_2625_;
v_isShared_2637_ = v_isSharedCheck_2651_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_tail_2634_);
lean_inc(v_head_2633_);
lean_dec(v_a_2625_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2651_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
lean_inc_ref(v_R_2624_);
lean_inc(v_head_2633_);
lean_inc(v_a_2626_);
v___x_2638_ = lean_apply_2(v_R_2624_, v_a_2626_, v_head_2633_);
v___x_2639_ = lean_unbox(v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
v___x_2640_ = lean_box(0);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 1, v_a_2627_);
lean_ctor_set(v___x_2636_, 0, v_a_2626_);
v___x_2642_ = v___x_2636_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2626_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_a_2627_);
v___x_2642_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = l_List_reverse___redArg(v___x_2642_);
v___x_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
lean_ctor_set(v___x_2644_, 1, v_a_2628_);
v_a_2625_ = v_tail_2634_;
v_a_2626_ = v_head_2633_;
v_a_2627_ = v___x_2640_;
v_a_2628_ = v___x_2644_;
goto _start;
}
}
else
{
lean_object* v___x_2648_; 
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 1, v_a_2627_);
lean_ctor_set(v___x_2636_, 0, v_a_2626_);
v___x_2648_ = v___x_2636_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2626_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_a_2627_);
v___x_2648_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
v_a_2625_ = v_tail_2634_;
v_a_2626_ = v_head_2633_;
v_a_2627_ = v___x_2648_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop(lean_object* v_00_u03b1_2652_, lean_object* v_R_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_List_splitBy_loop___redArg(v_R_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___redArg(lean_object* v_R_2659_, lean_object* v_x_2660_){
_start:
{
if (lean_obj_tag(v_x_2660_) == 0)
{
lean_object* v___x_2661_; 
lean_dec_ref(v_R_2659_);
v___x_2661_ = lean_box(0);
return v___x_2661_;
}
else
{
lean_object* v_head_2662_; lean_object* v_tail_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v_head_2662_ = lean_ctor_get(v_x_2660_, 0);
lean_inc(v_head_2662_);
v_tail_2663_ = lean_ctor_get(v_x_2660_, 1);
lean_inc(v_tail_2663_);
lean_dec_ref_known(v_x_2660_, 2);
v___x_2664_ = lean_box(0);
v___x_2665_ = l_List_splitBy_loop___redArg(v_R_2659_, v_tail_2663_, v_head_2662_, v___x_2664_, v___x_2664_);
return v___x_2665_;
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy(lean_object* v_00_u03b1_2666_, lean_object* v_R_2667_, lean_object* v_x_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_List_splitBy___redArg(v_R_2667_, v_x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___redArg___lam__0(lean_object* v_inst_2670_, lean_object* v_ys_2671_, lean_object* v_x_2672_){
_start:
{
uint8_t v___x_2673_; 
v___x_2673_ = l_List_elem___redArg(v_inst_2670_, v_x_2672_, v_ys_2671_);
if (v___x_2673_ == 0)
{
uint8_t v___x_2674_; 
v___x_2674_ = 1;
return v___x_2674_;
}
else
{
uint8_t v___x_2675_; 
v___x_2675_ = 0;
return v___x_2675_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg___lam__0___boxed(lean_object* v_inst_2676_, lean_object* v_ys_2677_, lean_object* v_x_2678_){
_start:
{
uint8_t v_res_2679_; lean_object* v_r_2680_; 
v_res_2679_ = l_List_removeAll___redArg___lam__0(v_inst_2676_, v_ys_2677_, v_x_2678_);
v_r_2680_ = lean_box(v_res_2679_);
return v_r_2680_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg(lean_object* v_inst_2681_, lean_object* v_xs_2682_, lean_object* v_ys_2683_){
_start:
{
lean_object* v___f_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___f_2684_ = lean_alloc_closure((void*)(l_List_removeAll___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2684_, 0, v_inst_2681_);
lean_closure_set(v___f_2684_, 1, v_ys_2683_);
v___x_2685_ = lean_box(0);
v___x_2686_ = l_List_filterTR_loop___redArg(v___f_2684_, v_xs_2682_, v___x_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll(lean_object* v_00_u03b1_2687_, lean_object* v_inst_2688_, lean_object* v_xs_2689_, lean_object* v_ys_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_List_removeAll___redArg(v_inst_2688_, v_xs_2689_, v_ys_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object* v_step_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_zero_2696_; uint8_t v_isZero_2697_; 
v_zero_2696_ = lean_unsigned_to_nat(0u);
v_isZero_2697_ = lean_nat_dec_eq(v_a_2693_, v_zero_2696_);
if (v_isZero_2697_ == 1)
{
lean_dec(v_a_2694_);
lean_dec(v_a_2693_);
return v_a_2695_;
}
else
{
lean_object* v_one_2698_; lean_object* v_n_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_one_2698_ = lean_unsigned_to_nat(1u);
v_n_2699_ = lean_nat_sub(v_a_2693_, v_one_2698_);
lean_dec(v_a_2693_);
v___x_2700_ = lean_nat_sub(v_a_2694_, v_step_2692_);
lean_dec(v_a_2694_);
lean_inc(v___x_2700_);
v___x_2701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v_a_2695_);
v_a_2693_ = v_n_2699_;
v_a_2694_ = v___x_2700_;
v_a_2695_ = v___x_2701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object* v_step_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_List_range_x27TR_go(v_step_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
lean_dec(v_step_2703_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object* v_s_2708_, lean_object* v_n_2709_, lean_object* v_step_2710_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2711_ = lean_nat_mul(v_step_2710_, v_n_2709_);
v___x_2712_ = lean_nat_add(v_s_2708_, v___x_2711_);
lean_dec(v___x_2711_);
v___x_2713_ = lean_box(0);
v___x_2714_ = l_List_range_x27TR_go(v_step_2710_, v_n_2709_, v___x_2712_, v___x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object* v_s_2715_, lean_object* v_n_2716_, lean_object* v_step_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_List_range_x27TR(v_s_2715_, v_n_2716_, v_step_2717_);
lean_dec(v_step_2717_);
lean_dec(v_s_2715_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(lean_object* v_x_2719_, lean_object* v_x_2720_, lean_object* v_x_2721_, lean_object* v_h__1_2722_, lean_object* v_h__2_2723_){
_start:
{
lean_object* v_zero_2724_; uint8_t v_isZero_2725_; 
v_zero_2724_ = lean_unsigned_to_nat(0u);
v_isZero_2725_ = lean_nat_dec_eq(v_x_2719_, v_zero_2724_);
if (v_isZero_2725_ == 1)
{
lean_object* v___x_2726_; 
lean_dec(v_h__2_2723_);
v___x_2726_ = lean_apply_2(v_h__1_2722_, v_x_2720_, v_x_2721_);
return v___x_2726_;
}
else
{
lean_object* v_one_2727_; lean_object* v_n_2728_; lean_object* v___x_2729_; 
lean_dec(v_h__1_2722_);
v_one_2727_ = lean_unsigned_to_nat(1u);
v_n_2728_ = lean_nat_sub(v_x_2719_, v_one_2727_);
v___x_2729_ = lean_apply_3(v_h__2_2723_, v_n_2728_, v_x_2720_, v_x_2721_);
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(lean_object* v_x_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_, lean_object* v_h__1_2733_, lean_object* v_h__2_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(v_x_2730_, v_x_2731_, v_x_2732_, v_h__1_2733_, v_h__2_2734_);
lean_dec(v_x_2730_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object* v_motive_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_, lean_object* v_x_2739_, lean_object* v_h__1_2740_, lean_object* v_h__2_2741_){
_start:
{
lean_object* v_zero_2742_; uint8_t v_isZero_2743_; 
v_zero_2742_ = lean_unsigned_to_nat(0u);
v_isZero_2743_ = lean_nat_dec_eq(v_x_2737_, v_zero_2742_);
if (v_isZero_2743_ == 1)
{
lean_object* v___x_2744_; 
lean_dec(v_h__2_2741_);
v___x_2744_ = lean_apply_2(v_h__1_2740_, v_x_2738_, v_x_2739_);
return v___x_2744_;
}
else
{
lean_object* v_one_2745_; lean_object* v_n_2746_; lean_object* v___x_2747_; 
lean_dec(v_h__1_2740_);
v_one_2745_ = lean_unsigned_to_nat(1u);
v_n_2746_ = lean_nat_sub(v_x_2737_, v_one_2745_);
v___x_2747_ = lean_apply_3(v_h__2_2741_, v_n_2746_, v_x_2738_, v_x_2739_);
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(lean_object* v_motive_2748_, lean_object* v_x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v_h__1_2752_, lean_object* v_h__2_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(v_motive_2748_, v_x_2749_, v_x_2750_, v_x_2751_, v_h__1_2752_, v_h__2_2753_);
lean_dec(v_x_2749_);
return v_res_2754_;
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
