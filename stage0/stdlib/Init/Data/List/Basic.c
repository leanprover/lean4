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
static lean_object* _init_l_List_lex___auto__1___closed__25(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_List_lex___auto__1___closed__24));
v___x_289_ = lean_string_utf8_byte_size(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_290_ = lean_obj_once(&l_List_lex___auto__1___closed__25, &l_List_lex___auto__1___closed__25_once, _init_l_List_lex___auto__1___closed__25);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = ((lean_object*)(l_List_lex___auto__1___closed__24));
v___x_293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_291_);
lean_ctor_set(v___x_293_, 2, v___x_290_);
return v___x_293_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_294_ = lean_box(0);
v___x_295_ = lean_box(0);
v___x_296_ = lean_obj_once(&l_List_lex___auto__1___closed__26, &l_List_lex___auto__1___closed__26_once, _init_l_List_lex___auto__1___closed__26);
v___x_297_ = lean_box(2);
v___x_298_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
lean_ctor_set(v___x_298_, 2, v___x_295_);
lean_ctor_set(v___x_298_, 3, v___x_294_);
return v___x_298_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_obj_once(&l_List_lex___auto__1___closed__27, &l_List_lex___auto__1___closed__27_once, _init_l_List_lex___auto__1___closed__27);
v___x_300_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_301_ = lean_array_push(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = lean_obj_once(&l_List_lex___auto__1___closed__28, &l_List_lex___auto__1___closed__28_once, _init_l_List_lex___auto__1___closed__28);
v___x_303_ = ((lean_object*)(l_List_lex___auto__1___closed__23));
v___x_304_ = lean_box(2);
v___x_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
lean_ctor_set(v___x_305_, 2, v___x_302_);
return v___x_305_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_307_ = lean_obj_once(&l_List_lex___auto__1___closed__21, &l_List_lex___auto__1___closed__21_once, _init_l_List_lex___auto__1___closed__21);
v___x_308_ = lean_array_push(v___x_307_, v___x_306_);
return v___x_308_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_obj_once(&l_List_lex___auto__1___closed__30, &l_List_lex___auto__1___closed__30_once, _init_l_List_lex___auto__1___closed__30);
v___x_310_ = ((lean_object*)(l_List_lex___auto__1___closed__18));
v___x_311_ = lean_box(2);
v___x_312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___x_310_);
lean_ctor_set(v___x_312_, 2, v___x_309_);
return v___x_312_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_obj_once(&l_List_lex___auto__1___closed__31, &l_List_lex___auto__1___closed__31_once, _init_l_List_lex___auto__1___closed__31);
v___x_314_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_315_ = lean_array_push(v___x_314_, v___x_313_);
return v___x_315_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_List_lex___auto__1___closed__37));
v___x_327_ = l_Lean_mkAtom(v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_List_lex___auto__1___closed__38, &l_List_lex___auto__1___closed__38_once, _init_l_List_lex___auto__1___closed__38);
v___x_329_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_330_ = lean_array_push(v___x_329_, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_332_ = lean_obj_once(&l_List_lex___auto__1___closed__39, &l_List_lex___auto__1___closed__39_once, _init_l_List_lex___auto__1___closed__39);
v___x_333_ = lean_array_push(v___x_332_, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = lean_obj_once(&l_List_lex___auto__1___closed__40, &l_List_lex___auto__1___closed__40_once, _init_l_List_lex___auto__1___closed__40);
v___x_335_ = ((lean_object*)(l_List_lex___auto__1___closed__36));
v___x_336_ = lean_box(2);
v___x_337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
lean_ctor_set(v___x_337_, 2, v___x_334_);
return v___x_337_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_339_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_340_ = lean_array_push(v___x_339_, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l_List_lex___auto__1___closed__43));
v___x_343_ = l_Lean_mkAtom(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_obj_once(&l_List_lex___auto__1___closed__44, &l_List_lex___auto__1___closed__44_once, _init_l_List_lex___auto__1___closed__44);
v___x_345_ = lean_obj_once(&l_List_lex___auto__1___closed__42, &l_List_lex___auto__1___closed__42_once, _init_l_List_lex___auto__1___closed__42);
v___x_346_ = lean_array_push(v___x_345_, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_348_ = lean_obj_once(&l_List_lex___auto__1___closed__45, &l_List_lex___auto__1___closed__45_once, _init_l_List_lex___auto__1___closed__45);
v___x_349_ = lean_array_push(v___x_348_, v___x_347_);
return v___x_349_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_350_ = lean_obj_once(&l_List_lex___auto__1___closed__46, &l_List_lex___auto__1___closed__46_once, _init_l_List_lex___auto__1___closed__46);
v___x_351_ = ((lean_object*)(l_List_lex___auto__1___closed__34));
v___x_352_ = lean_box(2);
v___x_353_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
lean_ctor_set(v___x_353_, 2, v___x_350_);
return v___x_353_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__48(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_obj_once(&l_List_lex___auto__1___closed__47, &l_List_lex___auto__1___closed__47_once, _init_l_List_lex___auto__1___closed__47);
v___x_355_ = lean_obj_once(&l_List_lex___auto__1___closed__32, &l_List_lex___auto__1___closed__32_once, _init_l_List_lex___auto__1___closed__32);
v___x_356_ = lean_array_push(v___x_355_, v___x_354_);
return v___x_356_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__50(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_List_lex___auto__1___closed__49));
v___x_359_ = l_Lean_mkAtom(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__51(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_obj_once(&l_List_lex___auto__1___closed__50, &l_List_lex___auto__1___closed__50_once, _init_l_List_lex___auto__1___closed__50);
v___x_361_ = lean_obj_once(&l_List_lex___auto__1___closed__48, &l_List_lex___auto__1___closed__48_once, _init_l_List_lex___auto__1___closed__48);
v___x_362_ = lean_array_push(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__52(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_363_ = lean_obj_once(&l_List_lex___auto__1___closed__51, &l_List_lex___auto__1___closed__51_once, _init_l_List_lex___auto__1___closed__51);
v___x_364_ = ((lean_object*)(l_List_lex___auto__1___closed__16));
v___x_365_ = lean_box(2);
v___x_366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
lean_ctor_set(v___x_366_, 2, v___x_363_);
return v___x_366_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__53(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_obj_once(&l_List_lex___auto__1___closed__52, &l_List_lex___auto__1___closed__52_once, _init_l_List_lex___auto__1___closed__52);
v___x_368_ = lean_obj_once(&l_List_lex___auto__1___closed__13, &l_List_lex___auto__1___closed__13_once, _init_l_List_lex___auto__1___closed__13);
v___x_369_ = lean_array_push(v___x_368_, v___x_367_);
return v___x_369_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__54(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_370_ = lean_obj_once(&l_List_lex___auto__1___closed__53, &l_List_lex___auto__1___closed__53_once, _init_l_List_lex___auto__1___closed__53);
v___x_371_ = ((lean_object*)(l_List_lex___auto__1___closed__11));
v___x_372_ = lean_box(2);
v___x_373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_370_);
return v___x_373_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__55(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_obj_once(&l_List_lex___auto__1___closed__54, &l_List_lex___auto__1___closed__54_once, _init_l_List_lex___auto__1___closed__54);
v___x_375_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_376_ = lean_array_push(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__56(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = lean_obj_once(&l_List_lex___auto__1___closed__55, &l_List_lex___auto__1___closed__55_once, _init_l_List_lex___auto__1___closed__55);
v___x_378_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_379_ = lean_box(2);
v___x_380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
lean_ctor_set(v___x_380_, 2, v___x_377_);
return v___x_380_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__57(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_obj_once(&l_List_lex___auto__1___closed__56, &l_List_lex___auto__1___closed__56_once, _init_l_List_lex___auto__1___closed__56);
v___x_382_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_383_ = lean_array_push(v___x_382_, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__58(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_obj_once(&l_List_lex___auto__1___closed__57, &l_List_lex___auto__1___closed__57_once, _init_l_List_lex___auto__1___closed__57);
v___x_385_ = ((lean_object*)(l_List_lex___auto__1___closed__7));
v___x_386_ = lean_box(2);
v___x_387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
lean_ctor_set(v___x_387_, 2, v___x_384_);
return v___x_387_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__59(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = lean_obj_once(&l_List_lex___auto__1___closed__58, &l_List_lex___auto__1___closed__58_once, _init_l_List_lex___auto__1___closed__58);
v___x_389_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_390_ = lean_array_push(v___x_389_, v___x_388_);
return v___x_390_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__60(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_391_ = lean_obj_once(&l_List_lex___auto__1___closed__59, &l_List_lex___auto__1___closed__59_once, _init_l_List_lex___auto__1___closed__59);
v___x_392_ = ((lean_object*)(l_List_lex___auto__1___closed__4));
v___x_393_ = lean_box(2);
v___x_394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_391_);
return v___x_394_;
}
}
static lean_object* _init_l_List_lex___auto__1(void){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_obj_once(&l_List_lex___auto__1___closed__60, &l_List_lex___auto__1___closed__60_once, _init_l_List_lex___auto__1___closed__60);
return v___x_395_;
}
}
LEAN_EXPORT uint8_t l_List_lex___redArg(lean_object* v_inst_396_, lean_object* v_l_u2081_397_, lean_object* v_l_u2082_398_, lean_object* v_lt_399_){
_start:
{
if (lean_obj_tag(v_l_u2081_397_) == 0)
{
lean_dec_ref(v_lt_399_);
lean_dec_ref(v_inst_396_);
if (lean_obj_tag(v_l_u2082_398_) == 0)
{
uint8_t v___x_400_; 
v___x_400_ = 0;
return v___x_400_;
}
else
{
uint8_t v___x_401_; 
lean_dec_ref_known(v_l_u2082_398_, 2);
v___x_401_ = 1;
return v___x_401_;
}
}
else
{
if (lean_obj_tag(v_l_u2082_398_) == 0)
{
uint8_t v___x_402_; 
lean_dec_ref_known(v_l_u2081_397_, 2);
lean_dec_ref(v_lt_399_);
lean_dec_ref(v_inst_396_);
v___x_402_ = 0;
return v___x_402_;
}
else
{
lean_object* v_head_403_; lean_object* v_tail_404_; lean_object* v_head_405_; lean_object* v_tail_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_head_403_ = lean_ctor_get(v_l_u2081_397_, 0);
lean_inc_n(v_head_403_, 2);
v_tail_404_ = lean_ctor_get(v_l_u2081_397_, 1);
lean_inc(v_tail_404_);
lean_dec_ref_known(v_l_u2081_397_, 2);
v_head_405_ = lean_ctor_get(v_l_u2082_398_, 0);
lean_inc_n(v_head_405_, 2);
v_tail_406_ = lean_ctor_get(v_l_u2082_398_, 1);
lean_inc(v_tail_406_);
lean_dec_ref_known(v_l_u2082_398_, 2);
lean_inc_ref(v_lt_399_);
v___x_407_ = lean_apply_2(v_lt_399_, v_head_403_, v_head_405_);
v___x_408_ = lean_unbox(v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; uint8_t v___x_410_; 
lean_inc_ref(v_inst_396_);
v___x_409_ = lean_apply_2(v_inst_396_, v_head_403_, v_head_405_);
v___x_410_ = lean_unbox(v___x_409_);
if (v___x_410_ == 0)
{
uint8_t v___x_411_; 
lean_dec(v_tail_406_);
lean_dec(v_tail_404_);
lean_dec_ref(v_lt_399_);
lean_dec_ref(v_inst_396_);
v___x_411_ = lean_unbox(v___x_409_);
return v___x_411_;
}
else
{
v_l_u2081_397_ = v_tail_404_;
v_l_u2082_398_ = v_tail_406_;
goto _start;
}
}
else
{
uint8_t v___x_413_; 
lean_dec(v_tail_406_);
lean_dec(v_head_405_);
lean_dec(v_tail_404_);
lean_dec(v_head_403_);
lean_dec_ref(v_lt_399_);
lean_dec_ref(v_inst_396_);
v___x_413_ = lean_unbox(v___x_407_);
return v___x_413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_lex___redArg___boxed(lean_object* v_inst_414_, lean_object* v_l_u2081_415_, lean_object* v_l_u2082_416_, lean_object* v_lt_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_List_lex___redArg(v_inst_414_, v_l_u2081_415_, v_l_u2082_416_, v_lt_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT uint8_t l_List_lex(lean_object* v_00_u03b1_420_, lean_object* v_inst_421_, lean_object* v_l_u2081_422_, lean_object* v_l_u2082_423_, lean_object* v_lt_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_List_lex___redArg(v_inst_421_, v_l_u2081_422_, v_l_u2082_423_, v_lt_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_List_lex___boxed(lean_object* v_00_u03b1_426_, lean_object* v_inst_427_, lean_object* v_l_u2081_428_, lean_object* v_l_u2082_429_, lean_object* v_lt_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_List_lex(v_00_u03b1_426_, v_inst_427_, v_l_u2081_428_, v_l_u2082_429_, v_lt_430_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg(lean_object* v_x_433_){
_start:
{
lean_object* v_tail_434_; 
v_tail_434_ = lean_ctor_get(v_x_433_, 1);
if (lean_obj_tag(v_tail_434_) == 0)
{
lean_object* v_head_435_; 
v_head_435_ = lean_ctor_get(v_x_433_, 0);
lean_inc(v_head_435_);
return v_head_435_;
}
else
{
v_x_433_ = v_tail_434_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg___boxed(lean_object* v_x_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_List_getLast___redArg(v_x_437_);
lean_dec(v_x_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_List_getLast(lean_object* v_00_u03b1_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_List_getLast___redArg(v_x_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___boxed(lean_object* v_00_u03b1_443_, lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_List_getLast(v_00_u03b1_443_, v_x_444_, v_x_445_);
lean_dec(v_x_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg(lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v___x_448_; 
v___x_448_ = lean_box(0);
return v___x_448_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = l_List_getLast___redArg(v_x_447_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg___boxed(lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_List_getLast_x3f___redArg(v_x_451_);
lean_dec(v_x_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f(lean_object* v_00_u03b1_453_, lean_object* v_x_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_List_getLast_x3f___redArg(v_x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___boxed(lean_object* v_00_u03b1_456_, lean_object* v_x_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_List_getLast_x3f(v_00_u03b1_456_, v_x_457_);
lean_dec(v_x_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg(lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_inc(v_x_460_);
return v_x_460_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = l_List_getLast___redArg(v_x_459_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg___boxed(lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_List_getLastD___redArg(v_x_462_, v_x_463_);
lean_dec(v_x_463_);
lean_dec(v_x_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD(lean_object* v_00_u03b1_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_List_getLastD___redArg(v_x_466_, v_x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___boxed(lean_object* v_00_u03b1_469_, lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_List_getLastD(v_00_u03b1_469_, v_x_470_, v_x_471_);
lean_dec(v_x_471_);
lean_dec(v_x_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg(lean_object* v_x_473_){
_start:
{
lean_object* v_head_474_; 
v_head_474_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_head_474_);
return v_head_474_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg___boxed(lean_object* v_x_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_List_head___redArg(v_x_475_);
lean_dec(v_x_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_List_head(lean_object* v_00_u03b1_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_head_480_; 
v_head_480_ = lean_ctor_get(v_x_478_, 0);
lean_inc(v_head_480_);
return v_head_480_;
}
}
LEAN_EXPORT lean_object* l_List_head___boxed(lean_object* v_00_u03b1_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_List_head(v_00_u03b1_481_, v_x_482_, v_x_483_);
lean_dec(v_x_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg(lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v___x_486_; 
v___x_486_ = lean_box(0);
return v___x_486_;
}
else
{
lean_object* v_head_487_; lean_object* v___x_488_; 
v_head_487_ = lean_ctor_get(v_x_485_, 0);
lean_inc(v_head_487_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v_head_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg___boxed(lean_object* v_x_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_List_head_x3f___redArg(v_x_489_);
lean_dec(v_x_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f(lean_object* v_00_u03b1_491_, lean_object* v_x_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_List_head_x3f___redArg(v_x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___boxed(lean_object* v_00_u03b1_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_List_head_x3f(v_00_u03b1_494_, v_x_495_);
lean_dec(v_x_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg(lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_497_) == 0)
{
lean_inc(v_x_498_);
return v_x_498_;
}
else
{
lean_object* v_head_499_; 
v_head_499_ = lean_ctor_get(v_x_497_, 0);
lean_inc(v_head_499_);
return v_head_499_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg___boxed(lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_List_headD___redArg(v_x_500_, v_x_501_);
lean_dec(v_x_501_);
lean_dec(v_x_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_List_headD(lean_object* v_00_u03b1_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
lean_inc(v_x_505_);
return v_x_505_;
}
else
{
lean_object* v_head_506_; 
v_head_506_ = lean_ctor_get(v_x_504_, 0);
lean_inc(v_head_506_);
return v_head_506_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___boxed(lean_object* v_00_u03b1_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_List_headD(v_00_u03b1_507_, v_x_508_, v_x_509_);
lean_dec(v_x_509_);
lean_dec(v_x_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg(lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_511_) == 0)
{
return v_x_511_;
}
else
{
lean_object* v_tail_512_; 
v_tail_512_ = lean_ctor_get(v_x_511_, 1);
lean_inc(v_tail_512_);
return v_tail_512_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg___boxed(lean_object* v_x_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_List_tail___redArg(v_x_513_);
lean_dec(v_x_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_List_tail(lean_object* v_00_u03b1_515_, lean_object* v_x_516_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
return v_x_516_;
}
else
{
lean_object* v_tail_517_; 
v_tail_517_ = lean_ctor_get(v_x_516_, 1);
lean_inc(v_tail_517_);
return v_tail_517_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___boxed(lean_object* v_00_u03b1_518_, lean_object* v_x_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_List_tail(v_00_u03b1_518_, v_x_519_);
lean_dec(v_x_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg(lean_object* v_x_521_){
_start:
{
if (lean_obj_tag(v_x_521_) == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_box(0);
return v___x_522_;
}
else
{
lean_object* v_tail_523_; lean_object* v___x_524_; 
v_tail_523_ = lean_ctor_get(v_x_521_, 1);
lean_inc(v_tail_523_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v_tail_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg___boxed(lean_object* v_x_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_List_tail_x3f___redArg(v_x_525_);
lean_dec(v_x_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f(lean_object* v_00_u03b1_527_, lean_object* v_x_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_List_tail_x3f___redArg(v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___boxed(lean_object* v_00_u03b1_530_, lean_object* v_x_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_List_tail_x3f(v_00_u03b1_530_, v_x_531_);
lean_dec(v_x_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg(lean_object* v_l_533_, lean_object* v_fallback_534_){
_start:
{
if (lean_obj_tag(v_l_533_) == 0)
{
lean_inc(v_fallback_534_);
return v_fallback_534_;
}
else
{
lean_object* v_tail_535_; 
v_tail_535_ = lean_ctor_get(v_l_533_, 1);
lean_inc(v_tail_535_);
return v_tail_535_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg___boxed(lean_object* v_l_536_, lean_object* v_fallback_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_List_tailD___redArg(v_l_536_, v_fallback_537_);
lean_dec(v_fallback_537_);
lean_dec(v_l_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_List_tailD(lean_object* v_00_u03b1_539_, lean_object* v_l_540_, lean_object* v_fallback_541_){
_start:
{
if (lean_obj_tag(v_l_540_) == 0)
{
lean_inc(v_fallback_541_);
return v_fallback_541_;
}
else
{
lean_object* v_tail_542_; 
v_tail_542_ = lean_ctor_get(v_l_540_, 1);
lean_inc(v_tail_542_);
return v_tail_542_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___boxed(lean_object* v_00_u03b1_543_, lean_object* v_l_544_, lean_object* v_fallback_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_List_tailD(v_00_u03b1_543_, v_l_544_, v_fallback_545_);
lean_dec(v_fallback_545_);
lean_dec(v_l_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_List_filter___redArg(lean_object* v_p_547_, lean_object* v_x_548_){
_start:
{
if (lean_obj_tag(v_x_548_) == 0)
{
lean_dec_ref(v_p_547_);
return v_x_548_;
}
else
{
lean_object* v_head_549_; lean_object* v_tail_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_561_; 
v_head_549_ = lean_ctor_get(v_x_548_, 0);
v_tail_550_ = lean_ctor_get(v_x_548_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_x_548_);
if (v_isSharedCheck_561_ == 0)
{
v___x_552_ = v_x_548_;
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_tail_550_);
lean_inc(v_head_549_);
lean_dec(v_x_548_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
lean_inc_ref(v_p_547_);
lean_inc(v_head_549_);
v___x_554_ = lean_apply_1(v_p_547_, v_head_549_);
v___x_555_ = lean_unbox(v___x_554_);
if (v___x_555_ == 0)
{
lean_del_object(v___x_552_);
lean_dec(v_head_549_);
v_x_548_ = v_tail_550_;
goto _start;
}
else
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = l_List_filter___redArg(v_p_547_, v_tail_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_557_);
v___x_559_ = v___x_552_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_head_549_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filter(lean_object* v_00_u03b1_562_, lean_object* v_p_563_, lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_List_filter___redArg(v_p_563_, v_x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg(lean_object* v_f_566_, lean_object* v_init_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_dec(v_f_566_);
lean_inc(v_init_567_);
return v_init_567_;
}
else
{
lean_object* v_head_569_; lean_object* v_tail_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_head_569_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_head_569_);
v_tail_570_ = lean_ctor_get(v_x_568_, 1);
lean_inc(v_tail_570_);
lean_dec_ref_known(v_x_568_, 2);
lean_inc(v_f_566_);
v___x_571_ = l_List_foldr___redArg(v_f_566_, v_init_567_, v_tail_570_);
v___x_572_ = lean_apply_2(v_f_566_, v_head_569_, v___x_571_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg___boxed(lean_object* v_f_573_, lean_object* v_init_574_, lean_object* v_x_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_List_foldr___redArg(v_f_573_, v_init_574_, v_x_575_);
lean_dec(v_init_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_List_foldr(lean_object* v_00_u03b1_577_, lean_object* v_00_u03b2_578_, lean_object* v_f_579_, lean_object* v_init_580_, lean_object* v_x_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_List_foldr___redArg(v_f_579_, v_init_580_, v_x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___boxed(lean_object* v_00_u03b1_583_, lean_object* v_00_u03b2_584_, lean_object* v_f_585_, lean_object* v_init_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_List_foldr(v_00_u03b1_583_, v_00_u03b2_584_, v_f_585_, v_init_586_, v_x_587_);
lean_dec(v_init_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_List_reverseAux___redArg(lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
return v_x_590_;
}
else
{
lean_object* v_head_591_; lean_object* v_tail_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_head_591_ = lean_ctor_get(v_x_589_, 0);
v_tail_592_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v_x_589_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_tail_592_);
lean_inc(v_head_591_);
lean_dec(v_x_589_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v_x_590_);
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_head_591_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_x_590_);
v___x_597_ = v_reuseFailAlloc_599_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
v_x_589_ = v_tail_592_;
v_x_590_ = v___x_597_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object* v_00_u03b1_601_, lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_List_reverseAux___redArg(v_x_602_, v_x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_List_reverse___redArg(lean_object* v_as_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_box(0);
v___x_607_ = l_List_reverseAux___redArg(v_as_605_, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_List_reverse(lean_object* v_00_u03b1_608_, lean_object* v_as_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_List_reverse___redArg(v_as_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_h__1_613_, lean_object* v_h__2_614_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
lean_object* v___x_615_; 
lean_dec(v_h__2_614_);
v___x_615_ = lean_apply_1(v_h__1_613_, v_x_612_);
return v___x_615_;
}
else
{
lean_object* v_head_616_; lean_object* v_tail_617_; lean_object* v___x_618_; 
lean_dec(v_h__1_613_);
v_head_616_ = lean_ctor_get(v_x_611_, 0);
lean_inc(v_head_616_);
v_tail_617_ = lean_ctor_get(v_x_611_, 1);
lean_inc(v_tail_617_);
lean_dec_ref_known(v_x_611_, 2);
v___x_618_ = lean_apply_3(v_h__2_614_, v_head_616_, v_tail_617_, v_x_612_);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_619_, lean_object* v_motive_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_h__1_623_, lean_object* v_h__2_624_){
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
lean_dec_ref_known(v_x_621_, 2);
v___x_628_ = lean_apply_3(v_h__2_624_, v_head_626_, v_tail_627_, v_x_622_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_List_appendTR___redArg(lean_object* v_as_629_, lean_object* v_bs_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = l_List_reverse___redArg(v_as_629_);
v___x_632_ = l_List_reverseAux___redArg(v___x_631_, v_bs_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR(lean_object* v_00_u03b1_633_, lean_object* v_as_634_, lean_object* v_bs_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_List_appendTR___redArg(v_as_634_, v_bs_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter___redArg(lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_h__1_639_, lean_object* v_h__2_640_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v___x_641_; 
lean_dec(v_h__2_640_);
v___x_641_ = lean_apply_1(v_h__1_639_, v_x_638_);
return v___x_641_;
}
else
{
lean_object* v_head_642_; lean_object* v_tail_643_; lean_object* v___x_644_; 
lean_dec(v_h__1_639_);
v_head_642_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_head_642_);
v_tail_643_ = lean_ctor_get(v_x_637_, 1);
lean_inc(v_tail_643_);
lean_dec_ref_known(v_x_637_, 2);
v___x_644_ = lean_apply_3(v_h__2_640_, v_head_642_, v_tail_643_, v_x_638_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_append_match__1_splitter(lean_object* v_00_u03b1_645_, lean_object* v_motive_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_h__1_649_, lean_object* v_h__2_650_){
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
lean_dec_ref_known(v_x_647_, 2);
v___x_654_ = lean_apply_3(v_h__2_650_, v_head_652_, v_tail_653_, v_x_648_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l_List_instAppend___redArg(){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = ((lean_object*)(l_List_instAppend___redArg___closed__0));
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend___redArg___boxed(lean_object* v___dummy_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_List_instAppend___redArg();
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend(lean_object* v_00_u03b1_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = ((lean_object*)(l_List_instAppend___redArg___closed__0));
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_List_singleton___redArg(lean_object* v_a_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_664_, 0, v_a_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_List_singleton(lean_object* v_00_u03b1_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_box(0);
v___x_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_668_, 0, v_a_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg(lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
lean_object* v_zero_671_; uint8_t v_isZero_672_; 
v_zero_671_ = lean_unsigned_to_nat(0u);
v_isZero_672_ = lean_nat_dec_eq(v_x_669_, v_zero_671_);
if (v_isZero_672_ == 1)
{
lean_object* v___x_673_; 
lean_dec(v_x_670_);
v___x_673_ = lean_box(0);
return v___x_673_;
}
else
{
lean_object* v_one_674_; lean_object* v_n_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_one_674_ = lean_unsigned_to_nat(1u);
v_n_675_ = lean_nat_sub(v_x_669_, v_one_674_);
lean_inc(v_x_670_);
v___x_676_ = l_List_replicate___redArg(v_n_675_, v_x_670_);
lean_dec(v_n_675_);
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v_x_670_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg___boxed(lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_List_replicate___redArg(v_x_678_, v_x_679_);
lean_dec(v_x_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_List_replicate(lean_object* v_00_u03b1_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_List_replicate___redArg(v_x_682_, v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___boxed(lean_object* v_00_u03b1_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_List_replicate(v_00_u03b1_685_, v_x_686_, v_x_687_);
lean_dec(v_x_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg(lean_object* v_n_689_, lean_object* v_a_690_, lean_object* v_l_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = l_List_length___redArg(v_l_691_);
v___x_693_ = lean_nat_sub(v_n_689_, v___x_692_);
lean_dec(v___x_692_);
v___x_694_ = l_List_replicate___redArg(v___x_693_, v_a_690_);
lean_dec(v___x_693_);
v___x_695_ = l_List_appendTR___redArg(v___x_694_, v_l_691_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg___boxed(lean_object* v_n_696_, lean_object* v_a_697_, lean_object* v_l_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_List_leftpad___redArg(v_n_696_, v_a_697_, v_l_698_);
lean_dec(v_n_696_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad(lean_object* v_00_u03b1_700_, lean_object* v_n_701_, lean_object* v_a_702_, lean_object* v_l_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_List_leftpad___redArg(v_n_701_, v_a_702_, v_l_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___boxed(lean_object* v_00_u03b1_705_, lean_object* v_n_706_, lean_object* v_a_707_, lean_object* v_l_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_List_leftpad(v_00_u03b1_705_, v_n_706_, v_a_707_, v_l_708_);
lean_dec(v_n_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg(lean_object* v_n_710_, lean_object* v_a_711_, lean_object* v_l_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_713_ = l_List_length___redArg(v_l_712_);
v___x_714_ = lean_nat_sub(v_n_710_, v___x_713_);
lean_dec(v___x_713_);
v___x_715_ = l_List_replicate___redArg(v___x_714_, v_a_711_);
lean_dec(v___x_714_);
v___x_716_ = l_List_appendTR___redArg(v_l_712_, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg___boxed(lean_object* v_n_717_, lean_object* v_a_718_, lean_object* v_l_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_List_rightpad___redArg(v_n_717_, v_a_718_, v_l_719_);
lean_dec(v_n_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad(lean_object* v_00_u03b1_721_, lean_object* v_n_722_, lean_object* v_a_723_, lean_object* v_l_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_List_rightpad___redArg(v_n_722_, v_a_723_, v_l_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___boxed(lean_object* v_00_u03b1_726_, lean_object* v_n_727_, lean_object* v_a_728_, lean_object* v_l_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_List_rightpad(v_00_u03b1_726_, v_n_727_, v_a_728_, v_l_729_);
lean_dec(v_n_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg___boxed(lean_object* v___dummy_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_List_instEmptyCollection___redArg();
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object* v_00_u03b1_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_box(0);
return v___x_736_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty___redArg(lean_object* v_x_737_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
{
uint8_t v___x_738_; 
v___x_738_ = 1;
return v___x_738_;
}
else
{
uint8_t v___x_739_; 
v___x_739_ = 0;
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___redArg___boxed(lean_object* v_x_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l_List_isEmpty___redArg(v_x_740_);
lean_dec(v_x_740_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty(lean_object* v_00_u03b1_743_, lean_object* v_x_744_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = l_List_isEmpty___redArg(v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___boxed(lean_object* v_00_u03b1_746_, lean_object* v_x_747_){
_start:
{
uint8_t v_res_748_; lean_object* v_r_749_; 
v_res_748_ = l_List_isEmpty(v_00_u03b1_746_, v_x_747_);
lean_dec(v_x_747_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT uint8_t l_List_elem___redArg(lean_object* v_inst_750_, lean_object* v_a_751_, lean_object* v_x_752_){
_start:
{
if (lean_obj_tag(v_x_752_) == 0)
{
uint8_t v___x_753_; 
lean_dec(v_a_751_);
lean_dec_ref(v_inst_750_);
v___x_753_ = 0;
return v___x_753_;
}
else
{
lean_object* v_head_754_; lean_object* v_tail_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_head_754_ = lean_ctor_get(v_x_752_, 0);
lean_inc(v_head_754_);
v_tail_755_ = lean_ctor_get(v_x_752_, 1);
lean_inc(v_tail_755_);
lean_dec_ref_known(v_x_752_, 2);
lean_inc_ref(v_inst_750_);
lean_inc(v_a_751_);
v___x_756_ = lean_apply_2(v_inst_750_, v_a_751_, v_head_754_);
v___x_757_ = lean_unbox(v___x_756_);
if (v___x_757_ == 0)
{
v_x_752_ = v_tail_755_;
goto _start;
}
else
{
uint8_t v___x_759_; 
lean_dec(v_tail_755_);
lean_dec(v_a_751_);
lean_dec_ref(v_inst_750_);
v___x_759_ = lean_unbox(v___x_756_);
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___redArg___boxed(lean_object* v_inst_760_, lean_object* v_a_761_, lean_object* v_x_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_List_elem___redArg(v_inst_760_, v_a_761_, v_x_762_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT uint8_t l_List_elem(lean_object* v_00_u03b1_765_, lean_object* v_inst_766_, lean_object* v_a_767_, lean_object* v_x_768_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = l_List_elem___redArg(v_inst_766_, v_a_767_, v_x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_List_elem___boxed(lean_object* v_00_u03b1_770_, lean_object* v_inst_771_, lean_object* v_a_772_, lean_object* v_x_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l_List_elem(v_00_u03b1_770_, v_inst_771_, v_a_772_, v_x_773_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT uint8_t l_List_contains___redArg(lean_object* v_inst_776_, lean_object* v_as_777_, lean_object* v_a_778_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = l_List_elem___redArg(v_inst_776_, v_a_778_, v_as_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_List_contains___redArg___boxed(lean_object* v_inst_780_, lean_object* v_as_781_, lean_object* v_a_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_List_contains___redArg(v_inst_780_, v_as_781_, v_a_782_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT uint8_t l_List_contains(lean_object* v_00_u03b1_785_, lean_object* v_inst_786_, lean_object* v_as_787_, lean_object* v_a_788_){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = l_List_elem___redArg(v_inst_786_, v_a_788_, v_as_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_List_contains___boxed(lean_object* v_00_u03b1_790_, lean_object* v_inst_791_, lean_object* v_as_792_, lean_object* v_a_793_){
_start:
{
uint8_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = l_List_contains(v_00_u03b1_790_, v_inst_791_, v_as_792_, v_a_793_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership___redArg(){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = lean_box(0);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership___redArg___boxed(lean_object* v___dummy_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_List_instMembership___redArg();
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership(lean_object* v_00_u03b1_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = lean_box(0);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_802_, lean_object* v_h__1_803_, lean_object* v_h__2_804_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v_h__2_804_);
v___x_805_ = lean_box(0);
v___x_806_ = lean_apply_1(v_h__1_803_, v___x_805_);
return v___x_806_;
}
else
{
lean_object* v_head_807_; lean_object* v_tail_808_; lean_object* v___x_809_; 
lean_dec(v_h__1_803_);
v_head_807_ = lean_ctor_get(v_x_802_, 0);
lean_inc(v_head_807_);
v_tail_808_ = lean_ctor_get(v_x_802_, 1);
lean_inc(v_tail_808_);
lean_dec_ref_known(v_x_802_, 2);
v___x_809_ = lean_apply_2(v_h__2_804_, v_head_807_, v_tail_808_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_810_, lean_object* v_motive_811_, lean_object* v_x_812_, lean_object* v_h__1_813_, lean_object* v_h__2_814_){
_start:
{
if (lean_obj_tag(v_x_812_) == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec(v_h__2_814_);
v___x_815_ = lean_box(0);
v___x_816_ = lean_apply_1(v_h__1_813_, v___x_815_);
return v___x_816_;
}
else
{
lean_object* v_head_817_; lean_object* v_tail_818_; lean_object* v___x_819_; 
lean_dec(v_h__1_813_);
v_head_817_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_head_817_);
v_tail_818_ = lean_ctor_get(v_x_812_, 1);
lean_inc(v_tail_818_);
lean_dec_ref_known(v_x_812_, 2);
v___x_819_ = lean_apply_2(v_h__2_814_, v_head_817_, v_tail_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(uint8_t v_x_820_, lean_object* v_h__1_821_, lean_object* v_h__2_822_){
_start:
{
if (v_x_820_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v_h__1_821_);
v___x_823_ = lean_box(0);
v___x_824_ = lean_apply_1(v_h__2_822_, v___x_823_);
return v___x_824_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec(v_h__2_822_);
v___x_825_ = lean_box(0);
v___x_826_ = lean_apply_1(v_h__1_821_, v___x_825_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_827_, lean_object* v_h__1_828_, lean_object* v_h__2_829_){
_start:
{
uint8_t v_x_24__boxed_830_; lean_object* v_res_831_; 
v_x_24__boxed_830_ = lean_unbox(v_x_827_);
v_res_831_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_830_, v_h__1_828_, v_h__2_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object* v_motive_832_, uint8_t v_x_833_, lean_object* v_h__1_834_, lean_object* v_h__2_835_){
_start:
{
if (v_x_833_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_h__1_834_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_apply_1(v_h__2_835_, v___x_836_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v_h__2_835_);
v___x_838_ = lean_box(0);
v___x_839_ = lean_apply_1(v_h__1_834_, v___x_838_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_840_, lean_object* v_x_841_, lean_object* v_h__1_842_, lean_object* v_h__2_843_){
_start:
{
uint8_t v_x_35__boxed_844_; lean_object* v_res_845_; 
v_x_35__boxed_844_ = lean_unbox(v_x_841_);
v_res_845_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(v_motive_840_, v_x_35__boxed_844_, v_h__1_842_, v_h__2_843_);
return v_res_845_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_846_, lean_object* v_a_847_, lean_object* v_as_848_){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = l_List_elem___redArg(v_inst_846_, v_a_847_, v_as_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_850_, lean_object* v_a_851_, lean_object* v_as_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l_List_instDecidableMemOfLawfulBEq___redArg(v_inst_850_, v_a_851_, v_as_852_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_a_858_, lean_object* v_as_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = l_List_elem___redArg(v_inst_856_, v_a_858_, v_as_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_a_864_, lean_object* v_as_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_List_instDecidableMemOfLawfulBEq(v_00_u03b1_861_, v_inst_862_, v_inst_863_, v_a_864_, v_as_865_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx___redArg(lean_object* v_inst_868_, lean_object* v_x_869_){
_start:
{
if (lean_obj_tag(v_x_869_) == 0)
{
uint8_t v___x_870_; 
lean_dec_ref(v_inst_868_);
v___x_870_ = 0;
return v___x_870_;
}
else
{
lean_object* v_head_871_; lean_object* v_tail_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_head_871_ = lean_ctor_get(v_x_869_, 0);
lean_inc(v_head_871_);
v_tail_872_ = lean_ctor_get(v_x_869_, 1);
lean_inc(v_tail_872_);
lean_dec_ref_known(v_x_869_, 2);
lean_inc_ref(v_inst_868_);
v___x_873_ = lean_apply_1(v_inst_868_, v_head_871_);
v___x_874_ = lean_unbox(v___x_873_);
if (v___x_874_ == 0)
{
uint8_t v_decide_875_; 
v_decide_875_ = l_List_decidableBEx___redArg(v_inst_868_, v_tail_872_);
if (v_decide_875_ == 0)
{
uint8_t v___x_876_; 
v___x_876_ = lean_unbox(v___x_873_);
return v___x_876_;
}
else
{
return v_decide_875_;
}
}
else
{
uint8_t v___x_877_; 
lean_dec(v_tail_872_);
lean_dec_ref(v_inst_868_);
v___x_877_ = lean_unbox(v___x_873_);
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___redArg___boxed(lean_object* v_inst_878_, lean_object* v_x_879_){
_start:
{
uint8_t v_res_880_; lean_object* v_r_881_; 
v_res_880_ = l_List_decidableBEx___redArg(v_inst_878_, v_x_879_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx(lean_object* v_00_u03b1_882_, lean_object* v_p_883_, lean_object* v_inst_884_, lean_object* v_x_885_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = l_List_decidableBEx___redArg(v_inst_884_, v_x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___boxed(lean_object* v_00_u03b1_887_, lean_object* v_p_888_, lean_object* v_inst_889_, lean_object* v_x_890_){
_start:
{
uint8_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_List_decidableBEx(v_00_u03b1_887_, v_p_888_, v_inst_889_, v_x_890_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll___redArg(lean_object* v_inst_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
uint8_t v___x_895_; 
lean_dec_ref(v_inst_893_);
v___x_895_ = 1;
return v___x_895_;
}
else
{
lean_object* v_head_896_; lean_object* v_tail_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_head_896_ = lean_ctor_get(v_x_894_, 0);
lean_inc(v_head_896_);
v_tail_897_ = lean_ctor_get(v_x_894_, 1);
lean_inc(v_tail_897_);
lean_dec_ref_known(v_x_894_, 2);
lean_inc_ref(v_inst_893_);
v___x_898_ = lean_apply_1(v_inst_893_, v_head_896_);
v___x_899_ = lean_unbox(v___x_898_);
if (v___x_899_ == 0)
{
uint8_t v___x_900_; 
lean_dec(v_tail_897_);
lean_dec_ref(v_inst_893_);
v___x_900_ = lean_unbox(v___x_898_);
return v___x_900_;
}
else
{
uint8_t v_decide_901_; 
v_decide_901_ = l_List_decidableBAll___redArg(v_inst_893_, v_tail_897_);
if (v_decide_901_ == 0)
{
return v_decide_901_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = lean_unbox(v___x_898_);
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___redArg___boxed(lean_object* v_inst_903_, lean_object* v_x_904_){
_start:
{
uint8_t v_res_905_; lean_object* v_r_906_; 
v_res_905_ = l_List_decidableBAll___redArg(v_inst_903_, v_x_904_);
v_r_906_ = lean_box(v_res_905_);
return v_r_906_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll(lean_object* v_00_u03b1_907_, lean_object* v_p_908_, lean_object* v_inst_909_, lean_object* v_x_910_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = l_List_decidableBAll___redArg(v_inst_909_, v_x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___boxed(lean_object* v_00_u03b1_912_, lean_object* v_p_913_, lean_object* v_inst_914_, lean_object* v_x_915_){
_start:
{
uint8_t v_res_916_; lean_object* v_r_917_; 
v_res_916_ = l_List_decidableBAll(v_00_u03b1_912_, v_p_913_, v_inst_914_, v_x_915_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_List_take___redArg(lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
lean_object* v_zero_920_; uint8_t v_isZero_921_; 
v_zero_920_ = lean_unsigned_to_nat(0u);
v_isZero_921_ = lean_nat_dec_eq(v_x_918_, v_zero_920_);
if (v_isZero_921_ == 1)
{
lean_object* v___x_922_; 
lean_dec(v_x_919_);
v___x_922_ = lean_box(0);
return v___x_922_;
}
else
{
if (lean_obj_tag(v_x_919_) == 0)
{
return v_x_919_;
}
else
{
lean_object* v_head_923_; lean_object* v_tail_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_934_; 
v_head_923_ = lean_ctor_get(v_x_919_, 0);
v_tail_924_ = lean_ctor_get(v_x_919_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_x_919_);
if (v_isSharedCheck_934_ == 0)
{
v___x_926_ = v_x_919_;
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_tail_924_);
lean_inc(v_head_923_);
lean_dec(v_x_919_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_one_928_; lean_object* v_n_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v_one_928_ = lean_unsigned_to_nat(1u);
v_n_929_ = lean_nat_sub(v_x_918_, v_one_928_);
v___x_930_ = l_List_take___redArg(v_n_929_, v_tail_924_);
lean_dec(v_n_929_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_930_);
v___x_932_ = v___x_926_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_head_923_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_take___redArg___boxed(lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_List_take___redArg(v_x_935_, v_x_936_);
lean_dec(v_x_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_List_take(lean_object* v_00_u03b1_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_List_take___redArg(v_x_939_, v_x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_List_take___boxed(lean_object* v_00_u03b1_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_List_take(v_00_u03b1_942_, v_x_943_, v_x_944_);
lean_dec(v_x_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg(lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
lean_object* v_zero_948_; uint8_t v_isZero_949_; 
v_zero_948_ = lean_unsigned_to_nat(0u);
v_isZero_949_ = lean_nat_dec_eq(v_x_946_, v_zero_948_);
if (v_isZero_949_ == 1)
{
lean_dec(v_x_946_);
lean_inc(v_x_947_);
return v_x_947_;
}
else
{
if (lean_obj_tag(v_x_947_) == 0)
{
lean_dec(v_x_946_);
return v_x_947_;
}
else
{
lean_object* v_tail_950_; lean_object* v_one_951_; lean_object* v_n_952_; 
v_tail_950_ = lean_ctor_get(v_x_947_, 1);
v_one_951_ = lean_unsigned_to_nat(1u);
v_n_952_ = lean_nat_sub(v_x_946_, v_one_951_);
lean_dec(v_x_946_);
v_x_946_ = v_n_952_;
v_x_947_ = v_tail_950_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg___boxed(lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_List_drop___redArg(v_x_954_, v_x_955_);
lean_dec(v_x_955_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_List_drop(lean_object* v_00_u03b1_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_List_drop___redArg(v_x_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_List_drop___boxed(lean_object* v_00_u03b1_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_List_drop(v_00_u03b1_961_, v_x_962_, v_x_963_);
lean_dec(v_x_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg(lean_object* v_l_965_, lean_object* v_start_966_, lean_object* v_stop_967_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_nat_sub(v_stop_967_, v_start_966_);
v___x_969_ = l_List_drop___redArg(v_start_966_, v_l_965_);
v___x_970_ = l_List_take___redArg(v___x_968_, v___x_969_);
lean_dec(v___x_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg___boxed(lean_object* v_l_971_, lean_object* v_start_972_, lean_object* v_stop_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_List_extract___redArg(v_l_971_, v_start_972_, v_stop_973_);
lean_dec(v_stop_973_);
lean_dec(v_l_971_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_List_extract(lean_object* v_00_u03b1_975_, lean_object* v_l_976_, lean_object* v_start_977_, lean_object* v_stop_978_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_nat_sub(v_stop_978_, v_start_977_);
v___x_980_ = l_List_drop___redArg(v_start_977_, v_l_976_);
v___x_981_ = l_List_take___redArg(v___x_979_, v___x_980_);
lean_dec(v___x_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_List_extract___boxed(lean_object* v_00_u03b1_982_, lean_object* v_l_983_, lean_object* v_start_984_, lean_object* v_stop_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_List_extract(v_00_u03b1_982_, v_l_983_, v_start_984_, v_stop_985_);
lean_dec(v_stop_985_);
lean_dec(v_l_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhile___redArg(lean_object* v_p_987_, lean_object* v_x_988_){
_start:
{
if (lean_obj_tag(v_x_988_) == 0)
{
lean_dec_ref(v_p_987_);
return v_x_988_;
}
else
{
lean_object* v_head_989_; lean_object* v_tail_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1001_; 
v_head_989_ = lean_ctor_get(v_x_988_, 0);
v_tail_990_ = lean_ctor_get(v_x_988_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_x_988_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_992_ = v_x_988_;
v_isShared_993_ = v_isSharedCheck_1001_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_tail_990_);
lean_inc(v_head_989_);
lean_dec(v_x_988_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1001_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; uint8_t v___x_995_; 
lean_inc_ref(v_p_987_);
lean_inc(v_head_989_);
v___x_994_ = lean_apply_1(v_p_987_, v_head_989_);
v___x_995_ = lean_unbox(v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
lean_del_object(v___x_992_);
lean_dec(v_tail_990_);
lean_dec(v_head_989_);
lean_dec_ref(v_p_987_);
v___x_996_ = lean_box(0);
return v___x_996_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = l_List_takeWhile___redArg(v_p_987_, v_tail_990_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v___x_997_);
v___x_999_ = v___x_992_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_head_989_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_takeWhile(lean_object* v_00_u03b1_1002_, lean_object* v_p_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_List_takeWhile___redArg(v_p_1003_, v_x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___redArg(lean_object* v_p_1006_, lean_object* v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 0)
{
lean_dec_ref(v_p_1006_);
return v_x_1007_;
}
else
{
lean_object* v_head_1008_; lean_object* v_tail_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v_head_1008_ = lean_ctor_get(v_x_1007_, 0);
v_tail_1009_ = lean_ctor_get(v_x_1007_, 1);
lean_inc_ref(v_p_1006_);
lean_inc(v_head_1008_);
v___x_1010_ = lean_apply_1(v_p_1006_, v_head_1008_);
v___x_1011_ = lean_unbox(v___x_1010_);
if (v___x_1011_ == 0)
{
lean_dec_ref(v_p_1006_);
return v_x_1007_;
}
else
{
lean_inc(v_tail_1009_);
lean_dec_ref_known(v_x_1007_, 2);
v_x_1007_ = v_tail_1009_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object* v_00_u03b1_1013_, lean_object* v_p_1014_, lean_object* v_x_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_List_dropWhile___redArg(v_p_1014_, v_x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___redArg(lean_object* v_p_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
if (lean_obj_tag(v_a_1018_) == 0)
{
lean_object* v_fst_1020_; lean_object* v_snd_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_p_1017_);
v_fst_1020_ = lean_ctor_get(v_a_1019_, 0);
v_snd_1021_ = lean_ctor_get(v_a_1019_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_a_1019_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1023_ = v_a_1019_;
v_isShared_1024_ = v_isSharedCheck_1030_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_snd_1021_);
lean_inc(v_fst_1020_);
lean_dec(v_a_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1030_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1025_ = l_List_reverse___redArg(v_fst_1020_);
v___x_1026_ = l_List_reverse___redArg(v_snd_1021_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1026_);
lean_ctor_set(v___x_1023_, 0, v___x_1025_);
v___x_1028_ = v___x_1023_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_object* v_head_1031_; lean_object* v_tail_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1058_; 
v_head_1031_ = lean_ctor_get(v_a_1018_, 0);
v_tail_1032_ = lean_ctor_get(v_a_1018_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_a_1018_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1034_ = v_a_1018_;
v_isShared_1035_ = v_isSharedCheck_1058_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_tail_1032_);
lean_inc(v_head_1031_);
lean_dec(v_a_1018_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1058_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_fst_1036_; lean_object* v_snd_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1057_; 
v_fst_1036_ = lean_ctor_get(v_a_1019_, 0);
v_snd_1037_ = lean_ctor_get(v_a_1019_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_a_1019_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1039_ = v_a_1019_;
v_isShared_1040_ = v_isSharedCheck_1057_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_snd_1037_);
lean_inc(v_fst_1036_);
lean_dec(v_a_1019_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1057_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
lean_inc_ref(v_p_1017_);
lean_inc(v_head_1031_);
v___x_1041_ = lean_apply_1(v_p_1017_, v_head_1031_);
v___x_1042_ = lean_unbox(v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1044_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v_snd_1037_);
v___x_1044_ = v___x_1034_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_head_1031_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_snd_1037_);
v___x_1044_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1046_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 1, v___x_1044_);
v___x_1046_ = v___x_1039_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_fst_1036_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
v_a_1018_ = v_tail_1032_;
v_a_1019_ = v___x_1046_;
goto _start;
}
}
}
else
{
lean_object* v___x_1051_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v_fst_1036_);
v___x_1051_ = v___x_1034_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_head_1031_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_fst_1036_);
v___x_1051_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1051_);
v___x_1053_ = v___x_1039_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_snd_1037_);
v___x_1053_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
v_a_1018_ = v_tail_1032_;
v_a_1019_ = v___x_1053_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object* v_00_u03b1_1059_, lean_object* v_p_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_List_partition_loop___redArg(v_p_1060_, v_a_1061_, v_a_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_List_partition___redArg(lean_object* v_p_1066_, lean_object* v_as_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1069_ = l_List_partition_loop___redArg(v_p_1066_, v_as_1067_, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_List_partition(lean_object* v_00_u03b1_1070_, lean_object* v_p_1071_, lean_object* v_as_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_1074_ = l_List_partition_loop___redArg(v_p_1071_, v_as_1072_, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_List_dropLast___redArg(lean_object* v_x_1075_){
_start:
{
if (lean_obj_tag(v_x_1075_) == 0)
{
return v_x_1075_;
}
else
{
lean_object* v_tail_1076_; 
v_tail_1076_ = lean_ctor_get(v_x_1075_, 1);
lean_inc(v_tail_1076_);
if (lean_obj_tag(v_tail_1076_) == 0)
{
lean_dec_ref_known(v_x_1075_, 2);
return v_tail_1076_;
}
else
{
lean_object* v_head_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1085_; 
v_head_1077_ = lean_ctor_get(v_x_1075_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v_x_1075_, 1);
lean_dec(v_unused_1086_);
v___x_1079_ = v_x_1075_;
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_head_1077_);
lean_dec(v_x_1075_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = l_List_dropLast___redArg(v_tail_1076_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v___x_1081_);
v___x_1083_ = v___x_1079_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_head_1077_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropLast(lean_object* v_00_u03b1_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_List_dropLast___redArg(v_x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_1090_, lean_object* v_h__1_1091_, lean_object* v_h__2_1092_, lean_object* v_h__3_1093_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec(v_h__3_1093_);
lean_dec(v_h__2_1092_);
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_apply_1(v_h__1_1091_, v___x_1094_);
return v___x_1095_;
}
else
{
lean_object* v_tail_1096_; 
lean_dec(v_h__1_1091_);
v_tail_1096_ = lean_ctor_get(v_x_1090_, 1);
if (lean_obj_tag(v_tail_1096_) == 0)
{
lean_object* v_head_1097_; lean_object* v___x_1098_; 
lean_dec(v_h__3_1093_);
v_head_1097_ = lean_ctor_get(v_x_1090_, 0);
lean_inc(v_head_1097_);
lean_dec_ref_known(v_x_1090_, 2);
v___x_1098_ = lean_apply_1(v_h__2_1092_, v_head_1097_);
return v___x_1098_;
}
else
{
lean_object* v_head_1099_; lean_object* v___x_1100_; 
lean_inc_ref(v_tail_1096_);
lean_dec(v_h__2_1092_);
v_head_1099_ = lean_ctor_get(v_x_1090_, 0);
lean_inc(v_head_1099_);
lean_dec_ref_known(v_x_1090_, 2);
v___x_1100_ = lean_apply_3(v_h__3_1093_, v_head_1099_, v_tail_1096_, lean_box(0));
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_1101_, lean_object* v_motive_1102_, lean_object* v_x_1103_, lean_object* v_h__1_1104_, lean_object* v_h__2_1105_, lean_object* v_h__3_1106_){
_start:
{
if (lean_obj_tag(v_x_1103_) == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v_h__3_1106_);
lean_dec(v_h__2_1105_);
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_apply_1(v_h__1_1104_, v___x_1107_);
return v___x_1108_;
}
else
{
lean_object* v_tail_1109_; 
lean_dec(v_h__1_1104_);
v_tail_1109_ = lean_ctor_get(v_x_1103_, 1);
if (lean_obj_tag(v_tail_1109_) == 0)
{
lean_object* v_head_1110_; lean_object* v___x_1111_; 
lean_dec(v_h__3_1106_);
v_head_1110_ = lean_ctor_get(v_x_1103_, 0);
lean_inc(v_head_1110_);
lean_dec_ref_known(v_x_1103_, 2);
v___x_1111_ = lean_apply_1(v_h__2_1105_, v_head_1110_);
return v___x_1111_;
}
else
{
lean_object* v_head_1112_; lean_object* v___x_1113_; 
lean_inc_ref(v_tail_1109_);
lean_dec(v_h__2_1105_);
v_head_1112_ = lean_ctor_get(v_x_1103_, 0);
lean_inc(v_head_1112_);
lean_dec_ref_known(v_x_1103_, 2);
v___x_1113_ = lean_apply_3(v_h__3_1106_, v_head_1112_, v_tail_1109_, lean_box(0));
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg(){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_box(0);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg___boxed(lean_object* v___dummy_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_List_instHasSubset___redArg();
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object* v_00_u03b1_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_box(0);
return v___x_1119_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(lean_object* v___f_1120_, lean_object* v_x_1121_, lean_object* v_a_1122_){
_start:
{
uint8_t v___x_1123_; 
v___x_1123_ = l_List_elem___redArg(v___f_1120_, v_a_1122_, v_x_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(lean_object* v___f_1124_, lean_object* v_x_1125_, lean_object* v_a_1126_){
_start:
{
uint8_t v_res_1127_; lean_object* v_r_1128_; 
v_res_1127_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(v___f_1124_, v_x_1125_, v_a_1126_);
v_r_1128_ = lean_box(v_res_1127_);
return v_r_1128_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg(lean_object* v_inst_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
lean_object* v___f_1132_; lean_object* v___f_1133_; uint8_t v___x_1134_; 
v___f_1132_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1132_, 0, v_inst_1129_);
v___f_1133_ = lean_alloc_closure((void*)(l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1133_, 0, v___f_1132_);
lean_closure_set(v___f_1133_, 1, v_x_1131_);
v___x_1134_ = l_List_decidableBAll___redArg(v___f_1133_, v_x_1130_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(lean_object* v_inst_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1135_, v_x_1136_, v_x_1137_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq(lean_object* v_00_u03b1_1140_, lean_object* v_inst_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1141_, v_x_1142_, v_x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___boxed(lean_object* v_00_u03b1_1145_, lean_object* v_inst_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
uint8_t v_res_1149_; lean_object* v_r_1150_; 
v_res_1149_ = l_List_instDecidableRelSubsetOfDecidableEq(v_00_u03b1_1145_, v_inst_1146_, v_x_1147_, v_x_1148_);
v_r_1150_ = lean_box(v_res_1149_);
return v_r_1150_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2));
v___x_1185_ = l_String_toRawSubstring_x27(v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object* v_x_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
lean_inc(v_x_1205_);
v___x_1209_ = l_Lean_Syntax_isOfKind(v_x_1205_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec(v_x_1205_);
v___x_1210_ = lean_box(1);
v___x_1211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v_a_1207_);
return v___x_1211_;
}
else
{
lean_object* v_quotContext_1212_; lean_object* v_currMacroScope_1213_; lean_object* v_ref_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_quotContext_1212_ = lean_ctor_get(v_a_1206_, 1);
v_currMacroScope_1213_ = lean_ctor_get(v_a_1206_, 2);
v_ref_1214_ = lean_ctor_get(v_a_1206_, 5);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = l_Lean_Syntax_getArg(v_x_1205_, v___x_1215_);
v___x_1217_ = lean_unsigned_to_nat(2u);
v___x_1218_ = l_Lean_Syntax_getArg(v_x_1205_, v___x_1217_);
lean_dec(v_x_1205_);
v___x_1219_ = 0;
v___x_1220_ = l_Lean_SourceInfo_fromRef(v_ref_1214_, v___x_1219_);
v___x_1221_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1222_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
v___x_1223_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4));
lean_inc(v_currMacroScope_1213_);
lean_inc(v_quotContext_1212_);
v___x_1224_ = l_Lean_addMacroScope(v_quotContext_1212_, v___x_1223_, v_currMacroScope_1213_);
v___x_1225_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10));
lean_inc_n(v___x_1220_, 2);
v___x_1226_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1220_);
lean_ctor_set(v___x_1226_, 1, v___x_1222_);
lean_ctor_set(v___x_1226_, 2, v___x_1224_);
lean_ctor_set(v___x_1226_, 3, v___x_1225_);
v___x_1227_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1228_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1227_, v___x_1216_, v___x_1218_);
v___x_1229_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1221_, v___x_1226_, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v_a_1207_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___boxed(lean_object* v_x_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(v_x_1231_, v_a_1232_, v_a_1233_);
lean_dec_ref(v_a_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object* v_x_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1238_);
v___x_1242_ = l_Lean_Syntax_isOfKind(v_x_1238_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v_x_1238_);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v_a_1240_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = l_Lean_Syntax_getArg(v_x_1238_, v___x_1245_);
v___x_1247_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1246_);
v___x_1248_ = l_Lean_Syntax_isOfKind(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec(v___x_1246_);
lean_dec(v_x_1238_);
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v_a_1240_);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = l_Lean_Syntax_getArg(v_x_1238_, v___x_1251_);
lean_dec(v_x_1238_);
v___x_1253_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1252_);
v___x_1254_ = l_Lean_Syntax_matchesNull(v___x_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec(v___x_1252_);
lean_dec(v___x_1246_);
v___x_1255_ = lean_box(0);
v___x_1256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v_a_1240_);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v_ref_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1257_ = l_Lean_Syntax_getArg(v___x_1252_, v___x_1245_);
v___x_1258_ = l_Lean_Syntax_getArg(v___x_1252_, v___x_1251_);
lean_dec(v___x_1252_);
v_ref_1259_ = l_Lean_replaceRef(v___x_1246_, v_a_1239_);
lean_dec(v___x_1246_);
v___x_1260_ = 0;
v___x_1261_ = l_Lean_SourceInfo_fromRef(v_ref_1259_, v___x_1260_);
lean_dec(v_ref_1259_);
v___x_1262_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
v___x_1263_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__5));
lean_inc(v___x_1261_);
v___x_1264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1261_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = l_Lean_Syntax_node3(v___x_1261_, v___x_1262_, v___x_1257_, v___x_1264_, v___x_1258_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v_a_1240_);
return v___x_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object* v_x_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(v_x_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1268_);
return v_res_1270_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist___redArg(lean_object* v_inst_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
if (lean_obj_tag(v_x_1272_) == 0)
{
uint8_t v___x_1274_; 
lean_dec(v_x_1273_);
lean_dec_ref(v_inst_1271_);
v___x_1274_ = 1;
return v___x_1274_;
}
else
{
if (lean_obj_tag(v_x_1273_) == 0)
{
uint8_t v___x_1275_; 
lean_dec_ref_known(v_x_1272_, 2);
lean_dec_ref(v_inst_1271_);
v___x_1275_ = 0;
return v___x_1275_;
}
else
{
lean_object* v_head_1276_; lean_object* v_tail_1277_; lean_object* v_head_1278_; lean_object* v_tail_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_head_1276_ = lean_ctor_get(v_x_1272_, 0);
v_tail_1277_ = lean_ctor_get(v_x_1272_, 1);
v_head_1278_ = lean_ctor_get(v_x_1273_, 0);
lean_inc(v_head_1278_);
v_tail_1279_ = lean_ctor_get(v_x_1273_, 1);
lean_inc(v_tail_1279_);
lean_dec_ref_known(v_x_1273_, 2);
lean_inc_ref(v_inst_1271_);
lean_inc(v_head_1276_);
v___x_1280_ = lean_apply_2(v_inst_1271_, v_head_1276_, v_head_1278_);
v___x_1281_ = lean_unbox(v___x_1280_);
if (v___x_1281_ == 0)
{
v_x_1273_ = v_tail_1279_;
goto _start;
}
else
{
lean_inc(v_tail_1277_);
lean_dec_ref_known(v_x_1272_, 2);
v_x_1272_ = v_tail_1277_;
v_x_1273_ = v_tail_1279_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSublist___redArg___boxed(lean_object* v_inst_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_List_isSublist___redArg(v_inst_1284_, v_x_1285_, v_x_1286_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist(lean_object* v_00_u03b1_1289_, lean_object* v_inst_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = l_List_isSublist___redArg(v_inst_1290_, v_x_1291_, v_x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_List_isSublist___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_inst_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
uint8_t v_res_1298_; lean_object* v_r_1299_; 
v_res_1298_ = l_List_isSublist(v_00_u03b1_1294_, v_inst_1295_, v_x_1296_, v_x_1297_);
v_r_1299_ = lean_box(v_res_1298_);
return v_r_1299_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0));
v___x_1318_ = l_String_toRawSubstring_x27(v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object* v_x_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
lean_inc(v_x_1330_);
v___x_1334_ = l_Lean_Syntax_isOfKind(v_x_1330_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v_x_1330_);
v___x_1335_ = lean_box(1);
v___x_1336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v_a_1332_);
return v___x_1336_;
}
else
{
lean_object* v_quotContext_1337_; lean_object* v_currMacroScope_1338_; lean_object* v_ref_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_quotContext_1337_ = lean_ctor_get(v_a_1331_, 1);
v_currMacroScope_1338_ = lean_ctor_get(v_a_1331_, 2);
v_ref_1339_ = lean_ctor_get(v_a_1331_, 5);
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = l_Lean_Syntax_getArg(v_x_1330_, v___x_1340_);
v___x_1342_ = lean_unsigned_to_nat(2u);
v___x_1343_ = l_Lean_Syntax_getArg(v_x_1330_, v___x_1342_);
lean_dec(v_x_1330_);
v___x_1344_ = 0;
v___x_1345_ = l_Lean_SourceInfo_fromRef(v_ref_1339_, v___x_1344_);
v___x_1346_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1347_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
v___x_1348_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1338_);
lean_inc(v_quotContext_1337_);
v___x_1349_ = l_Lean_addMacroScope(v_quotContext_1337_, v___x_1348_, v_currMacroScope_1338_);
v___x_1350_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1345_, 2);
v___x_1351_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1345_);
lean_ctor_set(v___x_1351_, 1, v___x_1347_);
lean_ctor_set(v___x_1351_, 2, v___x_1349_);
lean_ctor_set(v___x_1351_, 3, v___x_1350_);
v___x_1352_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1353_ = l_Lean_Syntax_node2(v___x_1345_, v___x_1352_, v___x_1341_, v___x_1343_);
v___x_1354_ = l_Lean_Syntax_node2(v___x_1345_, v___x_1346_, v___x_1351_, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_a_1332_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___boxed(lean_object* v_x_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(v_x_1356_, v_a_1357_, v_a_1358_);
lean_dec_ref(v_a_1357_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object* v_x_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1360_);
v___x_1364_ = l_Lean_Syntax_isOfKind(v_x_1360_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v_x_1360_);
v___x_1365_ = lean_box(0);
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v_a_1362_);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = l_Lean_Syntax_getArg(v_x_1360_, v___x_1367_);
v___x_1369_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1368_);
v___x_1370_ = l_Lean_Syntax_isOfKind(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec(v___x_1368_);
lean_dec(v_x_1360_);
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v_a_1362_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = l_Lean_Syntax_getArg(v_x_1360_, v___x_1373_);
lean_dec(v_x_1360_);
v___x_1375_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1374_);
v___x_1376_ = l_Lean_Syntax_matchesNull(v___x_1374_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec(v___x_1374_);
lean_dec(v___x_1368_);
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v_a_1362_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_ref_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1379_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1367_);
v___x_1380_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1373_);
lean_dec(v___x_1374_);
v_ref_1381_ = l_Lean_replaceRef(v___x_1368_, v_a_1361_);
lean_dec(v___x_1368_);
v___x_1382_ = 0;
v___x_1383_ = l_Lean_SourceInfo_fromRef(v_ref_1381_, v___x_1382_);
lean_dec(v_ref_1381_);
v___x_1384_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
v___x_1385_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__2));
lean_inc(v___x_1383_);
v___x_1386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1383_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = l_Lean_Syntax_node3(v___x_1383_, v___x_1384_, v___x_1379_, v___x_1386_, v___x_1380_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
lean_ctor_set(v___x_1388_, 1, v_a_1362_);
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object* v_x_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(v_x_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf___redArg(lean_object* v_inst_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1394_) == 0)
{
uint8_t v___x_1396_; 
lean_dec(v_x_1395_);
lean_dec_ref(v_inst_1393_);
v___x_1396_ = 1;
return v___x_1396_;
}
else
{
if (lean_obj_tag(v_x_1395_) == 0)
{
uint8_t v___x_1397_; 
lean_dec_ref_known(v_x_1394_, 2);
lean_dec_ref(v_inst_1393_);
v___x_1397_ = 0;
return v___x_1397_;
}
else
{
lean_object* v_head_1398_; lean_object* v_tail_1399_; lean_object* v_head_1400_; lean_object* v_tail_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_head_1398_ = lean_ctor_get(v_x_1394_, 0);
lean_inc(v_head_1398_);
v_tail_1399_ = lean_ctor_get(v_x_1394_, 1);
lean_inc(v_tail_1399_);
lean_dec_ref_known(v_x_1394_, 2);
v_head_1400_ = lean_ctor_get(v_x_1395_, 0);
lean_inc(v_head_1400_);
v_tail_1401_ = lean_ctor_get(v_x_1395_, 1);
lean_inc(v_tail_1401_);
lean_dec_ref_known(v_x_1395_, 2);
lean_inc_ref(v_inst_1393_);
v___x_1402_ = lean_apply_2(v_inst_1393_, v_head_1398_, v_head_1400_);
v___x_1403_ = lean_unbox(v___x_1402_);
if (v___x_1403_ == 0)
{
uint8_t v___x_1404_; 
lean_dec(v_tail_1401_);
lean_dec(v_tail_1399_);
lean_dec_ref(v_inst_1393_);
v___x_1404_ = lean_unbox(v___x_1402_);
return v___x_1404_;
}
else
{
v_x_1394_ = v_tail_1399_;
v_x_1395_ = v_tail_1401_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___redArg___boxed(lean_object* v_inst_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
uint8_t v_res_1409_; lean_object* v_r_1410_; 
v_res_1409_ = l_List_isPrefixOf___redArg(v_inst_1406_, v_x_1407_, v_x_1408_);
v_r_1410_ = lean_box(v_res_1409_);
return v_r_1410_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf(lean_object* v_00_u03b1_1411_, lean_object* v_inst_1412_, lean_object* v_x_1413_, lean_object* v_x_1414_){
_start:
{
uint8_t v___x_1415_; 
v___x_1415_ = l_List_isPrefixOf___redArg(v_inst_1412_, v_x_1413_, v_x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_inst_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_){
_start:
{
uint8_t v_res_1420_; lean_object* v_r_1421_; 
v_res_1420_ = l_List_isPrefixOf(v_00_u03b1_1416_, v_inst_1417_, v_x_1418_, v_x_1419_);
v_r_1421_ = lean_box(v_res_1420_);
return v_r_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_1422_, lean_object* v_x_1423_, lean_object* v_h__1_1424_, lean_object* v_h__2_1425_, lean_object* v_h__3_1426_){
_start:
{
if (lean_obj_tag(v_x_1422_) == 0)
{
lean_object* v___x_1427_; 
lean_dec(v_h__3_1426_);
lean_dec(v_h__2_1425_);
v___x_1427_ = lean_apply_1(v_h__1_1424_, v_x_1423_);
return v___x_1427_;
}
else
{
lean_dec(v_h__1_1424_);
if (lean_obj_tag(v_x_1423_) == 0)
{
lean_object* v___x_1428_; 
lean_dec(v_h__3_1426_);
v___x_1428_ = lean_apply_2(v_h__2_1425_, v_x_1422_, lean_box(0));
return v___x_1428_;
}
else
{
lean_object* v_head_1429_; lean_object* v_tail_1430_; lean_object* v_head_1431_; lean_object* v_tail_1432_; lean_object* v___x_1433_; 
lean_dec(v_h__2_1425_);
v_head_1429_ = lean_ctor_get(v_x_1422_, 0);
lean_inc(v_head_1429_);
v_tail_1430_ = lean_ctor_get(v_x_1422_, 1);
lean_inc(v_tail_1430_);
lean_dec_ref_known(v_x_1422_, 2);
v_head_1431_ = lean_ctor_get(v_x_1423_, 0);
lean_inc(v_head_1431_);
v_tail_1432_ = lean_ctor_get(v_x_1423_, 1);
lean_inc(v_tail_1432_);
lean_dec_ref_known(v_x_1423_, 2);
v___x_1433_ = lean_apply_4(v_h__3_1426_, v_head_1429_, v_tail_1430_, v_head_1431_, v_tail_1432_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object* v_00_u03b1_1434_, lean_object* v_motive_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v_h__1_1438_, lean_object* v_h__2_1439_, lean_object* v_h__3_1440_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v___x_1441_; 
lean_dec(v_h__3_1440_);
lean_dec(v_h__2_1439_);
v___x_1441_ = lean_apply_1(v_h__1_1438_, v_x_1437_);
return v___x_1441_;
}
else
{
lean_dec(v_h__1_1438_);
if (lean_obj_tag(v_x_1437_) == 0)
{
lean_object* v___x_1442_; 
lean_dec(v_h__3_1440_);
v___x_1442_ = lean_apply_2(v_h__2_1439_, v_x_1436_, lean_box(0));
return v___x_1442_;
}
else
{
lean_object* v_head_1443_; lean_object* v_tail_1444_; lean_object* v_head_1445_; lean_object* v_tail_1446_; lean_object* v___x_1447_; 
lean_dec(v_h__2_1439_);
v_head_1443_ = lean_ctor_get(v_x_1436_, 0);
lean_inc(v_head_1443_);
v_tail_1444_ = lean_ctor_get(v_x_1436_, 1);
lean_inc(v_tail_1444_);
lean_dec_ref_known(v_x_1436_, 2);
v_head_1445_ = lean_ctor_get(v_x_1437_, 0);
lean_inc(v_head_1445_);
v_tail_1446_ = lean_ctor_get(v_x_1437_, 1);
lean_inc(v_tail_1446_);
lean_dec_ref_known(v_x_1437_, 2);
v___x_1447_ = lean_apply_4(v_h__3_1440_, v_head_1443_, v_tail_1444_, v_head_1445_, v_tail_1446_);
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___redArg(lean_object* v_inst_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
if (lean_obj_tag(v_x_1449_) == 0)
{
lean_object* v___x_1451_; 
lean_dec_ref(v_inst_1448_);
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_x_1450_);
return v___x_1451_;
}
else
{
if (lean_obj_tag(v_x_1450_) == 0)
{
lean_object* v___x_1452_; 
lean_dec_ref_known(v_x_1449_, 2);
lean_dec_ref(v_inst_1448_);
v___x_1452_ = lean_box(0);
return v___x_1452_;
}
else
{
lean_object* v_head_1453_; lean_object* v_tail_1454_; lean_object* v_head_1455_; lean_object* v_tail_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v_head_1453_ = lean_ctor_get(v_x_1449_, 0);
lean_inc(v_head_1453_);
v_tail_1454_ = lean_ctor_get(v_x_1449_, 1);
lean_inc(v_tail_1454_);
lean_dec_ref_known(v_x_1449_, 2);
v_head_1455_ = lean_ctor_get(v_x_1450_, 0);
lean_inc(v_head_1455_);
v_tail_1456_ = lean_ctor_get(v_x_1450_, 1);
lean_inc(v_tail_1456_);
lean_dec_ref_known(v_x_1450_, 2);
lean_inc_ref(v_inst_1448_);
v___x_1457_ = lean_apply_2(v_inst_1448_, v_head_1453_, v_head_1455_);
v___x_1458_ = lean_unbox(v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_dec(v_tail_1456_);
lean_dec(v_tail_1454_);
lean_dec_ref(v_inst_1448_);
v___x_1459_ = lean_box(0);
return v___x_1459_;
}
else
{
v_x_1449_ = v_tail_1454_;
v_x_1450_ = v_tail_1456_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object* v_00_u03b1_1461_, lean_object* v_inst_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_List_isPrefixOf_x3f___redArg(v_inst_1462_, v_x_1463_, v_x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf___redArg(lean_object* v_inst_1466_, lean_object* v_l_u2081_1467_, lean_object* v_l_u2082_1468_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = l_List_reverse___redArg(v_l_u2081_1467_);
v___x_1470_ = l_List_reverse___redArg(v_l_u2082_1468_);
v___x_1471_ = l_List_isPrefixOf___redArg(v_inst_1466_, v___x_1469_, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___redArg___boxed(lean_object* v_inst_1472_, lean_object* v_l_u2081_1473_, lean_object* v_l_u2082_1474_){
_start:
{
uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_res_1475_ = l_List_isSuffixOf___redArg(v_inst_1472_, v_l_u2081_1473_, v_l_u2082_1474_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf(lean_object* v_00_u03b1_1477_, lean_object* v_inst_1478_, lean_object* v_l_u2081_1479_, lean_object* v_l_u2082_1480_){
_start:
{
uint8_t v___x_1481_; 
v___x_1481_ = l_List_isSuffixOf___redArg(v_inst_1478_, v_l_u2081_1479_, v_l_u2082_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___boxed(lean_object* v_00_u03b1_1482_, lean_object* v_inst_1483_, lean_object* v_l_u2081_1484_, lean_object* v_l_u2082_1485_){
_start:
{
uint8_t v_res_1486_; lean_object* v_r_1487_; 
v_res_1486_ = l_List_isSuffixOf(v_00_u03b1_1482_, v_inst_1483_, v_l_u2081_1484_, v_l_u2082_1485_);
v_r_1487_ = lean_box(v_res_1486_);
return v_r_1487_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___redArg(lean_object* v_inst_1488_, lean_object* v_l_u2081_1489_, lean_object* v_l_u2082_1490_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = l_List_reverse___redArg(v_l_u2081_1489_);
v___x_1492_ = l_List_reverse___redArg(v_l_u2082_1490_);
v___x_1493_ = l_List_isPrefixOf_x3f___redArg(v_inst_1488_, v___x_1491_, v___x_1492_);
if (lean_obj_tag(v___x_1493_) == 0)
{
return v___x_1493_;
}
else
{
lean_object* v_val_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1502_; 
v_val_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_val_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = l_List_reverse___redArg(v_val_1494_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object* v_00_u03b1_1503_, lean_object* v_inst_1504_, lean_object* v_l_u2081_1505_, lean_object* v_l_u2082_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_List_isSuffixOf_x3f___redArg(v_inst_1504_, v_l_u2081_1505_, v_l_u2082_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0));
v___x_1526_ = l_String_toRawSubstring_x27(v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object* v_x_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
lean_inc(v_x_1538_);
v___x_1542_ = l_Lean_Syntax_isOfKind(v_x_1538_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec(v_x_1538_);
v___x_1543_ = lean_box(1);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v_a_1540_);
return v___x_1544_;
}
else
{
lean_object* v_quotContext_1545_; lean_object* v_currMacroScope_1546_; lean_object* v_ref_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_quotContext_1545_ = lean_ctor_get(v_a_1539_, 1);
v_currMacroScope_1546_ = lean_ctor_get(v_a_1539_, 2);
v_ref_1547_ = lean_ctor_get(v_a_1539_, 5);
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = l_Lean_Syntax_getArg(v_x_1538_, v___x_1548_);
v___x_1550_ = lean_unsigned_to_nat(2u);
v___x_1551_ = l_Lean_Syntax_getArg(v_x_1538_, v___x_1550_);
lean_dec(v_x_1538_);
v___x_1552_ = 0;
v___x_1553_ = l_Lean_SourceInfo_fromRef(v_ref_1547_, v___x_1552_);
v___x_1554_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1555_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
v___x_1556_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2));
lean_inc(v_currMacroScope_1546_);
lean_inc(v_quotContext_1545_);
v___x_1557_ = l_Lean_addMacroScope(v_quotContext_1545_, v___x_1556_, v_currMacroScope_1546_);
v___x_1558_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5));
lean_inc_n(v___x_1553_, 2);
v___x_1559_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1553_);
lean_ctor_set(v___x_1559_, 1, v___x_1555_);
lean_ctor_set(v___x_1559_, 2, v___x_1557_);
lean_ctor_set(v___x_1559_, 3, v___x_1558_);
v___x_1560_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1561_ = l_Lean_Syntax_node2(v___x_1553_, v___x_1560_, v___x_1549_, v___x_1551_);
v___x_1562_ = l_Lean_Syntax_node2(v___x_1553_, v___x_1554_, v___x_1559_, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v_a_1540_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___boxed(lean_object* v_x_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(v_x_1564_, v_a_1565_, v_a_1566_);
lean_dec_ref(v_a_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object* v_x_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1568_);
v___x_1572_ = l_Lean_Syntax_isOfKind(v_x_1568_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec(v_x_1568_);
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v_a_1570_);
return v___x_1574_;
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = l_Lean_Syntax_getArg(v_x_1568_, v___x_1575_);
v___x_1577_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1576_);
v___x_1578_ = l_Lean_Syntax_isOfKind(v___x_1576_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec(v___x_1576_);
lean_dec(v_x_1568_);
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v_a_1570_);
return v___x_1580_;
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1581_ = lean_unsigned_to_nat(1u);
v___x_1582_ = l_Lean_Syntax_getArg(v_x_1568_, v___x_1581_);
lean_dec(v_x_1568_);
v___x_1583_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1582_);
v___x_1584_ = l_Lean_Syntax_matchesNull(v___x_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec(v___x_1582_);
lean_dec(v___x_1576_);
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v_a_1570_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_ref_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1587_ = l_Lean_Syntax_getArg(v___x_1582_, v___x_1575_);
v___x_1588_ = l_Lean_Syntax_getArg(v___x_1582_, v___x_1581_);
lean_dec(v___x_1582_);
v_ref_1589_ = l_Lean_replaceRef(v___x_1576_, v_a_1569_);
lean_dec(v___x_1576_);
v___x_1590_ = 0;
v___x_1591_ = l_Lean_SourceInfo_fromRef(v_ref_1589_, v___x_1590_);
lean_dec(v_ref_1589_);
v___x_1592_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
v___x_1593_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__2));
lean_inc(v___x_1591_);
v___x_1594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1591_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_Syntax_node3(v___x_1591_, v___x_1592_, v___x_1587_, v___x_1594_, v___x_1588_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v_a_1570_);
return v___x_1596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object* v_x_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(v_x_1597_, v_a_1598_, v_a_1599_);
lean_dec(v_a_1598_);
return v_res_1600_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0));
v___x_1619_ = l_String_toRawSubstring_x27(v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object* v_x_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
lean_inc(v_x_1631_);
v___x_1635_ = l_Lean_Syntax_isOfKind(v_x_1631_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v_x_1631_);
v___x_1636_ = lean_box(1);
v___x_1637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v_a_1633_);
return v___x_1637_;
}
else
{
lean_object* v_quotContext_1638_; lean_object* v_currMacroScope_1639_; lean_object* v_ref_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_quotContext_1638_ = lean_ctor_get(v_a_1632_, 1);
v_currMacroScope_1639_ = lean_ctor_get(v_a_1632_, 2);
v_ref_1640_ = lean_ctor_get(v_a_1632_, 5);
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = l_Lean_Syntax_getArg(v_x_1631_, v___x_1641_);
v___x_1643_ = lean_unsigned_to_nat(2u);
v___x_1644_ = l_Lean_Syntax_getArg(v_x_1631_, v___x_1643_);
lean_dec(v_x_1631_);
v___x_1645_ = 0;
v___x_1646_ = l_Lean_SourceInfo_fromRef(v_ref_1640_, v___x_1645_);
v___x_1647_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1648_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
v___x_1649_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1639_);
lean_inc(v_quotContext_1638_);
v___x_1650_ = l_Lean_addMacroScope(v_quotContext_1638_, v___x_1649_, v_currMacroScope_1639_);
v___x_1651_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1646_, 2);
v___x_1652_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1646_);
lean_ctor_set(v___x_1652_, 1, v___x_1648_);
lean_ctor_set(v___x_1652_, 2, v___x_1650_);
lean_ctor_set(v___x_1652_, 3, v___x_1651_);
v___x_1653_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1654_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1653_, v___x_1642_, v___x_1644_);
v___x_1655_ = l_Lean_Syntax_node2(v___x_1646_, v___x_1647_, v___x_1652_, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v_a_1633_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___boxed(lean_object* v_x_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(v_x_1657_, v_a_1658_, v_a_1659_);
lean_dec_ref(v_a_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object* v_x_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1661_);
v___x_1665_ = l_Lean_Syntax_isOfKind(v_x_1661_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v_x_1661_);
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_a_1663_);
return v___x_1667_;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = l_Lean_Syntax_getArg(v_x_1661_, v___x_1668_);
v___x_1670_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1669_);
v___x_1671_ = l_Lean_Syntax_isOfKind(v___x_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v___x_1669_);
lean_dec(v_x_1661_);
v___x_1672_ = lean_box(0);
v___x_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v_a_1663_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1674_ = lean_unsigned_to_nat(1u);
v___x_1675_ = l_Lean_Syntax_getArg(v_x_1661_, v___x_1674_);
lean_dec(v_x_1661_);
v___x_1676_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1675_);
v___x_1677_ = l_Lean_Syntax_matchesNull(v___x_1675_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v___x_1675_);
lean_dec(v___x_1669_);
v___x_1678_ = lean_box(0);
v___x_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
lean_ctor_set(v___x_1679_, 1, v_a_1663_);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v_ref_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1680_ = l_Lean_Syntax_getArg(v___x_1675_, v___x_1668_);
v___x_1681_ = l_Lean_Syntax_getArg(v___x_1675_, v___x_1674_);
lean_dec(v___x_1675_);
v_ref_1682_ = l_Lean_replaceRef(v___x_1669_, v_a_1662_);
lean_dec(v___x_1669_);
v___x_1683_ = 0;
v___x_1684_ = l_Lean_SourceInfo_fromRef(v_ref_1682_, v___x_1683_);
lean_dec(v_ref_1682_);
v___x_1685_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
v___x_1686_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__2));
lean_inc(v___x_1684_);
v___x_1687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1684_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = l_Lean_Syntax_node3(v___x_1684_, v___x_1685_, v___x_1680_, v___x_1687_, v___x_1681_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v_a_1663_);
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object* v_x_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(v_x_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_a_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal___redArg(lean_object* v_inst_1694_, lean_object* v_l_u2081_1695_, lean_object* v_l_u2082_1696_){
_start:
{
uint8_t v___x_1697_; 
lean_inc(v_l_u2082_1696_);
lean_inc(v_l_u2081_1695_);
lean_inc_ref(v_inst_1694_);
v___x_1697_ = l_List_isPrefixOf___redArg(v_inst_1694_, v_l_u2081_1695_, v_l_u2082_1696_);
if (v___x_1697_ == 0)
{
if (lean_obj_tag(v_l_u2082_1696_) == 0)
{
lean_dec(v_l_u2081_1695_);
lean_dec_ref(v_inst_1694_);
return v___x_1697_;
}
else
{
lean_object* v_tail_1698_; 
v_tail_1698_ = lean_ctor_get(v_l_u2082_1696_, 1);
lean_inc(v_tail_1698_);
lean_dec_ref_known(v_l_u2082_1696_, 2);
v_l_u2082_1696_ = v_tail_1698_;
goto _start;
}
}
else
{
lean_dec(v_l_u2082_1696_);
lean_dec(v_l_u2081_1695_);
lean_dec_ref(v_inst_1694_);
return v___x_1697_;
}
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___redArg___boxed(lean_object* v_inst_1700_, lean_object* v_l_u2081_1701_, lean_object* v_l_u2082_1702_){
_start:
{
uint8_t v_res_1703_; lean_object* v_r_1704_; 
v_res_1703_ = l_List_isInfixOf__internal___redArg(v_inst_1700_, v_l_u2081_1701_, v_l_u2082_1702_);
v_r_1704_ = lean_box(v_res_1703_);
return v_r_1704_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal(lean_object* v_00_u03b1_1705_, lean_object* v_inst_1706_, lean_object* v_l_u2081_1707_, lean_object* v_l_u2082_1708_){
_start:
{
uint8_t v___x_1709_; 
v___x_1709_ = l_List_isInfixOf__internal___redArg(v_inst_1706_, v_l_u2081_1707_, v_l_u2082_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___boxed(lean_object* v_00_u03b1_1710_, lean_object* v_inst_1711_, lean_object* v_l_u2081_1712_, lean_object* v_l_u2082_1713_){
_start:
{
uint8_t v_res_1714_; lean_object* v_r_1715_; 
v_res_1714_ = l_List_isInfixOf__internal(v_00_u03b1_1710_, v_inst_1711_, v_l_u2081_1712_, v_l_u2082_1713_);
v_r_1715_ = lean_box(v_res_1714_);
return v_r_1715_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go___redArg(lean_object* v_l_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
if (lean_obj_tag(v_a_1717_) == 0)
{
lean_object* v___x_1720_; 
lean_dec(v_a_1719_);
lean_dec(v_a_1718_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_l_1716_);
lean_ctor_set(v___x_1720_, 1, v_a_1717_);
return v___x_1720_;
}
else
{
lean_object* v_head_1721_; lean_object* v_tail_1722_; lean_object* v_zero_1723_; uint8_t v_isZero_1724_; 
v_head_1721_ = lean_ctor_get(v_a_1717_, 0);
v_tail_1722_ = lean_ctor_get(v_a_1717_, 1);
v_zero_1723_ = lean_unsigned_to_nat(0u);
v_isZero_1724_ = lean_nat_dec_eq(v_a_1718_, v_zero_1723_);
if (v_isZero_1724_ == 1)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_dec(v_a_1718_);
lean_dec(v_l_1716_);
v___x_1725_ = l_List_reverse___redArg(v_a_1719_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v_a_1717_);
return v___x_1726_;
}
else
{
lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1736_; 
lean_inc(v_tail_1722_);
lean_inc(v_head_1721_);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_a_1717_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; lean_object* v_unused_1738_; 
v_unused_1737_ = lean_ctor_get(v_a_1717_, 1);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_a_1717_, 0);
lean_dec(v_unused_1738_);
v___x_1728_ = v_a_1717_;
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
else
{
lean_dec(v_a_1717_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v_one_1730_; lean_object* v_n_1731_; lean_object* v___x_1733_; 
v_one_1730_ = lean_unsigned_to_nat(1u);
v_n_1731_ = lean_nat_sub(v_a_1718_, v_one_1730_);
lean_dec(v_a_1718_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v_a_1719_);
v___x_1733_ = v___x_1728_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_head_1721_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_a_1719_);
v___x_1733_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
v_a_1717_ = v_tail_1722_;
v_a_1718_ = v_n_1731_;
v_a_1719_ = v___x_1733_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object* v_00_u03b1_1739_, lean_object* v_l_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_List_splitAt_go___redArg(v_l_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt___redArg(lean_object* v_n_1745_, lean_object* v_l_1746_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_box(0);
lean_inc(v_l_1746_);
v___x_1748_ = l_List_splitAt_go___redArg(v_l_1746_, v_l_1746_, v_n_1745_, v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt(lean_object* v_00_u03b1_1749_, lean_object* v_n_1750_, lean_object* v_l_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_List_splitAt___redArg(v_n_1750_, v_l_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg(lean_object* v_xs_1753_, lean_object* v_i_1754_){
_start:
{
lean_object* v_len_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_len_1755_ = l_List_length___redArg(v_xs_1753_);
v___x_1756_ = lean_unsigned_to_nat(1u);
v___x_1757_ = lean_nat_dec_le(v_len_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v_i_1758_; lean_object* v_ys_1759_; lean_object* v_zs_1760_; lean_object* v___x_1761_; 
v_i_1758_ = lean_nat_mod(v_i_1754_, v_len_1755_);
lean_dec(v_len_1755_);
lean_inc(v_xs_1753_);
v_ys_1759_ = l_List_take___redArg(v_i_1758_, v_xs_1753_);
v_zs_1760_ = l_List_drop___redArg(v_i_1758_, v_xs_1753_);
lean_dec(v_xs_1753_);
v___x_1761_ = l_List_appendTR___redArg(v_zs_1760_, v_ys_1759_);
return v___x_1761_;
}
else
{
lean_dec(v_len_1755_);
return v_xs_1753_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg___boxed(lean_object* v_xs_1762_, lean_object* v_i_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_List_rotateLeft___redArg(v_xs_1762_, v_i_1763_);
lean_dec(v_i_1763_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft(lean_object* v_00_u03b1_1765_, lean_object* v_xs_1766_, lean_object* v_i_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_List_rotateLeft___redArg(v_xs_1766_, v_i_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___boxed(lean_object* v_00_u03b1_1769_, lean_object* v_xs_1770_, lean_object* v_i_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_List_rotateLeft(v_00_u03b1_1769_, v_xs_1770_, v_i_1771_);
lean_dec(v_i_1771_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg(lean_object* v_xs_1773_, lean_object* v_i_1774_){
_start:
{
lean_object* v_len_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_len_1775_ = l_List_length___redArg(v_xs_1773_);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_dec_le(v_len_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v_i_1779_; lean_object* v_ys_1780_; lean_object* v_zs_1781_; lean_object* v___x_1782_; 
v___x_1778_ = lean_nat_mod(v_i_1774_, v_len_1775_);
v_i_1779_ = lean_nat_sub(v_len_1775_, v___x_1778_);
lean_dec(v___x_1778_);
lean_dec(v_len_1775_);
lean_inc(v_xs_1773_);
v_ys_1780_ = l_List_take___redArg(v_i_1779_, v_xs_1773_);
v_zs_1781_ = l_List_drop___redArg(v_i_1779_, v_xs_1773_);
lean_dec(v_xs_1773_);
v___x_1782_ = l_List_appendTR___redArg(v_zs_1781_, v_ys_1780_);
return v___x_1782_;
}
else
{
lean_dec(v_len_1775_);
return v_xs_1773_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg___boxed(lean_object* v_xs_1783_, lean_object* v_i_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_List_rotateRight___redArg(v_xs_1783_, v_i_1784_);
lean_dec(v_i_1784_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight(lean_object* v_00_u03b1_1786_, lean_object* v_xs_1787_, lean_object* v_i_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_List_rotateRight___redArg(v_xs_1787_, v_i_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___boxed(lean_object* v_00_u03b1_1790_, lean_object* v_xs_1791_, lean_object* v_i_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_List_rotateRight(v_00_u03b1_1790_, v_xs_1791_, v_i_1792_);
lean_dec(v_i_1792_);
return v_res_1793_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise___redArg(lean_object* v_inst_1794_, lean_object* v_x_1795_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 0)
{
uint8_t v___x_1796_; 
lean_dec_ref(v_inst_1794_);
v___x_1796_ = 1;
return v___x_1796_;
}
else
{
lean_object* v_head_1797_; lean_object* v_tail_1798_; uint8_t v_decide_1799_; 
v_head_1797_ = lean_ctor_get(v_x_1795_, 0);
lean_inc(v_head_1797_);
v_tail_1798_ = lean_ctor_get(v_x_1795_, 1);
lean_inc_n(v_tail_1798_, 2);
lean_dec_ref_known(v_x_1795_, 2);
lean_inc_ref(v_inst_1794_);
v_decide_1799_ = l_List_instDecidablePairwise___redArg(v_inst_1794_, v_tail_1798_);
if (v_decide_1799_ == 0)
{
lean_dec(v_tail_1798_);
lean_dec(v_head_1797_);
lean_dec_ref(v_inst_1794_);
return v_decide_1799_;
}
else
{
lean_object* v___x_1800_; uint8_t v_decide_1801_; 
v___x_1800_ = lean_apply_1(v_inst_1794_, v_head_1797_);
v_decide_1801_ = l_List_decidableBAll___redArg(v___x_1800_, v_tail_1798_);
return v_decide_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___redArg___boxed(lean_object* v_inst_1802_, lean_object* v_x_1803_){
_start:
{
uint8_t v_res_1804_; lean_object* v_r_1805_; 
v_res_1804_ = l_List_instDecidablePairwise___redArg(v_inst_1802_, v_x_1803_);
v_r_1805_ = lean_box(v_res_1804_);
return v_r_1805_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise(lean_object* v_00_u03b1_1806_, lean_object* v_R_1807_, lean_object* v_inst_1808_, lean_object* v_x_1809_){
_start:
{
uint8_t v___x_1810_; 
v___x_1810_ = l_List_instDecidablePairwise___redArg(v_inst_1808_, v_x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___boxed(lean_object* v_00_u03b1_1811_, lean_object* v_R_1812_, lean_object* v_inst_1813_, lean_object* v_x_1814_){
_start:
{
uint8_t v_res_1815_; lean_object* v_r_1816_; 
v_res_1815_ = l_List_instDecidablePairwise(v_00_u03b1_1811_, v_R_1812_, v_inst_1813_, v_x_1814_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg___lam__0(lean_object* v_inst_1817_, lean_object* v_a_1818_, lean_object* v_b_1819_){
_start:
{
lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = lean_apply_2(v_inst_1817_, v_a_1818_, v_b_1819_);
v___x_1821_ = lean_unbox(v___x_1820_);
if (v___x_1821_ == 0)
{
uint8_t v___x_1822_; 
v___x_1822_ = 1;
return v___x_1822_;
}
else
{
uint8_t v___x_1823_; 
v___x_1823_ = 0;
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___lam__0___boxed(lean_object* v_inst_1824_, lean_object* v_a_1825_, lean_object* v_b_1826_){
_start:
{
uint8_t v_res_1827_; lean_object* v_r_1828_; 
v_res_1827_ = l_List_nodupDecidable___redArg___lam__0(v_inst_1824_, v_a_1825_, v_b_1826_);
v_r_1828_ = lean_box(v_res_1827_);
return v_r_1828_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg(lean_object* v_inst_1829_, lean_object* v_l_1830_){
_start:
{
lean_object* v___f_1831_; uint8_t v___x_1832_; 
v___f_1831_ = lean_alloc_closure((void*)(l_List_nodupDecidable___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1831_, 0, v_inst_1829_);
v___x_1832_ = l_List_instDecidablePairwise___redArg(v___f_1831_, v_l_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___boxed(lean_object* v_inst_1833_, lean_object* v_l_1834_){
_start:
{
uint8_t v_res_1835_; lean_object* v_r_1836_; 
v_res_1835_ = l_List_nodupDecidable___redArg(v_inst_1833_, v_l_1834_);
v_r_1836_ = lean_box(v_res_1835_);
return v_r_1836_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable(lean_object* v_00_u03b1_1837_, lean_object* v_inst_1838_, lean_object* v_l_1839_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = l_List_nodupDecidable___redArg(v_inst_1838_, v_l_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___boxed(lean_object* v_00_u03b1_1841_, lean_object* v_inst_1842_, lean_object* v_l_1843_){
_start:
{
uint8_t v_res_1844_; lean_object* v_r_1845_; 
v_res_1844_ = l_List_nodupDecidable(v_00_u03b1_1841_, v_inst_1842_, v_l_1843_);
v_r_1845_ = lean_box(v_res_1844_);
return v_r_1845_;
}
}
LEAN_EXPORT lean_object* l_List_replace___redArg(lean_object* v_inst_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_){
_start:
{
if (lean_obj_tag(v_x_1847_) == 0)
{
lean_dec(v_x_1849_);
lean_dec(v_x_1848_);
lean_dec_ref(v_inst_1846_);
return v_x_1847_;
}
else
{
lean_object* v_head_1850_; lean_object* v_tail_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1864_; 
v_head_1850_ = lean_ctor_get(v_x_1847_, 0);
v_tail_1851_ = lean_ctor_get(v_x_1847_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_x_1847_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1853_ = v_x_1847_;
v_isShared_1854_ = v_isSharedCheck_1864_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_tail_1851_);
lean_inc(v_head_1850_);
lean_dec(v_x_1847_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1864_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; uint8_t v___x_1856_; 
lean_inc_ref(v_inst_1846_);
lean_inc(v_head_1850_);
lean_inc(v_x_1848_);
v___x_1855_ = lean_apply_2(v_inst_1846_, v_x_1848_, v_head_1850_);
v___x_1856_ = lean_unbox(v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1857_ = l_List_replace___redArg(v_inst_1846_, v_tail_1851_, v_x_1848_, v_x_1849_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v___x_1857_);
v___x_1859_ = v___x_1853_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_head_1850_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
else
{
lean_object* v___x_1862_; 
lean_dec(v_head_1850_);
lean_dec(v_x_1848_);
lean_dec_ref(v_inst_1846_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v_x_1849_);
v___x_1862_ = v___x_1853_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_x_1849_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_tail_1851_);
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
LEAN_EXPORT lean_object* l_List_replace(lean_object* v_00_u03b1_1865_, lean_object* v_inst_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_List_replace___redArg(v_inst_1866_, v_x_1867_, v_x_1868_, v_x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg(lean_object* v_f_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v_zero_1874_; uint8_t v_isZero_1875_; 
v_zero_1874_ = lean_unsigned_to_nat(0u);
v_isZero_1875_ = lean_nat_dec_eq(v_a_1872_, v_zero_1874_);
if (v_isZero_1875_ == 1)
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_apply_1(v_f_1871_, v_a_1873_);
return v___x_1876_;
}
else
{
if (lean_obj_tag(v_a_1873_) == 0)
{
lean_dec_ref(v_f_1871_);
return v_a_1873_;
}
else
{
lean_object* v_head_1877_; lean_object* v_tail_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1888_; 
v_head_1877_ = lean_ctor_get(v_a_1873_, 0);
v_tail_1878_ = lean_ctor_get(v_a_1873_, 1);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_a_1873_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1880_ = v_a_1873_;
v_isShared_1881_ = v_isSharedCheck_1888_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_tail_1878_);
lean_inc(v_head_1877_);
lean_dec(v_a_1873_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1888_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v_one_1882_; lean_object* v_n_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
v_one_1882_ = lean_unsigned_to_nat(1u);
v_n_1883_ = lean_nat_sub(v_a_1872_, v_one_1882_);
v___x_1884_ = l_List_modifyTailIdx_go___redArg(v_f_1871_, v_n_1883_, v_tail_1878_);
lean_dec(v_n_1883_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 1, v___x_1884_);
v___x_1886_ = v___x_1880_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_head_1877_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg___boxed(lean_object* v_f_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_List_modifyTailIdx_go___redArg(v_f_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go(lean_object* v_00_u03b1_1893_, lean_object* v_f_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_List_modifyTailIdx_go___redArg(v_f_1894_, v_a_1895_, v_a_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___boxed(lean_object* v_00_u03b1_1898_, lean_object* v_f_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_List_modifyTailIdx_go(v_00_u03b1_1898_, v_f_1899_, v_a_1900_, v_a_1901_);
lean_dec(v_a_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg(lean_object* v_l_1903_, lean_object* v_i_1904_, lean_object* v_f_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_List_modifyTailIdx_go___redArg(v_f_1905_, v_i_1904_, v_l_1903_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg___boxed(lean_object* v_l_1907_, lean_object* v_i_1908_, lean_object* v_f_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_List_modifyTailIdx___redArg(v_l_1907_, v_i_1908_, v_f_1909_);
lean_dec(v_i_1908_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx(lean_object* v_00_u03b1_1911_, lean_object* v_l_1912_, lean_object* v_i_1913_, lean_object* v_f_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_List_modifyTailIdx_go___redArg(v_f_1914_, v_i_1913_, v_l_1912_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___boxed(lean_object* v_00_u03b1_1916_, lean_object* v_l_1917_, lean_object* v_i_1918_, lean_object* v_f_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_List_modifyTailIdx(v_00_u03b1_1916_, v_l_1917_, v_i_1918_, v_f_1919_);
lean_dec(v_i_1918_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_List_modifyHead___redArg(lean_object* v_f_1921_, lean_object* v_x_1922_){
_start:
{
if (lean_obj_tag(v_x_1922_) == 0)
{
lean_dec(v_f_1921_);
return v_x_1922_;
}
else
{
lean_object* v_head_1923_; lean_object* v_tail_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1932_; 
v_head_1923_ = lean_ctor_get(v_x_1922_, 0);
v_tail_1924_ = lean_ctor_get(v_x_1922_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_x_1922_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1926_ = v_x_1922_;
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_tail_1924_);
lean_inc(v_head_1923_);
lean_dec(v_x_1922_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_apply_1(v_f_1921_, v_head_1923_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1928_);
v___x_1930_ = v___x_1926_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_tail_1924_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyHead(lean_object* v_00_u03b1_1933_, lean_object* v_f_1934_, lean_object* v_x_1935_){
_start:
{
if (lean_obj_tag(v_x_1935_) == 0)
{
lean_dec(v_f_1934_);
return v_x_1935_;
}
else
{
lean_object* v_head_1936_; lean_object* v_tail_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1945_; 
v_head_1936_ = lean_ctor_get(v_x_1935_, 0);
v_tail_1937_ = lean_ctor_get(v_x_1935_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_x_1935_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1939_ = v_x_1935_;
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_tail_1937_);
lean_inc(v_head_1936_);
lean_dec(v_x_1935_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = lean_apply_1(v_f_1934_, v_head_1936_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_tail_1937_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg(lean_object* v_l_1946_, lean_object* v_i_1947_, lean_object* v_f_1948_){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1949_, 0, lean_box(0));
lean_closure_set(v___x_1949_, 1, v_f_1948_);
v___x_1950_ = l_List_modifyTailIdx_go___redArg(v___x_1949_, v_i_1947_, v_l_1946_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg___boxed(lean_object* v_l_1951_, lean_object* v_i_1952_, lean_object* v_f_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_List_modify___redArg(v_l_1951_, v_i_1952_, v_f_1953_);
lean_dec(v_i_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_List_modify(lean_object* v_00_u03b1_1955_, lean_object* v_l_1956_, lean_object* v_i_1957_, lean_object* v_f_1958_){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1959_, 0, lean_box(0));
lean_closure_set(v___x_1959_, 1, v_f_1958_);
v___x_1960_ = l_List_modifyTailIdx_go___redArg(v___x_1959_, v_i_1957_, v_l_1956_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_List_modify___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_l_1962_, lean_object* v_i_1963_, lean_object* v_f_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_List_modify(v_00_u03b1_1961_, v_l_1962_, v_i_1963_, v_f_1964_);
lean_dec(v_i_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object* v_inst_1966_, lean_object* v_a_1967_, lean_object* v_l_1968_){
_start:
{
uint8_t v___x_1969_; 
lean_inc(v_l_1968_);
lean_inc(v_a_1967_);
v___x_1969_ = l_List_elem___redArg(v_inst_1966_, v_a_1967_, v_l_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1970_, 0, v_a_1967_);
lean_ctor_set(v___x_1970_, 1, v_l_1968_);
return v___x_1970_;
}
else
{
lean_dec(v_a_1967_);
return v_l_1968_;
}
}
}
LEAN_EXPORT lean_object* l_List_insert(lean_object* v_00_u03b1_1971_, lean_object* v_inst_1972_, lean_object* v_a_1973_, lean_object* v_l_1974_){
_start:
{
uint8_t v___x_1975_; 
lean_inc(v_l_1974_);
lean_inc(v_a_1973_);
v___x_1975_ = l_List_elem___redArg(v_inst_1972_, v_a_1973_, v_l_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_a_1973_);
lean_ctor_set(v___x_1976_, 1, v_l_1974_);
return v___x_1976_;
}
else
{
lean_dec(v_a_1973_);
return v_l_1974_;
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_zero_1980_; uint8_t v_isZero_1981_; 
v_zero_1980_ = lean_unsigned_to_nat(0u);
v_isZero_1981_ = lean_nat_dec_eq(v_a_1978_, v_zero_1980_);
if (v_isZero_1981_ == 1)
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1982_, 0, v_a_1977_);
lean_ctor_set(v___x_1982_, 1, v_a_1979_);
return v___x_1982_;
}
else
{
if (lean_obj_tag(v_a_1979_) == 0)
{
lean_dec(v_a_1977_);
return v_a_1979_;
}
else
{
lean_object* v_head_1983_; lean_object* v_tail_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1994_; 
v_head_1983_ = lean_ctor_get(v_a_1979_, 0);
v_tail_1984_ = lean_ctor_get(v_a_1979_, 1);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1986_ = v_a_1979_;
v_isShared_1987_ = v_isSharedCheck_1994_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_tail_1984_);
lean_inc(v_head_1983_);
lean_dec(v_a_1979_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1994_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_one_1988_; lean_object* v_n_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
v_one_1988_ = lean_unsigned_to_nat(1u);
v_n_1989_ = lean_nat_sub(v_a_1978_, v_one_1988_);
v___x_1990_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1977_, v_n_1989_, v_tail_1984_);
lean_dec(v_n_1989_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 1, v___x_1990_);
v___x_1992_ = v___x_1986_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_head_1983_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg___boxed(lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1995_, v_a_1996_, v_a_1997_);
lean_dec(v_a_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg(lean_object* v_xs_1999_, lean_object* v_i_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_2001_, v_i_2000_, v_xs_1999_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___boxed(lean_object* v_xs_2003_, lean_object* v_i_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_List_insertIdx___redArg(v_xs_2003_, v_i_2004_, v_a_2005_);
lean_dec(v_i_2004_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx(lean_object* v_00_u03b1_2007_, lean_object* v_xs_2008_, lean_object* v_i_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_2010_, v_i_2009_, v_xs_2008_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_xs_2013_, lean_object* v_i_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_List_insertIdx(v_00_u03b1_2012_, v_xs_2013_, v_i_2014_, v_a_2015_);
lean_dec(v_i_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(lean_object* v_00_u03b1_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_2018_, v_a_2019_, v_a_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(v_00_u03b1_2022_, v_a_2023_, v_a_2024_, v_a_2025_);
lean_dec(v_a_2024_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_List_erase___redArg(lean_object* v_inst_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
if (lean_obj_tag(v_x_2028_) == 0)
{
lean_dec(v_x_2029_);
lean_dec_ref(v_inst_2027_);
return v_x_2028_;
}
else
{
lean_object* v_head_2030_; lean_object* v_tail_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2041_; 
v_head_2030_ = lean_ctor_get(v_x_2028_, 0);
v_tail_2031_ = lean_ctor_get(v_x_2028_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_x_2028_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2033_ = v_x_2028_;
v_isShared_2034_ = v_isSharedCheck_2041_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_tail_2031_);
lean_inc(v_head_2030_);
lean_dec(v_x_2028_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2041_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
lean_inc_ref(v_inst_2027_);
lean_inc(v_x_2029_);
lean_inc(v_head_2030_);
v___x_2035_ = lean_apply_2(v_inst_2027_, v_head_2030_, v_x_2029_);
v___x_2036_ = lean_unbox(v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2037_ = l_List_erase___redArg(v_inst_2027_, v_tail_2031_, v_x_2029_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v___x_2037_);
v___x_2039_ = v___x_2033_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_head_2030_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
else
{
lean_del_object(v___x_2033_);
lean_dec(v_head_2030_);
lean_dec(v_x_2029_);
lean_dec_ref(v_inst_2027_);
return v_tail_2031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_erase(lean_object* v_00_u03b1_2042_, lean_object* v_inst_2043_, lean_object* v_x_2044_, lean_object* v_x_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_List_erase___redArg(v_inst_2043_, v_x_2044_, v_x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v_h__1_2049_, lean_object* v_h__2_2050_){
_start:
{
if (lean_obj_tag(v_x_2047_) == 0)
{
lean_object* v___x_2051_; 
lean_dec(v_h__2_2050_);
v___x_2051_ = lean_apply_1(v_h__1_2049_, v_x_2048_);
return v___x_2051_;
}
else
{
lean_object* v_head_2052_; lean_object* v_tail_2053_; lean_object* v___x_2054_; 
lean_dec(v_h__1_2049_);
v_head_2052_ = lean_ctor_get(v_x_2047_, 0);
lean_inc(v_head_2052_);
v_tail_2053_ = lean_ctor_get(v_x_2047_, 1);
lean_inc(v_tail_2053_);
lean_dec_ref_known(v_x_2047_, 2);
v___x_2054_ = lean_apply_3(v_h__2_2050_, v_head_2052_, v_tail_2053_, v_x_2048_);
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object* v_00_u03b1_2055_, lean_object* v_motive_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_, lean_object* v_h__1_2059_, lean_object* v_h__2_2060_){
_start:
{
if (lean_obj_tag(v_x_2057_) == 0)
{
lean_object* v___x_2061_; 
lean_dec(v_h__2_2060_);
v___x_2061_ = lean_apply_1(v_h__1_2059_, v_x_2058_);
return v___x_2061_;
}
else
{
lean_object* v_head_2062_; lean_object* v_tail_2063_; lean_object* v___x_2064_; 
lean_dec(v_h__1_2059_);
v_head_2062_ = lean_ctor_get(v_x_2057_, 0);
lean_inc(v_head_2062_);
v_tail_2063_ = lean_ctor_get(v_x_2057_, 1);
lean_inc(v_tail_2063_);
lean_dec_ref_known(v_x_2057_, 2);
v___x_2064_ = lean_apply_3(v_h__2_2060_, v_head_2062_, v_tail_2063_, v_x_2058_);
return v___x_2064_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP___redArg(lean_object* v_p_2065_, lean_object* v_x_2066_){
_start:
{
if (lean_obj_tag(v_x_2066_) == 0)
{
lean_dec_ref(v_p_2065_);
return v_x_2066_;
}
else
{
lean_object* v_head_2067_; lean_object* v_tail_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2078_; 
v_head_2067_ = lean_ctor_get(v_x_2066_, 0);
v_tail_2068_ = lean_ctor_get(v_x_2066_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_x_2066_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2070_ = v_x_2066_;
v_isShared_2071_ = v_isSharedCheck_2078_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_tail_2068_);
lean_inc(v_head_2067_);
lean_dec(v_x_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2078_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; uint8_t v___x_2073_; 
lean_inc_ref(v_p_2065_);
lean_inc(v_head_2067_);
v___x_2072_ = lean_apply_1(v_p_2065_, v_head_2067_);
v___x_2073_ = lean_unbox(v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = l_List_eraseP___redArg(v_p_2065_, v_tail_2068_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2074_);
v___x_2076_ = v___x_2070_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_head_2067_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
else
{
lean_del_object(v___x_2070_);
lean_dec(v_head_2067_);
lean_dec_ref(v_p_2065_);
return v_tail_2068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP(lean_object* v_00_u03b1_2079_, lean_object* v_p_2080_, lean_object* v_x_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_List_eraseP___redArg(v_p_2080_, v_x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg(lean_object* v_x_2083_, lean_object* v_x_2084_){
_start:
{
if (lean_obj_tag(v_x_2083_) == 0)
{
return v_x_2083_;
}
else
{
lean_object* v_head_2085_; lean_object* v_tail_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2098_; 
v_head_2085_ = lean_ctor_get(v_x_2083_, 0);
v_tail_2086_ = lean_ctor_get(v_x_2083_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_x_2083_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2088_ = v_x_2083_;
v_isShared_2089_ = v_isSharedCheck_2098_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_tail_2086_);
lean_inc(v_head_2085_);
lean_dec(v_x_2083_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2098_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_zero_2090_; uint8_t v_isZero_2091_; 
v_zero_2090_ = lean_unsigned_to_nat(0u);
v_isZero_2091_ = lean_nat_dec_eq(v_x_2084_, v_zero_2090_);
if (v_isZero_2091_ == 1)
{
lean_del_object(v___x_2088_);
lean_dec(v_head_2085_);
return v_tail_2086_;
}
else
{
lean_object* v_one_2092_; lean_object* v_n_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v_one_2092_ = lean_unsigned_to_nat(1u);
v_n_2093_ = lean_nat_sub(v_x_2084_, v_one_2092_);
v___x_2094_ = l_List_eraseIdx___redArg(v_tail_2086_, v_n_2093_);
lean_dec(v_n_2093_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v___x_2094_);
v___x_2096_ = v___x_2088_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_head_2085_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg___boxed(lean_object* v_x_2099_, lean_object* v_x_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_List_eraseIdx___redArg(v_x_2099_, v_x_2100_);
lean_dec(v_x_2100_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object* v_00_u03b1_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_List_eraseIdx___redArg(v_x_2103_, v_x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_x_2107_, lean_object* v_x_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_List_eraseIdx(v_00_u03b1_2106_, v_x_2107_, v_x_2108_);
lean_dec(v_x_2108_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object* v_p_2110_, lean_object* v_x_2111_){
_start:
{
if (lean_obj_tag(v_x_2111_) == 0)
{
lean_object* v___x_2112_; 
lean_dec_ref(v_p_2110_);
v___x_2112_ = lean_box(0);
return v___x_2112_;
}
else
{
lean_object* v_head_2113_; lean_object* v_tail_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v_head_2113_ = lean_ctor_get(v_x_2111_, 0);
lean_inc_n(v_head_2113_, 2);
v_tail_2114_ = lean_ctor_get(v_x_2111_, 1);
lean_inc(v_tail_2114_);
lean_dec_ref_known(v_x_2111_, 2);
lean_inc_ref(v_p_2110_);
v___x_2115_ = lean_apply_1(v_p_2110_, v_head_2113_);
v___x_2116_ = lean_unbox(v___x_2115_);
if (v___x_2116_ == 0)
{
lean_dec(v_head_2113_);
v_x_2111_ = v_tail_2114_;
goto _start;
}
else
{
lean_object* v___x_2118_; 
lean_dec(v_tail_2114_);
lean_dec_ref(v_p_2110_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_head_2113_);
return v___x_2118_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object* v_00_u03b1_2119_, lean_object* v_p_2120_, lean_object* v_x_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_List_find_x3f___redArg(v_p_2120_, v_x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object* v_f_2123_, lean_object* v_x_2124_){
_start:
{
if (lean_obj_tag(v_x_2124_) == 0)
{
lean_object* v___x_2125_; 
lean_dec_ref(v_f_2123_);
v___x_2125_ = lean_box(0);
return v___x_2125_;
}
else
{
lean_object* v_head_2126_; lean_object* v_tail_2127_; lean_object* v___x_2128_; 
v_head_2126_ = lean_ctor_get(v_x_2124_, 0);
lean_inc(v_head_2126_);
v_tail_2127_ = lean_ctor_get(v_x_2124_, 1);
lean_inc(v_tail_2127_);
lean_dec_ref_known(v_x_2124_, 2);
lean_inc_ref(v_f_2123_);
v___x_2128_ = lean_apply_1(v_f_2123_, v_head_2126_);
if (lean_obj_tag(v___x_2128_) == 0)
{
v_x_2124_ = v_tail_2127_;
goto _start;
}
else
{
lean_dec(v_tail_2127_);
lean_dec_ref(v_f_2123_);
return v___x_2128_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object* v_00_u03b1_2130_, lean_object* v_00_u03b2_2131_, lean_object* v_f_2132_, lean_object* v_x_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_List_findSome_x3f___redArg(v_f_2132_, v_x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f___redArg(lean_object* v_p_2135_, lean_object* v_x_2136_){
_start:
{
if (lean_obj_tag(v_x_2136_) == 0)
{
lean_object* v___x_2137_; 
lean_dec_ref(v_p_2135_);
v___x_2137_ = lean_box(0);
return v___x_2137_;
}
else
{
lean_object* v_head_2138_; lean_object* v_tail_2139_; lean_object* v___x_2140_; 
v_head_2138_ = lean_ctor_get(v_x_2136_, 0);
lean_inc(v_head_2138_);
v_tail_2139_ = lean_ctor_get(v_x_2136_, 1);
lean_inc(v_tail_2139_);
lean_dec_ref_known(v_x_2136_, 2);
lean_inc_ref(v_p_2135_);
v___x_2140_ = l_List_findRev_x3f___redArg(v_p_2135_, v_tail_2139_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
lean_inc(v_head_2138_);
v___x_2141_ = lean_apply_1(v_p_2135_, v_head_2138_);
v___x_2142_ = lean_unbox(v___x_2141_);
if (v___x_2142_ == 0)
{
lean_dec(v_head_2138_);
return v___x_2140_;
}
else
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2143_, 0, v_head_2138_);
return v___x_2143_;
}
}
else
{
lean_dec(v_head_2138_);
lean_dec_ref(v_p_2135_);
return v___x_2140_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f(lean_object* v_00_u03b1_2144_, lean_object* v_p_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_List_findRev_x3f___redArg(v_p_2145_, v_x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f___redArg(lean_object* v_f_2148_, lean_object* v_x_2149_){
_start:
{
if (lean_obj_tag(v_x_2149_) == 0)
{
lean_object* v___x_2150_; 
lean_dec_ref(v_f_2148_);
v___x_2150_ = lean_box(0);
return v___x_2150_;
}
else
{
lean_object* v_head_2151_; lean_object* v_tail_2152_; lean_object* v___x_2153_; 
v_head_2151_ = lean_ctor_get(v_x_2149_, 0);
lean_inc(v_head_2151_);
v_tail_2152_ = lean_ctor_get(v_x_2149_, 1);
lean_inc(v_tail_2152_);
lean_dec_ref_known(v_x_2149_, 2);
lean_inc_ref(v_f_2148_);
v___x_2153_ = l_List_findSomeRev_x3f___redArg(v_f_2148_, v_tail_2152_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_apply_1(v_f_2148_, v_head_2151_);
return v___x_2154_;
}
else
{
lean_dec(v_head_2151_);
lean_dec_ref(v_f_2148_);
return v___x_2153_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f(lean_object* v_00_u03b1_2155_, lean_object* v_00_u03b2_2156_, lean_object* v_f_2157_, lean_object* v_x_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_List_findSomeRev_x3f___redArg(v_f_2157_, v_x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___redArg(lean_object* v_p_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
if (lean_obj_tag(v_a_2161_) == 0)
{
lean_dec_ref(v_p_2160_);
return v_a_2162_;
}
else
{
lean_object* v_head_2163_; lean_object* v_tail_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v_head_2163_ = lean_ctor_get(v_a_2161_, 0);
lean_inc(v_head_2163_);
v_tail_2164_ = lean_ctor_get(v_a_2161_, 1);
lean_inc(v_tail_2164_);
lean_dec_ref_known(v_a_2161_, 2);
lean_inc_ref(v_p_2160_);
v___x_2165_ = lean_apply_1(v_p_2160_, v_head_2163_);
v___x_2166_ = lean_unbox(v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = lean_unsigned_to_nat(1u);
v___x_2168_ = lean_nat_add(v_a_2162_, v___x_2167_);
lean_dec(v_a_2162_);
v_a_2161_ = v_tail_2164_;
v_a_2162_ = v___x_2168_;
goto _start;
}
else
{
lean_dec(v_tail_2164_);
lean_dec_ref(v_p_2160_);
return v_a_2162_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object* v_00_u03b1_2170_, lean_object* v_p_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_List_findIdx_go___redArg(v_p_2171_, v_a_2172_, v_a_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx___redArg(lean_object* v_p_2175_, lean_object* v_l_2176_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = l_List_findIdx_go___redArg(v_p_2175_, v_l_2176_, v___x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx(lean_object* v_00_u03b1_2179_, lean_object* v_p_2180_, lean_object* v_l_2181_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = l_List_findIdx_go___redArg(v_p_2180_, v_l_2181_, v___x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT uint8_t l_List_idxOf___redArg___lam__0(lean_object* v_inst_2184_, lean_object* v_a_2185_, lean_object* v_x_2186_){
_start:
{
lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2187_ = lean_apply_2(v_inst_2184_, v_x_2186_, v_a_2185_);
v___x_2188_ = lean_unbox(v___x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg___lam__0___boxed(lean_object* v_inst_2189_, lean_object* v_a_2190_, lean_object* v_x_2191_){
_start:
{
uint8_t v_res_2192_; lean_object* v_r_2193_; 
v_res_2192_ = l_List_idxOf___redArg___lam__0(v_inst_2189_, v_a_2190_, v_x_2191_);
v_r_2193_ = lean_box(v_res_2192_);
return v_r_2193_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg(lean_object* v_inst_2194_, lean_object* v_a_2195_, lean_object* v_l_2196_){
_start:
{
lean_object* v___f_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___f_2197_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2197_, 0, v_inst_2194_);
lean_closure_set(v___f_2197_, 1, v_a_2195_);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = l_List_findIdx_go___redArg(v___f_2197_, v_l_2196_, v___x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf(lean_object* v_00_u03b1_2200_, lean_object* v_inst_2201_, lean_object* v_a_2202_, lean_object* v_l_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_List_idxOf___redArg(v_inst_2201_, v_a_2202_, v_l_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___redArg(lean_object* v_p_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
if (lean_obj_tag(v_a_2206_) == 0)
{
lean_object* v___x_2208_; 
lean_dec(v_a_2207_);
lean_dec_ref(v_p_2205_);
v___x_2208_ = lean_box(0);
return v___x_2208_;
}
else
{
lean_object* v_head_2209_; lean_object* v_tail_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v_head_2209_ = lean_ctor_get(v_a_2206_, 0);
lean_inc(v_head_2209_);
v_tail_2210_ = lean_ctor_get(v_a_2206_, 1);
lean_inc(v_tail_2210_);
lean_dec_ref_known(v_a_2206_, 2);
lean_inc_ref(v_p_2205_);
v___x_2211_ = lean_apply_1(v_p_2205_, v_head_2209_);
v___x_2212_ = lean_unbox(v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_unsigned_to_nat(1u);
v___x_2214_ = lean_nat_add(v_a_2207_, v___x_2213_);
lean_dec(v_a_2207_);
v_a_2206_ = v_tail_2210_;
v_a_2207_ = v___x_2214_;
goto _start;
}
else
{
lean_object* v___x_2216_; 
lean_dec(v_tail_2210_);
lean_dec_ref(v_p_2205_);
v___x_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2216_, 0, v_a_2207_);
return v___x_2216_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go(lean_object* v_00_u03b1_2217_, lean_object* v_p_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_List_findIdx_x3f_go___redArg(v_p_2218_, v_a_2219_, v_a_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f___redArg(lean_object* v_p_2222_, lean_object* v_l_2223_){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = l_List_findIdx_x3f_go___redArg(v_p_2222_, v_l_2223_, v___x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object* v_00_u03b1_2226_, lean_object* v_p_2227_, lean_object* v_l_2228_){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_unsigned_to_nat(0u);
v___x_2230_ = l_List_findIdx_x3f_go___redArg(v_p_2227_, v_l_2228_, v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f___redArg(lean_object* v_inst_2231_, lean_object* v_a_2232_, lean_object* v_l_2233_){
_start:
{
lean_object* v___f_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___f_2234_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2234_, 0, v_inst_2231_);
lean_closure_set(v___f_2234_, 1, v_a_2232_);
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = l_List_findIdx_x3f_go___redArg(v___f_2234_, v_l_2233_, v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f(lean_object* v_00_u03b1_2237_, lean_object* v_inst_2238_, lean_object* v_a_2239_, lean_object* v_l_2240_){
_start:
{
lean_object* v___f_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___f_2241_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2241_, 0, v_inst_2238_);
lean_closure_set(v___f_2241_, 1, v_a_2239_);
v___x_2242_ = lean_unsigned_to_nat(0u);
v___x_2243_ = l_List_findIdx_x3f_go___redArg(v___f_2241_, v_l_2240_, v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___redArg(lean_object* v_p_2244_, lean_object* v_l_x27_2245_, lean_object* v_i_2246_){
_start:
{
if (lean_obj_tag(v_l_x27_2245_) == 0)
{
lean_object* v___x_2247_; 
lean_dec(v_i_2246_);
lean_dec_ref(v_p_2244_);
v___x_2247_ = lean_box(0);
return v___x_2247_;
}
else
{
lean_object* v_head_2248_; lean_object* v_tail_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_head_2248_ = lean_ctor_get(v_l_x27_2245_, 0);
lean_inc(v_head_2248_);
v_tail_2249_ = lean_ctor_get(v_l_x27_2245_, 1);
lean_inc(v_tail_2249_);
lean_dec_ref_known(v_l_x27_2245_, 2);
lean_inc_ref(v_p_2244_);
v___x_2250_ = lean_apply_1(v_p_2244_, v_head_2248_);
v___x_2251_ = lean_unbox(v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_unsigned_to_nat(1u);
v___x_2253_ = lean_nat_add(v_i_2246_, v___x_2252_);
lean_dec(v_i_2246_);
v_l_x27_2245_ = v_tail_2249_;
v_i_2246_ = v___x_2253_;
goto _start;
}
else
{
lean_object* v___x_2255_; 
lean_dec(v_tail_2249_);
lean_dec_ref(v_p_2244_);
v___x_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2255_, 0, v_i_2246_);
return v___x_2255_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go(lean_object* v_00_u03b1_2256_, lean_object* v_p_2257_, lean_object* v_l_2258_, lean_object* v_l_x27_2259_, lean_object* v_i_2260_, lean_object* v_h_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_List_findFinIdx_x3f_go___redArg(v_p_2257_, v_l_x27_2259_, v_i_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___boxed(lean_object* v_00_u03b1_2263_, lean_object* v_p_2264_, lean_object* v_l_2265_, lean_object* v_l_x27_2266_, lean_object* v_i_2267_, lean_object* v_h_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_List_findFinIdx_x3f_go(v_00_u03b1_2263_, v_p_2264_, v_l_2265_, v_l_x27_2266_, v_i_2267_, v_h_2268_);
lean_dec(v_l_2265_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f___redArg(lean_object* v_p_2270_, lean_object* v_l_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_unsigned_to_nat(0u);
v___x_2273_ = l_List_findFinIdx_x3f_go___redArg(v_p_2270_, v_l_2271_, v___x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f(lean_object* v_00_u03b1_2274_, lean_object* v_p_2275_, lean_object* v_l_2276_){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = l_List_findFinIdx_x3f_go___redArg(v_p_2275_, v_l_2276_, v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f___redArg(lean_object* v_inst_2279_, lean_object* v_a_2280_, lean_object* v_l_2281_){
_start:
{
lean_object* v___f_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___f_2282_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2282_, 0, v_inst_2279_);
lean_closure_set(v___f_2282_, 1, v_a_2280_);
v___x_2283_ = lean_unsigned_to_nat(0u);
v___x_2284_ = l_List_findFinIdx_x3f_go___redArg(v___f_2282_, v_l_2281_, v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f(lean_object* v_00_u03b1_2285_, lean_object* v_inst_2286_, lean_object* v_a_2287_, lean_object* v_l_2288_){
_start:
{
lean_object* v___f_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___f_2289_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2289_, 0, v_inst_2286_);
lean_closure_set(v___f_2289_, 1, v_a_2287_);
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = l_List_findFinIdx_x3f_go___redArg(v___f_2289_, v_l_2288_, v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___redArg(lean_object* v_p_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
if (lean_obj_tag(v_a_2293_) == 0)
{
lean_dec_ref(v_p_2292_);
return v_a_2294_;
}
else
{
lean_object* v_head_2295_; lean_object* v_tail_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
v_head_2295_ = lean_ctor_get(v_a_2293_, 0);
lean_inc(v_head_2295_);
v_tail_2296_ = lean_ctor_get(v_a_2293_, 1);
lean_inc(v_tail_2296_);
lean_dec_ref_known(v_a_2293_, 2);
lean_inc_ref(v_p_2292_);
v___x_2297_ = lean_apply_1(v_p_2292_, v_head_2295_);
v___x_2298_ = lean_unbox(v___x_2297_);
if (v___x_2298_ == 0)
{
v_a_2293_ = v_tail_2296_;
goto _start;
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = lean_unsigned_to_nat(1u);
v___x_2301_ = lean_nat_add(v_a_2294_, v___x_2300_);
lean_dec(v_a_2294_);
v_a_2293_ = v_tail_2296_;
v_a_2294_ = v___x_2301_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go(lean_object* v_00_u03b1_2303_, lean_object* v_p_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_List_countP_go___redArg(v_p_2304_, v_a_2305_, v_a_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_List_countP___redArg(lean_object* v_p_2308_, lean_object* v_l_2309_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = l_List_countP_go___redArg(v_p_2308_, v_l_2309_, v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_List_countP(lean_object* v_00_u03b1_2312_, lean_object* v_p_2313_, lean_object* v_l_2314_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = l_List_countP_go___redArg(v_p_2313_, v_l_2314_, v___x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_List_count___redArg(lean_object* v_inst_2317_, lean_object* v_a_2318_, lean_object* v_l_2319_){
_start:
{
lean_object* v___f_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___f_2320_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2320_, 0, v_inst_2317_);
lean_closure_set(v___f_2320_, 1, v_a_2318_);
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = l_List_countP_go___redArg(v___f_2320_, v_l_2319_, v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_List_count(lean_object* v_00_u03b1_2323_, lean_object* v_inst_2324_, lean_object* v_a_2325_, lean_object* v_l_2326_){
_start:
{
lean_object* v___f_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___f_2327_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2327_, 0, v_inst_2324_);
lean_closure_set(v___f_2327_, 1, v_a_2325_);
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2329_ = l_List_countP_go___redArg(v___f_2327_, v_l_2326_, v___x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___redArg(lean_object* v_inst_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_){
_start:
{
if (lean_obj_tag(v_x_2332_) == 0)
{
lean_object* v___x_2333_; 
lean_dec(v_x_2331_);
lean_dec_ref(v_inst_2330_);
v___x_2333_ = lean_box(0);
return v___x_2333_;
}
else
{
lean_object* v_head_2334_; lean_object* v_tail_2335_; lean_object* v_fst_2336_; lean_object* v_snd_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_head_2334_ = lean_ctor_get(v_x_2332_, 0);
lean_inc(v_head_2334_);
v_tail_2335_ = lean_ctor_get(v_x_2332_, 1);
lean_inc(v_tail_2335_);
lean_dec_ref_known(v_x_2332_, 2);
v_fst_2336_ = lean_ctor_get(v_head_2334_, 0);
lean_inc(v_fst_2336_);
v_snd_2337_ = lean_ctor_get(v_head_2334_, 1);
lean_inc(v_snd_2337_);
lean_dec(v_head_2334_);
lean_inc_ref(v_inst_2330_);
lean_inc(v_x_2331_);
v___x_2338_ = lean_apply_2(v_inst_2330_, v_x_2331_, v_fst_2336_);
v___x_2339_ = lean_unbox(v___x_2338_);
if (v___x_2339_ == 0)
{
lean_dec(v_snd_2337_);
v_x_2332_ = v_tail_2335_;
goto _start;
}
else
{
lean_object* v___x_2341_; 
lean_dec(v_tail_2335_);
lean_dec(v_x_2331_);
lean_dec_ref(v_inst_2330_);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v_snd_2337_);
return v___x_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup(lean_object* v_00_u03b1_2342_, lean_object* v_00_u03b2_2343_, lean_object* v_inst_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_List_lookup___redArg(v_inst_2344_, v_x_2345_, v_x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0));
v___x_2366_ = l_String_toRawSubstring_x27(v___x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object* v_x_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
lean_inc(v_x_2386_);
v___x_2390_ = l_Lean_Syntax_isOfKind(v_x_2386_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_dec(v_x_2386_);
v___x_2391_ = lean_box(1);
v___x_2392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
lean_ctor_set(v___x_2392_, 1, v_a_2388_);
return v___x_2392_;
}
else
{
lean_object* v_quotContext_2393_; lean_object* v_currMacroScope_2394_; lean_object* v_ref_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_quotContext_2393_ = lean_ctor_get(v_a_2387_, 1);
v_currMacroScope_2394_ = lean_ctor_get(v_a_2387_, 2);
v_ref_2395_ = lean_ctor_get(v_a_2387_, 5);
v___x_2396_ = lean_unsigned_to_nat(0u);
v___x_2397_ = l_Lean_Syntax_getArg(v_x_2386_, v___x_2396_);
v___x_2398_ = lean_unsigned_to_nat(2u);
v___x_2399_ = l_Lean_Syntax_getArg(v_x_2386_, v___x_2398_);
lean_dec(v_x_2386_);
v___x_2400_ = 0;
v___x_2401_ = l_Lean_SourceInfo_fromRef(v_ref_2395_, v___x_2400_);
v___x_2402_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_2403_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
v___x_2404_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2));
lean_inc(v_currMacroScope_2394_);
lean_inc(v_quotContext_2393_);
v___x_2405_ = l_Lean_addMacroScope(v_quotContext_2393_, v___x_2404_, v_currMacroScope_2394_);
v___x_2406_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8));
lean_inc_n(v___x_2401_, 2);
v___x_2407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2401_);
lean_ctor_set(v___x_2407_, 1, v___x_2403_);
lean_ctor_set(v___x_2407_, 2, v___x_2405_);
lean_ctor_set(v___x_2407_, 3, v___x_2406_);
v___x_2408_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_2409_ = l_Lean_Syntax_node2(v___x_2401_, v___x_2408_, v___x_2397_, v___x_2399_);
v___x_2410_ = l_Lean_Syntax_node2(v___x_2401_, v___x_2402_, v___x_2407_, v___x_2409_);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v_a_2388_);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___boxed(lean_object* v_x_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(v_x_2412_, v_a_2413_, v_a_2414_);
lean_dec_ref(v_a_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object* v_x_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_2416_);
v___x_2420_ = l_Lean_Syntax_isOfKind(v_x_2416_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_dec(v_x_2416_);
v___x_2421_ = lean_box(0);
v___x_2422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
lean_ctor_set(v___x_2422_, 1, v_a_2418_);
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2423_ = lean_unsigned_to_nat(0u);
v___x_2424_ = l_Lean_Syntax_getArg(v_x_2416_, v___x_2423_);
v___x_2425_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_2424_);
v___x_2426_ = l_Lean_Syntax_isOfKind(v___x_2424_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec(v___x_2424_);
lean_dec(v_x_2416_);
v___x_2427_ = lean_box(0);
v___x_2428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v_a_2418_);
return v___x_2428_;
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2429_ = lean_unsigned_to_nat(1u);
v___x_2430_ = l_Lean_Syntax_getArg(v_x_2416_, v___x_2429_);
lean_dec(v_x_2416_);
v___x_2431_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2430_);
v___x_2432_ = l_Lean_Syntax_matchesNull(v___x_2430_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec(v___x_2430_);
lean_dec(v___x_2424_);
v___x_2433_ = lean_box(0);
v___x_2434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v_a_2418_);
return v___x_2434_;
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v_ref_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2435_ = l_Lean_Syntax_getArg(v___x_2430_, v___x_2423_);
v___x_2436_ = l_Lean_Syntax_getArg(v___x_2430_, v___x_2429_);
lean_dec(v___x_2430_);
v_ref_2437_ = l_Lean_replaceRef(v___x_2424_, v_a_2417_);
lean_dec(v___x_2424_);
v___x_2438_ = 0;
v___x_2439_ = l_Lean_SourceInfo_fromRef(v_ref_2437_, v___x_2438_);
lean_dec(v_ref_2437_);
v___x_2440_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
v___x_2441_ = ((lean_object*)(l_List_term___x7e___00__closed__2));
lean_inc(v___x_2439_);
v___x_2442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2439_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = l_Lean_Syntax_node3(v___x_2439_, v___x_2440_, v___x_2435_, v___x_2442_, v___x_2436_);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v_a_2418_);
return v___x_2444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object* v_x_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(v_x_2445_, v_a_2446_, v_a_2447_);
lean_dec(v_a_2446_);
return v_res_2448_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm___redArg(lean_object* v_inst_2449_, lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
if (lean_obj_tag(v_x_2450_) == 0)
{
uint8_t v___x_2452_; 
lean_dec_ref(v_inst_2449_);
v___x_2452_ = l_List_isEmpty___redArg(v_x_2451_);
lean_dec(v_x_2451_);
return v___x_2452_;
}
else
{
lean_object* v_head_2453_; lean_object* v_tail_2454_; uint8_t v___x_2455_; 
v_head_2453_ = lean_ctor_get(v_x_2450_, 0);
lean_inc_n(v_head_2453_, 2);
v_tail_2454_ = lean_ctor_get(v_x_2450_, 1);
lean_inc(v_tail_2454_);
lean_dec_ref_known(v_x_2450_, 2);
lean_inc(v_x_2451_);
lean_inc_ref(v_inst_2449_);
v___x_2455_ = l_List_elem___redArg(v_inst_2449_, v_head_2453_, v_x_2451_);
if (v___x_2455_ == 0)
{
lean_dec(v_tail_2454_);
lean_dec(v_head_2453_);
lean_dec(v_x_2451_);
lean_dec_ref(v_inst_2449_);
return v___x_2455_;
}
else
{
lean_object* v___x_2456_; 
lean_inc_ref(v_inst_2449_);
v___x_2456_ = l_List_erase___redArg(v_inst_2449_, v_x_2451_, v_head_2453_);
v_x_2450_ = v_tail_2454_;
v_x_2451_ = v___x_2456_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPerm___redArg___boxed(lean_object* v_inst_2458_, lean_object* v_x_2459_, lean_object* v_x_2460_){
_start:
{
uint8_t v_res_2461_; lean_object* v_r_2462_; 
v_res_2461_ = l_List_isPerm___redArg(v_inst_2458_, v_x_2459_, v_x_2460_);
v_r_2462_ = lean_box(v_res_2461_);
return v_r_2462_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm(lean_object* v_00_u03b1_2463_, lean_object* v_inst_2464_, lean_object* v_x_2465_, lean_object* v_x_2466_){
_start:
{
uint8_t v___x_2467_; 
v___x_2467_ = l_List_isPerm___redArg(v_inst_2464_, v_x_2465_, v_x_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_List_isPerm___boxed(lean_object* v_00_u03b1_2468_, lean_object* v_inst_2469_, lean_object* v_x_2470_, lean_object* v_x_2471_){
_start:
{
uint8_t v_res_2472_; lean_object* v_r_2473_; 
v_res_2472_ = l_List_isPerm(v_00_u03b1_2468_, v_inst_2469_, v_x_2470_, v_x_2471_);
v_r_2473_ = lean_box(v_res_2472_);
return v_r_2473_;
}
}
LEAN_EXPORT uint8_t l_List_any___redArg(lean_object* v_x_2474_, lean_object* v_x_2475_){
_start:
{
if (lean_obj_tag(v_x_2474_) == 0)
{
uint8_t v___x_2476_; 
lean_dec_ref(v_x_2475_);
v___x_2476_ = 0;
return v___x_2476_;
}
else
{
lean_object* v_head_2477_; lean_object* v_tail_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v_head_2477_ = lean_ctor_get(v_x_2474_, 0);
lean_inc(v_head_2477_);
v_tail_2478_ = lean_ctor_get(v_x_2474_, 1);
lean_inc(v_tail_2478_);
lean_dec_ref_known(v_x_2474_, 2);
lean_inc_ref(v_x_2475_);
v___x_2479_ = lean_apply_1(v_x_2475_, v_head_2477_);
v___x_2480_ = lean_unbox(v___x_2479_);
if (v___x_2480_ == 0)
{
v_x_2474_ = v_tail_2478_;
goto _start;
}
else
{
uint8_t v___x_2482_; 
lean_dec(v_tail_2478_);
lean_dec_ref(v_x_2475_);
v___x_2482_ = lean_unbox(v___x_2479_);
return v___x_2482_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___redArg___boxed(lean_object* v_x_2483_, lean_object* v_x_2484_){
_start:
{
uint8_t v_res_2485_; lean_object* v_r_2486_; 
v_res_2485_ = l_List_any___redArg(v_x_2483_, v_x_2484_);
v_r_2486_ = lean_box(v_res_2485_);
return v_r_2486_;
}
}
LEAN_EXPORT uint8_t l_List_any(lean_object* v_00_u03b1_2487_, lean_object* v_x_2488_, lean_object* v_x_2489_){
_start:
{
uint8_t v___x_2490_; 
v___x_2490_ = l_List_any___redArg(v_x_2488_, v_x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_List_any___boxed(lean_object* v_00_u03b1_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_){
_start:
{
uint8_t v_res_2494_; lean_object* v_r_2495_; 
v_res_2494_ = l_List_any(v_00_u03b1_2491_, v_x_2492_, v_x_2493_);
v_r_2495_ = lean_box(v_res_2494_);
return v_r_2495_;
}
}
LEAN_EXPORT uint8_t l_List_all___redArg(lean_object* v_x_2496_, lean_object* v_x_2497_){
_start:
{
if (lean_obj_tag(v_x_2496_) == 0)
{
uint8_t v___x_2498_; 
lean_dec_ref(v_x_2497_);
v___x_2498_ = 1;
return v___x_2498_;
}
else
{
lean_object* v_head_2499_; lean_object* v_tail_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v_head_2499_ = lean_ctor_get(v_x_2496_, 0);
lean_inc(v_head_2499_);
v_tail_2500_ = lean_ctor_get(v_x_2496_, 1);
lean_inc(v_tail_2500_);
lean_dec_ref_known(v_x_2496_, 2);
lean_inc_ref(v_x_2497_);
v___x_2501_ = lean_apply_1(v_x_2497_, v_head_2499_);
v___x_2502_ = lean_unbox(v___x_2501_);
if (v___x_2502_ == 0)
{
uint8_t v___x_2503_; 
lean_dec(v_tail_2500_);
lean_dec_ref(v_x_2497_);
v___x_2503_ = lean_unbox(v___x_2501_);
return v___x_2503_;
}
else
{
v_x_2496_ = v_tail_2500_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___redArg___boxed(lean_object* v_x_2505_, lean_object* v_x_2506_){
_start:
{
uint8_t v_res_2507_; lean_object* v_r_2508_; 
v_res_2507_ = l_List_all___redArg(v_x_2505_, v_x_2506_);
v_r_2508_ = lean_box(v_res_2507_);
return v_r_2508_;
}
}
LEAN_EXPORT uint8_t l_List_all(lean_object* v_00_u03b1_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
uint8_t v___x_2512_; 
v___x_2512_ = l_List_all___redArg(v_x_2510_, v_x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_List_all___boxed(lean_object* v_00_u03b1_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_){
_start:
{
uint8_t v_res_2516_; lean_object* v_r_2517_; 
v_res_2516_ = l_List_all(v_00_u03b1_2513_, v_x_2514_, v_x_2515_);
v_r_2517_ = lean_box(v_res_2516_);
return v_r_2517_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_or_spec__0(lean_object* v_x_2518_){
_start:
{
if (lean_obj_tag(v_x_2518_) == 0)
{
uint8_t v___x_2519_; 
v___x_2519_ = 0;
return v___x_2519_;
}
else
{
lean_object* v_head_2520_; uint8_t v___x_2521_; 
v_head_2520_ = lean_ctor_get(v_x_2518_, 0);
v___x_2521_ = lean_unbox(v_head_2520_);
if (v___x_2521_ == 0)
{
lean_object* v_tail_2522_; 
v_tail_2522_ = lean_ctor_get(v_x_2518_, 1);
v_x_2518_ = v_tail_2522_;
goto _start;
}
else
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_unbox(v_head_2520_);
return v___x_2524_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_or_spec__0___boxed(lean_object* v_x_2525_){
_start:
{
uint8_t v_res_2526_; lean_object* v_r_2527_; 
v_res_2526_ = l_List_any___at___00List_or_spec__0(v_x_2525_);
lean_dec(v_x_2525_);
v_r_2527_ = lean_box(v_res_2526_);
return v_r_2527_;
}
}
LEAN_EXPORT uint8_t l_List_or(lean_object* v_bs_2528_){
_start:
{
uint8_t v___x_2529_; 
v___x_2529_ = l_List_any___at___00List_or_spec__0(v_bs_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object* v_bs_2530_){
_start:
{
uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_res_2531_ = l_List_or(v_bs_2530_);
lean_dec(v_bs_2530_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00List_and_spec__0(lean_object* v_x_2533_){
_start:
{
if (lean_obj_tag(v_x_2533_) == 0)
{
uint8_t v___x_2534_; 
v___x_2534_ = 1;
return v___x_2534_;
}
else
{
lean_object* v_head_2535_; uint8_t v___x_2536_; 
v_head_2535_ = lean_ctor_get(v_x_2533_, 0);
v___x_2536_ = lean_unbox(v_head_2535_);
if (v___x_2536_ == 0)
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_unbox(v_head_2535_);
return v___x_2537_;
}
else
{
lean_object* v_tail_2538_; 
v_tail_2538_ = lean_ctor_get(v_x_2533_, 1);
v_x_2533_ = v_tail_2538_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00List_and_spec__0___boxed(lean_object* v_x_2540_){
_start:
{
uint8_t v_res_2541_; lean_object* v_r_2542_; 
v_res_2541_ = l_List_all___at___00List_and_spec__0(v_x_2540_);
lean_dec(v_x_2540_);
v_r_2542_ = lean_box(v_res_2541_);
return v_r_2542_;
}
}
LEAN_EXPORT uint8_t l_List_and(lean_object* v_bs_2543_){
_start:
{
uint8_t v___x_2544_; 
v___x_2544_ = l_List_all___at___00List_and_spec__0(v_bs_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object* v_bs_2545_){
_start:
{
uint8_t v_res_2546_; lean_object* v_r_2547_; 
v_res_2546_ = l_List_and(v_bs_2545_);
lean_dec(v_bs_2545_);
v_r_2547_ = lean_box(v_res_2546_);
return v_r_2547_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___redArg(lean_object* v_f_2548_, lean_object* v_x_2549_, lean_object* v_x_2550_){
_start:
{
if (lean_obj_tag(v_x_2549_) == 0)
{
lean_object* v___x_2551_; 
lean_dec(v_x_2550_);
lean_dec(v_f_2548_);
v___x_2551_ = lean_box(0);
return v___x_2551_;
}
else
{
if (lean_obj_tag(v_x_2550_) == 0)
{
lean_object* v___x_2552_; 
lean_dec_ref_known(v_x_2549_, 2);
lean_dec(v_f_2548_);
v___x_2552_ = lean_box(0);
return v___x_2552_;
}
else
{
lean_object* v_head_2553_; lean_object* v_tail_2554_; lean_object* v_head_2555_; lean_object* v_tail_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2565_; 
v_head_2553_ = lean_ctor_get(v_x_2549_, 0);
lean_inc(v_head_2553_);
v_tail_2554_ = lean_ctor_get(v_x_2549_, 1);
lean_inc(v_tail_2554_);
lean_dec_ref_known(v_x_2549_, 2);
v_head_2555_ = lean_ctor_get(v_x_2550_, 0);
v_tail_2556_ = lean_ctor_get(v_x_2550_, 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_x_2550_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2558_ = v_x_2550_;
v_isShared_2559_ = v_isSharedCheck_2565_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_tail_2556_);
lean_inc(v_head_2555_);
lean_dec(v_x_2550_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2565_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
lean_inc(v_f_2548_);
v___x_2560_ = lean_apply_2(v_f_2548_, v_head_2553_, v_head_2555_);
v___x_2561_ = l_List_zipWith___redArg(v_f_2548_, v_tail_2554_, v_tail_2556_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 1, v___x_2561_);
lean_ctor_set(v___x_2558_, 0, v___x_2560_);
v___x_2563_ = v___x_2558_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith(lean_object* v_00_u03b1_2566_, lean_object* v_00_u03b2_2567_, lean_object* v_00_u03b3_2568_, lean_object* v_f_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_List_zipWith___redArg(v_f_2569_, v_x_2570_, v_x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object* v_x_2573_, lean_object* v_x_2574_, lean_object* v_h__1_2575_, lean_object* v_h__2_2576_){
_start:
{
if (lean_obj_tag(v_x_2573_) == 0)
{
lean_object* v___x_2577_; 
lean_dec(v_h__1_2575_);
v___x_2577_ = lean_apply_3(v_h__2_2576_, v_x_2573_, v_x_2574_, lean_box(0));
return v___x_2577_;
}
else
{
if (lean_obj_tag(v_x_2574_) == 0)
{
lean_object* v___x_2578_; 
lean_dec(v_h__1_2575_);
v___x_2578_ = lean_apply_3(v_h__2_2576_, v_x_2573_, v_x_2574_, lean_box(0));
return v___x_2578_;
}
else
{
lean_object* v_head_2579_; lean_object* v_tail_2580_; lean_object* v_head_2581_; lean_object* v_tail_2582_; lean_object* v___x_2583_; 
lean_dec(v_h__2_2576_);
v_head_2579_ = lean_ctor_get(v_x_2573_, 0);
lean_inc(v_head_2579_);
v_tail_2580_ = lean_ctor_get(v_x_2573_, 1);
lean_inc(v_tail_2580_);
lean_dec_ref_known(v_x_2573_, 2);
v_head_2581_ = lean_ctor_get(v_x_2574_, 0);
lean_inc(v_head_2581_);
v_tail_2582_ = lean_ctor_get(v_x_2574_, 1);
lean_inc(v_tail_2582_);
lean_dec_ref_known(v_x_2574_, 2);
v___x_2583_ = lean_apply_4(v_h__1_2575_, v_head_2579_, v_tail_2580_, v_head_2581_, v_tail_2582_);
return v___x_2583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object* v_00_u03b1_2584_, lean_object* v_00_u03b2_2585_, lean_object* v_motive_2586_, lean_object* v_x_2587_, lean_object* v_x_2588_, lean_object* v_h__1_2589_, lean_object* v_h__2_2590_){
_start:
{
if (lean_obj_tag(v_x_2587_) == 0)
{
lean_object* v___x_2591_; 
lean_dec(v_h__1_2589_);
v___x_2591_ = lean_apply_3(v_h__2_2590_, v_x_2587_, v_x_2588_, lean_box(0));
return v___x_2591_;
}
else
{
if (lean_obj_tag(v_x_2588_) == 0)
{
lean_object* v___x_2592_; 
lean_dec(v_h__1_2589_);
v___x_2592_ = lean_apply_3(v_h__2_2590_, v_x_2587_, v_x_2588_, lean_box(0));
return v___x_2592_;
}
else
{
lean_object* v_head_2593_; lean_object* v_tail_2594_; lean_object* v_head_2595_; lean_object* v_tail_2596_; lean_object* v___x_2597_; 
lean_dec(v_h__2_2590_);
v_head_2593_ = lean_ctor_get(v_x_2587_, 0);
lean_inc(v_head_2593_);
v_tail_2594_ = lean_ctor_get(v_x_2587_, 1);
lean_inc(v_tail_2594_);
lean_dec_ref_known(v_x_2587_, 2);
v_head_2595_ = lean_ctor_get(v_x_2588_, 0);
lean_inc(v_head_2595_);
v_tail_2596_ = lean_ctor_get(v_x_2588_, 1);
lean_inc(v_tail_2596_);
lean_dec_ref_known(v_x_2588_, 2);
v___x_2597_ = lean_apply_4(v_h__1_2589_, v_head_2593_, v_tail_2594_, v_head_2595_, v_tail_2596_);
return v___x_2597_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object* v_x_2598_, lean_object* v_x_2599_){
_start:
{
if (lean_obj_tag(v_x_2598_) == 0)
{
lean_object* v___x_2600_; 
lean_dec(v_x_2599_);
v___x_2600_ = lean_box(0);
return v___x_2600_;
}
else
{
if (lean_obj_tag(v_x_2599_) == 0)
{
lean_object* v___x_2601_; 
lean_dec_ref_known(v_x_2598_, 2);
v___x_2601_ = lean_box(0);
return v___x_2601_;
}
else
{
lean_object* v_head_2602_; lean_object* v_tail_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2620_; 
v_head_2602_ = lean_ctor_get(v_x_2598_, 0);
v_tail_2603_ = lean_ctor_get(v_x_2598_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_x_2598_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2605_ = v_x_2598_;
v_isShared_2606_ = v_isSharedCheck_2620_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_tail_2603_);
lean_inc(v_head_2602_);
lean_dec(v_x_2598_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2620_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v_head_2607_; lean_object* v_tail_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2619_; 
v_head_2607_ = lean_ctor_get(v_x_2599_, 0);
v_tail_2608_ = lean_ctor_get(v_x_2599_, 1);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_x_2599_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2610_ = v_x_2599_;
v_isShared_2611_ = v_isSharedCheck_2619_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_tail_2608_);
lean_inc(v_head_2607_);
lean_dec(v_x_2599_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2619_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set_tag(v___x_2605_, 0);
lean_ctor_set(v___x_2605_, 1, v_head_2607_);
v___x_2613_ = v___x_2605_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_head_2602_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_head_2607_);
v___x_2613_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
v___x_2614_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_tail_2603_, v_tail_2608_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 1, v___x_2614_);
lean_ctor_set(v___x_2610_, 0, v___x_2613_);
v___x_2616_ = v___x_2610_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zip___redArg(lean_object* v_xs_2621_, lean_object* v_ys_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2621_, v_ys_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_List_zip(lean_object* v_00_u03b1_2624_, lean_object* v_00_u03b2_2625_, lean_object* v_xs_2626_, lean_object* v_ys_2627_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2626_, v_ys_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object* v_00_u03b1_2629_, lean_object* v_00_u03b2_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_x_2631_, v_x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__0(lean_object* v_f_2634_, lean_object* v_b_2635_){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2636_ = lean_box(0);
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_b_2635_);
v___x_2638_ = lean_apply_2(v_f_2634_, v___x_2636_, v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__1(lean_object* v_f_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_a_2640_);
v___x_2642_ = lean_box(0);
v___x_2643_ = lean_apply_2(v_f_2639_, v___x_2641_, v___x_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object* v_f_2644_, lean_object* v_x_2645_, lean_object* v_x_2646_){
_start:
{
if (lean_obj_tag(v_x_2645_) == 0)
{
lean_object* v___f_2647_; lean_object* v___x_2648_; 
v___f_2647_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2647_, 0, v_f_2644_);
v___x_2648_ = l_List_map___redArg(v___f_2647_, v_x_2646_);
return v___x_2648_;
}
else
{
if (lean_obj_tag(v_x_2646_) == 0)
{
lean_object* v___f_2649_; lean_object* v___x_2650_; 
v___f_2649_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2649_, 0, v_f_2644_);
v___x_2650_ = l_List_map___redArg(v___f_2649_, v_x_2645_);
return v___x_2650_;
}
else
{
lean_object* v_head_2651_; lean_object* v_tail_2652_; lean_object* v_head_2653_; lean_object* v_tail_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2665_; 
v_head_2651_ = lean_ctor_get(v_x_2645_, 0);
lean_inc(v_head_2651_);
v_tail_2652_ = lean_ctor_get(v_x_2645_, 1);
lean_inc(v_tail_2652_);
lean_dec_ref_known(v_x_2645_, 2);
v_head_2653_ = lean_ctor_get(v_x_2646_, 0);
v_tail_2654_ = lean_ctor_get(v_x_2646_, 1);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_x_2646_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2656_ = v_x_2646_;
v_isShared_2657_ = v_isSharedCheck_2665_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_tail_2654_);
lean_inc(v_head_2653_);
lean_dec(v_x_2646_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2665_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_head_2651_);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_head_2653_);
lean_inc(v_f_2644_);
v___x_2660_ = lean_apply_2(v_f_2644_, v___x_2658_, v___x_2659_);
v___x_2661_ = l_List_zipWithAll___redArg(v_f_2644_, v_tail_2652_, v_tail_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 1, v___x_2661_);
lean_ctor_set(v___x_2656_, 0, v___x_2660_);
v___x_2663_ = v___x_2656_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object* v_00_u03b1_2666_, lean_object* v_00_u03b2_2667_, lean_object* v_00_u03b3_2668_, lean_object* v_f_2669_, lean_object* v_x_2670_, lean_object* v_x_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_List_zipWithAll___redArg(v_f_2669_, v_x_2670_, v_x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_List_unzip___redArg(lean_object* v_x_2673_){
_start:
{
if (lean_obj_tag(v_x_2673_) == 0)
{
lean_object* v___x_2674_; 
v___x_2674_ = ((lean_object*)(l_List_partition___redArg___closed__0));
return v___x_2674_;
}
else
{
lean_object* v_head_2675_; lean_object* v_tail_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2702_; 
v_head_2675_ = lean_ctor_get(v_x_2673_, 0);
v_tail_2676_ = lean_ctor_get(v_x_2673_, 1);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_x_2673_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2678_ = v_x_2673_;
v_isShared_2679_ = v_isSharedCheck_2702_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_tail_2676_);
lean_inc(v_head_2675_);
lean_dec(v_x_2673_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2702_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v_fst_2680_; lean_object* v_snd_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2701_; 
v_fst_2680_ = lean_ctor_get(v_head_2675_, 0);
v_snd_2681_ = lean_ctor_get(v_head_2675_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_head_2675_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2683_ = v_head_2675_;
v_isShared_2684_ = v_isSharedCheck_2701_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snd_2681_);
lean_inc(v_fst_2680_);
lean_dec(v_head_2675_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2701_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v_fst_2686_; lean_object* v_snd_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2700_; 
v___x_2685_ = l_List_unzip___redArg(v_tail_2676_);
v_fst_2686_ = lean_ctor_get(v___x_2685_, 0);
v_snd_2687_ = lean_ctor_get(v___x_2685_, 1);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2689_ = v___x_2685_;
v_isShared_2690_ = v_isSharedCheck_2700_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_snd_2687_);
lean_inc(v_fst_2686_);
lean_dec(v___x_2685_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2700_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v_fst_2686_);
lean_ctor_set(v___x_2678_, 0, v_fst_2680_);
v___x_2692_ = v___x_2678_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_fst_2680_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_fst_2686_);
v___x_2692_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2694_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set_tag(v___x_2683_, 1);
lean_ctor_set(v___x_2683_, 1, v_snd_2687_);
lean_ctor_set(v___x_2683_, 0, v_snd_2681_);
v___x_2694_ = v___x_2683_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_snd_2681_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_snd_2687_);
v___x_2694_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2696_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 1, v___x_2694_);
lean_ctor_set(v___x_2689_, 0, v___x_2692_);
v___x_2696_ = v___x_2689_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_unzip(lean_object* v_00_u03b1_2703_, lean_object* v_00_u03b2_2704_, lean_object* v_x_2705_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_List_unzip___redArg(v_x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___lam__0(lean_object* v_inst_2707_, lean_object* v_x1_2708_, lean_object* v_x2_2709_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_apply_2(v_inst_2707_, v_x1_2708_, v_x2_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg(lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_l_2713_){
_start:
{
lean_object* v___f_2714_; lean_object* v___x_2715_; 
v___f_2714_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2714_, 0, v_inst_2711_);
v___x_2715_ = l_List_foldr___redArg(v___f_2714_, v_inst_2712_, v_l_2713_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___boxed(lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_l_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_List_sum___redArg(v_inst_2716_, v_inst_2717_, v_l_2718_);
lean_dec(v_inst_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_List_sum(lean_object* v_00_u03b1_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_l_2723_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_List_sum___redArg(v_inst_2721_, v_inst_2722_, v_l_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_List_sum___boxed(lean_object* v_00_u03b1_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_l_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_List_sum(v_00_u03b1_2725_, v_inst_2726_, v_inst_2727_, v_l_2728_);
lean_dec(v_inst_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg(lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_l_2732_){
_start:
{
lean_object* v___f_2733_; lean_object* v___x_2734_; 
v___f_2733_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2733_, 0, v_inst_2730_);
v___x_2734_ = l_List_foldr___redArg(v___f_2733_, v_inst_2731_, v_l_2732_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg___boxed(lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_l_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_List_prod___redArg(v_inst_2735_, v_inst_2736_, v_l_2737_);
lean_dec(v_inst_2736_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_List_prod(lean_object* v_00_u03b1_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_l_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_List_prod___redArg(v_inst_2740_, v_inst_2741_, v_l_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_List_prod___boxed(lean_object* v_00_u03b1_2744_, lean_object* v_inst_2745_, lean_object* v_inst_2746_, lean_object* v_l_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_List_prod(v_00_u03b1_2744_, v_inst_2745_, v_inst_2746_, v_l_2747_);
lean_dec(v_inst_2746_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_List_range_loop(lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_zero_2751_; uint8_t v_isZero_2752_; 
v_zero_2751_ = lean_unsigned_to_nat(0u);
v_isZero_2752_ = lean_nat_dec_eq(v_a_2749_, v_zero_2751_);
if (v_isZero_2752_ == 1)
{
lean_dec(v_a_2749_);
return v_a_2750_;
}
else
{
lean_object* v_one_2753_; lean_object* v_n_2754_; lean_object* v___x_2755_; 
v_one_2753_ = lean_unsigned_to_nat(1u);
v_n_2754_ = lean_nat_sub(v_a_2749_, v_one_2753_);
lean_dec(v_a_2749_);
lean_inc(v_n_2754_);
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_n_2754_);
lean_ctor_set(v___x_2755_, 1, v_a_2750_);
v_a_2749_ = v_n_2754_;
v_a_2750_ = v___x_2755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range(lean_object* v_n_2757_){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_box(0);
v___x_2759_ = l_List_range_loop(v_n_2757_, v___x_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27(lean_object* v_x_2760_, lean_object* v_x_2761_, lean_object* v_x_2762_){
_start:
{
lean_object* v_zero_2763_; uint8_t v_isZero_2764_; 
v_zero_2763_ = lean_unsigned_to_nat(0u);
v_isZero_2764_ = lean_nat_dec_eq(v_x_2761_, v_zero_2763_);
if (v_isZero_2764_ == 1)
{
lean_object* v___x_2765_; 
lean_dec(v_x_2760_);
v___x_2765_ = lean_box(0);
return v___x_2765_;
}
else
{
lean_object* v_one_2766_; lean_object* v_n_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_one_2766_ = lean_unsigned_to_nat(1u);
v_n_2767_ = lean_nat_sub(v_x_2761_, v_one_2766_);
v___x_2768_ = lean_nat_add(v_x_2760_, v_x_2762_);
v___x_2769_ = l_List_range_x27(v___x_2768_, v_n_2767_, v_x_2762_);
lean_dec(v_n_2767_);
v___x_2770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2770_, 0, v_x_2760_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
return v___x_2770_;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object* v_x_2771_, lean_object* v_x_2772_, lean_object* v_x_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_List_range_x27(v_x_2771_, v_x_2772_, v_x_2773_);
lean_dec(v_x_2773_);
lean_dec(v_x_2772_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdx___redArg(lean_object* v_x_2775_, lean_object* v_x_2776_){
_start:
{
if (lean_obj_tag(v_x_2775_) == 0)
{
lean_object* v___x_2777_; 
lean_dec(v_x_2776_);
v___x_2777_ = lean_box(0);
return v___x_2777_;
}
else
{
lean_object* v_head_2778_; lean_object* v_tail_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2790_; 
v_head_2778_ = lean_ctor_get(v_x_2775_, 0);
v_tail_2779_ = lean_ctor_get(v_x_2775_, 1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_x_2775_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2781_ = v_x_2775_;
v_isShared_2782_ = v_isSharedCheck_2790_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_tail_2779_);
lean_inc(v_head_2778_);
lean_dec(v_x_2775_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2790_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
lean_inc(v_x_2776_);
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v_head_2778_);
lean_ctor_set(v___x_2783_, 1, v_x_2776_);
v___x_2784_ = lean_unsigned_to_nat(1u);
v___x_2785_ = lean_nat_add(v_x_2776_, v___x_2784_);
lean_dec(v_x_2776_);
v___x_2786_ = l_List_zipIdx___redArg(v_tail_2779_, v___x_2785_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 1, v___x_2786_);
lean_ctor_set(v___x_2781_, 0, v___x_2783_);
v___x_2788_ = v___x_2781_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdx(lean_object* v_00_u03b1_2791_, lean_object* v_x_2792_, lean_object* v_x_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_List_zipIdx___redArg(v_x_2792_, v_x_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object* v_inst_2795_, lean_object* v_x_2796_){
_start:
{
if (lean_obj_tag(v_x_2796_) == 0)
{
lean_object* v___x_2797_; 
lean_dec(v_inst_2795_);
v___x_2797_ = lean_box(0);
return v___x_2797_;
}
else
{
lean_object* v_head_2798_; lean_object* v_tail_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_head_2798_ = lean_ctor_get(v_x_2796_, 0);
lean_inc(v_head_2798_);
v_tail_2799_ = lean_ctor_get(v_x_2796_, 1);
lean_inc(v_tail_2799_);
lean_dec_ref_known(v_x_2796_, 2);
v___x_2800_ = l_List_foldl___redArg(v_inst_2795_, v_head_2798_, v_tail_2799_);
v___x_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object* v_00_u03b1_2802_, lean_object* v_inst_2803_, lean_object* v_x_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_List_min_x3f___redArg(v_inst_2803_, v_x_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object* v_inst_2806_, lean_object* v_x_2807_){
_start:
{
lean_object* v_head_2808_; lean_object* v_tail_2809_; lean_object* v___x_2810_; 
v_head_2808_ = lean_ctor_get(v_x_2807_, 0);
lean_inc(v_head_2808_);
v_tail_2809_ = lean_ctor_get(v_x_2807_, 1);
lean_inc(v_tail_2809_);
lean_dec(v_x_2807_);
v___x_2810_ = l_List_foldl___redArg(v_inst_2806_, v_head_2808_, v_tail_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_List_min(lean_object* v_00_u03b1_2811_, lean_object* v_inst_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_List_min___redArg(v_inst_2812_, v_x_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object* v_inst_2816_, lean_object* v_x_2817_){
_start:
{
if (lean_obj_tag(v_x_2817_) == 0)
{
lean_object* v___x_2818_; 
lean_dec(v_inst_2816_);
v___x_2818_ = lean_box(0);
return v___x_2818_;
}
else
{
lean_object* v_head_2819_; lean_object* v_tail_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_head_2819_ = lean_ctor_get(v_x_2817_, 0);
lean_inc(v_head_2819_);
v_tail_2820_ = lean_ctor_get(v_x_2817_, 1);
lean_inc(v_tail_2820_);
lean_dec_ref_known(v_x_2817_, 2);
v___x_2821_ = l_List_foldl___redArg(v_inst_2816_, v_head_2819_, v_tail_2820_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
return v___x_2822_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object* v_00_u03b1_2823_, lean_object* v_inst_2824_, lean_object* v_x_2825_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_List_max_x3f___redArg(v_inst_2824_, v_x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object* v_inst_2827_, lean_object* v_x_2828_){
_start:
{
lean_object* v_head_2829_; lean_object* v_tail_2830_; lean_object* v___x_2831_; 
v_head_2829_ = lean_ctor_get(v_x_2828_, 0);
lean_inc(v_head_2829_);
v_tail_2830_ = lean_ctor_get(v_x_2828_, 1);
lean_inc(v_tail_2830_);
lean_dec(v_x_2828_);
v___x_2831_ = l_List_foldl___redArg(v_inst_2827_, v_head_2829_, v_tail_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_List_max(lean_object* v_00_u03b1_2832_, lean_object* v_inst_2833_, lean_object* v_x_2834_, lean_object* v_x_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_List_max___redArg(v_inst_2833_, v_x_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_List_intersperse___redArg(lean_object* v_sep_2837_, lean_object* v_x_2838_){
_start:
{
if (lean_obj_tag(v_x_2838_) == 0)
{
lean_dec(v_sep_2837_);
return v_x_2838_;
}
else
{
lean_object* v_tail_2839_; 
v_tail_2839_ = lean_ctor_get(v_x_2838_, 1);
if (lean_obj_tag(v_tail_2839_) == 0)
{
lean_dec(v_sep_2837_);
return v_x_2838_;
}
else
{
lean_object* v_head_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2849_; 
lean_inc_ref(v_tail_2839_);
v_head_2840_ = lean_ctor_get(v_x_2838_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_x_2838_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v_x_2838_, 1);
lean_dec(v_unused_2850_);
v___x_2842_ = v_x_2838_;
v_isShared_2843_ = v_isSharedCheck_2849_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_head_2840_);
lean_dec(v_x_2838_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2849_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2846_; 
lean_inc(v_sep_2837_);
v___x_2844_ = l_List_intersperse___redArg(v_sep_2837_, v_tail_2839_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 1, v___x_2844_);
lean_ctor_set(v___x_2842_, 0, v_sep_2837_);
v___x_2846_ = v___x_2842_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_sep_2837_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2847_, 0, v_head_2840_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
return v___x_2847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperse(lean_object* v_00_u03b1_2851_, lean_object* v_sep_2852_, lean_object* v_x_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_List_intersperse___redArg(v_sep_2852_, v_x_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(lean_object* v___x_2855_, lean_object* v_x_2856_){
_start:
{
if (lean_obj_tag(v_x_2856_) == 0)
{
uint8_t v___x_2857_; 
lean_dec_ref(v___x_2855_);
v___x_2857_ = 0;
return v___x_2857_;
}
else
{
lean_object* v_head_2858_; lean_object* v_tail_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v_head_2858_ = lean_ctor_get(v_x_2856_, 0);
lean_inc(v_head_2858_);
v_tail_2859_ = lean_ctor_get(v_x_2856_, 1);
lean_inc(v_tail_2859_);
lean_dec_ref_known(v_x_2856_, 2);
lean_inc_ref(v___x_2855_);
v___x_2860_ = lean_apply_1(v___x_2855_, v_head_2858_);
v___x_2861_ = lean_unbox(v___x_2860_);
if (v___x_2861_ == 0)
{
v_x_2856_ = v_tail_2859_;
goto _start;
}
else
{
uint8_t v___x_2863_; 
lean_dec(v_tail_2859_);
lean_dec_ref(v___x_2855_);
v___x_2863_ = lean_unbox(v___x_2860_);
return v___x_2863_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg___boxed(lean_object* v___x_2864_, lean_object* v_x_2865_){
_start:
{
uint8_t v_res_2866_; lean_object* v_r_2867_; 
v_res_2866_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2864_, v_x_2865_);
v_r_2867_ = lean_box(v_res_2866_);
return v_r_2867_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object* v_r_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
if (lean_obj_tag(v_a_2869_) == 0)
{
lean_object* v___x_2871_; 
lean_dec_ref(v_r_2868_);
v___x_2871_ = l_List_reverse___redArg(v_a_2870_);
return v___x_2871_;
}
else
{
lean_object* v_head_2872_; lean_object* v_tail_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2884_; 
v_head_2872_ = lean_ctor_get(v_a_2869_, 0);
v_tail_2873_ = lean_ctor_get(v_a_2869_, 1);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_a_2869_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2875_ = v_a_2869_;
v_isShared_2876_ = v_isSharedCheck_2884_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_tail_2873_);
lean_inc(v_head_2872_);
lean_dec(v_a_2869_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2884_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; uint8_t v___x_2878_; 
lean_inc_ref(v_r_2868_);
lean_inc(v_head_2872_);
v___x_2877_ = lean_apply_1(v_r_2868_, v_head_2872_);
lean_inc(v_a_2870_);
v___x_2878_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2877_, v_a_2870_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2880_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v_a_2870_);
v___x_2880_ = v___x_2875_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_head_2872_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_a_2870_);
v___x_2880_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
v_a_2869_ = v_tail_2873_;
v_a_2870_ = v___x_2880_;
goto _start;
}
}
else
{
lean_del_object(v___x_2875_);
lean_dec(v_head_2872_);
v_a_2869_ = v_tail_2873_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object* v_00_u03b1_2885_, lean_object* v_r_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_List_eraseDupsBy_loop___redArg(v_r_2886_, v_a_2887_, v_a_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0(lean_object* v_00_u03b1_2890_, lean_object* v___x_2891_, lean_object* v_x_2892_){
_start:
{
uint8_t v___x_2893_; 
v___x_2893_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2891_, v_x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___boxed(lean_object* v_00_u03b1_2894_, lean_object* v___x_2895_, lean_object* v_x_2896_){
_start:
{
uint8_t v_res_2897_; lean_object* v_r_2898_; 
v_res_2897_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0(v_00_u03b1_2894_, v___x_2895_, v_x_2896_);
v_r_2898_ = lean_box(v_res_2897_);
return v_r_2898_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy___redArg(lean_object* v_r_2899_, lean_object* v_as_2900_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_box(0);
v___x_2902_ = l_List_eraseDupsBy_loop___redArg(v_r_2899_, v_as_2900_, v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy(lean_object* v_00_u03b1_2903_, lean_object* v_r_2904_, lean_object* v_as_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_List_eraseDupsBy___redArg(v_r_2904_, v_as_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT uint8_t l_List_eraseDups___redArg___lam__0(lean_object* v_inst_2907_, lean_object* v_x1_2908_, lean_object* v_x2_2909_){
_start:
{
lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = lean_apply_2(v_inst_2907_, v_x1_2908_, v_x2_2909_);
v___x_2911_ = lean_unbox(v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg___lam__0___boxed(lean_object* v_inst_2912_, lean_object* v_x1_2913_, lean_object* v_x2_2914_){
_start:
{
uint8_t v_res_2915_; lean_object* v_r_2916_; 
v_res_2915_ = l_List_eraseDups___redArg___lam__0(v_inst_2912_, v_x1_2913_, v_x2_2914_);
v_r_2916_ = lean_box(v_res_2915_);
return v_r_2916_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg(lean_object* v_inst_2917_, lean_object* v_as_2918_){
_start:
{
lean_object* v___f_2919_; lean_object* v___x_2920_; 
v___f_2919_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2919_, 0, v_inst_2917_);
v___x_2920_ = l_List_eraseDupsBy___redArg(v___f_2919_, v_as_2918_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object* v_00_u03b1_2921_, lean_object* v_inst_2922_, lean_object* v_as_2923_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_List_eraseDups___redArg(v_inst_2922_, v_as_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop___redArg(lean_object* v_r_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_){
_start:
{
if (lean_obj_tag(v_a_2927_) == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec_ref(v_r_2925_);
v___x_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2929_, 0, v_a_2926_);
lean_ctor_set(v___x_2929_, 1, v_a_2928_);
v___x_2930_ = l_List_reverse___redArg(v___x_2929_);
return v___x_2930_;
}
else
{
lean_object* v_head_2931_; lean_object* v_tail_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2943_; 
v_head_2931_ = lean_ctor_get(v_a_2927_, 0);
v_tail_2932_ = lean_ctor_get(v_a_2927_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_a_2927_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2934_ = v_a_2927_;
v_isShared_2935_ = v_isSharedCheck_2943_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_tail_2932_);
lean_inc(v_head_2931_);
lean_dec(v_a_2927_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2943_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; uint8_t v___x_2937_; 
lean_inc_ref(v_r_2925_);
lean_inc(v_head_2931_);
lean_inc(v_a_2926_);
v___x_2936_ = lean_apply_2(v_r_2925_, v_a_2926_, v_head_2931_);
v___x_2937_ = lean_unbox(v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2939_; 
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 1, v_a_2928_);
lean_ctor_set(v___x_2934_, 0, v_a_2926_);
v___x_2939_ = v___x_2934_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2926_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_a_2928_);
v___x_2939_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
v_a_2926_ = v_head_2931_;
v_a_2927_ = v_tail_2932_;
v_a_2928_ = v___x_2939_;
goto _start;
}
}
else
{
lean_del_object(v___x_2934_);
lean_dec(v_head_2931_);
v_a_2927_ = v_tail_2932_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop(lean_object* v_00_u03b1_2944_, lean_object* v_r_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_List_eraseRepsBy_loop___redArg(v_r_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy___redArg(lean_object* v_r_2950_, lean_object* v_x_2951_){
_start:
{
if (lean_obj_tag(v_x_2951_) == 0)
{
lean_dec_ref(v_r_2950_);
return v_x_2951_;
}
else
{
lean_object* v_head_2952_; lean_object* v_tail_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_head_2952_ = lean_ctor_get(v_x_2951_, 0);
lean_inc(v_head_2952_);
v_tail_2953_ = lean_ctor_get(v_x_2951_, 1);
lean_inc(v_tail_2953_);
lean_dec_ref_known(v_x_2951_, 2);
v___x_2954_ = lean_box(0);
v___x_2955_ = l_List_eraseRepsBy_loop___redArg(v_r_2950_, v_head_2952_, v_tail_2953_, v___x_2954_);
return v___x_2955_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy(lean_object* v_00_u03b1_2956_, lean_object* v_r_2957_, lean_object* v_x_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_List_eraseRepsBy___redArg(v_r_2957_, v_x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___redArg(lean_object* v_inst_2960_, lean_object* v_as_2961_){
_start:
{
lean_object* v___f_2962_; lean_object* v___x_2963_; 
v___f_2962_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2962_, 0, v_inst_2960_);
v___x_2963_ = l_List_eraseRepsBy___redArg(v___f_2962_, v_as_2961_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object* v_00_u03b1_2964_, lean_object* v_inst_2965_, lean_object* v_as_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_List_eraseReps___redArg(v_inst_2965_, v_as_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___redArg(lean_object* v_p_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
if (lean_obj_tag(v_a_2969_) == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_dec_ref(v_p_2968_);
v___x_2971_ = l_List_reverse___redArg(v_a_2970_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
lean_ctor_set(v___x_2972_, 1, v_a_2969_);
return v___x_2972_;
}
else
{
lean_object* v_head_2973_; lean_object* v_tail_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v_head_2973_ = lean_ctor_get(v_a_2969_, 0);
v_tail_2974_ = lean_ctor_get(v_a_2969_, 1);
lean_inc_ref(v_p_2968_);
lean_inc(v_head_2973_);
v___x_2975_ = lean_apply_1(v_p_2968_, v_head_2973_);
v___x_2976_ = lean_unbox(v___x_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec_ref(v_p_2968_);
v___x_2977_ = l_List_reverse___redArg(v_a_2970_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set(v___x_2978_, 1, v_a_2969_);
return v___x_2978_;
}
else
{
lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2986_; 
lean_inc(v_tail_2974_);
lean_inc(v_head_2973_);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_a_2969_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; lean_object* v_unused_2988_; 
v_unused_2987_ = lean_ctor_get(v_a_2969_, 1);
lean_dec(v_unused_2987_);
v_unused_2988_ = lean_ctor_get(v_a_2969_, 0);
lean_dec(v_unused_2988_);
v___x_2980_ = v_a_2969_;
v_isShared_2981_ = v_isSharedCheck_2986_;
goto v_resetjp_2979_;
}
else
{
lean_dec(v_a_2969_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2986_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 1, v_a_2970_);
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_head_2973_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_a_2970_);
v___x_2983_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
v_a_2969_ = v_tail_2974_;
v_a_2970_ = v___x_2983_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop(lean_object* v_00_u03b1_2989_, lean_object* v_p_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_List_span_loop___redArg(v_p_2990_, v_a_2991_, v_a_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_List_span___redArg(lean_object* v_p_2994_, lean_object* v_as_2995_){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_box(0);
v___x_2997_ = l_List_span_loop___redArg(v_p_2994_, v_as_2995_, v___x_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_List_span(lean_object* v_00_u03b1_2998_, lean_object* v_p_2999_, lean_object* v_as_3000_){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_box(0);
v___x_3002_ = l_List_span_loop___redArg(v_p_2999_, v_as_3000_, v___x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___redArg(lean_object* v_R_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
if (lean_obj_tag(v_a_3004_) == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_dec_ref(v_R_3003_);
v___x_3008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3008_, 0, v_a_3005_);
lean_ctor_set(v___x_3008_, 1, v_a_3006_);
v___x_3009_ = l_List_reverse___redArg(v___x_3008_);
v___x_3010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v_a_3007_);
v___x_3011_ = l_List_reverse___redArg(v___x_3010_);
return v___x_3011_;
}
else
{
lean_object* v_head_3012_; lean_object* v_tail_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3030_; 
v_head_3012_ = lean_ctor_get(v_a_3004_, 0);
v_tail_3013_ = lean_ctor_get(v_a_3004_, 1);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_a_3004_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3015_ = v_a_3004_;
v_isShared_3016_ = v_isSharedCheck_3030_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_tail_3013_);
lean_inc(v_head_3012_);
lean_dec(v_a_3004_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3030_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; uint8_t v___x_3018_; 
lean_inc_ref(v_R_3003_);
lean_inc(v_head_3012_);
lean_inc(v_a_3005_);
v___x_3017_ = lean_apply_2(v_R_3003_, v_a_3005_, v_head_3012_);
v___x_3018_ = lean_unbox(v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3019_ = lean_box(0);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v_a_3006_);
lean_ctor_set(v___x_3015_, 0, v_a_3005_);
v___x_3021_ = v___x_3015_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3005_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_a_3006_);
v___x_3021_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = l_List_reverse___redArg(v___x_3021_);
v___x_3023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
lean_ctor_set(v___x_3023_, 1, v_a_3007_);
v_a_3004_ = v_tail_3013_;
v_a_3005_ = v_head_3012_;
v_a_3006_ = v___x_3019_;
v_a_3007_ = v___x_3023_;
goto _start;
}
}
else
{
lean_object* v___x_3027_; 
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v_a_3006_);
lean_ctor_set(v___x_3015_, 0, v_a_3005_);
v___x_3027_ = v___x_3015_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3005_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_a_3006_);
v___x_3027_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
v_a_3004_ = v_tail_3013_;
v_a_3005_ = v_head_3012_;
v_a_3006_ = v___x_3027_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop(lean_object* v_00_u03b1_3031_, lean_object* v_R_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_List_splitBy_loop___redArg(v_R_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___redArg(lean_object* v_R_3038_, lean_object* v_x_3039_){
_start:
{
if (lean_obj_tag(v_x_3039_) == 0)
{
lean_object* v___x_3040_; 
lean_dec_ref(v_R_3038_);
v___x_3040_ = lean_box(0);
return v___x_3040_;
}
else
{
lean_object* v_head_3041_; lean_object* v_tail_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_head_3041_ = lean_ctor_get(v_x_3039_, 0);
lean_inc(v_head_3041_);
v_tail_3042_ = lean_ctor_get(v_x_3039_, 1);
lean_inc(v_tail_3042_);
lean_dec_ref_known(v_x_3039_, 2);
v___x_3043_ = lean_box(0);
v___x_3044_ = l_List_splitBy_loop___redArg(v_R_3038_, v_tail_3042_, v_head_3041_, v___x_3043_, v___x_3043_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy(lean_object* v_00_u03b1_3045_, lean_object* v_R_3046_, lean_object* v_x_3047_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_List_splitBy___redArg(v_R_3046_, v_x_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___redArg___lam__0(lean_object* v_inst_3049_, lean_object* v_ys_3050_, lean_object* v_x_3051_){
_start:
{
uint8_t v___x_3052_; 
v___x_3052_ = l_List_elem___redArg(v_inst_3049_, v_x_3051_, v_ys_3050_);
if (v___x_3052_ == 0)
{
uint8_t v___x_3053_; 
v___x_3053_ = 1;
return v___x_3053_;
}
else
{
uint8_t v___x_3054_; 
v___x_3054_ = 0;
return v___x_3054_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg___lam__0___boxed(lean_object* v_inst_3055_, lean_object* v_ys_3056_, lean_object* v_x_3057_){
_start:
{
uint8_t v_res_3058_; lean_object* v_r_3059_; 
v_res_3058_ = l_List_removeAll___redArg___lam__0(v_inst_3055_, v_ys_3056_, v_x_3057_);
v_r_3059_ = lean_box(v_res_3058_);
return v_r_3059_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg(lean_object* v_inst_3060_, lean_object* v_xs_3061_, lean_object* v_ys_3062_){
_start:
{
lean_object* v___f_3063_; lean_object* v___x_3064_; 
v___f_3063_ = lean_alloc_closure((void*)(l_List_removeAll___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3063_, 0, v_inst_3060_);
lean_closure_set(v___f_3063_, 1, v_ys_3062_);
v___x_3064_ = l_List_filter___redArg(v___f_3063_, v_xs_3061_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll(lean_object* v_00_u03b1_3065_, lean_object* v_inst_3066_, lean_object* v_xs_3067_, lean_object* v_ys_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_List_removeAll___redArg(v_inst_3066_, v_xs_3067_, v_ys_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_3070_, lean_object* v_h__1_3071_, lean_object* v_h__2_3072_){
_start:
{
if (lean_obj_tag(v_ys_3070_) == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_dec(v_h__2_3072_);
v___x_3073_ = lean_box(0);
v___x_3074_ = lean_apply_1(v_h__1_3071_, v___x_3073_);
return v___x_3074_;
}
else
{
lean_object* v_head_3075_; lean_object* v_tail_3076_; lean_object* v___x_3077_; 
lean_dec(v_h__1_3071_);
v_head_3075_ = lean_ctor_get(v_ys_3070_, 0);
lean_inc(v_head_3075_);
v_tail_3076_ = lean_ctor_get(v_ys_3070_, 1);
lean_inc(v_tail_3076_);
lean_dec_ref_known(v_ys_3070_, 2);
v___x_3077_ = lean_apply_2(v_h__2_3072_, v_head_3075_, v_tail_3076_);
return v___x_3077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_3078_, lean_object* v_motive_3079_, lean_object* v_ys_3080_, lean_object* v_h__1_3081_, lean_object* v_h__2_3082_){
_start:
{
if (lean_obj_tag(v_ys_3080_) == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
lean_dec(v_h__2_3082_);
v___x_3083_ = lean_box(0);
v___x_3084_ = lean_apply_1(v_h__1_3081_, v___x_3083_);
return v___x_3084_;
}
else
{
lean_object* v_head_3085_; lean_object* v_tail_3086_; lean_object* v___x_3087_; 
lean_dec(v_h__1_3081_);
v_head_3085_ = lean_ctor_get(v_ys_3080_, 0);
lean_inc(v_head_3085_);
v_tail_3086_ = lean_ctor_get(v_ys_3080_, 1);
lean_inc(v_tail_3086_);
lean_dec_ref_known(v_ys_3080_, 2);
v___x_3087_ = lean_apply_2(v_h__2_3082_, v_head_3085_, v_tail_3086_);
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(lean_object* v_x_3088_, lean_object* v_x_3089_, lean_object* v_h__1_3090_, lean_object* v_h__2_3091_){
_start:
{
if (lean_obj_tag(v_x_3088_) == 0)
{
lean_object* v___x_3092_; 
lean_dec(v_h__2_3091_);
v___x_3092_ = lean_apply_1(v_h__1_3090_, v_x_3089_);
return v___x_3092_;
}
else
{
lean_object* v_head_3093_; lean_object* v_tail_3094_; lean_object* v___x_3095_; 
lean_dec(v_h__1_3090_);
v_head_3093_ = lean_ctor_get(v_x_3088_, 0);
lean_inc(v_head_3093_);
v_tail_3094_ = lean_ctor_get(v_x_3088_, 1);
lean_inc(v_tail_3094_);
lean_dec_ref_known(v_x_3088_, 2);
v___x_3095_ = lean_apply_3(v_h__2_3091_, v_head_3093_, v_tail_3094_, v_x_3089_);
return v___x_3095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(lean_object* v_00_u03b1_3096_, lean_object* v_motive_3097_, lean_object* v_x_3098_, lean_object* v_x_3099_, lean_object* v_h__1_3100_, lean_object* v_h__2_3101_){
_start:
{
if (lean_obj_tag(v_x_3098_) == 0)
{
lean_object* v___x_3102_; 
lean_dec(v_h__2_3101_);
v___x_3102_ = lean_apply_1(v_h__1_3100_, v_x_3099_);
return v___x_3102_;
}
else
{
lean_object* v_head_3103_; lean_object* v_tail_3104_; lean_object* v___x_3105_; 
lean_dec(v_h__1_3100_);
v_head_3103_ = lean_ctor_get(v_x_3098_, 0);
lean_inc(v_head_3103_);
v_tail_3104_ = lean_ctor_get(v_x_3098_, 1);
lean_inc(v_tail_3104_);
lean_dec_ref_known(v_x_3098_, 2);
v___x_3105_ = lean_apply_3(v_h__2_3101_, v_head_3103_, v_tail_3104_, v_x_3099_);
return v___x_3105_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object* v_f_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_){
_start:
{
if (lean_obj_tag(v_a_3107_) == 0)
{
lean_object* v___x_3109_; 
lean_dec(v_f_3106_);
v___x_3109_ = l_List_reverse___redArg(v_a_3108_);
return v___x_3109_;
}
else
{
lean_object* v_head_3110_; lean_object* v_tail_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3120_; 
v_head_3110_ = lean_ctor_get(v_a_3107_, 0);
v_tail_3111_ = lean_ctor_get(v_a_3107_, 1);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_a_3107_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3113_ = v_a_3107_;
v_isShared_3114_ = v_isSharedCheck_3120_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_tail_3111_);
lean_inc(v_head_3110_);
lean_dec(v_a_3107_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3120_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
lean_inc(v_f_3106_);
v___x_3115_ = lean_apply_1(v_f_3106_, v_head_3110_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 1, v_a_3108_);
lean_ctor_set(v___x_3113_, 0, v___x_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_a_3108_);
v___x_3117_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
v_a_3107_ = v_tail_3111_;
v_a_3108_ = v___x_3117_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object* v_00_u03b1_3121_, lean_object* v_00_u03b2_3122_, lean_object* v_f_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_List_mapTR_loop___redArg(v_f_3123_, v_a_3124_, v_a_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object* v_f_3127_, lean_object* v_as_3128_){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_box(0);
v___x_3130_ = l_List_mapTR_loop___redArg(v_f_3127_, v_as_3128_, v___x_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR(lean_object* v_00_u03b1_3131_, lean_object* v_00_u03b2_3132_, lean_object* v_f_3133_, lean_object* v_as_3134_){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_box(0);
v___x_3136_ = l_List_mapTR_loop___redArg(v_f_3133_, v_as_3134_, v___x_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(lean_object* v_x_3137_, lean_object* v_x_3138_, lean_object* v_h__1_3139_, lean_object* v_h__2_3140_){
_start:
{
if (lean_obj_tag(v_x_3137_) == 0)
{
lean_object* v___x_3141_; 
lean_dec(v_h__2_3140_);
v___x_3141_ = lean_apply_1(v_h__1_3139_, v_x_3138_);
return v___x_3141_;
}
else
{
lean_object* v_head_3142_; lean_object* v_tail_3143_; lean_object* v___x_3144_; 
lean_dec(v_h__1_3139_);
v_head_3142_ = lean_ctor_get(v_x_3137_, 0);
lean_inc(v_head_3142_);
v_tail_3143_ = lean_ctor_get(v_x_3137_, 1);
lean_inc(v_tail_3143_);
lean_dec_ref_known(v_x_3137_, 2);
v___x_3144_ = lean_apply_3(v_h__2_3140_, v_head_3142_, v_tail_3143_, v_x_3138_);
return v___x_3144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(lean_object* v_00_u03b1_3145_, lean_object* v_00_u03b2_3146_, lean_object* v_motive_3147_, lean_object* v_x_3148_, lean_object* v_x_3149_, lean_object* v_h__1_3150_, lean_object* v_h__2_3151_){
_start:
{
if (lean_obj_tag(v_x_3148_) == 0)
{
lean_object* v___x_3152_; 
lean_dec(v_h__2_3151_);
v___x_3152_ = lean_apply_1(v_h__1_3150_, v_x_3149_);
return v___x_3152_;
}
else
{
lean_object* v_head_3153_; lean_object* v_tail_3154_; lean_object* v___x_3155_; 
lean_dec(v_h__1_3150_);
v_head_3153_ = lean_ctor_get(v_x_3148_, 0);
lean_inc(v_head_3153_);
v_tail_3154_ = lean_ctor_get(v_x_3148_, 1);
lean_inc(v_tail_3154_);
lean_dec_ref_known(v_x_3148_, 2);
v___x_3155_ = lean_apply_3(v_h__2_3151_, v_head_3153_, v_tail_3154_, v_x_3149_);
return v___x_3155_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object* v_p_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
if (lean_obj_tag(v_a_3157_) == 0)
{
lean_object* v___x_3159_; 
lean_dec_ref(v_p_3156_);
v___x_3159_ = l_List_reverse___redArg(v_a_3158_);
return v___x_3159_;
}
else
{
lean_object* v_head_3160_; lean_object* v_tail_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3172_; 
v_head_3160_ = lean_ctor_get(v_a_3157_, 0);
v_tail_3161_ = lean_ctor_get(v_a_3157_, 1);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_a_3157_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3163_ = v_a_3157_;
v_isShared_3164_ = v_isSharedCheck_3172_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_tail_3161_);
lean_inc(v_head_3160_);
lean_dec(v_a_3157_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3172_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; uint8_t v___x_3166_; 
lean_inc_ref(v_p_3156_);
lean_inc(v_head_3160_);
v___x_3165_ = lean_apply_1(v_p_3156_, v_head_3160_);
v___x_3166_ = lean_unbox(v___x_3165_);
if (v___x_3166_ == 0)
{
lean_del_object(v___x_3163_);
lean_dec(v_head_3160_);
v_a_3157_ = v_tail_3161_;
goto _start;
}
else
{
lean_object* v___x_3169_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v_a_3158_);
v___x_3169_ = v___x_3163_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_head_3160_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_a_3158_);
v___x_3169_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
v_a_3157_ = v_tail_3161_;
v_a_3158_ = v___x_3169_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object* v_00_u03b1_3173_, lean_object* v_p_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_List_filterTR_loop___redArg(v_p_3174_, v_a_3175_, v_a_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object* v_p_3178_, lean_object* v_as_3179_){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = lean_box(0);
v___x_3181_ = l_List_filterTR_loop___redArg(v_p_3178_, v_as_3179_, v___x_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR(lean_object* v_00_u03b1_3182_, lean_object* v_p_3183_, lean_object* v_as_3184_){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = lean_box(0);
v___x_3186_ = l_List_filterTR_loop___redArg(v_p_3183_, v_as_3184_, v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_zero_3190_; uint8_t v_isZero_3191_; 
v_zero_3190_ = lean_unsigned_to_nat(0u);
v_isZero_3191_ = lean_nat_dec_eq(v_a_3188_, v_zero_3190_);
if (v_isZero_3191_ == 1)
{
lean_dec(v_a_3188_);
lean_dec(v_a_3187_);
return v_a_3189_;
}
else
{
lean_object* v_one_3192_; lean_object* v_n_3193_; lean_object* v___x_3194_; 
v_one_3192_ = lean_unsigned_to_nat(1u);
v_n_3193_ = lean_nat_sub(v_a_3188_, v_one_3192_);
lean_dec(v_a_3188_);
lean_inc(v_a_3187_);
v___x_3194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3194_, 0, v_a_3187_);
lean_ctor_set(v___x_3194_, 1, v_a_3189_);
v_a_3188_ = v_n_3193_;
v_a_3189_ = v___x_3194_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object* v_00_u03b1_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_List_replicateTR_loop___redArg(v_a_3197_, v_a_3198_, v_a_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object* v_n_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = lean_box(0);
v___x_3204_ = l_List_replicateTR_loop___redArg(v_a_3202_, v_n_3201_, v___x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object* v_00_u03b1_3205_, lean_object* v_n_3206_, lean_object* v_a_3207_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_List_replicateTR___redArg(v_n_3206_, v_a_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(lean_object* v_x_3209_, lean_object* v_x_3210_, lean_object* v_h__1_3211_, lean_object* v_h__2_3212_){
_start:
{
lean_object* v_zero_3213_; uint8_t v_isZero_3214_; 
v_zero_3213_ = lean_unsigned_to_nat(0u);
v_isZero_3214_ = lean_nat_dec_eq(v_x_3209_, v_zero_3213_);
if (v_isZero_3214_ == 1)
{
lean_object* v___x_3215_; 
lean_dec(v_h__2_3212_);
v___x_3215_ = lean_apply_1(v_h__1_3211_, v_x_3210_);
return v___x_3215_;
}
else
{
lean_object* v_one_3216_; lean_object* v_n_3217_; lean_object* v___x_3218_; 
lean_dec(v_h__1_3211_);
v_one_3216_ = lean_unsigned_to_nat(1u);
v_n_3217_ = lean_nat_sub(v_x_3209_, v_one_3216_);
v___x_3218_ = lean_apply_2(v_h__2_3212_, v_n_3217_, v_x_3210_);
return v___x_3218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_3219_, lean_object* v_x_3220_, lean_object* v_h__1_3221_, lean_object* v_h__2_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(v_x_3219_, v_x_3220_, v_h__1_3221_, v_h__2_3222_);
lean_dec(v_x_3219_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(lean_object* v_00_u03b1_3224_, lean_object* v_motive_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_, lean_object* v_h__1_3228_, lean_object* v_h__2_3229_){
_start:
{
lean_object* v_zero_3230_; uint8_t v_isZero_3231_; 
v_zero_3230_ = lean_unsigned_to_nat(0u);
v_isZero_3231_ = lean_nat_dec_eq(v_x_3226_, v_zero_3230_);
if (v_isZero_3231_ == 1)
{
lean_object* v___x_3232_; 
lean_dec(v_h__2_3229_);
v___x_3232_ = lean_apply_1(v_h__1_3228_, v_x_3227_);
return v___x_3232_;
}
else
{
lean_object* v_one_3233_; lean_object* v_n_3234_; lean_object* v___x_3235_; 
lean_dec(v_h__1_3228_);
v_one_3233_ = lean_unsigned_to_nat(1u);
v_n_3234_ = lean_nat_sub(v_x_3226_, v_one_3233_);
v___x_3235_ = lean_apply_2(v_h__2_3229_, v_n_3234_, v_x_3227_);
return v___x_3235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_3236_, lean_object* v_motive_3237_, lean_object* v_x_3238_, lean_object* v_x_3239_, lean_object* v_h__1_3240_, lean_object* v_h__2_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(v_00_u03b1_3236_, v_motive_3237_, v_x_3238_, v_x_3239_, v_h__1_3240_, v_h__2_3241_);
lean_dec(v_x_3238_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(lean_object* v_x_3243_, lean_object* v_x_3244_, lean_object* v_h__1_3245_, lean_object* v_h__2_3246_){
_start:
{
lean_object* v_zero_3247_; uint8_t v_isZero_3248_; 
v_zero_3247_ = lean_unsigned_to_nat(0u);
v_isZero_3248_ = lean_nat_dec_eq(v_x_3243_, v_zero_3247_);
if (v_isZero_3248_ == 1)
{
lean_object* v___x_3249_; 
lean_dec(v_h__2_3246_);
v___x_3249_ = lean_apply_1(v_h__1_3245_, v_x_3244_);
return v___x_3249_;
}
else
{
lean_object* v_one_3250_; lean_object* v_n_3251_; lean_object* v___x_3252_; 
lean_dec(v_h__1_3245_);
v_one_3250_ = lean_unsigned_to_nat(1u);
v_n_3251_ = lean_nat_sub(v_x_3243_, v_one_3250_);
v___x_3252_ = lean_apply_2(v_h__2_3246_, v_n_3251_, v_x_3244_);
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_3253_, lean_object* v_x_3254_, lean_object* v_h__1_3255_, lean_object* v_h__2_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(v_x_3253_, v_x_3254_, v_h__1_3255_, v_h__2_3256_);
lean_dec(v_x_3253_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(lean_object* v_00_u03b1_3258_, lean_object* v_motive_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_, lean_object* v_h__1_3262_, lean_object* v_h__2_3263_){
_start:
{
lean_object* v_zero_3264_; uint8_t v_isZero_3265_; 
v_zero_3264_ = lean_unsigned_to_nat(0u);
v_isZero_3265_ = lean_nat_dec_eq(v_x_3260_, v_zero_3264_);
if (v_isZero_3265_ == 1)
{
lean_object* v___x_3266_; 
lean_dec(v_h__2_3263_);
v___x_3266_ = lean_apply_1(v_h__1_3262_, v_x_3261_);
return v___x_3266_;
}
else
{
lean_object* v_one_3267_; lean_object* v_n_3268_; lean_object* v___x_3269_; 
lean_dec(v_h__1_3262_);
v_one_3267_ = lean_unsigned_to_nat(1u);
v_n_3268_ = lean_nat_sub(v_x_3260_, v_one_3267_);
v___x_3269_ = lean_apply_2(v_h__2_3263_, v_n_3268_, v_x_3261_);
return v___x_3269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___boxed(lean_object* v_00_u03b1_3270_, lean_object* v_motive_3271_, lean_object* v_x_3272_, lean_object* v_x_3273_, lean_object* v_h__1_3274_, lean_object* v_h__2_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(v_00_u03b1_3270_, v_motive_3271_, v_x_3272_, v_x_3273_, v_h__1_3274_, v_h__2_3275_);
lean_dec(v_x_3272_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg(lean_object* v_n_3277_, lean_object* v_a_3278_, lean_object* v_l_3279_){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = l_List_lengthTR___redArg(v_l_3279_);
v___x_3281_ = lean_nat_sub(v_n_3277_, v___x_3280_);
lean_dec(v___x_3280_);
v___x_3282_ = l_List_replicateTR_loop___redArg(v_a_3278_, v___x_3281_, v_l_3279_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg___boxed(lean_object* v_n_3283_, lean_object* v_a_3284_, lean_object* v_l_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_List_leftpadTR___redArg(v_n_3283_, v_a_3284_, v_l_3285_);
lean_dec(v_n_3283_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object* v_00_u03b1_3287_, lean_object* v_n_3288_, lean_object* v_a_3289_, lean_object* v_l_3290_){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = l_List_lengthTR___redArg(v_l_3290_);
v___x_3292_ = lean_nat_sub(v_n_3288_, v___x_3291_);
lean_dec(v___x_3291_);
v___x_3293_ = l_List_replicateTR_loop___redArg(v_a_3289_, v___x_3292_, v_l_3290_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___boxed(lean_object* v_00_u03b1_3294_, lean_object* v_n_3295_, lean_object* v_a_3296_, lean_object* v_l_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_List_leftpadTR(v_00_u03b1_3294_, v_n_3295_, v_a_3296_, v_l_3297_);
lean_dec(v_n_3295_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg(lean_object* v_init_3299_, lean_object* v_x_3300_){
_start:
{
if (lean_obj_tag(v_x_3300_) == 0)
{
lean_inc_ref(v_init_3299_);
return v_init_3299_;
}
else
{
lean_object* v_head_3301_; lean_object* v_tail_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3328_; 
v_head_3301_ = lean_ctor_get(v_x_3300_, 0);
v_tail_3302_ = lean_ctor_get(v_x_3300_, 1);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_x_3300_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3304_ = v_x_3300_;
v_isShared_3305_ = v_isSharedCheck_3328_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_tail_3302_);
lean_inc(v_head_3301_);
lean_dec(v_x_3300_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3328_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_fst_3306_; lean_object* v_snd_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3327_; 
v_fst_3306_ = lean_ctor_get(v_head_3301_, 0);
v_snd_3307_ = lean_ctor_get(v_head_3301_, 1);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_head_3301_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3309_ = v_head_3301_;
v_isShared_3310_ = v_isSharedCheck_3327_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_snd_3307_);
lean_inc(v_fst_3306_);
lean_dec(v_head_3301_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3327_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v_fst_3312_; lean_object* v_snd_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3326_; 
v___x_3311_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3299_, v_tail_3302_);
v_fst_3312_ = lean_ctor_get(v___x_3311_, 0);
v_snd_3313_ = lean_ctor_get(v___x_3311_, 1);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3315_ = v___x_3311_;
v_isShared_3316_ = v_isSharedCheck_3326_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_snd_3313_);
lean_inc(v_fst_3312_);
lean_dec(v___x_3311_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3326_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 1, v_fst_3312_);
lean_ctor_set(v___x_3304_, 0, v_fst_3306_);
v___x_3318_ = v___x_3304_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_fst_3306_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_fst_3312_);
v___x_3318_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3320_; 
if (v_isShared_3310_ == 0)
{
lean_ctor_set_tag(v___x_3309_, 1);
lean_ctor_set(v___x_3309_, 1, v_snd_3313_);
lean_ctor_set(v___x_3309_, 0, v_snd_3307_);
v___x_3320_ = v___x_3309_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_snd_3307_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_snd_3313_);
v___x_3320_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
lean_object* v___x_3322_; 
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 1, v___x_3320_);
lean_ctor_set(v___x_3315_, 0, v___x_3318_);
v___x_3322_ = v___x_3315_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3318_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg___boxed(lean_object* v_init_3329_, lean_object* v_x_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3329_, v_x_3330_);
lean_dec_ref(v_init_3329_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object* v_l_3332_){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_3334_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v___x_3333_, v_l_3332_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object* v_00_u03b1_3335_, lean_object* v_00_u03b2_3336_, lean_object* v_l_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_List_unzipTR___redArg(v_l_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0(lean_object* v_00_u03b1_3339_, lean_object* v_00_u03b2_3340_, lean_object* v_init_3341_, lean_object* v_x_3342_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3341_, v_x_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___boxed(lean_object* v_00_u03b1_3344_, lean_object* v_00_u03b2_3345_, lean_object* v_init_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_List_foldr___at___00List_unzipTR_spec__0(v_00_u03b1_3344_, v_00_u03b2_3345_, v_init_3346_, v_x_3347_);
lean_dec_ref(v_init_3346_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object* v_step_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v_zero_3353_; uint8_t v_isZero_3354_; 
v_zero_3353_ = lean_unsigned_to_nat(0u);
v_isZero_3354_ = lean_nat_dec_eq(v_a_3350_, v_zero_3353_);
if (v_isZero_3354_ == 1)
{
lean_dec(v_a_3351_);
lean_dec(v_a_3350_);
return v_a_3352_;
}
else
{
lean_object* v_one_3355_; lean_object* v_n_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v_one_3355_ = lean_unsigned_to_nat(1u);
v_n_3356_ = lean_nat_sub(v_a_3350_, v_one_3355_);
lean_dec(v_a_3350_);
v___x_3357_ = lean_nat_sub(v_a_3351_, v_step_3349_);
lean_dec(v_a_3351_);
lean_inc(v___x_3357_);
v___x_3358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v_a_3352_);
v_a_3350_ = v_n_3356_;
v_a_3351_ = v___x_3357_;
v_a_3352_ = v___x_3358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object* v_step_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_List_range_x27TR_go(v_step_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
lean_dec(v_step_3360_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object* v_s_3365_, lean_object* v_n_3366_, lean_object* v_step_3367_){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3368_ = lean_nat_mul(v_step_3367_, v_n_3366_);
v___x_3369_ = lean_nat_add(v_s_3365_, v___x_3368_);
lean_dec(v___x_3368_);
v___x_3370_ = lean_box(0);
v___x_3371_ = l_List_range_x27TR_go(v_step_3367_, v_n_3366_, v___x_3369_, v___x_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object* v_s_3372_, lean_object* v_n_3373_, lean_object* v_step_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_List_range_x27TR(v_s_3372_, v_n_3373_, v_step_3374_);
lean_dec(v_step_3374_);
lean_dec(v_s_3372_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(lean_object* v_x_3376_, lean_object* v_x_3377_, lean_object* v_x_3378_, lean_object* v_h__1_3379_, lean_object* v_h__2_3380_){
_start:
{
lean_object* v_zero_3381_; uint8_t v_isZero_3382_; 
v_zero_3381_ = lean_unsigned_to_nat(0u);
v_isZero_3382_ = lean_nat_dec_eq(v_x_3376_, v_zero_3381_);
if (v_isZero_3382_ == 1)
{
lean_object* v___x_3383_; 
lean_dec(v_h__2_3380_);
v___x_3383_ = lean_apply_2(v_h__1_3379_, v_x_3377_, v_x_3378_);
return v___x_3383_;
}
else
{
lean_object* v_one_3384_; lean_object* v_n_3385_; lean_object* v___x_3386_; 
lean_dec(v_h__1_3379_);
v_one_3384_ = lean_unsigned_to_nat(1u);
v_n_3385_ = lean_nat_sub(v_x_3376_, v_one_3384_);
v___x_3386_ = lean_apply_3(v_h__2_3380_, v_n_3385_, v_x_3377_, v_x_3378_);
return v___x_3386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(lean_object* v_x_3387_, lean_object* v_x_3388_, lean_object* v_x_3389_, lean_object* v_h__1_3390_, lean_object* v_h__2_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(v_x_3387_, v_x_3388_, v_x_3389_, v_h__1_3390_, v_h__2_3391_);
lean_dec(v_x_3387_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object* v_motive_3393_, lean_object* v_x_3394_, lean_object* v_x_3395_, lean_object* v_x_3396_, lean_object* v_h__1_3397_, lean_object* v_h__2_3398_){
_start:
{
lean_object* v_zero_3399_; uint8_t v_isZero_3400_; 
v_zero_3399_ = lean_unsigned_to_nat(0u);
v_isZero_3400_ = lean_nat_dec_eq(v_x_3394_, v_zero_3399_);
if (v_isZero_3400_ == 1)
{
lean_object* v___x_3401_; 
lean_dec(v_h__2_3398_);
v___x_3401_ = lean_apply_2(v_h__1_3397_, v_x_3395_, v_x_3396_);
return v___x_3401_;
}
else
{
lean_object* v_one_3402_; lean_object* v_n_3403_; lean_object* v___x_3404_; 
lean_dec(v_h__1_3397_);
v_one_3402_ = lean_unsigned_to_nat(1u);
v_n_3403_ = lean_nat_sub(v_x_3394_, v_one_3402_);
v___x_3404_ = lean_apply_3(v_h__2_3398_, v_n_3403_, v_x_3395_, v_x_3396_);
return v___x_3404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(lean_object* v_motive_3405_, lean_object* v_x_3406_, lean_object* v_x_3407_, lean_object* v_x_3408_, lean_object* v_h__1_3409_, lean_object* v_h__2_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(v_motive_3405_, v_x_3406_, v_x_3407_, v_x_3408_, v_h__1_3409_, v_h__2_3410_);
lean_dec(v_x_3406_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg(lean_object* v_sep_3412_, lean_object* v_init_3413_, lean_object* v_x_3414_){
_start:
{
if (lean_obj_tag(v_x_3414_) == 0)
{
lean_dec(v_sep_3412_);
lean_inc(v_init_3413_);
return v_init_3413_;
}
else
{
lean_object* v_head_3415_; lean_object* v_tail_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3425_; 
v_head_3415_ = lean_ctor_get(v_x_3414_, 0);
v_tail_3416_ = lean_ctor_get(v_x_3414_, 1);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_x_3414_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3418_ = v_x_3414_;
v_isShared_3419_ = v_isSharedCheck_3425_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_tail_3416_);
lean_inc(v_head_3415_);
lean_dec(v_x_3414_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3425_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
lean_inc(v_sep_3412_);
v___x_3420_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3412_, v_init_3413_, v_tail_3416_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 1, v___x_3420_);
v___x_3422_ = v___x_3418_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_head_3415_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3423_, 0, v_sep_3412_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
return v___x_3423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(lean_object* v_sep_3426_, lean_object* v_init_3427_, lean_object* v_x_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3426_, v_init_3427_, v_x_3428_);
lean_dec(v_init_3427_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object* v_sep_3430_, lean_object* v_x_3431_){
_start:
{
if (lean_obj_tag(v_x_3431_) == 0)
{
lean_dec(v_sep_3430_);
return v_x_3431_;
}
else
{
lean_object* v_tail_3432_; 
v_tail_3432_ = lean_ctor_get(v_x_3431_, 1);
lean_inc(v_tail_3432_);
if (lean_obj_tag(v_tail_3432_) == 0)
{
lean_dec(v_sep_3430_);
return v_x_3431_;
}
else
{
lean_object* v_head_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3452_; 
v_head_3433_ = lean_ctor_get(v_x_3431_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_x_3431_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; 
v_unused_3453_ = lean_ctor_get(v_x_3431_, 1);
lean_dec(v_unused_3453_);
v___x_3435_ = v_x_3431_;
v_isShared_3436_ = v_isSharedCheck_3452_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_head_3433_);
lean_dec(v_x_3431_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3452_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v_head_3437_; lean_object* v_tail_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3451_; 
v_head_3437_ = lean_ctor_get(v_tail_3432_, 0);
v_tail_3438_ = lean_ctor_get(v_tail_3432_, 1);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_tail_3432_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3440_ = v_tail_3432_;
v_isShared_3441_ = v_isSharedCheck_3451_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_tail_3438_);
lean_inc(v_head_3437_);
lean_dec(v_tail_3432_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3451_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3442_ = lean_box(0);
lean_inc(v_sep_3430_);
v___x_3443_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3430_, v___x_3442_, v_tail_3438_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3443_);
v___x_3445_ = v___x_3440_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_head_3437_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3447_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v___x_3445_);
lean_ctor_set(v___x_3435_, 0, v_sep_3430_);
v___x_3447_ = v___x_3435_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_sep_3430_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3448_, 0, v_head_3433_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
return v___x_3448_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object* v_00_u03b1_3454_, lean_object* v_sep_3455_, lean_object* v_x_3456_){
_start:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_List_intersperseTR___redArg(v_sep_3455_, v_x_3456_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0(lean_object* v_00_u03b1_3458_, lean_object* v_sep_3459_, lean_object* v_init_3460_, lean_object* v_x_3461_){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3459_, v_init_3460_, v_x_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___boxed(lean_object* v_00_u03b1_3463_, lean_object* v_sep_3464_, lean_object* v_init_3465_, lean_object* v_x_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_List_foldr___at___00List_intersperseTR_spec__0(v_00_u03b1_3463_, v_sep_3464_, v_init_3465_, v_x_3466_);
lean_dec(v_init_3465_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(lean_object* v_x_3468_, lean_object* v_h__1_3469_, lean_object* v_h__2_3470_, lean_object* v_h__3_3471_){
_start:
{
if (lean_obj_tag(v_x_3468_) == 0)
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
lean_dec(v_h__3_3471_);
lean_dec(v_h__2_3470_);
v___x_3472_ = lean_box(0);
v___x_3473_ = lean_apply_1(v_h__1_3469_, v___x_3472_);
return v___x_3473_;
}
else
{
lean_object* v_tail_3474_; 
lean_dec(v_h__1_3469_);
v_tail_3474_ = lean_ctor_get(v_x_3468_, 1);
if (lean_obj_tag(v_tail_3474_) == 0)
{
lean_object* v_head_3475_; lean_object* v___x_3476_; 
lean_dec(v_h__3_3471_);
v_head_3475_ = lean_ctor_get(v_x_3468_, 0);
lean_inc(v_head_3475_);
lean_dec_ref_known(v_x_3468_, 2);
v___x_3476_ = lean_apply_1(v_h__2_3470_, v_head_3475_);
return v___x_3476_;
}
else
{
lean_object* v_head_3477_; lean_object* v_head_3478_; lean_object* v_tail_3479_; lean_object* v___x_3480_; 
lean_inc_ref(v_tail_3474_);
lean_dec(v_h__2_3470_);
v_head_3477_ = lean_ctor_get(v_x_3468_, 0);
lean_inc(v_head_3477_);
lean_dec_ref_known(v_x_3468_, 2);
v_head_3478_ = lean_ctor_get(v_tail_3474_, 0);
lean_inc(v_head_3478_);
v_tail_3479_ = lean_ctor_get(v_tail_3474_, 1);
lean_inc(v_tail_3479_);
lean_dec_ref_known(v_tail_3474_, 2);
v___x_3480_ = lean_apply_3(v_h__3_3471_, v_head_3477_, v_head_3478_, v_tail_3479_);
return v___x_3480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object* v_00_u03b1_3481_, lean_object* v_motive_3482_, lean_object* v_x_3483_, lean_object* v_h__1_3484_, lean_object* v_h__2_3485_, lean_object* v_h__3_3486_){
_start:
{
if (lean_obj_tag(v_x_3483_) == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec(v_h__3_3486_);
lean_dec(v_h__2_3485_);
v___x_3487_ = lean_box(0);
v___x_3488_ = lean_apply_1(v_h__1_3484_, v___x_3487_);
return v___x_3488_;
}
else
{
lean_object* v_tail_3489_; 
lean_dec(v_h__1_3484_);
v_tail_3489_ = lean_ctor_get(v_x_3483_, 1);
if (lean_obj_tag(v_tail_3489_) == 0)
{
lean_object* v_head_3490_; lean_object* v___x_3491_; 
lean_dec(v_h__3_3486_);
v_head_3490_ = lean_ctor_get(v_x_3483_, 0);
lean_inc(v_head_3490_);
lean_dec_ref_known(v_x_3483_, 2);
v___x_3491_ = lean_apply_1(v_h__2_3485_, v_head_3490_);
return v___x_3491_;
}
else
{
lean_object* v_head_3492_; lean_object* v_head_3493_; lean_object* v_tail_3494_; lean_object* v___x_3495_; 
lean_inc_ref(v_tail_3489_);
lean_dec(v_h__2_3485_);
v_head_3492_ = lean_ctor_get(v_x_3483_, 0);
lean_inc(v_head_3492_);
lean_dec_ref_known(v_x_3483_, 2);
v_head_3493_ = lean_ctor_get(v_tail_3489_, 0);
lean_inc(v_head_3493_);
v_tail_3494_ = lean_ctor_get(v_tail_3489_, 1);
lean_inc(v_tail_3494_);
lean_dec_ref_known(v_tail_3489_, 2);
v___x_3495_ = lean_apply_3(v_h__3_3486_, v_head_3492_, v_head_3493_, v_tail_3494_);
return v___x_3495_;
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
