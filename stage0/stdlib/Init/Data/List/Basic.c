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
LEAN_EXPORT lean_object* l_List_instBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instBEq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instBEq___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_2_, 0, lean_box(0));
lean_closure_set(v___x_2_, 1, v_inst_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_List_instBEq(lean_object* v_00_u03b1_3_, lean_object* v_inst_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_closure((void*)(l_List_beq___boxed), 4, 2);
lean_closure_set(v___x_5_, 0, lean_box(0));
lean_closure_set(v___x_5_, 1, v_inst_4_);
return v___x_5_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv___redArg(lean_object* v_x_6_, lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_6_) == 0)
{
lean_dec_ref(v_x_8_);
if (lean_obj_tag(v_x_7_) == 0)
{
uint8_t v___x_9_; 
v___x_9_ = 1;
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec_ref_known(v_x_7_, 2);
v___x_10_ = 0;
return v___x_10_;
}
}
else
{
if (lean_obj_tag(v_x_7_) == 0)
{
uint8_t v___x_11_; 
lean_dec_ref_known(v_x_6_, 2);
lean_dec_ref(v_x_8_);
v___x_11_ = 0;
return v___x_11_;
}
else
{
lean_object* v_head_12_; lean_object* v_tail_13_; lean_object* v_head_14_; lean_object* v_tail_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v_head_12_ = lean_ctor_get(v_x_6_, 0);
lean_inc(v_head_12_);
v_tail_13_ = lean_ctor_get(v_x_6_, 1);
lean_inc(v_tail_13_);
lean_dec_ref_known(v_x_6_, 2);
v_head_14_ = lean_ctor_get(v_x_7_, 0);
lean_inc(v_head_14_);
v_tail_15_ = lean_ctor_get(v_x_7_, 1);
lean_inc(v_tail_15_);
lean_dec_ref_known(v_x_7_, 2);
lean_inc_ref(v_x_8_);
v___x_16_ = lean_apply_2(v_x_8_, v_head_12_, v_head_14_);
v___x_17_ = lean_unbox(v___x_16_);
if (v___x_17_ == 0)
{
uint8_t v___x_18_; 
lean_dec(v_tail_15_);
lean_dec(v_tail_13_);
lean_dec_ref(v_x_8_);
v___x_18_ = lean_unbox(v___x_16_);
return v___x_18_;
}
else
{
v_x_6_ = v_tail_13_;
v_x_7_ = v_tail_15_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___redArg___boxed(lean_object* v_x_20_, lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_List_isEqv___redArg(v_x_20_, v_x_21_, v_x_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv(lean_object* v_00_u03b1_25_, lean_object* v_x_26_, lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = l_List_isEqv___redArg(v_x_26_, v_x_27_, v_x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_List_isEqv___boxed(lean_object* v_00_u03b1_30_, lean_object* v_x_31_, lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_List_isEqv(v_00_u03b1_30_, v_x_31_, v_x_32_, v_x_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLex___redArg(lean_object* v_inst_36_, lean_object* v_h_37_, lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
lean_dec_ref(v_h_37_);
lean_dec_ref(v_inst_36_);
if (lean_obj_tag(v_x_39_) == 0)
{
uint8_t v___x_40_; 
v___x_40_ = 0;
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
lean_dec_ref_known(v_x_39_, 2);
v___x_41_ = 1;
return v___x_41_;
}
}
else
{
if (lean_obj_tag(v_x_39_) == 0)
{
uint8_t v___x_42_; 
lean_dec_ref_known(v_x_38_, 2);
lean_dec_ref(v_h_37_);
lean_dec_ref(v_inst_36_);
v___x_42_ = 0;
return v___x_42_;
}
else
{
lean_object* v_head_43_; lean_object* v_tail_44_; lean_object* v_head_45_; lean_object* v_tail_46_; lean_object* v_decide_47_; uint8_t v___x_48_; 
v_head_43_ = lean_ctor_get(v_x_38_, 0);
lean_inc_n(v_head_43_, 2);
v_tail_44_ = lean_ctor_get(v_x_38_, 1);
lean_inc(v_tail_44_);
lean_dec_ref_known(v_x_38_, 2);
v_head_45_ = lean_ctor_get(v_x_39_, 0);
lean_inc_n(v_head_45_, 2);
v_tail_46_ = lean_ctor_get(v_x_39_, 1);
lean_inc(v_tail_46_);
lean_dec_ref_known(v_x_39_, 2);
lean_inc_ref(v_h_37_);
v_decide_47_ = lean_apply_2(v_h_37_, v_head_43_, v_head_45_);
v___x_48_ = lean_unbox(v_decide_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; uint8_t v___x_50_; 
lean_inc_ref(v_inst_36_);
v___x_49_ = lean_apply_2(v_inst_36_, v_head_43_, v_head_45_);
v___x_50_ = lean_unbox(v___x_49_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
lean_dec(v_tail_46_);
lean_dec(v_tail_44_);
lean_dec_ref(v_h_37_);
lean_dec_ref(v_inst_36_);
v___x_51_ = lean_unbox(v___x_49_);
return v___x_51_;
}
else
{
uint8_t v_decide_52_; 
v_decide_52_ = l_List_decidableLex___redArg(v_inst_36_, v_h_37_, v_tail_44_, v_tail_46_);
if (v_decide_52_ == 0)
{
return v_decide_52_;
}
else
{
uint8_t v___x_53_; 
v___x_53_ = lean_unbox(v___x_49_);
return v___x_53_;
}
}
}
else
{
uint8_t v___x_54_; 
lean_dec(v_tail_46_);
lean_dec(v_head_45_);
lean_dec(v_tail_44_);
lean_dec(v_head_43_);
lean_dec_ref(v_h_37_);
lean_dec_ref(v_inst_36_);
v___x_54_ = lean_unbox(v_decide_47_);
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableLex___redArg___boxed(lean_object* v_inst_55_, lean_object* v_h_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_List_decidableLex___redArg(v_inst_55_, v_h_56_, v_x_57_, v_x_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLex(lean_object* v_00_u03b1_61_, lean_object* v_inst_62_, lean_object* v_r_63_, lean_object* v_h_64_, lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = l_List_decidableLex___redArg(v_inst_62_, v_h_64_, v_x_65_, v_x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLex___boxed(lean_object* v_00_u03b1_68_, lean_object* v_inst_69_, lean_object* v_r_70_, lean_object* v_h_71_, lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_List_decidableLex(v_00_u03b1_68_, v_inst_69_, v_r_70_, v_h_71_, v_x_72_, v_x_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT lean_object* l_List_instLT___redArg(){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_List_instLT___redArg___boxed(lean_object* v___dummy_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_List_instLT___redArg();
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_List_instLT(lean_object* v_00_u03b1_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLT___redArg(lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_l_u2081_85_, lean_object* v_l_u2082_86_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = l_List_decidableLex___redArg(v_inst_83_, v_inst_84_, v_l_u2081_85_, v_l_u2082_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLT___redArg___boxed(lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_l_u2081_90_, lean_object* v_l_u2082_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_List_decidableLT___redArg(v_inst_88_, v_inst_89_, v_l_u2081_90_, v_l_u2082_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLT(lean_object* v_00_u03b1_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_l_u2081_98_, lean_object* v_l_u2082_99_){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = l_List_decidableLex___redArg(v_inst_95_, v_inst_97_, v_l_u2081_98_, v_l_u2082_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLT___boxed(lean_object* v_00_u03b1_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_l_u2081_105_, lean_object* v_l_u2082_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_List_decidableLT(v_00_u03b1_101_, v_inst_102_, v_inst_103_, v_inst_104_, v_l_u2081_105_, v_l_u2082_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT lean_object* l_List_instLE___redArg(){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_List_instLE___redArg___boxed(lean_object* v___dummy_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_List_instLE___redArg();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_List_instLE(lean_object* v_00_u03b1_113_, lean_object* v_inst_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(0);
return v___x_115_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLE___redArg(lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_l_u2081_118_, lean_object* v_l_u2082_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = l_List_decidableLex___redArg(v_inst_116_, v_inst_117_, v_l_u2082_119_, v_l_u2081_118_);
if (v___x_120_ == 0)
{
uint8_t v___x_121_; 
v___x_121_ = 1;
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_List_decidableLE___redArg___boxed(lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_l_u2081_125_, lean_object* v_l_u2082_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_List_decidableLE___redArg(v_inst_123_, v_inst_124_, v_l_u2081_125_, v_l_u2082_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l_List_decidableLE(lean_object* v_00_u03b1_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_l_u2081_133_, lean_object* v_l_u2082_134_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = l_List_decidableLE___redArg(v_inst_130_, v_inst_132_, v_l_u2081_133_, v_l_u2082_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_List_decidableLE___boxed(lean_object* v_00_u03b1_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_l_u2081_140_, lean_object* v_l_u2082_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_List_decidableLE(v_00_u03b1_136_, v_inst_137_, v_inst_138_, v_inst_139_, v_l_u2081_140_, v_l_u2082_141_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__12(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l_List_lex___auto__1___closed__10));
v___x_171_ = l_Lean_mkAtom(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_List_lex___auto__1___closed__12, &l_List_lex___auto__1___closed__12_once, _init_l_List_lex___auto__1___closed__12);
v___x_173_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_174_ = lean_array_push(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_List_lex___auto__1___closed__19));
v___x_190_ = l_Lean_mkAtom(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__21(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_List_lex___auto__1___closed__20, &l_List_lex___auto__1___closed__20_once, _init_l_List_lex___auto__1___closed__20);
v___x_192_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_193_ = lean_array_push(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = ((lean_object*)(l_List_lex___auto__1___closed__26));
v___x_208_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_209_ = lean_array_push(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = lean_obj_once(&l_List_lex___auto__1___closed__27, &l_List_lex___auto__1___closed__27_once, _init_l_List_lex___auto__1___closed__27);
v___x_211_ = ((lean_object*)(l_List_lex___auto__1___closed__23));
v___x_212_ = lean_box(2);
v___x_213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_211_);
lean_ctor_set(v___x_213_, 2, v___x_210_);
return v___x_213_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_obj_once(&l_List_lex___auto__1___closed__28, &l_List_lex___auto__1___closed__28_once, _init_l_List_lex___auto__1___closed__28);
v___x_215_ = lean_obj_once(&l_List_lex___auto__1___closed__21, &l_List_lex___auto__1___closed__21_once, _init_l_List_lex___auto__1___closed__21);
v___x_216_ = lean_array_push(v___x_215_, v___x_214_);
return v___x_216_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_217_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_218_ = ((lean_object*)(l_List_lex___auto__1___closed__18));
v___x_219_ = lean_box(2);
v___x_220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_217_);
return v___x_220_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_obj_once(&l_List_lex___auto__1___closed__30, &l_List_lex___auto__1___closed__30_once, _init_l_List_lex___auto__1___closed__30);
v___x_222_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_223_ = lean_array_push(v___x_222_, v___x_221_);
return v___x_223_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_List_lex___auto__1___closed__36));
v___x_235_ = l_Lean_mkAtom(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_obj_once(&l_List_lex___auto__1___closed__37, &l_List_lex___auto__1___closed__37_once, _init_l_List_lex___auto__1___closed__37);
v___x_237_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_238_ = lean_array_push(v___x_237_, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&l_List_lex___auto__1___closed__28, &l_List_lex___auto__1___closed__28_once, _init_l_List_lex___auto__1___closed__28);
v___x_240_ = lean_obj_once(&l_List_lex___auto__1___closed__38, &l_List_lex___auto__1___closed__38_once, _init_l_List_lex___auto__1___closed__38);
v___x_241_ = lean_array_push(v___x_240_, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = lean_obj_once(&l_List_lex___auto__1___closed__39, &l_List_lex___auto__1___closed__39_once, _init_l_List_lex___auto__1___closed__39);
v___x_243_ = ((lean_object*)(l_List_lex___auto__1___closed__35));
v___x_244_ = lean_box(2);
v___x_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_242_);
return v___x_245_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&l_List_lex___auto__1___closed__40, &l_List_lex___auto__1___closed__40_once, _init_l_List_lex___auto__1___closed__40);
v___x_247_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_248_ = lean_array_push(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_List_lex___auto__1___closed__42));
v___x_251_ = l_Lean_mkAtom(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_obj_once(&l_List_lex___auto__1___closed__43, &l_List_lex___auto__1___closed__43_once, _init_l_List_lex___auto__1___closed__43);
v___x_253_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_254_ = lean_array_push(v___x_253_, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_obj_once(&l_List_lex___auto__1___closed__40, &l_List_lex___auto__1___closed__40_once, _init_l_List_lex___auto__1___closed__40);
v___x_256_ = lean_obj_once(&l_List_lex___auto__1___closed__44, &l_List_lex___auto__1___closed__44_once, _init_l_List_lex___auto__1___closed__44);
v___x_257_ = lean_array_push(v___x_256_, v___x_255_);
return v___x_257_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_258_ = lean_obj_once(&l_List_lex___auto__1___closed__45, &l_List_lex___auto__1___closed__45_once, _init_l_List_lex___auto__1___closed__45);
v___x_259_ = ((lean_object*)(l_List_lex___auto__1___closed__33));
v___x_260_ = lean_box(2);
v___x_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
lean_ctor_set(v___x_261_, 2, v___x_258_);
return v___x_261_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l_List_lex___auto__1___closed__46, &l_List_lex___auto__1___closed__46_once, _init_l_List_lex___auto__1___closed__46);
v___x_263_ = lean_obj_once(&l_List_lex___auto__1___closed__31, &l_List_lex___auto__1___closed__31_once, _init_l_List_lex___auto__1___closed__31);
v___x_264_ = lean_array_push(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__49(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l_List_lex___auto__1___closed__48));
v___x_267_ = l_Lean_mkAtom(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__50(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_obj_once(&l_List_lex___auto__1___closed__49, &l_List_lex___auto__1___closed__49_once, _init_l_List_lex___auto__1___closed__49);
v___x_269_ = lean_obj_once(&l_List_lex___auto__1___closed__47, &l_List_lex___auto__1___closed__47_once, _init_l_List_lex___auto__1___closed__47);
v___x_270_ = lean_array_push(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__51(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = lean_obj_once(&l_List_lex___auto__1___closed__50, &l_List_lex___auto__1___closed__50_once, _init_l_List_lex___auto__1___closed__50);
v___x_272_ = ((lean_object*)(l_List_lex___auto__1___closed__16));
v___x_273_ = lean_box(2);
v___x_274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_271_);
return v___x_274_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__52(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_obj_once(&l_List_lex___auto__1___closed__51, &l_List_lex___auto__1___closed__51_once, _init_l_List_lex___auto__1___closed__51);
v___x_276_ = lean_obj_once(&l_List_lex___auto__1___closed__13, &l_List_lex___auto__1___closed__13_once, _init_l_List_lex___auto__1___closed__13);
v___x_277_ = lean_array_push(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__53(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_278_ = lean_obj_once(&l_List_lex___auto__1___closed__52, &l_List_lex___auto__1___closed__52_once, _init_l_List_lex___auto__1___closed__52);
v___x_279_ = ((lean_object*)(l_List_lex___auto__1___closed__11));
v___x_280_ = lean_box(2);
v___x_281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_278_);
return v___x_281_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__54(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_obj_once(&l_List_lex___auto__1___closed__53, &l_List_lex___auto__1___closed__53_once, _init_l_List_lex___auto__1___closed__53);
v___x_283_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_284_ = lean_array_push(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__55(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_285_ = lean_obj_once(&l_List_lex___auto__1___closed__54, &l_List_lex___auto__1___closed__54_once, _init_l_List_lex___auto__1___closed__54);
v___x_286_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_287_ = lean_box(2);
v___x_288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
lean_ctor_set(v___x_288_, 2, v___x_285_);
return v___x_288_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__56(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_obj_once(&l_List_lex___auto__1___closed__55, &l_List_lex___auto__1___closed__55_once, _init_l_List_lex___auto__1___closed__55);
v___x_290_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_291_ = lean_array_push(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__57(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l_List_lex___auto__1___closed__56, &l_List_lex___auto__1___closed__56_once, _init_l_List_lex___auto__1___closed__56);
v___x_293_ = ((lean_object*)(l_List_lex___auto__1___closed__7));
v___x_294_ = lean_box(2);
v___x_295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_292_);
return v___x_295_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__58(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_List_lex___auto__1___closed__57, &l_List_lex___auto__1___closed__57_once, _init_l_List_lex___auto__1___closed__57);
v___x_297_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_298_ = lean_array_push(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__59(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = lean_obj_once(&l_List_lex___auto__1___closed__58, &l_List_lex___auto__1___closed__58_once, _init_l_List_lex___auto__1___closed__58);
v___x_300_ = ((lean_object*)(l_List_lex___auto__1___closed__4));
v___x_301_ = lean_box(2);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_299_);
return v___x_302_;
}
}
static lean_object* _init_l_List_lex___auto__1(void){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_List_lex___auto__1___closed__59, &l_List_lex___auto__1___closed__59_once, _init_l_List_lex___auto__1___closed__59);
return v___x_303_;
}
}
LEAN_EXPORT uint8_t l_List_lex___redArg(lean_object* v_inst_304_, lean_object* v_l_u2081_305_, lean_object* v_l_u2082_306_, lean_object* v_lt_307_){
_start:
{
if (lean_obj_tag(v_l_u2081_305_) == 0)
{
lean_dec_ref(v_lt_307_);
lean_dec_ref(v_inst_304_);
if (lean_obj_tag(v_l_u2082_306_) == 0)
{
uint8_t v___x_308_; 
v___x_308_ = 0;
return v___x_308_;
}
else
{
uint8_t v___x_309_; 
lean_dec_ref_known(v_l_u2082_306_, 2);
v___x_309_ = 1;
return v___x_309_;
}
}
else
{
if (lean_obj_tag(v_l_u2082_306_) == 0)
{
uint8_t v___x_310_; 
lean_dec_ref_known(v_l_u2081_305_, 2);
lean_dec_ref(v_lt_307_);
lean_dec_ref(v_inst_304_);
v___x_310_ = 0;
return v___x_310_;
}
else
{
lean_object* v_head_311_; lean_object* v_tail_312_; lean_object* v_head_313_; lean_object* v_tail_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_head_311_ = lean_ctor_get(v_l_u2081_305_, 0);
lean_inc_n(v_head_311_, 2);
v_tail_312_ = lean_ctor_get(v_l_u2081_305_, 1);
lean_inc(v_tail_312_);
lean_dec_ref_known(v_l_u2081_305_, 2);
v_head_313_ = lean_ctor_get(v_l_u2082_306_, 0);
lean_inc_n(v_head_313_, 2);
v_tail_314_ = lean_ctor_get(v_l_u2082_306_, 1);
lean_inc(v_tail_314_);
lean_dec_ref_known(v_l_u2082_306_, 2);
lean_inc_ref(v_lt_307_);
v___x_315_ = lean_apply_2(v_lt_307_, v_head_311_, v_head_313_);
v___x_316_ = lean_unbox(v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; uint8_t v___x_318_; 
lean_inc_ref(v_inst_304_);
v___x_317_ = lean_apply_2(v_inst_304_, v_head_311_, v_head_313_);
v___x_318_ = lean_unbox(v___x_317_);
if (v___x_318_ == 0)
{
uint8_t v___x_319_; 
lean_dec(v_tail_314_);
lean_dec(v_tail_312_);
lean_dec_ref(v_lt_307_);
lean_dec_ref(v_inst_304_);
v___x_319_ = lean_unbox(v___x_317_);
return v___x_319_;
}
else
{
v_l_u2081_305_ = v_tail_312_;
v_l_u2082_306_ = v_tail_314_;
goto _start;
}
}
else
{
uint8_t v___x_321_; 
lean_dec(v_tail_314_);
lean_dec(v_head_313_);
lean_dec(v_tail_312_);
lean_dec(v_head_311_);
lean_dec_ref(v_lt_307_);
lean_dec_ref(v_inst_304_);
v___x_321_ = lean_unbox(v___x_315_);
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_lex___redArg___boxed(lean_object* v_inst_322_, lean_object* v_l_u2081_323_, lean_object* v_l_u2082_324_, lean_object* v_lt_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_List_lex___redArg(v_inst_322_, v_l_u2081_323_, v_l_u2082_324_, v_lt_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l_List_lex(lean_object* v_00_u03b1_328_, lean_object* v_inst_329_, lean_object* v_l_u2081_330_, lean_object* v_l_u2082_331_, lean_object* v_lt_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = l_List_lex___redArg(v_inst_329_, v_l_u2081_330_, v_l_u2082_331_, v_lt_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_List_lex___boxed(lean_object* v_00_u03b1_334_, lean_object* v_inst_335_, lean_object* v_l_u2081_336_, lean_object* v_l_u2082_337_, lean_object* v_lt_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_List_lex(v_00_u03b1_334_, v_inst_335_, v_l_u2081_336_, v_l_u2082_337_, v_lt_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg(lean_object* v_x_341_){
_start:
{
lean_object* v_tail_342_; 
v_tail_342_ = lean_ctor_get(v_x_341_, 1);
if (lean_obj_tag(v_tail_342_) == 0)
{
lean_object* v_head_343_; 
v_head_343_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_head_343_);
return v_head_343_;
}
else
{
v_x_341_ = v_tail_342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg___boxed(lean_object* v_x_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_List_getLast___redArg(v_x_345_);
lean_dec(v_x_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_List_getLast(lean_object* v_00_u03b1_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_List_getLast___redArg(v_x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___boxed(lean_object* v_00_u03b1_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_List_getLast(v_00_u03b1_351_, v_x_352_, v_x_353_);
lean_dec(v_x_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg(lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_box(0);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = l_List_getLast___redArg(v_x_355_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg___boxed(lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_List_getLast_x3f___redArg(v_x_359_);
lean_dec(v_x_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f(lean_object* v_00_u03b1_361_, lean_object* v_x_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_List_getLast_x3f___redArg(v_x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___boxed(lean_object* v_00_u03b1_364_, lean_object* v_x_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_List_getLast_x3f(v_00_u03b1_364_, v_x_365_);
lean_dec(v_x_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg(lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_inc(v_x_368_);
return v_x_368_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = l_List_getLast___redArg(v_x_367_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg___boxed(lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_List_getLastD___redArg(v_x_370_, v_x_371_);
lean_dec(v_x_371_);
lean_dec(v_x_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD(lean_object* v_00_u03b1_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_List_getLastD___redArg(v_x_374_, v_x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___boxed(lean_object* v_00_u03b1_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_List_getLastD(v_00_u03b1_377_, v_x_378_, v_x_379_);
lean_dec(v_x_379_);
lean_dec(v_x_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg(lean_object* v_x_381_){
_start:
{
lean_object* v_head_382_; 
v_head_382_ = lean_ctor_get(v_x_381_, 0);
lean_inc(v_head_382_);
return v_head_382_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg___boxed(lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_List_head___redArg(v_x_383_);
lean_dec(v_x_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_List_head(lean_object* v_00_u03b1_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
lean_object* v_head_388_; 
v_head_388_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_head_388_);
return v_head_388_;
}
}
LEAN_EXPORT lean_object* l_List_head___boxed(lean_object* v_00_u03b1_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_List_head(v_00_u03b1_389_, v_x_390_, v_x_391_);
lean_dec(v_x_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg(lean_object* v_x_393_){
_start:
{
if (lean_obj_tag(v_x_393_) == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_box(0);
return v___x_394_;
}
else
{
lean_object* v_head_395_; lean_object* v___x_396_; 
v_head_395_ = lean_ctor_get(v_x_393_, 0);
lean_inc(v_head_395_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_head_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg___boxed(lean_object* v_x_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_List_head_x3f___redArg(v_x_397_);
lean_dec(v_x_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f(lean_object* v_00_u03b1_399_, lean_object* v_x_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_List_head_x3f___redArg(v_x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___boxed(lean_object* v_00_u03b1_402_, lean_object* v_x_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_List_head_x3f(v_00_u03b1_402_, v_x_403_);
lean_dec(v_x_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg(lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_inc(v_x_406_);
return v_x_406_;
}
else
{
lean_object* v_head_407_; 
v_head_407_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_head_407_);
return v_head_407_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg___boxed(lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_List_headD___redArg(v_x_408_, v_x_409_);
lean_dec(v_x_409_);
lean_dec(v_x_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_List_headD(lean_object* v_00_u03b1_411_, lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_412_) == 0)
{
lean_inc(v_x_413_);
return v_x_413_;
}
else
{
lean_object* v_head_414_; 
v_head_414_ = lean_ctor_get(v_x_412_, 0);
lean_inc(v_head_414_);
return v_head_414_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___boxed(lean_object* v_00_u03b1_415_, lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_List_headD(v_00_u03b1_415_, v_x_416_, v_x_417_);
lean_dec(v_x_417_);
lean_dec(v_x_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg(lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
return v_x_419_;
}
else
{
lean_object* v_tail_420_; 
v_tail_420_ = lean_ctor_get(v_x_419_, 1);
lean_inc(v_tail_420_);
return v_tail_420_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg___boxed(lean_object* v_x_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_List_tail___redArg(v_x_421_);
lean_dec(v_x_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_List_tail(lean_object* v_00_u03b1_423_, lean_object* v_x_424_){
_start:
{
if (lean_obj_tag(v_x_424_) == 0)
{
return v_x_424_;
}
else
{
lean_object* v_tail_425_; 
v_tail_425_ = lean_ctor_get(v_x_424_, 1);
lean_inc(v_tail_425_);
return v_tail_425_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___boxed(lean_object* v_00_u03b1_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_List_tail(v_00_u03b1_426_, v_x_427_);
lean_dec(v_x_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg(lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_box(0);
return v___x_430_;
}
else
{
lean_object* v_tail_431_; lean_object* v___x_432_; 
v_tail_431_ = lean_ctor_get(v_x_429_, 1);
lean_inc(v_tail_431_);
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v_tail_431_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg___boxed(lean_object* v_x_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_List_tail_x3f___redArg(v_x_433_);
lean_dec(v_x_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f(lean_object* v_00_u03b1_435_, lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_List_tail_x3f___redArg(v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___boxed(lean_object* v_00_u03b1_438_, lean_object* v_x_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_List_tail_x3f(v_00_u03b1_438_, v_x_439_);
lean_dec(v_x_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg(lean_object* v_l_441_, lean_object* v_fallback_442_){
_start:
{
if (lean_obj_tag(v_l_441_) == 0)
{
lean_inc(v_fallback_442_);
return v_fallback_442_;
}
else
{
lean_object* v_tail_443_; 
v_tail_443_ = lean_ctor_get(v_l_441_, 1);
lean_inc(v_tail_443_);
return v_tail_443_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg___boxed(lean_object* v_l_444_, lean_object* v_fallback_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_List_tailD___redArg(v_l_444_, v_fallback_445_);
lean_dec(v_fallback_445_);
lean_dec(v_l_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_List_tailD(lean_object* v_00_u03b1_447_, lean_object* v_l_448_, lean_object* v_fallback_449_){
_start:
{
if (lean_obj_tag(v_l_448_) == 0)
{
lean_inc(v_fallback_449_);
return v_fallback_449_;
}
else
{
lean_object* v_tail_450_; 
v_tail_450_ = lean_ctor_get(v_l_448_, 1);
lean_inc(v_tail_450_);
return v_tail_450_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___boxed(lean_object* v_00_u03b1_451_, lean_object* v_l_452_, lean_object* v_fallback_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_List_tailD(v_00_u03b1_451_, v_l_452_, v_fallback_453_);
lean_dec(v_fallback_453_);
lean_dec(v_l_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_List_filter___redArg(lean_object* v_p_455_, lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
lean_dec_ref(v_p_455_);
return v_x_456_;
}
else
{
lean_object* v_head_457_; lean_object* v_tail_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_469_; 
v_head_457_ = lean_ctor_get(v_x_456_, 0);
v_tail_458_ = lean_ctor_get(v_x_456_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_x_456_);
if (v_isSharedCheck_469_ == 0)
{
v___x_460_ = v_x_456_;
v_isShared_461_ = v_isSharedCheck_469_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_tail_458_);
lean_inc(v_head_457_);
lean_dec(v_x_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_469_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; uint8_t v___x_463_; 
lean_inc_ref(v_p_455_);
lean_inc(v_head_457_);
v___x_462_ = lean_apply_1(v_p_455_, v_head_457_);
v___x_463_ = lean_unbox(v___x_462_);
if (v___x_463_ == 0)
{
lean_del_object(v___x_460_);
lean_dec(v_head_457_);
v_x_456_ = v_tail_458_;
goto _start;
}
else
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = l_List_filter___redArg(v_p_455_, v_tail_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v___x_465_);
v___x_467_ = v___x_460_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_head_457_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filter(lean_object* v_00_u03b1_470_, lean_object* v_p_471_, lean_object* v_x_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_List_filter___redArg(v_p_471_, v_x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg(lean_object* v_f_474_, lean_object* v_init_475_, lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_dec(v_f_474_);
lean_inc(v_init_475_);
return v_init_475_;
}
else
{
lean_object* v_head_477_; lean_object* v_tail_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_head_477_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_head_477_);
v_tail_478_ = lean_ctor_get(v_x_476_, 1);
lean_inc(v_tail_478_);
lean_dec_ref_known(v_x_476_, 2);
lean_inc(v_f_474_);
v___x_479_ = l_List_foldr___redArg(v_f_474_, v_init_475_, v_tail_478_);
v___x_480_ = lean_apply_2(v_f_474_, v_head_477_, v___x_479_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg___boxed(lean_object* v_f_481_, lean_object* v_init_482_, lean_object* v_x_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_List_foldr___redArg(v_f_481_, v_init_482_, v_x_483_);
lean_dec(v_init_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_List_foldr(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_f_487_, lean_object* v_init_488_, lean_object* v_x_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_List_foldr___redArg(v_f_487_, v_init_488_, v_x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___boxed(lean_object* v_00_u03b1_491_, lean_object* v_00_u03b2_492_, lean_object* v_f_493_, lean_object* v_init_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_List_foldr(v_00_u03b1_491_, v_00_u03b2_492_, v_f_493_, v_init_494_, v_x_495_);
lean_dec(v_init_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_List_reverseAux___redArg(lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_497_) == 0)
{
return v_x_498_;
}
else
{
lean_object* v_head_499_; lean_object* v_tail_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_head_499_ = lean_ctor_get(v_x_497_, 0);
v_tail_500_ = lean_ctor_get(v_x_497_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_x_497_);
if (v_isSharedCheck_508_ == 0)
{
v___x_502_ = v_x_497_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_tail_500_);
lean_inc(v_head_499_);
lean_dec(v_x_497_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v_x_498_);
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_head_499_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_x_498_);
v___x_505_ = v_reuseFailAlloc_507_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
v_x_497_ = v_tail_500_;
v_x_498_ = v___x_505_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object* v_00_u03b1_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_List_reverseAux___redArg(v_x_510_, v_x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_List_reverse___redArg(lean_object* v_as_513_){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_box(0);
v___x_515_ = l_List_reverseAux___redArg(v_as_513_, v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_List_reverse(lean_object* v_00_u03b1_516_, lean_object* v_as_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_List_reverse___redArg(v_as_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR___redArg(lean_object* v_as_519_, lean_object* v_bs_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = l_List_reverse___redArg(v_as_519_);
v___x_522_ = l_List_reverseAux___redArg(v___x_521_, v_bs_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR(lean_object* v_00_u03b1_523_, lean_object* v_as_524_, lean_object* v_bs_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_List_appendTR___redArg(v_as_524_, v_bs_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend___redArg(){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = ((lean_object*)(l_List_instAppend___redArg___closed__0));
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend___redArg___boxed(lean_object* v___dummy_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_List_instAppend___redArg();
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend(lean_object* v_00_u03b1_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = ((lean_object*)(l_List_instAppend___redArg___closed__0));
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_List_singleton___redArg(lean_object* v_a_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_box(0);
v___x_536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_List_singleton(lean_object* v_00_u03b1_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_box(0);
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v_a_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg(lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v_zero_543_; uint8_t v_isZero_544_; 
v_zero_543_ = lean_unsigned_to_nat(0u);
v_isZero_544_ = lean_nat_dec_eq(v_x_541_, v_zero_543_);
if (v_isZero_544_ == 1)
{
lean_object* v___x_545_; 
lean_dec(v_x_542_);
v___x_545_ = lean_box(0);
return v___x_545_;
}
else
{
lean_object* v_one_546_; lean_object* v_n_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_one_546_ = lean_unsigned_to_nat(1u);
v_n_547_ = lean_nat_sub(v_x_541_, v_one_546_);
lean_inc(v_x_542_);
v___x_548_ = l_List_replicate___redArg(v_n_547_, v_x_542_);
lean_dec(v_n_547_);
v___x_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_549_, 0, v_x_542_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg___boxed(lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_List_replicate___redArg(v_x_550_, v_x_551_);
lean_dec(v_x_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_List_replicate(lean_object* v_00_u03b1_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_List_replicate___redArg(v_x_554_, v_x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___boxed(lean_object* v_00_u03b1_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_List_replicate(v_00_u03b1_557_, v_x_558_, v_x_559_);
lean_dec(v_x_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg(lean_object* v_n_561_, lean_object* v_a_562_, lean_object* v_l_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_564_ = l_List_length___redArg(v_l_563_);
v___x_565_ = lean_nat_sub(v_n_561_, v___x_564_);
lean_dec(v___x_564_);
v___x_566_ = l_List_replicate___redArg(v___x_565_, v_a_562_);
lean_dec(v___x_565_);
v___x_567_ = l_List_appendTR___redArg(v___x_566_, v_l_563_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg___boxed(lean_object* v_n_568_, lean_object* v_a_569_, lean_object* v_l_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_List_leftpad___redArg(v_n_568_, v_a_569_, v_l_570_);
lean_dec(v_n_568_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad(lean_object* v_00_u03b1_572_, lean_object* v_n_573_, lean_object* v_a_574_, lean_object* v_l_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_List_leftpad___redArg(v_n_573_, v_a_574_, v_l_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___boxed(lean_object* v_00_u03b1_577_, lean_object* v_n_578_, lean_object* v_a_579_, lean_object* v_l_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_List_leftpad(v_00_u03b1_577_, v_n_578_, v_a_579_, v_l_580_);
lean_dec(v_n_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg(lean_object* v_n_582_, lean_object* v_a_583_, lean_object* v_l_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_585_ = l_List_length___redArg(v_l_584_);
v___x_586_ = lean_nat_sub(v_n_582_, v___x_585_);
lean_dec(v___x_585_);
v___x_587_ = l_List_replicate___redArg(v___x_586_, v_a_583_);
lean_dec(v___x_586_);
v___x_588_ = l_List_appendTR___redArg(v_l_584_, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg___boxed(lean_object* v_n_589_, lean_object* v_a_590_, lean_object* v_l_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_List_rightpad___redArg(v_n_589_, v_a_590_, v_l_591_);
lean_dec(v_n_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad(lean_object* v_00_u03b1_593_, lean_object* v_n_594_, lean_object* v_a_595_, lean_object* v_l_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_List_rightpad___redArg(v_n_594_, v_a_595_, v_l_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___boxed(lean_object* v_00_u03b1_598_, lean_object* v_n_599_, lean_object* v_a_600_, lean_object* v_l_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_List_rightpad(v_00_u03b1_598_, v_n_599_, v_a_600_, v_l_601_);
lean_dec(v_n_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = lean_box(0);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg___boxed(lean_object* v___dummy_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_List_instEmptyCollection___redArg();
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object* v_00_u03b1_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_box(0);
return v___x_608_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty___redArg(lean_object* v_x_609_){
_start:
{
if (lean_obj_tag(v_x_609_) == 0)
{
uint8_t v___x_610_; 
v___x_610_ = 1;
return v___x_610_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = 0;
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___redArg___boxed(lean_object* v_x_612_){
_start:
{
uint8_t v_res_613_; lean_object* v_r_614_; 
v_res_613_ = l_List_isEmpty___redArg(v_x_612_);
lean_dec(v_x_612_);
v_r_614_ = lean_box(v_res_613_);
return v_r_614_;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty(lean_object* v_00_u03b1_615_, lean_object* v_x_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = l_List_isEmpty___redArg(v_x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___boxed(lean_object* v_00_u03b1_618_, lean_object* v_x_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_List_isEmpty(v_00_u03b1_618_, v_x_619_);
lean_dec(v_x_619_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT uint8_t l_List_elem___redArg(lean_object* v_inst_622_, lean_object* v_a_623_, lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
uint8_t v___x_625_; 
lean_dec(v_a_623_);
lean_dec_ref(v_inst_622_);
v___x_625_ = 0;
return v___x_625_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_head_626_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_head_626_);
v_tail_627_ = lean_ctor_get(v_x_624_, 1);
lean_inc(v_tail_627_);
lean_dec_ref_known(v_x_624_, 2);
lean_inc_ref(v_inst_622_);
lean_inc(v_a_623_);
v___x_628_ = lean_apply_2(v_inst_622_, v_a_623_, v_head_626_);
v___x_629_ = lean_unbox(v___x_628_);
if (v___x_629_ == 0)
{
v_x_624_ = v_tail_627_;
goto _start;
}
else
{
uint8_t v___x_631_; 
lean_dec(v_tail_627_);
lean_dec(v_a_623_);
lean_dec_ref(v_inst_622_);
v___x_631_ = lean_unbox(v___x_628_);
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___redArg___boxed(lean_object* v_inst_632_, lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_List_elem___redArg(v_inst_632_, v_a_633_, v_x_634_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT uint8_t l_List_elem(lean_object* v_00_u03b1_637_, lean_object* v_inst_638_, lean_object* v_a_639_, lean_object* v_x_640_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = l_List_elem___redArg(v_inst_638_, v_a_639_, v_x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_List_elem___boxed(lean_object* v_00_u03b1_642_, lean_object* v_inst_643_, lean_object* v_a_644_, lean_object* v_x_645_){
_start:
{
uint8_t v_res_646_; lean_object* v_r_647_; 
v_res_646_ = l_List_elem(v_00_u03b1_642_, v_inst_643_, v_a_644_, v_x_645_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT uint8_t l_List_contains___redArg(lean_object* v_inst_648_, lean_object* v_as_649_, lean_object* v_a_650_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = l_List_elem___redArg(v_inst_648_, v_a_650_, v_as_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_List_contains___redArg___boxed(lean_object* v_inst_652_, lean_object* v_as_653_, lean_object* v_a_654_){
_start:
{
uint8_t v_res_655_; lean_object* v_r_656_; 
v_res_655_ = l_List_contains___redArg(v_inst_652_, v_as_653_, v_a_654_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT uint8_t l_List_contains(lean_object* v_00_u03b1_657_, lean_object* v_inst_658_, lean_object* v_as_659_, lean_object* v_a_660_){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = l_List_elem___redArg(v_inst_658_, v_a_660_, v_as_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_List_contains___boxed(lean_object* v_00_u03b1_662_, lean_object* v_inst_663_, lean_object* v_as_664_, lean_object* v_a_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l_List_contains(v_00_u03b1_662_, v_inst_663_, v_as_664_, v_a_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership___redArg(){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = lean_box(0);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership___redArg___boxed(lean_object* v___dummy_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_List_instMembership___redArg();
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership(lean_object* v_00_u03b1_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = lean_box(0);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(uint8_t v_x_674_, lean_object* v_h__1_675_, lean_object* v_h__2_676_){
_start:
{
if (v_x_674_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v_h__1_675_);
v___x_677_ = lean_box(0);
v___x_678_ = lean_apply_1(v_h__2_676_, v___x_677_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v_h__2_676_);
v___x_679_ = lean_box(0);
v___x_680_ = lean_apply_1(v_h__1_675_, v___x_679_);
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_681_, lean_object* v_h__1_682_, lean_object* v_h__2_683_){
_start:
{
uint8_t v_x_24__boxed_684_; lean_object* v_res_685_; 
v_x_24__boxed_684_ = lean_unbox(v_x_681_);
v_res_685_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_684_, v_h__1_682_, v_h__2_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object* v_motive_686_, uint8_t v_x_687_, lean_object* v_h__1_688_, lean_object* v_h__2_689_){
_start:
{
if (v_x_687_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec(v_h__1_688_);
v___x_690_ = lean_box(0);
v___x_691_ = lean_apply_1(v_h__2_689_, v___x_690_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v_h__2_689_);
v___x_692_ = lean_box(0);
v___x_693_ = lean_apply_1(v_h__1_688_, v___x_692_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_694_, lean_object* v_x_695_, lean_object* v_h__1_696_, lean_object* v_h__2_697_){
_start:
{
uint8_t v_x_35__boxed_698_; lean_object* v_res_699_; 
v_x_35__boxed_698_ = lean_unbox(v_x_695_);
v_res_699_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(v_motive_694_, v_x_35__boxed_698_, v_h__1_696_, v_h__2_697_);
return v_res_699_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_700_, lean_object* v_a_701_, lean_object* v_as_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = l_List_elem___redArg(v_inst_700_, v_a_701_, v_as_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_704_, lean_object* v_a_705_, lean_object* v_as_706_){
_start:
{
uint8_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_List_instDecidableMemOfLawfulBEq___redArg(v_inst_704_, v_a_705_, v_as_706_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_a_712_, lean_object* v_as_713_){
_start:
{
uint8_t v___x_714_; 
v___x_714_ = l_List_elem___redArg(v_inst_710_, v_a_712_, v_as_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_a_718_, lean_object* v_as_719_){
_start:
{
uint8_t v_res_720_; lean_object* v_r_721_; 
v_res_720_ = l_List_instDecidableMemOfLawfulBEq(v_00_u03b1_715_, v_inst_716_, v_inst_717_, v_a_718_, v_as_719_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx___redArg(lean_object* v_inst_722_, lean_object* v_x_723_){
_start:
{
if (lean_obj_tag(v_x_723_) == 0)
{
uint8_t v___x_724_; 
lean_dec_ref(v_inst_722_);
v___x_724_ = 0;
return v___x_724_;
}
else
{
lean_object* v_head_725_; lean_object* v_tail_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_head_725_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_head_725_);
v_tail_726_ = lean_ctor_get(v_x_723_, 1);
lean_inc(v_tail_726_);
lean_dec_ref_known(v_x_723_, 2);
lean_inc_ref(v_inst_722_);
v___x_727_ = lean_apply_1(v_inst_722_, v_head_725_);
v___x_728_ = lean_unbox(v___x_727_);
if (v___x_728_ == 0)
{
uint8_t v_decide_729_; 
v_decide_729_ = l_List_decidableBEx___redArg(v_inst_722_, v_tail_726_);
if (v_decide_729_ == 0)
{
uint8_t v___x_730_; 
v___x_730_ = lean_unbox(v___x_727_);
return v___x_730_;
}
else
{
return v_decide_729_;
}
}
else
{
uint8_t v___x_731_; 
lean_dec(v_tail_726_);
lean_dec_ref(v_inst_722_);
v___x_731_ = lean_unbox(v___x_727_);
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___redArg___boxed(lean_object* v_inst_732_, lean_object* v_x_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_List_decidableBEx___redArg(v_inst_732_, v_x_733_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx(lean_object* v_00_u03b1_736_, lean_object* v_p_737_, lean_object* v_inst_738_, lean_object* v_x_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = l_List_decidableBEx___redArg(v_inst_738_, v_x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___boxed(lean_object* v_00_u03b1_741_, lean_object* v_p_742_, lean_object* v_inst_743_, lean_object* v_x_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_List_decidableBEx(v_00_u03b1_741_, v_p_742_, v_inst_743_, v_x_744_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll___redArg(lean_object* v_inst_747_, lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
uint8_t v___x_749_; 
lean_dec_ref(v_inst_747_);
v___x_749_ = 1;
return v___x_749_;
}
else
{
lean_object* v_head_750_; lean_object* v_tail_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_head_750_ = lean_ctor_get(v_x_748_, 0);
lean_inc(v_head_750_);
v_tail_751_ = lean_ctor_get(v_x_748_, 1);
lean_inc(v_tail_751_);
lean_dec_ref_known(v_x_748_, 2);
lean_inc_ref(v_inst_747_);
v___x_752_ = lean_apply_1(v_inst_747_, v_head_750_);
v___x_753_ = lean_unbox(v___x_752_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; 
lean_dec(v_tail_751_);
lean_dec_ref(v_inst_747_);
v___x_754_ = lean_unbox(v___x_752_);
return v___x_754_;
}
else
{
uint8_t v_decide_755_; 
v_decide_755_ = l_List_decidableBAll___redArg(v_inst_747_, v_tail_751_);
if (v_decide_755_ == 0)
{
return v_decide_755_;
}
else
{
uint8_t v___x_756_; 
v___x_756_ = lean_unbox(v___x_752_);
return v___x_756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___redArg___boxed(lean_object* v_inst_757_, lean_object* v_x_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_List_decidableBAll___redArg(v_inst_757_, v_x_758_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll(lean_object* v_00_u03b1_761_, lean_object* v_p_762_, lean_object* v_inst_763_, lean_object* v_x_764_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = l_List_decidableBAll___redArg(v_inst_763_, v_x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___boxed(lean_object* v_00_u03b1_766_, lean_object* v_p_767_, lean_object* v_inst_768_, lean_object* v_x_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_List_decidableBAll(v_00_u03b1_766_, v_p_767_, v_inst_768_, v_x_769_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT lean_object* l_List_take___redArg(lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
lean_object* v_zero_774_; uint8_t v_isZero_775_; 
v_zero_774_ = lean_unsigned_to_nat(0u);
v_isZero_775_ = lean_nat_dec_eq(v_x_772_, v_zero_774_);
if (v_isZero_775_ == 1)
{
lean_object* v___x_776_; 
lean_dec(v_x_773_);
v___x_776_ = lean_box(0);
return v___x_776_;
}
else
{
if (lean_obj_tag(v_x_773_) == 0)
{
return v_x_773_;
}
else
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_788_; 
v_head_777_ = lean_ctor_get(v_x_773_, 0);
v_tail_778_ = lean_ctor_get(v_x_773_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_x_773_);
if (v_isSharedCheck_788_ == 0)
{
v___x_780_ = v_x_773_;
v_isShared_781_ = v_isSharedCheck_788_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_tail_778_);
lean_inc(v_head_777_);
lean_dec(v_x_773_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_788_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_one_782_; lean_object* v_n_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v_one_782_ = lean_unsigned_to_nat(1u);
v_n_783_ = lean_nat_sub(v_x_772_, v_one_782_);
v___x_784_ = l_List_take___redArg(v_n_783_, v_tail_778_);
lean_dec(v_n_783_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 1, v___x_784_);
v___x_786_ = v___x_780_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_head_777_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_take___redArg___boxed(lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_List_take___redArg(v_x_789_, v_x_790_);
lean_dec(v_x_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_List_take(lean_object* v_00_u03b1_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_List_take___redArg(v_x_793_, v_x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_List_take___boxed(lean_object* v_00_u03b1_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_List_take(v_00_u03b1_796_, v_x_797_, v_x_798_);
lean_dec(v_x_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg(lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_zero_802_; uint8_t v_isZero_803_; 
v_zero_802_ = lean_unsigned_to_nat(0u);
v_isZero_803_ = lean_nat_dec_eq(v_x_800_, v_zero_802_);
if (v_isZero_803_ == 1)
{
lean_dec(v_x_800_);
lean_inc(v_x_801_);
return v_x_801_;
}
else
{
if (lean_obj_tag(v_x_801_) == 0)
{
lean_dec(v_x_800_);
return v_x_801_;
}
else
{
lean_object* v_tail_804_; lean_object* v_one_805_; lean_object* v_n_806_; 
v_tail_804_ = lean_ctor_get(v_x_801_, 1);
v_one_805_ = lean_unsigned_to_nat(1u);
v_n_806_ = lean_nat_sub(v_x_800_, v_one_805_);
lean_dec(v_x_800_);
v_x_800_ = v_n_806_;
v_x_801_ = v_tail_804_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg___boxed(lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_List_drop___redArg(v_x_808_, v_x_809_);
lean_dec(v_x_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_List_drop(lean_object* v_00_u03b1_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_List_drop___redArg(v_x_812_, v_x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_List_drop___boxed(lean_object* v_00_u03b1_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_List_drop(v_00_u03b1_815_, v_x_816_, v_x_817_);
lean_dec(v_x_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg(lean_object* v_l_819_, lean_object* v_start_820_, lean_object* v_stop_821_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = lean_nat_sub(v_stop_821_, v_start_820_);
v___x_823_ = l_List_drop___redArg(v_start_820_, v_l_819_);
v___x_824_ = l_List_take___redArg(v___x_822_, v___x_823_);
lean_dec(v___x_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg___boxed(lean_object* v_l_825_, lean_object* v_start_826_, lean_object* v_stop_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_List_extract___redArg(v_l_825_, v_start_826_, v_stop_827_);
lean_dec(v_stop_827_);
lean_dec(v_l_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_List_extract(lean_object* v_00_u03b1_829_, lean_object* v_l_830_, lean_object* v_start_831_, lean_object* v_stop_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_nat_sub(v_stop_832_, v_start_831_);
v___x_834_ = l_List_drop___redArg(v_start_831_, v_l_830_);
v___x_835_ = l_List_take___redArg(v___x_833_, v___x_834_);
lean_dec(v___x_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_List_extract___boxed(lean_object* v_00_u03b1_836_, lean_object* v_l_837_, lean_object* v_start_838_, lean_object* v_stop_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_List_extract(v_00_u03b1_836_, v_l_837_, v_start_838_, v_stop_839_);
lean_dec(v_stop_839_);
lean_dec(v_l_837_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhile___redArg(lean_object* v_p_841_, lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_dec_ref(v_p_841_);
return v_x_842_;
}
else
{
lean_object* v_head_843_; lean_object* v_tail_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_855_; 
v_head_843_ = lean_ctor_get(v_x_842_, 0);
v_tail_844_ = lean_ctor_get(v_x_842_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_855_ == 0)
{
v___x_846_ = v_x_842_;
v_isShared_847_ = v_isSharedCheck_855_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_tail_844_);
lean_inc(v_head_843_);
lean_dec(v_x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_855_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
lean_inc_ref(v_p_841_);
lean_inc(v_head_843_);
v___x_848_ = lean_apply_1(v_p_841_, v_head_843_);
v___x_849_ = lean_unbox(v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_del_object(v___x_846_);
lean_dec(v_tail_844_);
lean_dec(v_head_843_);
lean_dec_ref(v_p_841_);
v___x_850_ = lean_box(0);
return v___x_850_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = l_List_takeWhile___redArg(v_p_841_, v_tail_844_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_851_);
v___x_853_ = v___x_846_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_head_843_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_takeWhile(lean_object* v_00_u03b1_856_, lean_object* v_p_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_List_takeWhile___redArg(v_p_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___redArg(lean_object* v_p_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_dec_ref(v_p_860_);
return v_x_861_;
}
else
{
lean_object* v_head_862_; lean_object* v_tail_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v_head_862_ = lean_ctor_get(v_x_861_, 0);
v_tail_863_ = lean_ctor_get(v_x_861_, 1);
lean_inc_ref(v_p_860_);
lean_inc(v_head_862_);
v___x_864_ = lean_apply_1(v_p_860_, v_head_862_);
v___x_865_ = lean_unbox(v___x_864_);
if (v___x_865_ == 0)
{
lean_dec_ref(v_p_860_);
return v_x_861_;
}
else
{
lean_inc(v_tail_863_);
lean_dec_ref_known(v_x_861_, 2);
v_x_861_ = v_tail_863_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object* v_00_u03b1_867_, lean_object* v_p_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_List_dropWhile___redArg(v_p_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___redArg(lean_object* v_p_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
if (lean_obj_tag(v_a_872_) == 0)
{
lean_object* v_fst_874_; lean_object* v_snd_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v_p_871_);
v_fst_874_ = lean_ctor_get(v_a_873_, 0);
v_snd_875_ = lean_ctor_get(v_a_873_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_a_873_);
if (v_isSharedCheck_884_ == 0)
{
v___x_877_ = v_a_873_;
v_isShared_878_ = v_isSharedCheck_884_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_snd_875_);
lean_inc(v_fst_874_);
lean_dec(v_a_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_884_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_879_ = l_List_reverse___redArg(v_fst_874_);
v___x_880_ = l_List_reverse___redArg(v_snd_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v___x_880_);
lean_ctor_set(v___x_877_, 0, v___x_879_);
v___x_882_ = v___x_877_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
lean_object* v_head_885_; lean_object* v_tail_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_912_; 
v_head_885_ = lean_ctor_get(v_a_872_, 0);
v_tail_886_ = lean_ctor_get(v_a_872_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_a_872_);
if (v_isSharedCheck_912_ == 0)
{
v___x_888_ = v_a_872_;
v_isShared_889_ = v_isSharedCheck_912_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_tail_886_);
lean_inc(v_head_885_);
lean_dec(v_a_872_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_912_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v_fst_890_; lean_object* v_snd_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_911_; 
v_fst_890_ = lean_ctor_get(v_a_873_, 0);
v_snd_891_ = lean_ctor_get(v_a_873_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_a_873_);
if (v_isSharedCheck_911_ == 0)
{
v___x_893_ = v_a_873_;
v_isShared_894_ = v_isSharedCheck_911_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_snd_891_);
lean_inc(v_fst_890_);
lean_dec(v_a_873_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_911_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; uint8_t v___x_896_; 
lean_inc_ref(v_p_871_);
lean_inc(v_head_885_);
v___x_895_ = lean_apply_1(v_p_871_, v_head_885_);
v___x_896_ = lean_unbox(v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_898_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v_snd_891_);
v___x_898_ = v___x_888_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_head_885_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_snd_891_);
v___x_898_ = v_reuseFailAlloc_903_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v___x_898_);
v___x_900_ = v___x_893_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_fst_890_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_898_);
v___x_900_ = v_reuseFailAlloc_902_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
v_a_872_ = v_tail_886_;
v_a_873_ = v___x_900_;
goto _start;
}
}
}
else
{
lean_object* v___x_905_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v_fst_890_);
v___x_905_ = v___x_888_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_head_885_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_fst_890_);
v___x_905_ = v_reuseFailAlloc_910_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_907_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_905_);
v___x_907_ = v___x_893_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_snd_891_);
v___x_907_ = v_reuseFailAlloc_909_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
v_a_872_ = v_tail_886_;
v_a_873_ = v___x_907_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object* v_00_u03b1_913_, lean_object* v_p_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_List_partition_loop___redArg(v_p_914_, v_a_915_, v_a_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_List_partition___redArg(lean_object* v_p_920_, lean_object* v_as_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_923_ = l_List_partition_loop___redArg(v_p_920_, v_as_921_, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_List_partition(lean_object* v_00_u03b1_924_, lean_object* v_p_925_, lean_object* v_as_926_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_928_ = l_List_partition_loop___redArg(v_p_925_, v_as_926_, v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_List_dropLast___redArg(lean_object* v_x_929_){
_start:
{
if (lean_obj_tag(v_x_929_) == 0)
{
return v_x_929_;
}
else
{
lean_object* v_tail_930_; 
v_tail_930_ = lean_ctor_get(v_x_929_, 1);
lean_inc(v_tail_930_);
if (lean_obj_tag(v_tail_930_) == 0)
{
lean_dec_ref_known(v_x_929_, 2);
return v_tail_930_;
}
else
{
lean_object* v_head_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
v_head_931_ = lean_ctor_get(v_x_929_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v_x_929_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v_x_929_, 1);
lean_dec(v_unused_940_);
v___x_933_ = v_x_929_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_head_931_);
lean_dec(v_x_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = l_List_dropLast___redArg(v_tail_930_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_head_931_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropLast(lean_object* v_00_u03b1_941_, lean_object* v_x_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_List_dropLast___redArg(v_x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_944_, lean_object* v_h__1_945_, lean_object* v_h__2_946_, lean_object* v_h__3_947_){
_start:
{
if (lean_obj_tag(v_x_944_) == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_h__3_947_);
lean_dec(v_h__2_946_);
v___x_948_ = lean_box(0);
v___x_949_ = lean_apply_1(v_h__1_945_, v___x_948_);
return v___x_949_;
}
else
{
lean_object* v_tail_950_; 
lean_dec(v_h__1_945_);
v_tail_950_ = lean_ctor_get(v_x_944_, 1);
if (lean_obj_tag(v_tail_950_) == 0)
{
lean_object* v_head_951_; lean_object* v___x_952_; 
lean_dec(v_h__3_947_);
v_head_951_ = lean_ctor_get(v_x_944_, 0);
lean_inc(v_head_951_);
lean_dec_ref_known(v_x_944_, 2);
v___x_952_ = lean_apply_1(v_h__2_946_, v_head_951_);
return v___x_952_;
}
else
{
lean_object* v_head_953_; lean_object* v___x_954_; 
lean_inc_ref(v_tail_950_);
lean_dec(v_h__2_946_);
v_head_953_ = lean_ctor_get(v_x_944_, 0);
lean_inc(v_head_953_);
lean_dec_ref_known(v_x_944_, 2);
v___x_954_ = lean_apply_3(v_h__3_947_, v_head_953_, v_tail_950_, lean_box(0));
return v___x_954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_955_, lean_object* v_motive_956_, lean_object* v_x_957_, lean_object* v_h__1_958_, lean_object* v_h__2_959_, lean_object* v_h__3_960_){
_start:
{
if (lean_obj_tag(v_x_957_) == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec(v_h__3_960_);
lean_dec(v_h__2_959_);
v___x_961_ = lean_box(0);
v___x_962_ = lean_apply_1(v_h__1_958_, v___x_961_);
return v___x_962_;
}
else
{
lean_object* v_tail_963_; 
lean_dec(v_h__1_958_);
v_tail_963_ = lean_ctor_get(v_x_957_, 1);
if (lean_obj_tag(v_tail_963_) == 0)
{
lean_object* v_head_964_; lean_object* v___x_965_; 
lean_dec(v_h__3_960_);
v_head_964_ = lean_ctor_get(v_x_957_, 0);
lean_inc(v_head_964_);
lean_dec_ref_known(v_x_957_, 2);
v___x_965_ = lean_apply_1(v_h__2_959_, v_head_964_);
return v___x_965_;
}
else
{
lean_object* v_head_966_; lean_object* v___x_967_; 
lean_inc_ref(v_tail_963_);
lean_dec(v_h__2_959_);
v_head_966_ = lean_ctor_get(v_x_957_, 0);
lean_inc(v_head_966_);
lean_dec_ref_known(v_x_957_, 2);
v___x_967_ = lean_apply_3(v_h__3_960_, v_head_966_, v_tail_963_, lean_box(0));
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg(){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = lean_box(0);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg___boxed(lean_object* v___dummy_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_List_instHasSubset___redArg();
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object* v_00_u03b1_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_box(0);
return v___x_973_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(lean_object* v___f_974_, lean_object* v_x_975_, lean_object* v_a_976_){
_start:
{
uint8_t v___x_977_; 
v___x_977_ = l_List_elem___redArg(v___f_974_, v_a_976_, v_x_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(lean_object* v___f_978_, lean_object* v_x_979_, lean_object* v_a_980_){
_start:
{
uint8_t v_res_981_; lean_object* v_r_982_; 
v_res_981_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(v___f_978_, v_x_979_, v_a_980_);
v_r_982_ = lean_box(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg(lean_object* v_inst_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
lean_object* v___f_986_; lean_object* v___f_987_; uint8_t v___x_988_; 
v___f_986_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_986_, 0, v_inst_983_);
v___f_987_ = lean_alloc_closure((void*)(l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_987_, 0, v___f_986_);
lean_closure_set(v___f_987_, 1, v_x_985_);
v___x_988_ = l_List_decidableBAll___redArg(v___f_987_, v_x_984_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(lean_object* v_inst_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
uint8_t v_res_992_; lean_object* v_r_993_; 
v_res_992_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_989_, v_x_990_, v_x_991_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq(lean_object* v_00_u03b1_994_, lean_object* v_inst_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_995_, v_x_996_, v_x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___boxed(lean_object* v_00_u03b1_999_, lean_object* v_inst_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_res_1003_ = l_List_instDecidableRelSubsetOfDecidableEq(v_00_u03b1_999_, v_inst_1000_, v_x_1001_, v_x_1002_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2));
v___x_1039_ = l_String_toRawSubstring_x27(v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object* v_x_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
lean_inc(v_x_1059_);
v___x_1063_ = l_Lean_Syntax_isOfKind(v_x_1059_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec(v_x_1059_);
v___x_1064_ = lean_box(1);
v___x_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_a_1061_);
return v___x_1065_;
}
else
{
lean_object* v_quotContext_1066_; lean_object* v_currMacroScope_1067_; lean_object* v_ref_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_quotContext_1066_ = lean_ctor_get(v_a_1060_, 1);
v_currMacroScope_1067_ = lean_ctor_get(v_a_1060_, 2);
v_ref_1068_ = lean_ctor_get(v_a_1060_, 5);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = l_Lean_Syntax_getArg(v_x_1059_, v___x_1069_);
v___x_1071_ = lean_unsigned_to_nat(2u);
v___x_1072_ = l_Lean_Syntax_getArg(v_x_1059_, v___x_1071_);
lean_dec(v_x_1059_);
v___x_1073_ = 0;
v___x_1074_ = l_Lean_SourceInfo_fromRef(v_ref_1068_, v___x_1073_);
v___x_1075_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1076_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
v___x_1077_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4));
lean_inc(v_currMacroScope_1067_);
lean_inc(v_quotContext_1066_);
v___x_1078_ = l_Lean_addMacroScope(v_quotContext_1066_, v___x_1077_, v_currMacroScope_1067_);
v___x_1079_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10));
lean_inc_n(v___x_1074_, 2);
v___x_1080_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1074_);
lean_ctor_set(v___x_1080_, 1, v___x_1076_);
lean_ctor_set(v___x_1080_, 2, v___x_1078_);
lean_ctor_set(v___x_1080_, 3, v___x_1079_);
v___x_1081_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1082_ = l_Lean_Syntax_node2(v___x_1074_, v___x_1081_, v___x_1070_, v___x_1072_);
v___x_1083_ = l_Lean_Syntax_node2(v___x_1074_, v___x_1075_, v___x_1080_, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1061_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___boxed(lean_object* v_x_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(v_x_1085_, v_a_1086_, v_a_1087_);
lean_dec_ref(v_a_1086_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object* v_x_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1092_);
v___x_1096_ = l_Lean_Syntax_isOfKind(v_x_1092_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v_x_1092_);
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_a_1094_);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = l_Lean_Syntax_getArg(v_x_1092_, v___x_1099_);
v___x_1101_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1100_);
v___x_1102_ = l_Lean_Syntax_isOfKind(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec(v___x_1100_);
lean_dec(v_x_1092_);
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v_a_1094_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = l_Lean_Syntax_getArg(v_x_1092_, v___x_1105_);
lean_dec(v_x_1092_);
v___x_1107_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1106_);
v___x_1108_ = l_Lean_Syntax_matchesNull(v___x_1106_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_dec(v___x_1106_);
lean_dec(v___x_1100_);
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v_a_1094_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_ref_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1111_ = l_Lean_Syntax_getArg(v___x_1106_, v___x_1099_);
v___x_1112_ = l_Lean_Syntax_getArg(v___x_1106_, v___x_1105_);
lean_dec(v___x_1106_);
v_ref_1113_ = l_Lean_replaceRef(v___x_1100_, v_a_1093_);
lean_dec(v___x_1100_);
v___x_1114_ = 0;
v___x_1115_ = l_Lean_SourceInfo_fromRef(v_ref_1113_, v___x_1114_);
lean_dec(v_ref_1113_);
v___x_1116_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
v___x_1117_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__5));
lean_inc(v___x_1115_);
v___x_1118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1115_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node3(v___x_1115_, v___x_1116_, v___x_1111_, v___x_1118_, v___x_1112_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_a_1094_);
return v___x_1120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object* v_x_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(v_x_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_a_1122_);
return v_res_1124_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist___redArg(lean_object* v_inst_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1126_) == 0)
{
uint8_t v___x_1128_; 
lean_dec(v_x_1127_);
lean_dec_ref(v_inst_1125_);
v___x_1128_ = 1;
return v___x_1128_;
}
else
{
if (lean_obj_tag(v_x_1127_) == 0)
{
uint8_t v___x_1129_; 
lean_dec_ref_known(v_x_1126_, 2);
lean_dec_ref(v_inst_1125_);
v___x_1129_ = 0;
return v___x_1129_;
}
else
{
lean_object* v_head_1130_; lean_object* v_tail_1131_; lean_object* v_head_1132_; lean_object* v_tail_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_head_1130_ = lean_ctor_get(v_x_1126_, 0);
v_tail_1131_ = lean_ctor_get(v_x_1126_, 1);
v_head_1132_ = lean_ctor_get(v_x_1127_, 0);
lean_inc(v_head_1132_);
v_tail_1133_ = lean_ctor_get(v_x_1127_, 1);
lean_inc(v_tail_1133_);
lean_dec_ref_known(v_x_1127_, 2);
lean_inc_ref(v_inst_1125_);
lean_inc(v_head_1130_);
v___x_1134_ = lean_apply_2(v_inst_1125_, v_head_1130_, v_head_1132_);
v___x_1135_ = lean_unbox(v___x_1134_);
if (v___x_1135_ == 0)
{
v_x_1127_ = v_tail_1133_;
goto _start;
}
else
{
lean_inc(v_tail_1131_);
lean_dec_ref_known(v_x_1126_, 2);
v_x_1126_ = v_tail_1131_;
v_x_1127_ = v_tail_1133_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSublist___redArg___boxed(lean_object* v_inst_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
uint8_t v_res_1141_; lean_object* v_r_1142_; 
v_res_1141_ = l_List_isSublist___redArg(v_inst_1138_, v_x_1139_, v_x_1140_);
v_r_1142_ = lean_box(v_res_1141_);
return v_r_1142_;
}
}
LEAN_EXPORT uint8_t l_List_isSublist(lean_object* v_00_u03b1_1143_, lean_object* v_inst_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_){
_start:
{
uint8_t v___x_1147_; 
v___x_1147_ = l_List_isSublist___redArg(v_inst_1144_, v_x_1145_, v_x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_List_isSublist___boxed(lean_object* v_00_u03b1_1148_, lean_object* v_inst_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l_List_isSublist(v_00_u03b1_1148_, v_inst_1149_, v_x_1150_, v_x_1151_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0));
v___x_1172_ = l_String_toRawSubstring_x27(v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object* v_x_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
lean_inc(v_x_1184_);
v___x_1188_ = l_Lean_Syntax_isOfKind(v_x_1184_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v_x_1184_);
v___x_1189_ = lean_box(1);
v___x_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v_a_1186_);
return v___x_1190_;
}
else
{
lean_object* v_quotContext_1191_; lean_object* v_currMacroScope_1192_; lean_object* v_ref_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_quotContext_1191_ = lean_ctor_get(v_a_1185_, 1);
v_currMacroScope_1192_ = lean_ctor_get(v_a_1185_, 2);
v_ref_1193_ = lean_ctor_get(v_a_1185_, 5);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = l_Lean_Syntax_getArg(v_x_1184_, v___x_1194_);
v___x_1196_ = lean_unsigned_to_nat(2u);
v___x_1197_ = l_Lean_Syntax_getArg(v_x_1184_, v___x_1196_);
lean_dec(v_x_1184_);
v___x_1198_ = 0;
v___x_1199_ = l_Lean_SourceInfo_fromRef(v_ref_1193_, v___x_1198_);
v___x_1200_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1201_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
v___x_1202_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1192_);
lean_inc(v_quotContext_1191_);
v___x_1203_ = l_Lean_addMacroScope(v_quotContext_1191_, v___x_1202_, v_currMacroScope_1192_);
v___x_1204_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1199_, 2);
v___x_1205_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1199_);
lean_ctor_set(v___x_1205_, 1, v___x_1201_);
lean_ctor_set(v___x_1205_, 2, v___x_1203_);
lean_ctor_set(v___x_1205_, 3, v___x_1204_);
v___x_1206_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1207_ = l_Lean_Syntax_node2(v___x_1199_, v___x_1206_, v___x_1195_, v___x_1197_);
v___x_1208_ = l_Lean_Syntax_node2(v___x_1199_, v___x_1200_, v___x_1205_, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v_a_1186_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___boxed(lean_object* v_x_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(v_x_1210_, v_a_1211_, v_a_1212_);
lean_dec_ref(v_a_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object* v_x_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
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
v___x_1238_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
v___x_1239_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__2));
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
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object* v_x_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(v_x_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf___redArg(lean_object* v_inst_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
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
lean_inc(v_head_1252_);
v_tail_1253_ = lean_ctor_get(v_x_1248_, 1);
lean_inc(v_tail_1253_);
lean_dec_ref_known(v_x_1248_, 2);
v_head_1254_ = lean_ctor_get(v_x_1249_, 0);
lean_inc(v_head_1254_);
v_tail_1255_ = lean_ctor_get(v_x_1249_, 1);
lean_inc(v_tail_1255_);
lean_dec_ref_known(v_x_1249_, 2);
lean_inc_ref(v_inst_1247_);
v___x_1256_ = lean_apply_2(v_inst_1247_, v_head_1252_, v_head_1254_);
v___x_1257_ = lean_unbox(v___x_1256_);
if (v___x_1257_ == 0)
{
uint8_t v___x_1258_; 
lean_dec(v_tail_1255_);
lean_dec(v_tail_1253_);
lean_dec_ref(v_inst_1247_);
v___x_1258_ = lean_unbox(v___x_1256_);
return v___x_1258_;
}
else
{
v_x_1248_ = v_tail_1253_;
v_x_1249_ = v_tail_1255_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___redArg___boxed(lean_object* v_inst_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
uint8_t v_res_1263_; lean_object* v_r_1264_; 
v_res_1263_ = l_List_isPrefixOf___redArg(v_inst_1260_, v_x_1261_, v_x_1262_);
v_r_1264_ = lean_box(v_res_1263_);
return v_r_1264_;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf(lean_object* v_00_u03b1_1265_, lean_object* v_inst_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
uint8_t v___x_1269_; 
v___x_1269_ = l_List_isPrefixOf___redArg(v_inst_1266_, v_x_1267_, v_x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___boxed(lean_object* v_00_u03b1_1270_, lean_object* v_inst_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l_List_isPrefixOf(v_00_u03b1_1270_, v_inst_1271_, v_x_1272_, v_x_1273_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_h__1_1278_, lean_object* v_h__2_1279_, lean_object* v_h__3_1280_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
lean_object* v___x_1281_; 
lean_dec(v_h__3_1280_);
lean_dec(v_h__2_1279_);
v___x_1281_ = lean_apply_1(v_h__1_1278_, v_x_1277_);
return v___x_1281_;
}
else
{
lean_dec(v_h__1_1278_);
if (lean_obj_tag(v_x_1277_) == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_h__3_1280_);
v___x_1282_ = lean_apply_2(v_h__2_1279_, v_x_1276_, lean_box(0));
return v___x_1282_;
}
else
{
lean_object* v_head_1283_; lean_object* v_tail_1284_; lean_object* v_head_1285_; lean_object* v_tail_1286_; lean_object* v___x_1287_; 
lean_dec(v_h__2_1279_);
v_head_1283_ = lean_ctor_get(v_x_1276_, 0);
lean_inc(v_head_1283_);
v_tail_1284_ = lean_ctor_get(v_x_1276_, 1);
lean_inc(v_tail_1284_);
lean_dec_ref_known(v_x_1276_, 2);
v_head_1285_ = lean_ctor_get(v_x_1277_, 0);
lean_inc(v_head_1285_);
v_tail_1286_ = lean_ctor_get(v_x_1277_, 1);
lean_inc(v_tail_1286_);
lean_dec_ref_known(v_x_1277_, 2);
v___x_1287_ = lean_apply_4(v_h__3_1280_, v_head_1283_, v_tail_1284_, v_head_1285_, v_tail_1286_);
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object* v_00_u03b1_1288_, lean_object* v_motive_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_h__1_1292_, lean_object* v_h__2_1293_, lean_object* v_h__3_1294_){
_start:
{
if (lean_obj_tag(v_x_1290_) == 0)
{
lean_object* v___x_1295_; 
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
v___x_1295_ = lean_apply_1(v_h__1_1292_, v_x_1291_);
return v___x_1295_;
}
else
{
lean_dec(v_h__1_1292_);
if (lean_obj_tag(v_x_1291_) == 0)
{
lean_object* v___x_1296_; 
lean_dec(v_h__3_1294_);
v___x_1296_ = lean_apply_2(v_h__2_1293_, v_x_1290_, lean_box(0));
return v___x_1296_;
}
else
{
lean_object* v_head_1297_; lean_object* v_tail_1298_; lean_object* v_head_1299_; lean_object* v_tail_1300_; lean_object* v___x_1301_; 
lean_dec(v_h__2_1293_);
v_head_1297_ = lean_ctor_get(v_x_1290_, 0);
lean_inc(v_head_1297_);
v_tail_1298_ = lean_ctor_get(v_x_1290_, 1);
lean_inc(v_tail_1298_);
lean_dec_ref_known(v_x_1290_, 2);
v_head_1299_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_head_1299_);
v_tail_1300_ = lean_ctor_get(v_x_1291_, 1);
lean_inc(v_tail_1300_);
lean_dec_ref_known(v_x_1291_, 2);
v___x_1301_ = lean_apply_4(v_h__3_1294_, v_head_1297_, v_tail_1298_, v_head_1299_, v_tail_1300_);
return v___x_1301_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___redArg(lean_object* v_inst_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
if (lean_obj_tag(v_x_1303_) == 0)
{
lean_object* v___x_1305_; 
lean_dec_ref(v_inst_1302_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_x_1304_);
return v___x_1305_;
}
else
{
if (lean_obj_tag(v_x_1304_) == 0)
{
lean_object* v___x_1306_; 
lean_dec_ref_known(v_x_1303_, 2);
lean_dec_ref(v_inst_1302_);
v___x_1306_ = lean_box(0);
return v___x_1306_;
}
else
{
lean_object* v_head_1307_; lean_object* v_tail_1308_; lean_object* v_head_1309_; lean_object* v_tail_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_head_1307_ = lean_ctor_get(v_x_1303_, 0);
lean_inc(v_head_1307_);
v_tail_1308_ = lean_ctor_get(v_x_1303_, 1);
lean_inc(v_tail_1308_);
lean_dec_ref_known(v_x_1303_, 2);
v_head_1309_ = lean_ctor_get(v_x_1304_, 0);
lean_inc(v_head_1309_);
v_tail_1310_ = lean_ctor_get(v_x_1304_, 1);
lean_inc(v_tail_1310_);
lean_dec_ref_known(v_x_1304_, 2);
lean_inc_ref(v_inst_1302_);
v___x_1311_ = lean_apply_2(v_inst_1302_, v_head_1307_, v_head_1309_);
v___x_1312_ = lean_unbox(v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec(v_tail_1310_);
lean_dec(v_tail_1308_);
lean_dec_ref(v_inst_1302_);
v___x_1313_ = lean_box(0);
return v___x_1313_;
}
else
{
v_x_1303_ = v_tail_1308_;
v_x_1304_ = v_tail_1310_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object* v_00_u03b1_1315_, lean_object* v_inst_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_List_isPrefixOf_x3f___redArg(v_inst_1316_, v_x_1317_, v_x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf___redArg(lean_object* v_inst_1320_, lean_object* v_l_u2081_1321_, lean_object* v_l_u2082_1322_){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1323_ = l_List_reverse___redArg(v_l_u2081_1321_);
v___x_1324_ = l_List_reverse___redArg(v_l_u2082_1322_);
v___x_1325_ = l_List_isPrefixOf___redArg(v_inst_1320_, v___x_1323_, v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___redArg___boxed(lean_object* v_inst_1326_, lean_object* v_l_u2081_1327_, lean_object* v_l_u2082_1328_){
_start:
{
uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_res_1329_ = l_List_isSuffixOf___redArg(v_inst_1326_, v_l_u2081_1327_, v_l_u2082_1328_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf(lean_object* v_00_u03b1_1331_, lean_object* v_inst_1332_, lean_object* v_l_u2081_1333_, lean_object* v_l_u2082_1334_){
_start:
{
uint8_t v___x_1335_; 
v___x_1335_ = l_List_isSuffixOf___redArg(v_inst_1332_, v_l_u2081_1333_, v_l_u2082_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___boxed(lean_object* v_00_u03b1_1336_, lean_object* v_inst_1337_, lean_object* v_l_u2081_1338_, lean_object* v_l_u2082_1339_){
_start:
{
uint8_t v_res_1340_; lean_object* v_r_1341_; 
v_res_1340_ = l_List_isSuffixOf(v_00_u03b1_1336_, v_inst_1337_, v_l_u2081_1338_, v_l_u2082_1339_);
v_r_1341_ = lean_box(v_res_1340_);
return v_r_1341_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___redArg(lean_object* v_inst_1342_, lean_object* v_l_u2081_1343_, lean_object* v_l_u2082_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = l_List_reverse___redArg(v_l_u2081_1343_);
v___x_1346_ = l_List_reverse___redArg(v_l_u2082_1344_);
v___x_1347_ = l_List_isPrefixOf_x3f___redArg(v_inst_1342_, v___x_1345_, v___x_1346_);
if (lean_obj_tag(v___x_1347_) == 0)
{
return v___x_1347_;
}
else
{
lean_object* v_val_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1356_; 
v_val_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1356_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_val_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1356_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = l_List_reverse___redArg(v_val_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1352_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object* v_00_u03b1_1357_, lean_object* v_inst_1358_, lean_object* v_l_u2081_1359_, lean_object* v_l_u2082_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_List_isSuffixOf_x3f___redArg(v_inst_1358_, v_l_u2081_1359_, v_l_u2082_1360_);
return v___x_1361_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0));
v___x_1380_ = l_String_toRawSubstring_x27(v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object* v_x_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
lean_inc(v_x_1392_);
v___x_1396_ = l_Lean_Syntax_isOfKind(v_x_1392_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec(v_x_1392_);
v___x_1397_ = lean_box(1);
v___x_1398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v_a_1394_);
return v___x_1398_;
}
else
{
lean_object* v_quotContext_1399_; lean_object* v_currMacroScope_1400_; lean_object* v_ref_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_quotContext_1399_ = lean_ctor_get(v_a_1393_, 1);
v_currMacroScope_1400_ = lean_ctor_get(v_a_1393_, 2);
v_ref_1401_ = lean_ctor_get(v_a_1393_, 5);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = l_Lean_Syntax_getArg(v_x_1392_, v___x_1402_);
v___x_1404_ = lean_unsigned_to_nat(2u);
v___x_1405_ = l_Lean_Syntax_getArg(v_x_1392_, v___x_1404_);
lean_dec(v_x_1392_);
v___x_1406_ = 0;
v___x_1407_ = l_Lean_SourceInfo_fromRef(v_ref_1401_, v___x_1406_);
v___x_1408_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1409_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
v___x_1410_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2));
lean_inc(v_currMacroScope_1400_);
lean_inc(v_quotContext_1399_);
v___x_1411_ = l_Lean_addMacroScope(v_quotContext_1399_, v___x_1410_, v_currMacroScope_1400_);
v___x_1412_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5));
lean_inc_n(v___x_1407_, 2);
v___x_1413_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1407_);
lean_ctor_set(v___x_1413_, 1, v___x_1409_);
lean_ctor_set(v___x_1413_, 2, v___x_1411_);
lean_ctor_set(v___x_1413_, 3, v___x_1412_);
v___x_1414_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1415_ = l_Lean_Syntax_node2(v___x_1407_, v___x_1414_, v___x_1403_, v___x_1405_);
v___x_1416_ = l_Lean_Syntax_node2(v___x_1407_, v___x_1408_, v___x_1413_, v___x_1415_);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v_a_1394_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___boxed(lean_object* v_x_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(v_x_1418_, v_a_1419_, v_a_1420_);
lean_dec_ref(v_a_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object* v_x_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1422_);
v___x_1426_ = l_Lean_Syntax_isOfKind(v_x_1422_, v___x_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec(v_x_1422_);
v___x_1427_ = lean_box(0);
v___x_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
lean_ctor_set(v___x_1428_, 1, v_a_1424_);
return v___x_1428_;
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = l_Lean_Syntax_getArg(v_x_1422_, v___x_1429_);
v___x_1431_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1430_);
v___x_1432_ = l_Lean_Syntax_isOfKind(v___x_1430_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v___x_1430_);
lean_dec(v_x_1422_);
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v_a_1424_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1435_ = lean_unsigned_to_nat(1u);
v___x_1436_ = l_Lean_Syntax_getArg(v_x_1422_, v___x_1435_);
lean_dec(v_x_1422_);
v___x_1437_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1436_);
v___x_1438_ = l_Lean_Syntax_matchesNull(v___x_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec(v___x_1436_);
lean_dec(v___x_1430_);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v_a_1424_);
return v___x_1440_;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v_ref_1443_; uint8_t v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1441_ = l_Lean_Syntax_getArg(v___x_1436_, v___x_1429_);
v___x_1442_ = l_Lean_Syntax_getArg(v___x_1436_, v___x_1435_);
lean_dec(v___x_1436_);
v_ref_1443_ = l_Lean_replaceRef(v___x_1430_, v_a_1423_);
lean_dec(v___x_1430_);
v___x_1444_ = 0;
v___x_1445_ = l_Lean_SourceInfo_fromRef(v_ref_1443_, v___x_1444_);
lean_dec(v_ref_1443_);
v___x_1446_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
v___x_1447_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__2));
lean_inc(v___x_1445_);
v___x_1448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1445_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = l_Lean_Syntax_node3(v___x_1445_, v___x_1446_, v___x_1441_, v___x_1448_, v___x_1442_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v_a_1424_);
return v___x_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object* v_x_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(v_x_1451_, v_a_1452_, v_a_1453_);
lean_dec(v_a_1452_);
return v_res_1454_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0));
v___x_1473_ = l_String_toRawSubstring_x27(v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object* v_x_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
lean_inc(v_x_1485_);
v___x_1489_ = l_Lean_Syntax_isOfKind(v_x_1485_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec(v_x_1485_);
v___x_1490_ = lean_box(1);
v___x_1491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v_a_1487_);
return v___x_1491_;
}
else
{
lean_object* v_quotContext_1492_; lean_object* v_currMacroScope_1493_; lean_object* v_ref_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_quotContext_1492_ = lean_ctor_get(v_a_1486_, 1);
v_currMacroScope_1493_ = lean_ctor_get(v_a_1486_, 2);
v_ref_1494_ = lean_ctor_get(v_a_1486_, 5);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = l_Lean_Syntax_getArg(v_x_1485_, v___x_1495_);
v___x_1497_ = lean_unsigned_to_nat(2u);
v___x_1498_ = l_Lean_Syntax_getArg(v_x_1485_, v___x_1497_);
lean_dec(v_x_1485_);
v___x_1499_ = 0;
v___x_1500_ = l_Lean_SourceInfo_fromRef(v_ref_1494_, v___x_1499_);
v___x_1501_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1502_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
v___x_1503_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1493_);
lean_inc(v_quotContext_1492_);
v___x_1504_ = l_Lean_addMacroScope(v_quotContext_1492_, v___x_1503_, v_currMacroScope_1493_);
v___x_1505_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1500_, 2);
v___x_1506_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1500_);
lean_ctor_set(v___x_1506_, 1, v___x_1502_);
lean_ctor_set(v___x_1506_, 2, v___x_1504_);
lean_ctor_set(v___x_1506_, 3, v___x_1505_);
v___x_1507_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1508_ = l_Lean_Syntax_node2(v___x_1500_, v___x_1507_, v___x_1496_, v___x_1498_);
v___x_1509_ = l_Lean_Syntax_node2(v___x_1500_, v___x_1501_, v___x_1506_, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v_a_1487_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___boxed(lean_object* v_x_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(v_x_1511_, v_a_1512_, v_a_1513_);
lean_dec_ref(v_a_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object* v_x_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1515_);
v___x_1519_ = l_Lean_Syntax_isOfKind(v_x_1515_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec(v_x_1515_);
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v_a_1517_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1522_);
v___x_1524_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1523_);
v___x_1525_ = l_Lean_Syntax_isOfKind(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v___x_1523_);
lean_dec(v_x_1515_);
v___x_1526_ = lean_box(0);
v___x_1527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v_a_1517_);
return v___x_1527_;
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1528_);
lean_dec(v_x_1515_);
v___x_1530_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1529_);
v___x_1531_ = l_Lean_Syntax_matchesNull(v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v___x_1529_);
lean_dec(v___x_1523_);
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v_a_1517_);
return v___x_1533_;
}
else
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v_ref_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1534_ = l_Lean_Syntax_getArg(v___x_1529_, v___x_1522_);
v___x_1535_ = l_Lean_Syntax_getArg(v___x_1529_, v___x_1528_);
lean_dec(v___x_1529_);
v_ref_1536_ = l_Lean_replaceRef(v___x_1523_, v_a_1516_);
lean_dec(v___x_1523_);
v___x_1537_ = 0;
v___x_1538_ = l_Lean_SourceInfo_fromRef(v_ref_1536_, v___x_1537_);
lean_dec(v_ref_1536_);
v___x_1539_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
v___x_1540_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__2));
lean_inc(v___x_1538_);
v___x_1541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1538_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = l_Lean_Syntax_node3(v___x_1538_, v___x_1539_, v___x_1534_, v___x_1541_, v___x_1535_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v_a_1517_);
return v___x_1543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object* v_x_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(v_x_1544_, v_a_1545_, v_a_1546_);
lean_dec(v_a_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal___redArg(lean_object* v_inst_1548_, lean_object* v_l_u2081_1549_, lean_object* v_l_u2082_1550_){
_start:
{
uint8_t v___x_1551_; 
lean_inc(v_l_u2082_1550_);
lean_inc(v_l_u2081_1549_);
lean_inc_ref(v_inst_1548_);
v___x_1551_ = l_List_isPrefixOf___redArg(v_inst_1548_, v_l_u2081_1549_, v_l_u2082_1550_);
if (v___x_1551_ == 0)
{
if (lean_obj_tag(v_l_u2082_1550_) == 0)
{
lean_dec(v_l_u2081_1549_);
lean_dec_ref(v_inst_1548_);
return v___x_1551_;
}
else
{
lean_object* v_tail_1552_; 
v_tail_1552_ = lean_ctor_get(v_l_u2082_1550_, 1);
lean_inc(v_tail_1552_);
lean_dec_ref_known(v_l_u2082_1550_, 2);
v_l_u2082_1550_ = v_tail_1552_;
goto _start;
}
}
else
{
lean_dec(v_l_u2082_1550_);
lean_dec(v_l_u2081_1549_);
lean_dec_ref(v_inst_1548_);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___redArg___boxed(lean_object* v_inst_1554_, lean_object* v_l_u2081_1555_, lean_object* v_l_u2082_1556_){
_start:
{
uint8_t v_res_1557_; lean_object* v_r_1558_; 
v_res_1557_ = l_List_isInfixOf__internal___redArg(v_inst_1554_, v_l_u2081_1555_, v_l_u2082_1556_);
v_r_1558_ = lean_box(v_res_1557_);
return v_r_1558_;
}
}
LEAN_EXPORT uint8_t l_List_isInfixOf__internal(lean_object* v_00_u03b1_1559_, lean_object* v_inst_1560_, lean_object* v_l_u2081_1561_, lean_object* v_l_u2082_1562_){
_start:
{
uint8_t v___x_1563_; 
v___x_1563_ = l_List_isInfixOf__internal___redArg(v_inst_1560_, v_l_u2081_1561_, v_l_u2082_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___boxed(lean_object* v_00_u03b1_1564_, lean_object* v_inst_1565_, lean_object* v_l_u2081_1566_, lean_object* v_l_u2082_1567_){
_start:
{
uint8_t v_res_1568_; lean_object* v_r_1569_; 
v_res_1568_ = l_List_isInfixOf__internal(v_00_u03b1_1564_, v_inst_1565_, v_l_u2081_1566_, v_l_u2082_1567_);
v_r_1569_ = lean_box(v_res_1568_);
return v_r_1569_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go___redArg(lean_object* v_l_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
if (lean_obj_tag(v_a_1571_) == 0)
{
lean_object* v___x_1574_; 
lean_dec(v_a_1573_);
lean_dec(v_a_1572_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_l_1570_);
lean_ctor_set(v___x_1574_, 1, v_a_1571_);
return v___x_1574_;
}
else
{
lean_object* v_head_1575_; lean_object* v_tail_1576_; lean_object* v_zero_1577_; uint8_t v_isZero_1578_; 
v_head_1575_ = lean_ctor_get(v_a_1571_, 0);
v_tail_1576_ = lean_ctor_get(v_a_1571_, 1);
v_zero_1577_ = lean_unsigned_to_nat(0u);
v_isZero_1578_ = lean_nat_dec_eq(v_a_1572_, v_zero_1577_);
if (v_isZero_1578_ == 1)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec(v_a_1572_);
lean_dec(v_l_1570_);
v___x_1579_ = l_List_reverse___redArg(v_a_1573_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v_a_1571_);
return v___x_1580_;
}
else
{
lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1590_; 
lean_inc(v_tail_1576_);
lean_inc(v_head_1575_);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_a_1571_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; lean_object* v_unused_1592_; 
v_unused_1591_ = lean_ctor_get(v_a_1571_, 1);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_a_1571_, 0);
lean_dec(v_unused_1592_);
v___x_1582_ = v_a_1571_;
v_isShared_1583_ = v_isSharedCheck_1590_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v_a_1571_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1590_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_one_1584_; lean_object* v_n_1585_; lean_object* v___x_1587_; 
v_one_1584_ = lean_unsigned_to_nat(1u);
v_n_1585_ = lean_nat_sub(v_a_1572_, v_one_1584_);
lean_dec(v_a_1572_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 1, v_a_1573_);
v___x_1587_ = v___x_1582_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_head_1575_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_a_1573_);
v___x_1587_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
v_a_1571_ = v_tail_1576_;
v_a_1572_ = v_n_1585_;
v_a_1573_ = v___x_1587_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object* v_00_u03b1_1593_, lean_object* v_l_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_List_splitAt_go___redArg(v_l_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt___redArg(lean_object* v_n_1599_, lean_object* v_l_1600_){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_box(0);
lean_inc(v_l_1600_);
v___x_1602_ = l_List_splitAt_go___redArg(v_l_1600_, v_l_1600_, v_n_1599_, v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt(lean_object* v_00_u03b1_1603_, lean_object* v_n_1604_, lean_object* v_l_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_List_splitAt___redArg(v_n_1604_, v_l_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg(lean_object* v_xs_1607_, lean_object* v_i_1608_){
_start:
{
lean_object* v_len_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v_len_1609_ = l_List_length___redArg(v_xs_1607_);
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_nat_dec_le(v_len_1609_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v_i_1612_; lean_object* v_ys_1613_; lean_object* v_zs_1614_; lean_object* v___x_1615_; 
v_i_1612_ = lean_nat_mod(v_i_1608_, v_len_1609_);
lean_dec(v_len_1609_);
lean_inc(v_xs_1607_);
v_ys_1613_ = l_List_take___redArg(v_i_1612_, v_xs_1607_);
v_zs_1614_ = l_List_drop___redArg(v_i_1612_, v_xs_1607_);
lean_dec(v_xs_1607_);
v___x_1615_ = l_List_appendTR___redArg(v_zs_1614_, v_ys_1613_);
return v___x_1615_;
}
else
{
lean_dec(v_len_1609_);
return v_xs_1607_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg___boxed(lean_object* v_xs_1616_, lean_object* v_i_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_List_rotateLeft___redArg(v_xs_1616_, v_i_1617_);
lean_dec(v_i_1617_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft(lean_object* v_00_u03b1_1619_, lean_object* v_xs_1620_, lean_object* v_i_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_List_rotateLeft___redArg(v_xs_1620_, v_i_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___boxed(lean_object* v_00_u03b1_1623_, lean_object* v_xs_1624_, lean_object* v_i_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_List_rotateLeft(v_00_u03b1_1623_, v_xs_1624_, v_i_1625_);
lean_dec(v_i_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg(lean_object* v_xs_1627_, lean_object* v_i_1628_){
_start:
{
lean_object* v_len_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v_len_1629_ = l_List_length___redArg(v_xs_1627_);
v___x_1630_ = lean_unsigned_to_nat(1u);
v___x_1631_ = lean_nat_dec_le(v_len_1629_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v_i_1633_; lean_object* v_ys_1634_; lean_object* v_zs_1635_; lean_object* v___x_1636_; 
v___x_1632_ = lean_nat_mod(v_i_1628_, v_len_1629_);
v_i_1633_ = lean_nat_sub(v_len_1629_, v___x_1632_);
lean_dec(v___x_1632_);
lean_dec(v_len_1629_);
lean_inc(v_xs_1627_);
v_ys_1634_ = l_List_take___redArg(v_i_1633_, v_xs_1627_);
v_zs_1635_ = l_List_drop___redArg(v_i_1633_, v_xs_1627_);
lean_dec(v_xs_1627_);
v___x_1636_ = l_List_appendTR___redArg(v_zs_1635_, v_ys_1634_);
return v___x_1636_;
}
else
{
lean_dec(v_len_1629_);
return v_xs_1627_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg___boxed(lean_object* v_xs_1637_, lean_object* v_i_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_List_rotateRight___redArg(v_xs_1637_, v_i_1638_);
lean_dec(v_i_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight(lean_object* v_00_u03b1_1640_, lean_object* v_xs_1641_, lean_object* v_i_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_List_rotateRight___redArg(v_xs_1641_, v_i_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___boxed(lean_object* v_00_u03b1_1644_, lean_object* v_xs_1645_, lean_object* v_i_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_List_rotateRight(v_00_u03b1_1644_, v_xs_1645_, v_i_1646_);
lean_dec(v_i_1646_);
return v_res_1647_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise___redArg(lean_object* v_inst_1648_, lean_object* v_x_1649_){
_start:
{
if (lean_obj_tag(v_x_1649_) == 0)
{
uint8_t v___x_1650_; 
lean_dec_ref(v_inst_1648_);
v___x_1650_ = 1;
return v___x_1650_;
}
else
{
lean_object* v_head_1651_; lean_object* v_tail_1652_; uint8_t v_decide_1653_; 
v_head_1651_ = lean_ctor_get(v_x_1649_, 0);
lean_inc(v_head_1651_);
v_tail_1652_ = lean_ctor_get(v_x_1649_, 1);
lean_inc_n(v_tail_1652_, 2);
lean_dec_ref_known(v_x_1649_, 2);
lean_inc_ref(v_inst_1648_);
v_decide_1653_ = l_List_instDecidablePairwise___redArg(v_inst_1648_, v_tail_1652_);
if (v_decide_1653_ == 0)
{
lean_dec(v_tail_1652_);
lean_dec(v_head_1651_);
lean_dec_ref(v_inst_1648_);
return v_decide_1653_;
}
else
{
lean_object* v___x_1654_; uint8_t v_decide_1655_; 
v___x_1654_ = lean_apply_1(v_inst_1648_, v_head_1651_);
v_decide_1655_ = l_List_decidableBAll___redArg(v___x_1654_, v_tail_1652_);
return v_decide_1655_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___redArg___boxed(lean_object* v_inst_1656_, lean_object* v_x_1657_){
_start:
{
uint8_t v_res_1658_; lean_object* v_r_1659_; 
v_res_1658_ = l_List_instDecidablePairwise___redArg(v_inst_1656_, v_x_1657_);
v_r_1659_ = lean_box(v_res_1658_);
return v_r_1659_;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise(lean_object* v_00_u03b1_1660_, lean_object* v_R_1661_, lean_object* v_inst_1662_, lean_object* v_x_1663_){
_start:
{
uint8_t v___x_1664_; 
v___x_1664_ = l_List_instDecidablePairwise___redArg(v_inst_1662_, v_x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___boxed(lean_object* v_00_u03b1_1665_, lean_object* v_R_1666_, lean_object* v_inst_1667_, lean_object* v_x_1668_){
_start:
{
uint8_t v_res_1669_; lean_object* v_r_1670_; 
v_res_1669_ = l_List_instDecidablePairwise(v_00_u03b1_1665_, v_R_1666_, v_inst_1667_, v_x_1668_);
v_r_1670_ = lean_box(v_res_1669_);
return v_r_1670_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg___lam__0(lean_object* v_inst_1671_, lean_object* v_a_1672_, lean_object* v_b_1673_){
_start:
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = lean_apply_2(v_inst_1671_, v_a_1672_, v_b_1673_);
v___x_1675_ = lean_unbox(v___x_1674_);
if (v___x_1675_ == 0)
{
uint8_t v___x_1676_; 
v___x_1676_ = 1;
return v___x_1676_;
}
else
{
uint8_t v___x_1677_; 
v___x_1677_ = 0;
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___lam__0___boxed(lean_object* v_inst_1678_, lean_object* v_a_1679_, lean_object* v_b_1680_){
_start:
{
uint8_t v_res_1681_; lean_object* v_r_1682_; 
v_res_1681_ = l_List_nodupDecidable___redArg___lam__0(v_inst_1678_, v_a_1679_, v_b_1680_);
v_r_1682_ = lean_box(v_res_1681_);
return v_r_1682_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___redArg(lean_object* v_inst_1683_, lean_object* v_l_1684_){
_start:
{
lean_object* v___f_1685_; uint8_t v___x_1686_; 
v___f_1685_ = lean_alloc_closure((void*)(l_List_nodupDecidable___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1685_, 0, v_inst_1683_);
v___x_1686_ = l_List_instDecidablePairwise___redArg(v___f_1685_, v_l_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___boxed(lean_object* v_inst_1687_, lean_object* v_l_1688_){
_start:
{
uint8_t v_res_1689_; lean_object* v_r_1690_; 
v_res_1689_ = l_List_nodupDecidable___redArg(v_inst_1687_, v_l_1688_);
v_r_1690_ = lean_box(v_res_1689_);
return v_r_1690_;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable(lean_object* v_00_u03b1_1691_, lean_object* v_inst_1692_, lean_object* v_l_1693_){
_start:
{
uint8_t v___x_1694_; 
v___x_1694_ = l_List_nodupDecidable___redArg(v_inst_1692_, v_l_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_inst_1696_, lean_object* v_l_1697_){
_start:
{
uint8_t v_res_1698_; lean_object* v_r_1699_; 
v_res_1698_ = l_List_nodupDecidable(v_00_u03b1_1695_, v_inst_1696_, v_l_1697_);
v_r_1699_ = lean_box(v_res_1698_);
return v_r_1699_;
}
}
LEAN_EXPORT lean_object* l_List_replace___redArg(lean_object* v_inst_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1701_) == 0)
{
lean_dec(v_x_1703_);
lean_dec(v_x_1702_);
lean_dec_ref(v_inst_1700_);
return v_x_1701_;
}
else
{
lean_object* v_head_1704_; lean_object* v_tail_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1718_; 
v_head_1704_ = lean_ctor_get(v_x_1701_, 0);
v_tail_1705_ = lean_ctor_get(v_x_1701_, 1);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_x_1701_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1707_ = v_x_1701_;
v_isShared_1708_ = v_isSharedCheck_1718_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_tail_1705_);
lean_inc(v_head_1704_);
lean_dec(v_x_1701_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1718_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
lean_inc_ref(v_inst_1700_);
lean_inc(v_head_1704_);
lean_inc(v_x_1702_);
v___x_1709_ = lean_apply_2(v_inst_1700_, v_x_1702_, v_head_1704_);
v___x_1710_ = lean_unbox(v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1711_ = l_List_replace___redArg(v_inst_1700_, v_tail_1705_, v_x_1702_, v_x_1703_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v___x_1711_);
v___x_1713_ = v___x_1707_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_head_1704_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
else
{
lean_object* v___x_1716_; 
lean_dec(v_head_1704_);
lean_dec(v_x_1702_);
lean_dec_ref(v_inst_1700_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v_x_1703_);
v___x_1716_ = v___x_1707_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_x_1703_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_tail_1705_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_replace(lean_object* v_00_u03b1_1719_, lean_object* v_inst_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_List_replace___redArg(v_inst_1720_, v_x_1721_, v_x_1722_, v_x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg(lean_object* v_f_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_zero_1728_; uint8_t v_isZero_1729_; 
v_zero_1728_ = lean_unsigned_to_nat(0u);
v_isZero_1729_ = lean_nat_dec_eq(v_a_1726_, v_zero_1728_);
if (v_isZero_1729_ == 1)
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_apply_1(v_f_1725_, v_a_1727_);
return v___x_1730_;
}
else
{
if (lean_obj_tag(v_a_1727_) == 0)
{
lean_dec_ref(v_f_1725_);
return v_a_1727_;
}
else
{
lean_object* v_head_1731_; lean_object* v_tail_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1742_; 
v_head_1731_ = lean_ctor_get(v_a_1727_, 0);
v_tail_1732_ = lean_ctor_get(v_a_1727_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_a_1727_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1734_ = v_a_1727_;
v_isShared_1735_ = v_isSharedCheck_1742_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_tail_1732_);
lean_inc(v_head_1731_);
lean_dec(v_a_1727_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1742_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_one_1736_; lean_object* v_n_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v_one_1736_ = lean_unsigned_to_nat(1u);
v_n_1737_ = lean_nat_sub(v_a_1726_, v_one_1736_);
v___x_1738_ = l_List_modifyTailIdx_go___redArg(v_f_1725_, v_n_1737_, v_tail_1732_);
lean_dec(v_n_1737_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1738_);
v___x_1740_ = v___x_1734_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_head_1731_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg___boxed(lean_object* v_f_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_List_modifyTailIdx_go___redArg(v_f_1743_, v_a_1744_, v_a_1745_);
lean_dec(v_a_1744_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go(lean_object* v_00_u03b1_1747_, lean_object* v_f_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_List_modifyTailIdx_go___redArg(v_f_1748_, v_a_1749_, v_a_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___boxed(lean_object* v_00_u03b1_1752_, lean_object* v_f_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_List_modifyTailIdx_go(v_00_u03b1_1752_, v_f_1753_, v_a_1754_, v_a_1755_);
lean_dec(v_a_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg(lean_object* v_l_1757_, lean_object* v_i_1758_, lean_object* v_f_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_List_modifyTailIdx_go___redArg(v_f_1759_, v_i_1758_, v_l_1757_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg___boxed(lean_object* v_l_1761_, lean_object* v_i_1762_, lean_object* v_f_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_List_modifyTailIdx___redArg(v_l_1761_, v_i_1762_, v_f_1763_);
lean_dec(v_i_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx(lean_object* v_00_u03b1_1765_, lean_object* v_l_1766_, lean_object* v_i_1767_, lean_object* v_f_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_List_modifyTailIdx_go___redArg(v_f_1768_, v_i_1767_, v_l_1766_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_l_1771_, lean_object* v_i_1772_, lean_object* v_f_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_List_modifyTailIdx(v_00_u03b1_1770_, v_l_1771_, v_i_1772_, v_f_1773_);
lean_dec(v_i_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_List_modifyHead___redArg(lean_object* v_f_1775_, lean_object* v_x_1776_){
_start:
{
if (lean_obj_tag(v_x_1776_) == 0)
{
lean_dec(v_f_1775_);
return v_x_1776_;
}
else
{
lean_object* v_head_1777_; lean_object* v_tail_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1786_; 
v_head_1777_ = lean_ctor_get(v_x_1776_, 0);
v_tail_1778_ = lean_ctor_get(v_x_1776_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_x_1776_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1780_ = v_x_1776_;
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_tail_1778_);
lean_inc(v_head_1777_);
lean_dec(v_x_1776_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_apply_1(v_f_1775_, v_head_1777_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_tail_1778_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyHead(lean_object* v_00_u03b1_1787_, lean_object* v_f_1788_, lean_object* v_x_1789_){
_start:
{
if (lean_obj_tag(v_x_1789_) == 0)
{
lean_dec(v_f_1788_);
return v_x_1789_;
}
else
{
lean_object* v_head_1790_; lean_object* v_tail_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1799_; 
v_head_1790_ = lean_ctor_get(v_x_1789_, 0);
v_tail_1791_ = lean_ctor_get(v_x_1789_, 1);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_x_1789_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1793_ = v_x_1789_;
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_tail_1791_);
lean_inc(v_head_1790_);
lean_dec(v_x_1789_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1795_ = lean_apply_1(v_f_1788_, v_head_1790_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1795_);
v___x_1797_ = v___x_1793_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_tail_1791_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg(lean_object* v_l_1800_, lean_object* v_i_1801_, lean_object* v_f_1802_){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1803_, 0, lean_box(0));
lean_closure_set(v___x_1803_, 1, v_f_1802_);
v___x_1804_ = l_List_modifyTailIdx_go___redArg(v___x_1803_, v_i_1801_, v_l_1800_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg___boxed(lean_object* v_l_1805_, lean_object* v_i_1806_, lean_object* v_f_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_List_modify___redArg(v_l_1805_, v_i_1806_, v_f_1807_);
lean_dec(v_i_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_List_modify(lean_object* v_00_u03b1_1809_, lean_object* v_l_1810_, lean_object* v_i_1811_, lean_object* v_f_1812_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1813_, 0, lean_box(0));
lean_closure_set(v___x_1813_, 1, v_f_1812_);
v___x_1814_ = l_List_modifyTailIdx_go___redArg(v___x_1813_, v_i_1811_, v_l_1810_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_List_modify___boxed(lean_object* v_00_u03b1_1815_, lean_object* v_l_1816_, lean_object* v_i_1817_, lean_object* v_f_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_List_modify(v_00_u03b1_1815_, v_l_1816_, v_i_1817_, v_f_1818_);
lean_dec(v_i_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object* v_inst_1820_, lean_object* v_a_1821_, lean_object* v_l_1822_){
_start:
{
uint8_t v___x_1823_; 
lean_inc(v_l_1822_);
lean_inc(v_a_1821_);
v___x_1823_ = l_List_elem___redArg(v_inst_1820_, v_a_1821_, v_l_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1824_, 0, v_a_1821_);
lean_ctor_set(v___x_1824_, 1, v_l_1822_);
return v___x_1824_;
}
else
{
lean_dec(v_a_1821_);
return v_l_1822_;
}
}
}
LEAN_EXPORT lean_object* l_List_insert(lean_object* v_00_u03b1_1825_, lean_object* v_inst_1826_, lean_object* v_a_1827_, lean_object* v_l_1828_){
_start:
{
uint8_t v___x_1829_; 
lean_inc(v_l_1828_);
lean_inc(v_a_1827_);
v___x_1829_ = l_List_elem___redArg(v_inst_1826_, v_a_1827_, v_l_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1830_, 0, v_a_1827_);
lean_ctor_set(v___x_1830_, 1, v_l_1828_);
return v___x_1830_;
}
else
{
lean_dec(v_a_1827_);
return v_l_1828_;
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_zero_1834_; uint8_t v_isZero_1835_; 
v_zero_1834_ = lean_unsigned_to_nat(0u);
v_isZero_1835_ = lean_nat_dec_eq(v_a_1832_, v_zero_1834_);
if (v_isZero_1835_ == 1)
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1836_, 0, v_a_1831_);
lean_ctor_set(v___x_1836_, 1, v_a_1833_);
return v___x_1836_;
}
else
{
if (lean_obj_tag(v_a_1833_) == 0)
{
lean_dec(v_a_1831_);
return v_a_1833_;
}
else
{
lean_object* v_head_1837_; lean_object* v_tail_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1848_; 
v_head_1837_ = lean_ctor_get(v_a_1833_, 0);
v_tail_1838_ = lean_ctor_get(v_a_1833_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_a_1833_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1840_ = v_a_1833_;
v_isShared_1841_ = v_isSharedCheck_1848_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_tail_1838_);
lean_inc(v_head_1837_);
lean_dec(v_a_1833_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1848_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_one_1842_; lean_object* v_n_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v_one_1842_ = lean_unsigned_to_nat(1u);
v_n_1843_ = lean_nat_sub(v_a_1832_, v_one_1842_);
v___x_1844_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1831_, v_n_1843_, v_tail_1838_);
lean_dec(v_n_1843_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 1, v___x_1844_);
v___x_1846_ = v___x_1840_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_head_1837_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg___boxed(lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg(lean_object* v_xs_1853_, lean_object* v_i_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1855_, v_i_1854_, v_xs_1853_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___boxed(lean_object* v_xs_1857_, lean_object* v_i_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_List_insertIdx___redArg(v_xs_1857_, v_i_1858_, v_a_1859_);
lean_dec(v_i_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx(lean_object* v_00_u03b1_1861_, lean_object* v_xs_1862_, lean_object* v_i_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1864_, v_i_1863_, v_xs_1862_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___boxed(lean_object* v_00_u03b1_1866_, lean_object* v_xs_1867_, lean_object* v_i_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_List_insertIdx(v_00_u03b1_1866_, v_xs_1867_, v_i_1868_, v_a_1869_);
lean_dec(v_i_1868_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(lean_object* v_00_u03b1_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___boxed(lean_object* v_00_u03b1_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(v_00_u03b1_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
lean_dec(v_a_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_List_erase___redArg(lean_object* v_inst_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_){
_start:
{
if (lean_obj_tag(v_x_1882_) == 0)
{
lean_dec(v_x_1883_);
lean_dec_ref(v_inst_1881_);
return v_x_1882_;
}
else
{
lean_object* v_head_1884_; lean_object* v_tail_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1895_; 
v_head_1884_ = lean_ctor_get(v_x_1882_, 0);
v_tail_1885_ = lean_ctor_get(v_x_1882_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_x_1882_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1887_ = v_x_1882_;
v_isShared_1888_ = v_isSharedCheck_1895_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_tail_1885_);
lean_inc(v_head_1884_);
lean_dec(v_x_1882_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1895_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; uint8_t v___x_1890_; 
lean_inc_ref(v_inst_1881_);
lean_inc(v_x_1883_);
lean_inc(v_head_1884_);
v___x_1889_ = lean_apply_2(v_inst_1881_, v_head_1884_, v_x_1883_);
v___x_1890_ = lean_unbox(v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = l_List_erase___redArg(v_inst_1881_, v_tail_1885_, v_x_1883_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v___x_1891_);
v___x_1893_ = v___x_1887_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_head_1884_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
lean_del_object(v___x_1887_);
lean_dec(v_head_1884_);
lean_dec(v_x_1883_);
lean_dec_ref(v_inst_1881_);
return v_tail_1885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_erase(lean_object* v_00_u03b1_1896_, lean_object* v_inst_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_List_erase___redArg(v_inst_1897_, v_x_1898_, v_x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_List_eraseP___redArg(lean_object* v_p_1901_, lean_object* v_x_1902_){
_start:
{
if (lean_obj_tag(v_x_1902_) == 0)
{
lean_dec_ref(v_p_1901_);
return v_x_1902_;
}
else
{
lean_object* v_head_1903_; lean_object* v_tail_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1914_; 
v_head_1903_ = lean_ctor_get(v_x_1902_, 0);
v_tail_1904_ = lean_ctor_get(v_x_1902_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_x_1902_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1906_ = v_x_1902_;
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_tail_1904_);
lean_inc(v_head_1903_);
lean_dec(v_x_1902_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; uint8_t v___x_1909_; 
lean_inc_ref(v_p_1901_);
lean_inc(v_head_1903_);
v___x_1908_ = lean_apply_1(v_p_1901_, v_head_1903_);
v___x_1909_ = lean_unbox(v___x_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1910_ = l_List_eraseP___redArg(v_p_1901_, v_tail_1904_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 1, v___x_1910_);
v___x_1912_ = v___x_1906_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_head_1903_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
else
{
lean_del_object(v___x_1906_);
lean_dec(v_head_1903_);
lean_dec_ref(v_p_1901_);
return v_tail_1904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP(lean_object* v_00_u03b1_1915_, lean_object* v_p_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_List_eraseP___redArg(v_p_1916_, v_x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg(lean_object* v_x_1919_, lean_object* v_x_1920_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
return v_x_1919_;
}
else
{
lean_object* v_head_1921_; lean_object* v_tail_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1934_; 
v_head_1921_ = lean_ctor_get(v_x_1919_, 0);
v_tail_1922_ = lean_ctor_get(v_x_1919_, 1);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_x_1919_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1924_ = v_x_1919_;
v_isShared_1925_ = v_isSharedCheck_1934_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_tail_1922_);
lean_inc(v_head_1921_);
lean_dec(v_x_1919_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1934_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_zero_1926_; uint8_t v_isZero_1927_; 
v_zero_1926_ = lean_unsigned_to_nat(0u);
v_isZero_1927_ = lean_nat_dec_eq(v_x_1920_, v_zero_1926_);
if (v_isZero_1927_ == 1)
{
lean_del_object(v___x_1924_);
lean_dec(v_head_1921_);
return v_tail_1922_;
}
else
{
lean_object* v_one_1928_; lean_object* v_n_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v_one_1928_ = lean_unsigned_to_nat(1u);
v_n_1929_ = lean_nat_sub(v_x_1920_, v_one_1928_);
v___x_1930_ = l_List_eraseIdx___redArg(v_tail_1922_, v_n_1929_);
lean_dec(v_n_1929_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___x_1930_);
v___x_1932_ = v___x_1924_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_head_1921_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg___boxed(lean_object* v_x_1935_, lean_object* v_x_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_List_eraseIdx___redArg(v_x_1935_, v_x_1936_);
lean_dec(v_x_1936_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object* v_00_u03b1_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_List_eraseIdx___redArg(v_x_1939_, v_x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___boxed(lean_object* v_00_u03b1_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_List_eraseIdx(v_00_u03b1_1942_, v_x_1943_, v_x_1944_);
lean_dec(v_x_1944_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object* v_p_1946_, lean_object* v_x_1947_){
_start:
{
if (lean_obj_tag(v_x_1947_) == 0)
{
lean_object* v___x_1948_; 
lean_dec_ref(v_p_1946_);
v___x_1948_ = lean_box(0);
return v___x_1948_;
}
else
{
lean_object* v_head_1949_; lean_object* v_tail_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v_head_1949_ = lean_ctor_get(v_x_1947_, 0);
lean_inc_n(v_head_1949_, 2);
v_tail_1950_ = lean_ctor_get(v_x_1947_, 1);
lean_inc(v_tail_1950_);
lean_dec_ref_known(v_x_1947_, 2);
lean_inc_ref(v_p_1946_);
v___x_1951_ = lean_apply_1(v_p_1946_, v_head_1949_);
v___x_1952_ = lean_unbox(v___x_1951_);
if (v___x_1952_ == 0)
{
lean_dec(v_head_1949_);
v_x_1947_ = v_tail_1950_;
goto _start;
}
else
{
lean_object* v___x_1954_; 
lean_dec(v_tail_1950_);
lean_dec_ref(v_p_1946_);
v___x_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_head_1949_);
return v___x_1954_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object* v_00_u03b1_1955_, lean_object* v_p_1956_, lean_object* v_x_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_List_find_x3f___redArg(v_p_1956_, v_x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object* v_f_1959_, lean_object* v_x_1960_){
_start:
{
if (lean_obj_tag(v_x_1960_) == 0)
{
lean_object* v___x_1961_; 
lean_dec_ref(v_f_1959_);
v___x_1961_ = lean_box(0);
return v___x_1961_;
}
else
{
lean_object* v_head_1962_; lean_object* v_tail_1963_; lean_object* v___x_1964_; 
v_head_1962_ = lean_ctor_get(v_x_1960_, 0);
lean_inc(v_head_1962_);
v_tail_1963_ = lean_ctor_get(v_x_1960_, 1);
lean_inc(v_tail_1963_);
lean_dec_ref_known(v_x_1960_, 2);
lean_inc_ref(v_f_1959_);
v___x_1964_ = lean_apply_1(v_f_1959_, v_head_1962_);
if (lean_obj_tag(v___x_1964_) == 0)
{
v_x_1960_ = v_tail_1963_;
goto _start;
}
else
{
lean_dec(v_tail_1963_);
lean_dec_ref(v_f_1959_);
return v___x_1964_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object* v_00_u03b1_1966_, lean_object* v_00_u03b2_1967_, lean_object* v_f_1968_, lean_object* v_x_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_List_findSome_x3f___redArg(v_f_1968_, v_x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f___redArg(lean_object* v_p_1971_, lean_object* v_x_1972_){
_start:
{
if (lean_obj_tag(v_x_1972_) == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref(v_p_1971_);
v___x_1973_ = lean_box(0);
return v___x_1973_;
}
else
{
lean_object* v_head_1974_; lean_object* v_tail_1975_; lean_object* v___x_1976_; 
v_head_1974_ = lean_ctor_get(v_x_1972_, 0);
lean_inc(v_head_1974_);
v_tail_1975_ = lean_ctor_get(v_x_1972_, 1);
lean_inc(v_tail_1975_);
lean_dec_ref_known(v_x_1972_, 2);
lean_inc_ref(v_p_1971_);
v___x_1976_ = l_List_findRev_x3f___redArg(v_p_1971_, v_tail_1975_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v___x_1977_; uint8_t v___x_1978_; 
lean_inc(v_head_1974_);
v___x_1977_ = lean_apply_1(v_p_1971_, v_head_1974_);
v___x_1978_ = lean_unbox(v___x_1977_);
if (v___x_1978_ == 0)
{
lean_dec(v_head_1974_);
return v___x_1976_;
}
else
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_head_1974_);
return v___x_1979_;
}
}
else
{
lean_dec(v_head_1974_);
lean_dec_ref(v_p_1971_);
return v___x_1976_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f(lean_object* v_00_u03b1_1980_, lean_object* v_p_1981_, lean_object* v_x_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_List_findRev_x3f___redArg(v_p_1981_, v_x_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f___redArg(lean_object* v_f_1984_, lean_object* v_x_1985_){
_start:
{
if (lean_obj_tag(v_x_1985_) == 0)
{
lean_object* v___x_1986_; 
lean_dec_ref(v_f_1984_);
v___x_1986_ = lean_box(0);
return v___x_1986_;
}
else
{
lean_object* v_head_1987_; lean_object* v_tail_1988_; lean_object* v___x_1989_; 
v_head_1987_ = lean_ctor_get(v_x_1985_, 0);
lean_inc(v_head_1987_);
v_tail_1988_ = lean_ctor_get(v_x_1985_, 1);
lean_inc(v_tail_1988_);
lean_dec_ref_known(v_x_1985_, 2);
lean_inc_ref(v_f_1984_);
v___x_1989_ = l_List_findSomeRev_x3f___redArg(v_f_1984_, v_tail_1988_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_apply_1(v_f_1984_, v_head_1987_);
return v___x_1990_;
}
else
{
lean_dec(v_head_1987_);
lean_dec_ref(v_f_1984_);
return v___x_1989_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f(lean_object* v_00_u03b1_1991_, lean_object* v_00_u03b2_1992_, lean_object* v_f_1993_, lean_object* v_x_1994_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_List_findSomeRev_x3f___redArg(v_f_1993_, v_x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___redArg(lean_object* v_p_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
if (lean_obj_tag(v_a_1997_) == 0)
{
lean_dec_ref(v_p_1996_);
return v_a_1998_;
}
else
{
lean_object* v_head_1999_; lean_object* v_tail_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v_head_1999_ = lean_ctor_get(v_a_1997_, 0);
lean_inc(v_head_1999_);
v_tail_2000_ = lean_ctor_get(v_a_1997_, 1);
lean_inc(v_tail_2000_);
lean_dec_ref_known(v_a_1997_, 2);
lean_inc_ref(v_p_1996_);
v___x_2001_ = lean_apply_1(v_p_1996_, v_head_1999_);
v___x_2002_ = lean_unbox(v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_add(v_a_1998_, v___x_2003_);
lean_dec(v_a_1998_);
v_a_1997_ = v_tail_2000_;
v_a_1998_ = v___x_2004_;
goto _start;
}
else
{
lean_dec(v_tail_2000_);
lean_dec_ref(v_p_1996_);
return v_a_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object* v_00_u03b1_2006_, lean_object* v_p_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_List_findIdx_go___redArg(v_p_2007_, v_a_2008_, v_a_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx___redArg(lean_object* v_p_2011_, lean_object* v_l_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = l_List_findIdx_go___redArg(v_p_2011_, v_l_2012_, v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx(lean_object* v_00_u03b1_2015_, lean_object* v_p_2016_, lean_object* v_l_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = l_List_findIdx_go___redArg(v_p_2016_, v_l_2017_, v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT uint8_t l_List_idxOf___redArg___lam__0(lean_object* v_inst_2020_, lean_object* v_a_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = lean_apply_2(v_inst_2020_, v_x_2022_, v_a_2021_);
v___x_2024_ = lean_unbox(v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg___lam__0___boxed(lean_object* v_inst_2025_, lean_object* v_a_2026_, lean_object* v_x_2027_){
_start:
{
uint8_t v_res_2028_; lean_object* v_r_2029_; 
v_res_2028_ = l_List_idxOf___redArg___lam__0(v_inst_2025_, v_a_2026_, v_x_2027_);
v_r_2029_ = lean_box(v_res_2028_);
return v_r_2029_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg(lean_object* v_inst_2030_, lean_object* v_a_2031_, lean_object* v_l_2032_){
_start:
{
lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___f_2033_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2033_, 0, v_inst_2030_);
lean_closure_set(v___f_2033_, 1, v_a_2031_);
v___x_2034_ = lean_unsigned_to_nat(0u);
v___x_2035_ = l_List_findIdx_go___redArg(v___f_2033_, v_l_2032_, v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf(lean_object* v_00_u03b1_2036_, lean_object* v_inst_2037_, lean_object* v_a_2038_, lean_object* v_l_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_List_idxOf___redArg(v_inst_2037_, v_a_2038_, v_l_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___redArg(lean_object* v_p_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
if (lean_obj_tag(v_a_2042_) == 0)
{
lean_object* v___x_2044_; 
lean_dec(v_a_2043_);
lean_dec_ref(v_p_2041_);
v___x_2044_ = lean_box(0);
return v___x_2044_;
}
else
{
lean_object* v_head_2045_; lean_object* v_tail_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_head_2045_ = lean_ctor_get(v_a_2042_, 0);
lean_inc(v_head_2045_);
v_tail_2046_ = lean_ctor_get(v_a_2042_, 1);
lean_inc(v_tail_2046_);
lean_dec_ref_known(v_a_2042_, 2);
lean_inc_ref(v_p_2041_);
v___x_2047_ = lean_apply_1(v_p_2041_, v_head_2045_);
v___x_2048_ = lean_unbox(v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_nat_add(v_a_2043_, v___x_2049_);
lean_dec(v_a_2043_);
v_a_2042_ = v_tail_2046_;
v_a_2043_ = v___x_2050_;
goto _start;
}
else
{
lean_object* v___x_2052_; 
lean_dec(v_tail_2046_);
lean_dec_ref(v_p_2041_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_a_2043_);
return v___x_2052_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go(lean_object* v_00_u03b1_2053_, lean_object* v_p_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_List_findIdx_x3f_go___redArg(v_p_2054_, v_a_2055_, v_a_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f___redArg(lean_object* v_p_2058_, lean_object* v_l_2059_){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = l_List_findIdx_x3f_go___redArg(v_p_2058_, v_l_2059_, v___x_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object* v_00_u03b1_2062_, lean_object* v_p_2063_, lean_object* v_l_2064_){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = l_List_findIdx_x3f_go___redArg(v_p_2063_, v_l_2064_, v___x_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f___redArg(lean_object* v_inst_2067_, lean_object* v_a_2068_, lean_object* v_l_2069_){
_start:
{
lean_object* v___f_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___f_2070_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2070_, 0, v_inst_2067_);
lean_closure_set(v___f_2070_, 1, v_a_2068_);
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = l_List_findIdx_x3f_go___redArg(v___f_2070_, v_l_2069_, v___x_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f(lean_object* v_00_u03b1_2073_, lean_object* v_inst_2074_, lean_object* v_a_2075_, lean_object* v_l_2076_){
_start:
{
lean_object* v___f_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___f_2077_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2077_, 0, v_inst_2074_);
lean_closure_set(v___f_2077_, 1, v_a_2075_);
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = l_List_findIdx_x3f_go___redArg(v___f_2077_, v_l_2076_, v___x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___redArg(lean_object* v_p_2080_, lean_object* v_l_x27_2081_, lean_object* v_i_2082_){
_start:
{
if (lean_obj_tag(v_l_x27_2081_) == 0)
{
lean_object* v___x_2083_; 
lean_dec(v_i_2082_);
lean_dec_ref(v_p_2080_);
v___x_2083_ = lean_box(0);
return v___x_2083_;
}
else
{
lean_object* v_head_2084_; lean_object* v_tail_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_head_2084_ = lean_ctor_get(v_l_x27_2081_, 0);
lean_inc(v_head_2084_);
v_tail_2085_ = lean_ctor_get(v_l_x27_2081_, 1);
lean_inc(v_tail_2085_);
lean_dec_ref_known(v_l_x27_2081_, 2);
lean_inc_ref(v_p_2080_);
v___x_2086_ = lean_apply_1(v_p_2080_, v_head_2084_);
v___x_2087_ = lean_unbox(v___x_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = lean_nat_add(v_i_2082_, v___x_2088_);
lean_dec(v_i_2082_);
v_l_x27_2081_ = v_tail_2085_;
v_i_2082_ = v___x_2089_;
goto _start;
}
else
{
lean_object* v___x_2091_; 
lean_dec(v_tail_2085_);
lean_dec_ref(v_p_2080_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_i_2082_);
return v___x_2091_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go(lean_object* v_00_u03b1_2092_, lean_object* v_p_2093_, lean_object* v_l_2094_, lean_object* v_l_x27_2095_, lean_object* v_i_2096_, lean_object* v_h_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_List_findFinIdx_x3f_go___redArg(v_p_2093_, v_l_x27_2095_, v_i_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___boxed(lean_object* v_00_u03b1_2099_, lean_object* v_p_2100_, lean_object* v_l_2101_, lean_object* v_l_x27_2102_, lean_object* v_i_2103_, lean_object* v_h_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_List_findFinIdx_x3f_go(v_00_u03b1_2099_, v_p_2100_, v_l_2101_, v_l_x27_2102_, v_i_2103_, v_h_2104_);
lean_dec(v_l_2101_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f___redArg(lean_object* v_p_2106_, lean_object* v_l_2107_){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = l_List_findFinIdx_x3f_go___redArg(v_p_2106_, v_l_2107_, v___x_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f(lean_object* v_00_u03b1_2110_, lean_object* v_p_2111_, lean_object* v_l_2112_){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2114_ = l_List_findFinIdx_x3f_go___redArg(v_p_2111_, v_l_2112_, v___x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f___redArg(lean_object* v_inst_2115_, lean_object* v_a_2116_, lean_object* v_l_2117_){
_start:
{
lean_object* v___f_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___f_2118_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2118_, 0, v_inst_2115_);
lean_closure_set(v___f_2118_, 1, v_a_2116_);
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = l_List_findFinIdx_x3f_go___redArg(v___f_2118_, v_l_2117_, v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f(lean_object* v_00_u03b1_2121_, lean_object* v_inst_2122_, lean_object* v_a_2123_, lean_object* v_l_2124_){
_start:
{
lean_object* v___f_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___f_2125_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2125_, 0, v_inst_2122_);
lean_closure_set(v___f_2125_, 1, v_a_2123_);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = l_List_findFinIdx_x3f_go___redArg(v___f_2125_, v_l_2124_, v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___redArg(lean_object* v_p_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
if (lean_obj_tag(v_a_2129_) == 0)
{
lean_dec_ref(v_p_2128_);
return v_a_2130_;
}
else
{
lean_object* v_head_2131_; lean_object* v_tail_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v_head_2131_ = lean_ctor_get(v_a_2129_, 0);
lean_inc(v_head_2131_);
v_tail_2132_ = lean_ctor_get(v_a_2129_, 1);
lean_inc(v_tail_2132_);
lean_dec_ref_known(v_a_2129_, 2);
lean_inc_ref(v_p_2128_);
v___x_2133_ = lean_apply_1(v_p_2128_, v_head_2131_);
v___x_2134_ = lean_unbox(v___x_2133_);
if (v___x_2134_ == 0)
{
v_a_2129_ = v_tail_2132_;
goto _start;
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_unsigned_to_nat(1u);
v___x_2137_ = lean_nat_add(v_a_2130_, v___x_2136_);
lean_dec(v_a_2130_);
v_a_2129_ = v_tail_2132_;
v_a_2130_ = v___x_2137_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go(lean_object* v_00_u03b1_2139_, lean_object* v_p_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_List_countP_go___redArg(v_p_2140_, v_a_2141_, v_a_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_List_countP___redArg(lean_object* v_p_2144_, lean_object* v_l_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_unsigned_to_nat(0u);
v___x_2147_ = l_List_countP_go___redArg(v_p_2144_, v_l_2145_, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_List_countP(lean_object* v_00_u03b1_2148_, lean_object* v_p_2149_, lean_object* v_l_2150_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = lean_unsigned_to_nat(0u);
v___x_2152_ = l_List_countP_go___redArg(v_p_2149_, v_l_2150_, v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_List_count___redArg(lean_object* v_inst_2153_, lean_object* v_a_2154_, lean_object* v_l_2155_){
_start:
{
lean_object* v___f_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___f_2156_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2156_, 0, v_inst_2153_);
lean_closure_set(v___f_2156_, 1, v_a_2154_);
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = l_List_countP_go___redArg(v___f_2156_, v_l_2155_, v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_List_count(lean_object* v_00_u03b1_2159_, lean_object* v_inst_2160_, lean_object* v_a_2161_, lean_object* v_l_2162_){
_start:
{
lean_object* v___f_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___f_2163_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2163_, 0, v_inst_2160_);
lean_closure_set(v___f_2163_, 1, v_a_2161_);
v___x_2164_ = lean_unsigned_to_nat(0u);
v___x_2165_ = l_List_countP_go___redArg(v___f_2163_, v_l_2162_, v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___redArg(lean_object* v_inst_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
if (lean_obj_tag(v_x_2168_) == 0)
{
lean_object* v___x_2169_; 
lean_dec(v_x_2167_);
lean_dec_ref(v_inst_2166_);
v___x_2169_ = lean_box(0);
return v___x_2169_;
}
else
{
lean_object* v_head_2170_; lean_object* v_tail_2171_; lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v_head_2170_ = lean_ctor_get(v_x_2168_, 0);
lean_inc(v_head_2170_);
v_tail_2171_ = lean_ctor_get(v_x_2168_, 1);
lean_inc(v_tail_2171_);
lean_dec_ref_known(v_x_2168_, 2);
v_fst_2172_ = lean_ctor_get(v_head_2170_, 0);
lean_inc(v_fst_2172_);
v_snd_2173_ = lean_ctor_get(v_head_2170_, 1);
lean_inc(v_snd_2173_);
lean_dec(v_head_2170_);
lean_inc_ref(v_inst_2166_);
lean_inc(v_x_2167_);
v___x_2174_ = lean_apply_2(v_inst_2166_, v_x_2167_, v_fst_2172_);
v___x_2175_ = lean_unbox(v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec(v_snd_2173_);
v_x_2168_ = v_tail_2171_;
goto _start;
}
else
{
lean_object* v___x_2177_; 
lean_dec(v_tail_2171_);
lean_dec(v_x_2167_);
lean_dec_ref(v_inst_2166_);
v___x_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_snd_2173_);
return v___x_2177_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup(lean_object* v_00_u03b1_2178_, lean_object* v_00_u03b2_2179_, lean_object* v_inst_2180_, lean_object* v_x_2181_, lean_object* v_x_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_List_lookup___redArg(v_inst_2180_, v_x_2181_, v_x_2182_);
return v___x_2183_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0));
v___x_2202_ = l_String_toRawSubstring_x27(v___x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object* v_x_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
lean_inc(v_x_2222_);
v___x_2226_ = l_Lean_Syntax_isOfKind(v_x_2222_, v___x_2225_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec(v_x_2222_);
v___x_2227_ = lean_box(1);
v___x_2228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v_a_2224_);
return v___x_2228_;
}
else
{
lean_object* v_quotContext_2229_; lean_object* v_currMacroScope_2230_; lean_object* v_ref_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_quotContext_2229_ = lean_ctor_get(v_a_2223_, 1);
v_currMacroScope_2230_ = lean_ctor_get(v_a_2223_, 2);
v_ref_2231_ = lean_ctor_get(v_a_2223_, 5);
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = l_Lean_Syntax_getArg(v_x_2222_, v___x_2232_);
v___x_2234_ = lean_unsigned_to_nat(2u);
v___x_2235_ = l_Lean_Syntax_getArg(v_x_2222_, v___x_2234_);
lean_dec(v_x_2222_);
v___x_2236_ = 0;
v___x_2237_ = l_Lean_SourceInfo_fromRef(v_ref_2231_, v___x_2236_);
v___x_2238_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_2239_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
v___x_2240_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2));
lean_inc(v_currMacroScope_2230_);
lean_inc(v_quotContext_2229_);
v___x_2241_ = l_Lean_addMacroScope(v_quotContext_2229_, v___x_2240_, v_currMacroScope_2230_);
v___x_2242_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8));
lean_inc_n(v___x_2237_, 2);
v___x_2243_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2237_);
lean_ctor_set(v___x_2243_, 1, v___x_2239_);
lean_ctor_set(v___x_2243_, 2, v___x_2241_);
lean_ctor_set(v___x_2243_, 3, v___x_2242_);
v___x_2244_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_2245_ = l_Lean_Syntax_node2(v___x_2237_, v___x_2244_, v___x_2233_, v___x_2235_);
v___x_2246_ = l_Lean_Syntax_node2(v___x_2237_, v___x_2238_, v___x_2243_, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v_a_2224_);
return v___x_2247_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___boxed(lean_object* v_x_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(v_x_2248_, v_a_2249_, v_a_2250_);
lean_dec_ref(v_a_2249_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object* v_x_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_2252_);
v___x_2256_ = l_Lean_Syntax_isOfKind(v_x_2252_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_dec(v_x_2252_);
v___x_2257_ = lean_box(0);
v___x_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v_a_2254_);
return v___x_2258_;
}
else
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = l_Lean_Syntax_getArg(v_x_2252_, v___x_2259_);
v___x_2261_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_2260_);
v___x_2262_ = l_Lean_Syntax_isOfKind(v___x_2260_, v___x_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_dec(v___x_2260_);
lean_dec(v_x_2252_);
v___x_2263_ = lean_box(0);
v___x_2264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v_a_2254_);
return v___x_2264_;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2265_ = lean_unsigned_to_nat(1u);
v___x_2266_ = l_Lean_Syntax_getArg(v_x_2252_, v___x_2265_);
lean_dec(v_x_2252_);
v___x_2267_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2266_);
v___x_2268_ = l_Lean_Syntax_matchesNull(v___x_2266_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec(v___x_2266_);
lean_dec(v___x_2260_);
v___x_2269_ = lean_box(0);
v___x_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v_a_2254_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v_ref_2273_; uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2271_ = l_Lean_Syntax_getArg(v___x_2266_, v___x_2259_);
v___x_2272_ = l_Lean_Syntax_getArg(v___x_2266_, v___x_2265_);
lean_dec(v___x_2266_);
v_ref_2273_ = l_Lean_replaceRef(v___x_2260_, v_a_2253_);
lean_dec(v___x_2260_);
v___x_2274_ = 0;
v___x_2275_ = l_Lean_SourceInfo_fromRef(v_ref_2273_, v___x_2274_);
lean_dec(v_ref_2273_);
v___x_2276_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
v___x_2277_ = ((lean_object*)(l_List_term___x7e___00__closed__2));
lean_inc(v___x_2275_);
v___x_2278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2275_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = l_Lean_Syntax_node3(v___x_2275_, v___x_2276_, v___x_2271_, v___x_2278_, v___x_2272_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v_a_2254_);
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object* v_x_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(v_x_2281_, v_a_2282_, v_a_2283_);
lean_dec(v_a_2282_);
return v_res_2284_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm___redArg(lean_object* v_inst_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_){
_start:
{
if (lean_obj_tag(v_x_2286_) == 0)
{
uint8_t v___x_2288_; 
lean_dec_ref(v_inst_2285_);
v___x_2288_ = l_List_isEmpty___redArg(v_x_2287_);
lean_dec(v_x_2287_);
return v___x_2288_;
}
else
{
lean_object* v_head_2289_; lean_object* v_tail_2290_; uint8_t v___x_2291_; 
v_head_2289_ = lean_ctor_get(v_x_2286_, 0);
lean_inc_n(v_head_2289_, 2);
v_tail_2290_ = lean_ctor_get(v_x_2286_, 1);
lean_inc(v_tail_2290_);
lean_dec_ref_known(v_x_2286_, 2);
lean_inc(v_x_2287_);
lean_inc_ref(v_inst_2285_);
v___x_2291_ = l_List_elem___redArg(v_inst_2285_, v_head_2289_, v_x_2287_);
if (v___x_2291_ == 0)
{
lean_dec(v_tail_2290_);
lean_dec(v_head_2289_);
lean_dec(v_x_2287_);
lean_dec_ref(v_inst_2285_);
return v___x_2291_;
}
else
{
lean_object* v___x_2292_; 
lean_inc_ref(v_inst_2285_);
v___x_2292_ = l_List_erase___redArg(v_inst_2285_, v_x_2287_, v_head_2289_);
v_x_2286_ = v_tail_2290_;
v_x_2287_ = v___x_2292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPerm___redArg___boxed(lean_object* v_inst_2294_, lean_object* v_x_2295_, lean_object* v_x_2296_){
_start:
{
uint8_t v_res_2297_; lean_object* v_r_2298_; 
v_res_2297_ = l_List_isPerm___redArg(v_inst_2294_, v_x_2295_, v_x_2296_);
v_r_2298_ = lean_box(v_res_2297_);
return v_r_2298_;
}
}
LEAN_EXPORT uint8_t l_List_isPerm(lean_object* v_00_u03b1_2299_, lean_object* v_inst_2300_, lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
uint8_t v___x_2303_; 
v___x_2303_ = l_List_isPerm___redArg(v_inst_2300_, v_x_2301_, v_x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_List_isPerm___boxed(lean_object* v_00_u03b1_2304_, lean_object* v_inst_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_){
_start:
{
uint8_t v_res_2308_; lean_object* v_r_2309_; 
v_res_2308_ = l_List_isPerm(v_00_u03b1_2304_, v_inst_2305_, v_x_2306_, v_x_2307_);
v_r_2309_ = lean_box(v_res_2308_);
return v_r_2309_;
}
}
LEAN_EXPORT uint8_t l_List_any___redArg(lean_object* v_x_2310_, lean_object* v_x_2311_){
_start:
{
if (lean_obj_tag(v_x_2310_) == 0)
{
uint8_t v___x_2312_; 
lean_dec_ref(v_x_2311_);
v___x_2312_ = 0;
return v___x_2312_;
}
else
{
lean_object* v_head_2313_; lean_object* v_tail_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v_head_2313_ = lean_ctor_get(v_x_2310_, 0);
lean_inc(v_head_2313_);
v_tail_2314_ = lean_ctor_get(v_x_2310_, 1);
lean_inc(v_tail_2314_);
lean_dec_ref_known(v_x_2310_, 2);
lean_inc_ref(v_x_2311_);
v___x_2315_ = lean_apply_1(v_x_2311_, v_head_2313_);
v___x_2316_ = lean_unbox(v___x_2315_);
if (v___x_2316_ == 0)
{
v_x_2310_ = v_tail_2314_;
goto _start;
}
else
{
uint8_t v___x_2318_; 
lean_dec(v_tail_2314_);
lean_dec_ref(v_x_2311_);
v___x_2318_ = lean_unbox(v___x_2315_);
return v___x_2318_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___redArg___boxed(lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
uint8_t v_res_2321_; lean_object* v_r_2322_; 
v_res_2321_ = l_List_any___redArg(v_x_2319_, v_x_2320_);
v_r_2322_ = lean_box(v_res_2321_);
return v_r_2322_;
}
}
LEAN_EXPORT uint8_t l_List_any(lean_object* v_00_u03b1_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_){
_start:
{
uint8_t v___x_2326_; 
v___x_2326_ = l_List_any___redArg(v_x_2324_, v_x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_List_any___boxed(lean_object* v_00_u03b1_2327_, lean_object* v_x_2328_, lean_object* v_x_2329_){
_start:
{
uint8_t v_res_2330_; lean_object* v_r_2331_; 
v_res_2330_ = l_List_any(v_00_u03b1_2327_, v_x_2328_, v_x_2329_);
v_r_2331_ = lean_box(v_res_2330_);
return v_r_2331_;
}
}
LEAN_EXPORT uint8_t l_List_all___redArg(lean_object* v_x_2332_, lean_object* v_x_2333_){
_start:
{
if (lean_obj_tag(v_x_2332_) == 0)
{
uint8_t v___x_2334_; 
lean_dec_ref(v_x_2333_);
v___x_2334_ = 1;
return v___x_2334_;
}
else
{
lean_object* v_head_2335_; lean_object* v_tail_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v_head_2335_ = lean_ctor_get(v_x_2332_, 0);
lean_inc(v_head_2335_);
v_tail_2336_ = lean_ctor_get(v_x_2332_, 1);
lean_inc(v_tail_2336_);
lean_dec_ref_known(v_x_2332_, 2);
lean_inc_ref(v_x_2333_);
v___x_2337_ = lean_apply_1(v_x_2333_, v_head_2335_);
v___x_2338_ = lean_unbox(v___x_2337_);
if (v___x_2338_ == 0)
{
uint8_t v___x_2339_; 
lean_dec(v_tail_2336_);
lean_dec_ref(v_x_2333_);
v___x_2339_ = lean_unbox(v___x_2337_);
return v___x_2339_;
}
else
{
v_x_2332_ = v_tail_2336_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___redArg___boxed(lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
uint8_t v_res_2343_; lean_object* v_r_2344_; 
v_res_2343_ = l_List_all___redArg(v_x_2341_, v_x_2342_);
v_r_2344_ = lean_box(v_res_2343_);
return v_r_2344_;
}
}
LEAN_EXPORT uint8_t l_List_all(lean_object* v_00_u03b1_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
uint8_t v___x_2348_; 
v___x_2348_ = l_List_all___redArg(v_x_2346_, v_x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_List_all___boxed(lean_object* v_00_u03b1_2349_, lean_object* v_x_2350_, lean_object* v_x_2351_){
_start:
{
uint8_t v_res_2352_; lean_object* v_r_2353_; 
v_res_2352_ = l_List_all(v_00_u03b1_2349_, v_x_2350_, v_x_2351_);
v_r_2353_ = lean_box(v_res_2352_);
return v_r_2353_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_or_spec__0(lean_object* v_x_2354_){
_start:
{
if (lean_obj_tag(v_x_2354_) == 0)
{
uint8_t v___x_2355_; 
v___x_2355_ = 0;
return v___x_2355_;
}
else
{
lean_object* v_head_2356_; uint8_t v___x_2357_; 
v_head_2356_ = lean_ctor_get(v_x_2354_, 0);
v___x_2357_ = lean_unbox(v_head_2356_);
if (v___x_2357_ == 0)
{
lean_object* v_tail_2358_; 
v_tail_2358_ = lean_ctor_get(v_x_2354_, 1);
v_x_2354_ = v_tail_2358_;
goto _start;
}
else
{
uint8_t v___x_2360_; 
v___x_2360_ = lean_unbox(v_head_2356_);
return v___x_2360_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_or_spec__0___boxed(lean_object* v_x_2361_){
_start:
{
uint8_t v_res_2362_; lean_object* v_r_2363_; 
v_res_2362_ = l_List_any___at___00List_or_spec__0(v_x_2361_);
lean_dec(v_x_2361_);
v_r_2363_ = lean_box(v_res_2362_);
return v_r_2363_;
}
}
LEAN_EXPORT uint8_t l_List_or(lean_object* v_bs_2364_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = l_List_any___at___00List_or_spec__0(v_bs_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object* v_bs_2366_){
_start:
{
uint8_t v_res_2367_; lean_object* v_r_2368_; 
v_res_2367_ = l_List_or(v_bs_2366_);
lean_dec(v_bs_2366_);
v_r_2368_ = lean_box(v_res_2367_);
return v_r_2368_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00List_and_spec__0(lean_object* v_x_2369_){
_start:
{
if (lean_obj_tag(v_x_2369_) == 0)
{
uint8_t v___x_2370_; 
v___x_2370_ = 1;
return v___x_2370_;
}
else
{
lean_object* v_head_2371_; uint8_t v___x_2372_; 
v_head_2371_ = lean_ctor_get(v_x_2369_, 0);
v___x_2372_ = lean_unbox(v_head_2371_);
if (v___x_2372_ == 0)
{
uint8_t v___x_2373_; 
v___x_2373_ = lean_unbox(v_head_2371_);
return v___x_2373_;
}
else
{
lean_object* v_tail_2374_; 
v_tail_2374_ = lean_ctor_get(v_x_2369_, 1);
v_x_2369_ = v_tail_2374_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00List_and_spec__0___boxed(lean_object* v_x_2376_){
_start:
{
uint8_t v_res_2377_; lean_object* v_r_2378_; 
v_res_2377_ = l_List_all___at___00List_and_spec__0(v_x_2376_);
lean_dec(v_x_2376_);
v_r_2378_ = lean_box(v_res_2377_);
return v_r_2378_;
}
}
LEAN_EXPORT uint8_t l_List_and(lean_object* v_bs_2379_){
_start:
{
uint8_t v___x_2380_; 
v___x_2380_ = l_List_all___at___00List_and_spec__0(v_bs_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object* v_bs_2381_){
_start:
{
uint8_t v_res_2382_; lean_object* v_r_2383_; 
v_res_2382_ = l_List_and(v_bs_2381_);
lean_dec(v_bs_2381_);
v_r_2383_ = lean_box(v_res_2382_);
return v_r_2383_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___redArg(lean_object* v_f_2384_, lean_object* v_x_2385_, lean_object* v_x_2386_){
_start:
{
if (lean_obj_tag(v_x_2385_) == 0)
{
lean_object* v___x_2387_; 
lean_dec(v_x_2386_);
lean_dec(v_f_2384_);
v___x_2387_ = lean_box(0);
return v___x_2387_;
}
else
{
if (lean_obj_tag(v_x_2386_) == 0)
{
lean_object* v___x_2388_; 
lean_dec_ref_known(v_x_2385_, 2);
lean_dec(v_f_2384_);
v___x_2388_ = lean_box(0);
return v___x_2388_;
}
else
{
lean_object* v_head_2389_; lean_object* v_tail_2390_; lean_object* v_head_2391_; lean_object* v_tail_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2401_; 
v_head_2389_ = lean_ctor_get(v_x_2385_, 0);
lean_inc(v_head_2389_);
v_tail_2390_ = lean_ctor_get(v_x_2385_, 1);
lean_inc(v_tail_2390_);
lean_dec_ref_known(v_x_2385_, 2);
v_head_2391_ = lean_ctor_get(v_x_2386_, 0);
v_tail_2392_ = lean_ctor_get(v_x_2386_, 1);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_x_2386_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2394_ = v_x_2386_;
v_isShared_2395_ = v_isSharedCheck_2401_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_tail_2392_);
lean_inc(v_head_2391_);
lean_dec(v_x_2386_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2401_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
lean_inc(v_f_2384_);
v___x_2396_ = lean_apply_2(v_f_2384_, v_head_2389_, v_head_2391_);
v___x_2397_ = l_List_zipWith___redArg(v_f_2384_, v_tail_2390_, v_tail_2392_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 1, v___x_2397_);
lean_ctor_set(v___x_2394_, 0, v___x_2396_);
v___x_2399_ = v___x_2394_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith(lean_object* v_00_u03b1_2402_, lean_object* v_00_u03b2_2403_, lean_object* v_00_u03b3_2404_, lean_object* v_f_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_List_zipWith___redArg(v_f_2405_, v_x_2406_, v_x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object* v_x_2409_, lean_object* v_x_2410_, lean_object* v_h__1_2411_, lean_object* v_h__2_2412_){
_start:
{
if (lean_obj_tag(v_x_2409_) == 0)
{
lean_object* v___x_2413_; 
lean_dec(v_h__1_2411_);
v___x_2413_ = lean_apply_3(v_h__2_2412_, v_x_2409_, v_x_2410_, lean_box(0));
return v___x_2413_;
}
else
{
if (lean_obj_tag(v_x_2410_) == 0)
{
lean_object* v___x_2414_; 
lean_dec(v_h__1_2411_);
v___x_2414_ = lean_apply_3(v_h__2_2412_, v_x_2409_, v_x_2410_, lean_box(0));
return v___x_2414_;
}
else
{
lean_object* v_head_2415_; lean_object* v_tail_2416_; lean_object* v_head_2417_; lean_object* v_tail_2418_; lean_object* v___x_2419_; 
lean_dec(v_h__2_2412_);
v_head_2415_ = lean_ctor_get(v_x_2409_, 0);
lean_inc(v_head_2415_);
v_tail_2416_ = lean_ctor_get(v_x_2409_, 1);
lean_inc(v_tail_2416_);
lean_dec_ref_known(v_x_2409_, 2);
v_head_2417_ = lean_ctor_get(v_x_2410_, 0);
lean_inc(v_head_2417_);
v_tail_2418_ = lean_ctor_get(v_x_2410_, 1);
lean_inc(v_tail_2418_);
lean_dec_ref_known(v_x_2410_, 2);
v___x_2419_ = lean_apply_4(v_h__1_2411_, v_head_2415_, v_tail_2416_, v_head_2417_, v_tail_2418_);
return v___x_2419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object* v_00_u03b1_2420_, lean_object* v_00_u03b2_2421_, lean_object* v_motive_2422_, lean_object* v_x_2423_, lean_object* v_x_2424_, lean_object* v_h__1_2425_, lean_object* v_h__2_2426_){
_start:
{
if (lean_obj_tag(v_x_2423_) == 0)
{
lean_object* v___x_2427_; 
lean_dec(v_h__1_2425_);
v___x_2427_ = lean_apply_3(v_h__2_2426_, v_x_2423_, v_x_2424_, lean_box(0));
return v___x_2427_;
}
else
{
if (lean_obj_tag(v_x_2424_) == 0)
{
lean_object* v___x_2428_; 
lean_dec(v_h__1_2425_);
v___x_2428_ = lean_apply_3(v_h__2_2426_, v_x_2423_, v_x_2424_, lean_box(0));
return v___x_2428_;
}
else
{
lean_object* v_head_2429_; lean_object* v_tail_2430_; lean_object* v_head_2431_; lean_object* v_tail_2432_; lean_object* v___x_2433_; 
lean_dec(v_h__2_2426_);
v_head_2429_ = lean_ctor_get(v_x_2423_, 0);
lean_inc(v_head_2429_);
v_tail_2430_ = lean_ctor_get(v_x_2423_, 1);
lean_inc(v_tail_2430_);
lean_dec_ref_known(v_x_2423_, 2);
v_head_2431_ = lean_ctor_get(v_x_2424_, 0);
lean_inc(v_head_2431_);
v_tail_2432_ = lean_ctor_get(v_x_2424_, 1);
lean_inc(v_tail_2432_);
lean_dec_ref_known(v_x_2424_, 2);
v___x_2433_ = lean_apply_4(v_h__1_2425_, v_head_2429_, v_tail_2430_, v_head_2431_, v_tail_2432_);
return v___x_2433_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object* v_x_2434_, lean_object* v_x_2435_){
_start:
{
if (lean_obj_tag(v_x_2434_) == 0)
{
lean_object* v___x_2436_; 
lean_dec(v_x_2435_);
v___x_2436_ = lean_box(0);
return v___x_2436_;
}
else
{
if (lean_obj_tag(v_x_2435_) == 0)
{
lean_object* v___x_2437_; 
lean_dec_ref_known(v_x_2434_, 2);
v___x_2437_ = lean_box(0);
return v___x_2437_;
}
else
{
lean_object* v_head_2438_; lean_object* v_tail_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2456_; 
v_head_2438_ = lean_ctor_get(v_x_2434_, 0);
v_tail_2439_ = lean_ctor_get(v_x_2434_, 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_x_2434_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2441_ = v_x_2434_;
v_isShared_2442_ = v_isSharedCheck_2456_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_tail_2439_);
lean_inc(v_head_2438_);
lean_dec(v_x_2434_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2456_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v_head_2443_; lean_object* v_tail_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2455_; 
v_head_2443_ = lean_ctor_get(v_x_2435_, 0);
v_tail_2444_ = lean_ctor_get(v_x_2435_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_x_2435_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2446_ = v_x_2435_;
v_isShared_2447_ = v_isSharedCheck_2455_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_tail_2444_);
lean_inc(v_head_2443_);
lean_dec(v_x_2435_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2455_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set_tag(v___x_2441_, 0);
lean_ctor_set(v___x_2441_, 1, v_head_2443_);
v___x_2449_ = v___x_2441_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_head_2438_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_head_2443_);
v___x_2449_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_tail_2439_, v_tail_2444_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 1, v___x_2450_);
lean_ctor_set(v___x_2446_, 0, v___x_2449_);
v___x_2452_ = v___x_2446_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zip___redArg(lean_object* v_xs_2457_, lean_object* v_ys_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2457_, v_ys_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_List_zip(lean_object* v_00_u03b1_2460_, lean_object* v_00_u03b2_2461_, lean_object* v_xs_2462_, lean_object* v_ys_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2462_, v_ys_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object* v_00_u03b1_2465_, lean_object* v_00_u03b2_2466_, lean_object* v_x_2467_, lean_object* v_x_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_x_2467_, v_x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__0(lean_object* v_f_2470_, lean_object* v_b_2471_){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2472_ = lean_box(0);
v___x_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_b_2471_);
v___x_2474_ = lean_apply_2(v_f_2470_, v___x_2472_, v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__1(lean_object* v_f_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2477_, 0, v_a_2476_);
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_apply_2(v_f_2475_, v___x_2477_, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object* v_f_2480_, lean_object* v_x_2481_, lean_object* v_x_2482_){
_start:
{
if (lean_obj_tag(v_x_2481_) == 0)
{
lean_object* v___f_2483_; lean_object* v___x_2484_; 
v___f_2483_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2483_, 0, v_f_2480_);
v___x_2484_ = l_List_map___redArg(v___f_2483_, v_x_2482_);
return v___x_2484_;
}
else
{
if (lean_obj_tag(v_x_2482_) == 0)
{
lean_object* v___f_2485_; lean_object* v___x_2486_; 
v___f_2485_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2485_, 0, v_f_2480_);
v___x_2486_ = l_List_map___redArg(v___f_2485_, v_x_2481_);
return v___x_2486_;
}
else
{
lean_object* v_head_2487_; lean_object* v_tail_2488_; lean_object* v_head_2489_; lean_object* v_tail_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2501_; 
v_head_2487_ = lean_ctor_get(v_x_2481_, 0);
lean_inc(v_head_2487_);
v_tail_2488_ = lean_ctor_get(v_x_2481_, 1);
lean_inc(v_tail_2488_);
lean_dec_ref_known(v_x_2481_, 2);
v_head_2489_ = lean_ctor_get(v_x_2482_, 0);
v_tail_2490_ = lean_ctor_get(v_x_2482_, 1);
v_isSharedCheck_2501_ = !lean_is_exclusive(v_x_2482_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2492_ = v_x_2482_;
v_isShared_2493_ = v_isSharedCheck_2501_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_tail_2490_);
lean_inc(v_head_2489_);
lean_dec(v_x_2482_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2501_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v_head_2487_);
v___x_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2495_, 0, v_head_2489_);
lean_inc(v_f_2480_);
v___x_2496_ = lean_apply_2(v_f_2480_, v___x_2494_, v___x_2495_);
v___x_2497_ = l_List_zipWithAll___redArg(v_f_2480_, v_tail_2488_, v_tail_2490_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 1, v___x_2497_);
lean_ctor_set(v___x_2492_, 0, v___x_2496_);
v___x_2499_ = v___x_2492_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object* v_00_u03b1_2502_, lean_object* v_00_u03b2_2503_, lean_object* v_00_u03b3_2504_, lean_object* v_f_2505_, lean_object* v_x_2506_, lean_object* v_x_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_List_zipWithAll___redArg(v_f_2505_, v_x_2506_, v_x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_List_unzip___redArg(lean_object* v_x_2509_){
_start:
{
if (lean_obj_tag(v_x_2509_) == 0)
{
lean_object* v___x_2510_; 
v___x_2510_ = ((lean_object*)(l_List_partition___redArg___closed__0));
return v___x_2510_;
}
else
{
lean_object* v_head_2511_; lean_object* v_tail_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2538_; 
v_head_2511_ = lean_ctor_get(v_x_2509_, 0);
v_tail_2512_ = lean_ctor_get(v_x_2509_, 1);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2514_ = v_x_2509_;
v_isShared_2515_ = v_isSharedCheck_2538_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_tail_2512_);
lean_inc(v_head_2511_);
lean_dec(v_x_2509_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2538_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v_fst_2516_; lean_object* v_snd_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2537_; 
v_fst_2516_ = lean_ctor_get(v_head_2511_, 0);
v_snd_2517_ = lean_ctor_get(v_head_2511_, 1);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_head_2511_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2519_ = v_head_2511_;
v_isShared_2520_ = v_isSharedCheck_2537_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_snd_2517_);
lean_inc(v_fst_2516_);
lean_dec(v_head_2511_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2537_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v_fst_2522_; lean_object* v_snd_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2536_; 
v___x_2521_ = l_List_unzip___redArg(v_tail_2512_);
v_fst_2522_ = lean_ctor_get(v___x_2521_, 0);
v_snd_2523_ = lean_ctor_get(v___x_2521_, 1);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2525_ = v___x_2521_;
v_isShared_2526_ = v_isSharedCheck_2536_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_snd_2523_);
lean_inc(v_fst_2522_);
lean_dec(v___x_2521_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2536_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 1, v_fst_2522_);
lean_ctor_set(v___x_2514_, 0, v_fst_2516_);
v___x_2528_ = v___x_2514_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_fst_2516_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_fst_2522_);
v___x_2528_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2530_; 
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 1);
lean_ctor_set(v___x_2519_, 1, v_snd_2523_);
lean_ctor_set(v___x_2519_, 0, v_snd_2517_);
v___x_2530_ = v___x_2519_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_snd_2517_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_snd_2523_);
v___x_2530_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2532_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 1, v___x_2530_);
lean_ctor_set(v___x_2525_, 0, v___x_2528_);
v___x_2532_ = v___x_2525_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_unzip(lean_object* v_00_u03b1_2539_, lean_object* v_00_u03b2_2540_, lean_object* v_x_2541_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_List_unzip___redArg(v_x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___lam__0(lean_object* v_inst_2543_, lean_object* v_x1_2544_, lean_object* v_x2_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_apply_2(v_inst_2543_, v_x1_2544_, v_x2_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg(lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_l_2549_){
_start:
{
lean_object* v___f_2550_; lean_object* v___x_2551_; 
v___f_2550_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2550_, 0, v_inst_2547_);
v___x_2551_ = l_List_foldr___redArg(v___f_2550_, v_inst_2548_, v_l_2549_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___boxed(lean_object* v_inst_2552_, lean_object* v_inst_2553_, lean_object* v_l_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_List_sum___redArg(v_inst_2552_, v_inst_2553_, v_l_2554_);
lean_dec(v_inst_2553_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_List_sum(lean_object* v_00_u03b1_2556_, lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_l_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_List_sum___redArg(v_inst_2557_, v_inst_2558_, v_l_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_List_sum___boxed(lean_object* v_00_u03b1_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_l_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_List_sum(v_00_u03b1_2561_, v_inst_2562_, v_inst_2563_, v_l_2564_);
lean_dec(v_inst_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg(lean_object* v_inst_2566_, lean_object* v_inst_2567_, lean_object* v_l_2568_){
_start:
{
lean_object* v___f_2569_; lean_object* v___x_2570_; 
v___f_2569_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2569_, 0, v_inst_2566_);
v___x_2570_ = l_List_foldr___redArg(v___f_2569_, v_inst_2567_, v_l_2568_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg___boxed(lean_object* v_inst_2571_, lean_object* v_inst_2572_, lean_object* v_l_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_List_prod___redArg(v_inst_2571_, v_inst_2572_, v_l_2573_);
lean_dec(v_inst_2572_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_List_prod(lean_object* v_00_u03b1_2575_, lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_l_2578_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_List_prod___redArg(v_inst_2576_, v_inst_2577_, v_l_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_List_prod___boxed(lean_object* v_00_u03b1_2580_, lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_l_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_List_prod(v_00_u03b1_2580_, v_inst_2581_, v_inst_2582_, v_l_2583_);
lean_dec(v_inst_2582_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_List_range_loop(lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_zero_2587_; uint8_t v_isZero_2588_; 
v_zero_2587_ = lean_unsigned_to_nat(0u);
v_isZero_2588_ = lean_nat_dec_eq(v_a_2585_, v_zero_2587_);
if (v_isZero_2588_ == 1)
{
lean_dec(v_a_2585_);
return v_a_2586_;
}
else
{
lean_object* v_one_2589_; lean_object* v_n_2590_; lean_object* v___x_2591_; 
v_one_2589_ = lean_unsigned_to_nat(1u);
v_n_2590_ = lean_nat_sub(v_a_2585_, v_one_2589_);
lean_dec(v_a_2585_);
lean_inc(v_n_2590_);
v___x_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_n_2590_);
lean_ctor_set(v___x_2591_, 1, v_a_2586_);
v_a_2585_ = v_n_2590_;
v_a_2586_ = v___x_2591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range(lean_object* v_n_2593_){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_box(0);
v___x_2595_ = l_List_range_loop(v_n_2593_, v___x_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27(lean_object* v_x_2596_, lean_object* v_x_2597_, lean_object* v_x_2598_){
_start:
{
lean_object* v_zero_2599_; uint8_t v_isZero_2600_; 
v_zero_2599_ = lean_unsigned_to_nat(0u);
v_isZero_2600_ = lean_nat_dec_eq(v_x_2597_, v_zero_2599_);
if (v_isZero_2600_ == 1)
{
lean_object* v___x_2601_; 
lean_dec(v_x_2596_);
v___x_2601_ = lean_box(0);
return v___x_2601_;
}
else
{
lean_object* v_one_2602_; lean_object* v_n_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_one_2602_ = lean_unsigned_to_nat(1u);
v_n_2603_ = lean_nat_sub(v_x_2597_, v_one_2602_);
v___x_2604_ = lean_nat_add(v_x_2596_, v_x_2598_);
v___x_2605_ = l_List_range_x27(v___x_2604_, v_n_2603_, v_x_2598_);
lean_dec(v_n_2603_);
v___x_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2606_, 0, v_x_2596_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
return v___x_2606_;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object* v_x_2607_, lean_object* v_x_2608_, lean_object* v_x_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_List_range_x27(v_x_2607_, v_x_2608_, v_x_2609_);
lean_dec(v_x_2609_);
lean_dec(v_x_2608_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdx___redArg(lean_object* v_x_2611_, lean_object* v_x_2612_){
_start:
{
if (lean_obj_tag(v_x_2611_) == 0)
{
lean_object* v___x_2613_; 
lean_dec(v_x_2612_);
v___x_2613_ = lean_box(0);
return v___x_2613_;
}
else
{
lean_object* v_head_2614_; lean_object* v_tail_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2626_; 
v_head_2614_ = lean_ctor_get(v_x_2611_, 0);
v_tail_2615_ = lean_ctor_get(v_x_2611_, 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_x_2611_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2617_ = v_x_2611_;
v_isShared_2618_ = v_isSharedCheck_2626_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_tail_2615_);
lean_inc(v_head_2614_);
lean_dec(v_x_2611_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2626_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
lean_inc(v_x_2612_);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v_head_2614_);
lean_ctor_set(v___x_2619_, 1, v_x_2612_);
v___x_2620_ = lean_unsigned_to_nat(1u);
v___x_2621_ = lean_nat_add(v_x_2612_, v___x_2620_);
lean_dec(v_x_2612_);
v___x_2622_ = l_List_zipIdx___redArg(v_tail_2615_, v___x_2621_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 1, v___x_2622_);
lean_ctor_set(v___x_2617_, 0, v___x_2619_);
v___x_2624_ = v___x_2617_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdx(lean_object* v_00_u03b1_2627_, lean_object* v_x_2628_, lean_object* v_x_2629_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_List_zipIdx___redArg(v_x_2628_, v_x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object* v_inst_2631_, lean_object* v_x_2632_){
_start:
{
if (lean_obj_tag(v_x_2632_) == 0)
{
lean_object* v___x_2633_; 
lean_dec(v_inst_2631_);
v___x_2633_ = lean_box(0);
return v___x_2633_;
}
else
{
lean_object* v_head_2634_; lean_object* v_tail_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_head_2634_ = lean_ctor_get(v_x_2632_, 0);
lean_inc(v_head_2634_);
v_tail_2635_ = lean_ctor_get(v_x_2632_, 1);
lean_inc(v_tail_2635_);
lean_dec_ref_known(v_x_2632_, 2);
v___x_2636_ = l_List_foldl___redArg(v_inst_2631_, v_head_2634_, v_tail_2635_);
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
return v___x_2637_;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object* v_00_u03b1_2638_, lean_object* v_inst_2639_, lean_object* v_x_2640_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_List_min_x3f___redArg(v_inst_2639_, v_x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object* v_inst_2642_, lean_object* v_x_2643_){
_start:
{
lean_object* v_head_2644_; lean_object* v_tail_2645_; lean_object* v___x_2646_; 
v_head_2644_ = lean_ctor_get(v_x_2643_, 0);
lean_inc(v_head_2644_);
v_tail_2645_ = lean_ctor_get(v_x_2643_, 1);
lean_inc(v_tail_2645_);
lean_dec(v_x_2643_);
v___x_2646_ = l_List_foldl___redArg(v_inst_2642_, v_head_2644_, v_tail_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_List_min(lean_object* v_00_u03b1_2647_, lean_object* v_inst_2648_, lean_object* v_x_2649_, lean_object* v_x_2650_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_List_min___redArg(v_inst_2648_, v_x_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object* v_inst_2652_, lean_object* v_x_2653_){
_start:
{
if (lean_obj_tag(v_x_2653_) == 0)
{
lean_object* v___x_2654_; 
lean_dec(v_inst_2652_);
v___x_2654_ = lean_box(0);
return v___x_2654_;
}
else
{
lean_object* v_head_2655_; lean_object* v_tail_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_head_2655_ = lean_ctor_get(v_x_2653_, 0);
lean_inc(v_head_2655_);
v_tail_2656_ = lean_ctor_get(v_x_2653_, 1);
lean_inc(v_tail_2656_);
lean_dec_ref_known(v_x_2653_, 2);
v___x_2657_ = l_List_foldl___redArg(v_inst_2652_, v_head_2655_, v_tail_2656_);
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
return v___x_2658_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object* v_00_u03b1_2659_, lean_object* v_inst_2660_, lean_object* v_x_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_List_max_x3f___redArg(v_inst_2660_, v_x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object* v_inst_2663_, lean_object* v_x_2664_){
_start:
{
lean_object* v_head_2665_; lean_object* v_tail_2666_; lean_object* v___x_2667_; 
v_head_2665_ = lean_ctor_get(v_x_2664_, 0);
lean_inc(v_head_2665_);
v_tail_2666_ = lean_ctor_get(v_x_2664_, 1);
lean_inc(v_tail_2666_);
lean_dec(v_x_2664_);
v___x_2667_ = l_List_foldl___redArg(v_inst_2663_, v_head_2665_, v_tail_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_List_max(lean_object* v_00_u03b1_2668_, lean_object* v_inst_2669_, lean_object* v_x_2670_, lean_object* v_x_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_List_max___redArg(v_inst_2669_, v_x_2670_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_List_intersperse___redArg(lean_object* v_sep_2673_, lean_object* v_x_2674_){
_start:
{
if (lean_obj_tag(v_x_2674_) == 0)
{
lean_dec(v_sep_2673_);
return v_x_2674_;
}
else
{
lean_object* v_tail_2675_; 
v_tail_2675_ = lean_ctor_get(v_x_2674_, 1);
if (lean_obj_tag(v_tail_2675_) == 0)
{
lean_dec(v_sep_2673_);
return v_x_2674_;
}
else
{
lean_object* v_head_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2685_; 
lean_inc_ref(v_tail_2675_);
v_head_2676_ = lean_ctor_get(v_x_2674_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_x_2674_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v_x_2674_, 1);
lean_dec(v_unused_2686_);
v___x_2678_ = v_x_2674_;
v_isShared_2679_ = v_isSharedCheck_2685_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_head_2676_);
lean_dec(v_x_2674_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2685_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_inc(v_sep_2673_);
v___x_2680_ = l_List_intersperse___redArg(v_sep_2673_, v_tail_2675_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2680_);
lean_ctor_set(v___x_2678_, 0, v_sep_2673_);
v___x_2682_ = v___x_2678_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_sep_2673_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_head_2676_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
return v___x_2683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperse(lean_object* v_00_u03b1_2687_, lean_object* v_sep_2688_, lean_object* v_x_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_List_intersperse___redArg(v_sep_2688_, v_x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(lean_object* v___x_2691_, lean_object* v_x_2692_){
_start:
{
if (lean_obj_tag(v_x_2692_) == 0)
{
uint8_t v___x_2693_; 
lean_dec_ref(v___x_2691_);
v___x_2693_ = 0;
return v___x_2693_;
}
else
{
lean_object* v_head_2694_; lean_object* v_tail_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_head_2694_ = lean_ctor_get(v_x_2692_, 0);
lean_inc(v_head_2694_);
v_tail_2695_ = lean_ctor_get(v_x_2692_, 1);
lean_inc(v_tail_2695_);
lean_dec_ref_known(v_x_2692_, 2);
lean_inc_ref(v___x_2691_);
v___x_2696_ = lean_apply_1(v___x_2691_, v_head_2694_);
v___x_2697_ = lean_unbox(v___x_2696_);
if (v___x_2697_ == 0)
{
v_x_2692_ = v_tail_2695_;
goto _start;
}
else
{
uint8_t v___x_2699_; 
lean_dec(v_tail_2695_);
lean_dec_ref(v___x_2691_);
v___x_2699_ = lean_unbox(v___x_2696_);
return v___x_2699_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg___boxed(lean_object* v___x_2700_, lean_object* v_x_2701_){
_start:
{
uint8_t v_res_2702_; lean_object* v_r_2703_; 
v_res_2702_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2700_, v_x_2701_);
v_r_2703_ = lean_box(v_res_2702_);
return v_r_2703_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object* v_r_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
if (lean_obj_tag(v_a_2705_) == 0)
{
lean_object* v___x_2707_; 
lean_dec_ref(v_r_2704_);
v___x_2707_ = l_List_reverse___redArg(v_a_2706_);
return v___x_2707_;
}
else
{
lean_object* v_head_2708_; lean_object* v_tail_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2720_; 
v_head_2708_ = lean_ctor_get(v_a_2705_, 0);
v_tail_2709_ = lean_ctor_get(v_a_2705_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_a_2705_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2711_ = v_a_2705_;
v_isShared_2712_ = v_isSharedCheck_2720_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_tail_2709_);
lean_inc(v_head_2708_);
lean_dec(v_a_2705_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2720_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; 
lean_inc_ref(v_r_2704_);
lean_inc(v_head_2708_);
v___x_2713_ = lean_apply_1(v_r_2704_, v_head_2708_);
lean_inc(v_a_2706_);
v___x_2714_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2713_, v_a_2706_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2716_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v_a_2706_);
v___x_2716_ = v___x_2711_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_head_2708_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_a_2706_);
v___x_2716_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
v_a_2705_ = v_tail_2709_;
v_a_2706_ = v___x_2716_;
goto _start;
}
}
else
{
lean_del_object(v___x_2711_);
lean_dec(v_head_2708_);
v_a_2705_ = v_tail_2709_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object* v_00_u03b1_2721_, lean_object* v_r_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_List_eraseDupsBy_loop___redArg(v_r_2722_, v_a_2723_, v_a_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0(lean_object* v_00_u03b1_2726_, lean_object* v___x_2727_, lean_object* v_x_2728_){
_start:
{
uint8_t v___x_2729_; 
v___x_2729_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2727_, v_x_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___boxed(lean_object* v_00_u03b1_2730_, lean_object* v___x_2731_, lean_object* v_x_2732_){
_start:
{
uint8_t v_res_2733_; lean_object* v_r_2734_; 
v_res_2733_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0(v_00_u03b1_2730_, v___x_2731_, v_x_2732_);
v_r_2734_ = lean_box(v_res_2733_);
return v_r_2734_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy___redArg(lean_object* v_r_2735_, lean_object* v_as_2736_){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_box(0);
v___x_2738_ = l_List_eraseDupsBy_loop___redArg(v_r_2735_, v_as_2736_, v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy(lean_object* v_00_u03b1_2739_, lean_object* v_r_2740_, lean_object* v_as_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_List_eraseDupsBy___redArg(v_r_2740_, v_as_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT uint8_t l_List_eraseDups___redArg___lam__0(lean_object* v_inst_2743_, lean_object* v_x1_2744_, lean_object* v_x2_2745_){
_start:
{
lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2746_ = lean_apply_2(v_inst_2743_, v_x1_2744_, v_x2_2745_);
v___x_2747_ = lean_unbox(v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg___lam__0___boxed(lean_object* v_inst_2748_, lean_object* v_x1_2749_, lean_object* v_x2_2750_){
_start:
{
uint8_t v_res_2751_; lean_object* v_r_2752_; 
v_res_2751_ = l_List_eraseDups___redArg___lam__0(v_inst_2748_, v_x1_2749_, v_x2_2750_);
v_r_2752_ = lean_box(v_res_2751_);
return v_r_2752_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg(lean_object* v_inst_2753_, lean_object* v_as_2754_){
_start:
{
lean_object* v___f_2755_; lean_object* v___x_2756_; 
v___f_2755_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2755_, 0, v_inst_2753_);
v___x_2756_ = l_List_eraseDupsBy___redArg(v___f_2755_, v_as_2754_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object* v_00_u03b1_2757_, lean_object* v_inst_2758_, lean_object* v_as_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_List_eraseDups___redArg(v_inst_2758_, v_as_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop___redArg(lean_object* v_r_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
if (lean_obj_tag(v_a_2763_) == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec_ref(v_r_2761_);
v___x_2765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2765_, 0, v_a_2762_);
lean_ctor_set(v___x_2765_, 1, v_a_2764_);
v___x_2766_ = l_List_reverse___redArg(v___x_2765_);
return v___x_2766_;
}
else
{
lean_object* v_head_2767_; lean_object* v_tail_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2779_; 
v_head_2767_ = lean_ctor_get(v_a_2763_, 0);
v_tail_2768_ = lean_ctor_get(v_a_2763_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_a_2763_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2770_ = v_a_2763_;
v_isShared_2771_ = v_isSharedCheck_2779_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_tail_2768_);
lean_inc(v_head_2767_);
lean_dec(v_a_2763_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2779_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; uint8_t v___x_2773_; 
lean_inc_ref(v_r_2761_);
lean_inc(v_head_2767_);
lean_inc(v_a_2762_);
v___x_2772_ = lean_apply_2(v_r_2761_, v_a_2762_, v_head_2767_);
v___x_2773_ = lean_unbox(v___x_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2775_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 1, v_a_2764_);
lean_ctor_set(v___x_2770_, 0, v_a_2762_);
v___x_2775_ = v___x_2770_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2762_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_a_2764_);
v___x_2775_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
v_a_2762_ = v_head_2767_;
v_a_2763_ = v_tail_2768_;
v_a_2764_ = v___x_2775_;
goto _start;
}
}
else
{
lean_del_object(v___x_2770_);
lean_dec(v_head_2767_);
v_a_2763_ = v_tail_2768_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop(lean_object* v_00_u03b1_2780_, lean_object* v_r_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_List_eraseRepsBy_loop___redArg(v_r_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy___redArg(lean_object* v_r_2786_, lean_object* v_x_2787_){
_start:
{
if (lean_obj_tag(v_x_2787_) == 0)
{
lean_dec_ref(v_r_2786_);
return v_x_2787_;
}
else
{
lean_object* v_head_2788_; lean_object* v_tail_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_head_2788_ = lean_ctor_get(v_x_2787_, 0);
lean_inc(v_head_2788_);
v_tail_2789_ = lean_ctor_get(v_x_2787_, 1);
lean_inc(v_tail_2789_);
lean_dec_ref_known(v_x_2787_, 2);
v___x_2790_ = lean_box(0);
v___x_2791_ = l_List_eraseRepsBy_loop___redArg(v_r_2786_, v_head_2788_, v_tail_2789_, v___x_2790_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy(lean_object* v_00_u03b1_2792_, lean_object* v_r_2793_, lean_object* v_x_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_List_eraseRepsBy___redArg(v_r_2793_, v_x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___redArg(lean_object* v_inst_2796_, lean_object* v_as_2797_){
_start:
{
lean_object* v___f_2798_; lean_object* v___x_2799_; 
v___f_2798_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2798_, 0, v_inst_2796_);
v___x_2799_ = l_List_eraseRepsBy___redArg(v___f_2798_, v_as_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object* v_00_u03b1_2800_, lean_object* v_inst_2801_, lean_object* v_as_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_List_eraseReps___redArg(v_inst_2801_, v_as_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___redArg(lean_object* v_p_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
if (lean_obj_tag(v_a_2805_) == 0)
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
lean_dec_ref(v_p_2804_);
v___x_2807_ = l_List_reverse___redArg(v_a_2806_);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
lean_ctor_set(v___x_2808_, 1, v_a_2805_);
return v___x_2808_;
}
else
{
lean_object* v_head_2809_; lean_object* v_tail_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v_head_2809_ = lean_ctor_get(v_a_2805_, 0);
v_tail_2810_ = lean_ctor_get(v_a_2805_, 1);
lean_inc_ref(v_p_2804_);
lean_inc(v_head_2809_);
v___x_2811_ = lean_apply_1(v_p_2804_, v_head_2809_);
v___x_2812_ = lean_unbox(v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_dec_ref(v_p_2804_);
v___x_2813_ = l_List_reverse___redArg(v_a_2806_);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v_a_2805_);
return v___x_2814_;
}
else
{
lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2822_; 
lean_inc(v_tail_2810_);
lean_inc(v_head_2809_);
v_isSharedCheck_2822_ = !lean_is_exclusive(v_a_2805_);
if (v_isSharedCheck_2822_ == 0)
{
lean_object* v_unused_2823_; lean_object* v_unused_2824_; 
v_unused_2823_ = lean_ctor_get(v_a_2805_, 1);
lean_dec(v_unused_2823_);
v_unused_2824_ = lean_ctor_get(v_a_2805_, 0);
lean_dec(v_unused_2824_);
v___x_2816_ = v_a_2805_;
v_isShared_2817_ = v_isSharedCheck_2822_;
goto v_resetjp_2815_;
}
else
{
lean_dec(v_a_2805_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2822_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 1, v_a_2806_);
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_head_2809_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_a_2806_);
v___x_2819_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
v_a_2805_ = v_tail_2810_;
v_a_2806_ = v___x_2819_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop(lean_object* v_00_u03b1_2825_, lean_object* v_p_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_List_span_loop___redArg(v_p_2826_, v_a_2827_, v_a_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_List_span___redArg(lean_object* v_p_2830_, lean_object* v_as_2831_){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_box(0);
v___x_2833_ = l_List_span_loop___redArg(v_p_2830_, v_as_2831_, v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_List_span(lean_object* v_00_u03b1_2834_, lean_object* v_p_2835_, lean_object* v_as_2836_){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_box(0);
v___x_2838_ = l_List_span_loop___redArg(v_p_2835_, v_as_2836_, v___x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___redArg(lean_object* v_R_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
if (lean_obj_tag(v_a_2840_) == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v_R_2839_);
v___x_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2844_, 0, v_a_2841_);
lean_ctor_set(v___x_2844_, 1, v_a_2842_);
v___x_2845_ = l_List_reverse___redArg(v___x_2844_);
v___x_2846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
lean_ctor_set(v___x_2846_, 1, v_a_2843_);
v___x_2847_ = l_List_reverse___redArg(v___x_2846_);
return v___x_2847_;
}
else
{
lean_object* v_head_2848_; lean_object* v_tail_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2866_; 
v_head_2848_ = lean_ctor_get(v_a_2840_, 0);
v_tail_2849_ = lean_ctor_get(v_a_2840_, 1);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_a_2840_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2851_ = v_a_2840_;
v_isShared_2852_ = v_isSharedCheck_2866_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_tail_2849_);
lean_inc(v_head_2848_);
lean_dec(v_a_2840_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2866_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; uint8_t v___x_2854_; 
lean_inc_ref(v_R_2839_);
lean_inc(v_head_2848_);
lean_inc(v_a_2841_);
v___x_2853_ = lean_apply_2(v_R_2839_, v_a_2841_, v_head_2848_);
v___x_2854_ = lean_unbox(v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2855_ = lean_box(0);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_a_2842_);
lean_ctor_set(v___x_2851_, 0, v_a_2841_);
v___x_2857_ = v___x_2851_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2841_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_a_2842_);
v___x_2857_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = l_List_reverse___redArg(v___x_2857_);
v___x_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v_a_2843_);
v_a_2840_ = v_tail_2849_;
v_a_2841_ = v_head_2848_;
v_a_2842_ = v___x_2855_;
v_a_2843_ = v___x_2859_;
goto _start;
}
}
else
{
lean_object* v___x_2863_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_a_2842_);
lean_ctor_set(v___x_2851_, 0, v_a_2841_);
v___x_2863_ = v___x_2851_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2841_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_a_2842_);
v___x_2863_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
v_a_2840_ = v_tail_2849_;
v_a_2841_ = v_head_2848_;
v_a_2842_ = v___x_2863_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop(lean_object* v_00_u03b1_2867_, lean_object* v_R_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_List_splitBy_loop___redArg(v_R_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___redArg(lean_object* v_R_2874_, lean_object* v_x_2875_){
_start:
{
if (lean_obj_tag(v_x_2875_) == 0)
{
lean_object* v___x_2876_; 
lean_dec_ref(v_R_2874_);
v___x_2876_ = lean_box(0);
return v___x_2876_;
}
else
{
lean_object* v_head_2877_; lean_object* v_tail_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_head_2877_ = lean_ctor_get(v_x_2875_, 0);
lean_inc(v_head_2877_);
v_tail_2878_ = lean_ctor_get(v_x_2875_, 1);
lean_inc(v_tail_2878_);
lean_dec_ref_known(v_x_2875_, 2);
v___x_2879_ = lean_box(0);
v___x_2880_ = l_List_splitBy_loop___redArg(v_R_2874_, v_tail_2878_, v_head_2877_, v___x_2879_, v___x_2879_);
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy(lean_object* v_00_u03b1_2881_, lean_object* v_R_2882_, lean_object* v_x_2883_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_List_splitBy___redArg(v_R_2882_, v_x_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___redArg___lam__0(lean_object* v_inst_2885_, lean_object* v_ys_2886_, lean_object* v_x_2887_){
_start:
{
uint8_t v___x_2888_; 
v___x_2888_ = l_List_elem___redArg(v_inst_2885_, v_x_2887_, v_ys_2886_);
if (v___x_2888_ == 0)
{
uint8_t v___x_2889_; 
v___x_2889_ = 1;
return v___x_2889_;
}
else
{
uint8_t v___x_2890_; 
v___x_2890_ = 0;
return v___x_2890_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg___lam__0___boxed(lean_object* v_inst_2891_, lean_object* v_ys_2892_, lean_object* v_x_2893_){
_start:
{
uint8_t v_res_2894_; lean_object* v_r_2895_; 
v_res_2894_ = l_List_removeAll___redArg___lam__0(v_inst_2891_, v_ys_2892_, v_x_2893_);
v_r_2895_ = lean_box(v_res_2894_);
return v_r_2895_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg(lean_object* v_inst_2896_, lean_object* v_xs_2897_, lean_object* v_ys_2898_){
_start:
{
lean_object* v___f_2899_; lean_object* v___x_2900_; 
v___f_2899_ = lean_alloc_closure((void*)(l_List_removeAll___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2899_, 0, v_inst_2896_);
lean_closure_set(v___f_2899_, 1, v_ys_2898_);
v___x_2900_ = l_List_filter___redArg(v___f_2899_, v_xs_2897_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll(lean_object* v_00_u03b1_2901_, lean_object* v_inst_2902_, lean_object* v_xs_2903_, lean_object* v_ys_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_List_removeAll___redArg(v_inst_2902_, v_xs_2903_, v_ys_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object* v_f_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
if (lean_obj_tag(v_a_2907_) == 0)
{
lean_object* v___x_2909_; 
lean_dec(v_f_2906_);
v___x_2909_ = l_List_reverse___redArg(v_a_2908_);
return v___x_2909_;
}
else
{
lean_object* v_head_2910_; lean_object* v_tail_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2920_; 
v_head_2910_ = lean_ctor_get(v_a_2907_, 0);
v_tail_2911_ = lean_ctor_get(v_a_2907_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_a_2907_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2913_ = v_a_2907_;
v_isShared_2914_ = v_isSharedCheck_2920_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_tail_2911_);
lean_inc(v_head_2910_);
lean_dec(v_a_2907_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2920_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
lean_inc(v_f_2906_);
v___x_2915_ = lean_apply_1(v_f_2906_, v_head_2910_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v_a_2908_);
lean_ctor_set(v___x_2913_, 0, v___x_2915_);
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_a_2908_);
v___x_2917_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
v_a_2907_ = v_tail_2911_;
v_a_2908_ = v___x_2917_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object* v_00_u03b1_2921_, lean_object* v_00_u03b2_2922_, lean_object* v_f_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_List_mapTR_loop___redArg(v_f_2923_, v_a_2924_, v_a_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object* v_f_2927_, lean_object* v_as_2928_){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = lean_box(0);
v___x_2930_ = l_List_mapTR_loop___redArg(v_f_2927_, v_as_2928_, v___x_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR(lean_object* v_00_u03b1_2931_, lean_object* v_00_u03b2_2932_, lean_object* v_f_2933_, lean_object* v_as_2934_){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_box(0);
v___x_2936_ = l_List_mapTR_loop___redArg(v_f_2933_, v_as_2934_, v___x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object* v_p_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_){
_start:
{
if (lean_obj_tag(v_a_2938_) == 0)
{
lean_object* v___x_2940_; 
lean_dec_ref(v_p_2937_);
v___x_2940_ = l_List_reverse___redArg(v_a_2939_);
return v___x_2940_;
}
else
{
lean_object* v_head_2941_; lean_object* v_tail_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2953_; 
v_head_2941_ = lean_ctor_get(v_a_2938_, 0);
v_tail_2942_ = lean_ctor_get(v_a_2938_, 1);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2944_ = v_a_2938_;
v_isShared_2945_ = v_isSharedCheck_2953_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_tail_2942_);
lean_inc(v_head_2941_);
lean_dec(v_a_2938_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2953_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; uint8_t v___x_2947_; 
lean_inc_ref(v_p_2937_);
lean_inc(v_head_2941_);
v___x_2946_ = lean_apply_1(v_p_2937_, v_head_2941_);
v___x_2947_ = lean_unbox(v___x_2946_);
if (v___x_2947_ == 0)
{
lean_del_object(v___x_2944_);
lean_dec(v_head_2941_);
v_a_2938_ = v_tail_2942_;
goto _start;
}
else
{
lean_object* v___x_2950_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v_a_2939_);
v___x_2950_ = v___x_2944_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_head_2941_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_a_2939_);
v___x_2950_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
v_a_2938_ = v_tail_2942_;
v_a_2939_ = v___x_2950_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object* v_00_u03b1_2954_, lean_object* v_p_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_List_filterTR_loop___redArg(v_p_2955_, v_a_2956_, v_a_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object* v_p_2959_, lean_object* v_as_2960_){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_box(0);
v___x_2962_ = l_List_filterTR_loop___redArg(v_p_2959_, v_as_2960_, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR(lean_object* v_00_u03b1_2963_, lean_object* v_p_2964_, lean_object* v_as_2965_){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_box(0);
v___x_2967_ = l_List_filterTR_loop___redArg(v_p_2964_, v_as_2965_, v___x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_zero_2971_; uint8_t v_isZero_2972_; 
v_zero_2971_ = lean_unsigned_to_nat(0u);
v_isZero_2972_ = lean_nat_dec_eq(v_a_2969_, v_zero_2971_);
if (v_isZero_2972_ == 1)
{
lean_dec(v_a_2969_);
lean_dec(v_a_2968_);
return v_a_2970_;
}
else
{
lean_object* v_one_2973_; lean_object* v_n_2974_; lean_object* v___x_2975_; 
v_one_2973_ = lean_unsigned_to_nat(1u);
v_n_2974_ = lean_nat_sub(v_a_2969_, v_one_2973_);
lean_dec(v_a_2969_);
lean_inc(v_a_2968_);
v___x_2975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2975_, 0, v_a_2968_);
lean_ctor_set(v___x_2975_, 1, v_a_2970_);
v_a_2969_ = v_n_2974_;
v_a_2970_ = v___x_2975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object* v_00_u03b1_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_List_replicateTR_loop___redArg(v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object* v_n_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_box(0);
v___x_2985_ = l_List_replicateTR_loop___redArg(v_a_2983_, v_n_2982_, v___x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object* v_00_u03b1_2986_, lean_object* v_n_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_List_replicateTR___redArg(v_n_2987_, v_a_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg(lean_object* v_n_2990_, lean_object* v_a_2991_, lean_object* v_l_2992_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2993_ = l_List_lengthTR___redArg(v_l_2992_);
v___x_2994_ = lean_nat_sub(v_n_2990_, v___x_2993_);
lean_dec(v___x_2993_);
v___x_2995_ = l_List_replicateTR_loop___redArg(v_a_2991_, v___x_2994_, v_l_2992_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg___boxed(lean_object* v_n_2996_, lean_object* v_a_2997_, lean_object* v_l_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_List_leftpadTR___redArg(v_n_2996_, v_a_2997_, v_l_2998_);
lean_dec(v_n_2996_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object* v_00_u03b1_3000_, lean_object* v_n_3001_, lean_object* v_a_3002_, lean_object* v_l_3003_){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = l_List_lengthTR___redArg(v_l_3003_);
v___x_3005_ = lean_nat_sub(v_n_3001_, v___x_3004_);
lean_dec(v___x_3004_);
v___x_3006_ = l_List_replicateTR_loop___redArg(v_a_3002_, v___x_3005_, v_l_3003_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___boxed(lean_object* v_00_u03b1_3007_, lean_object* v_n_3008_, lean_object* v_a_3009_, lean_object* v_l_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_List_leftpadTR(v_00_u03b1_3007_, v_n_3008_, v_a_3009_, v_l_3010_);
lean_dec(v_n_3008_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg(lean_object* v_init_3012_, lean_object* v_x_3013_){
_start:
{
if (lean_obj_tag(v_x_3013_) == 0)
{
lean_inc_ref(v_init_3012_);
return v_init_3012_;
}
else
{
lean_object* v_head_3014_; lean_object* v_tail_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3041_; 
v_head_3014_ = lean_ctor_get(v_x_3013_, 0);
v_tail_3015_ = lean_ctor_get(v_x_3013_, 1);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_x_3013_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3017_ = v_x_3013_;
v_isShared_3018_ = v_isSharedCheck_3041_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_tail_3015_);
lean_inc(v_head_3014_);
lean_dec(v_x_3013_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3041_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v_fst_3019_; lean_object* v_snd_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3040_; 
v_fst_3019_ = lean_ctor_get(v_head_3014_, 0);
v_snd_3020_ = lean_ctor_get(v_head_3014_, 1);
v_isSharedCheck_3040_ = !lean_is_exclusive(v_head_3014_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3022_ = v_head_3014_;
v_isShared_3023_ = v_isSharedCheck_3040_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_snd_3020_);
lean_inc(v_fst_3019_);
lean_dec(v_head_3014_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3040_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v_fst_3025_; lean_object* v_snd_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3039_; 
v___x_3024_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3012_, v_tail_3015_);
v_fst_3025_ = lean_ctor_get(v___x_3024_, 0);
v_snd_3026_ = lean_ctor_get(v___x_3024_, 1);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3028_ = v___x_3024_;
v_isShared_3029_ = v_isSharedCheck_3039_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_snd_3026_);
lean_inc(v_fst_3025_);
lean_dec(v___x_3024_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3039_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 1, v_fst_3025_);
lean_ctor_set(v___x_3017_, 0, v_fst_3019_);
v___x_3031_ = v___x_3017_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_fst_3019_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_fst_3025_);
v___x_3031_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3033_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set_tag(v___x_3022_, 1);
lean_ctor_set(v___x_3022_, 1, v_snd_3026_);
lean_ctor_set(v___x_3022_, 0, v_snd_3020_);
v___x_3033_ = v___x_3022_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_snd_3020_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_snd_3026_);
v___x_3033_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3035_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v___x_3033_);
lean_ctor_set(v___x_3028_, 0, v___x_3031_);
v___x_3035_ = v___x_3028_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg___boxed(lean_object* v_init_3042_, lean_object* v_x_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3042_, v_x_3043_);
lean_dec_ref(v_init_3042_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object* v_l_3045_){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_3047_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v___x_3046_, v_l_3045_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object* v_00_u03b1_3048_, lean_object* v_00_u03b2_3049_, lean_object* v_l_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l_List_unzipTR___redArg(v_l_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0(lean_object* v_00_u03b1_3052_, lean_object* v_00_u03b2_3053_, lean_object* v_init_3054_, lean_object* v_x_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3054_, v_x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___boxed(lean_object* v_00_u03b1_3057_, lean_object* v_00_u03b2_3058_, lean_object* v_init_3059_, lean_object* v_x_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_List_foldr___at___00List_unzipTR_spec__0(v_00_u03b1_3057_, v_00_u03b2_3058_, v_init_3059_, v_x_3060_);
lean_dec_ref(v_init_3059_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object* v_step_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_zero_3066_; uint8_t v_isZero_3067_; 
v_zero_3066_ = lean_unsigned_to_nat(0u);
v_isZero_3067_ = lean_nat_dec_eq(v_a_3063_, v_zero_3066_);
if (v_isZero_3067_ == 1)
{
lean_dec(v_a_3064_);
lean_dec(v_a_3063_);
return v_a_3065_;
}
else
{
lean_object* v_one_3068_; lean_object* v_n_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_one_3068_ = lean_unsigned_to_nat(1u);
v_n_3069_ = lean_nat_sub(v_a_3063_, v_one_3068_);
lean_dec(v_a_3063_);
v___x_3070_ = lean_nat_sub(v_a_3064_, v_step_3062_);
lean_dec(v_a_3064_);
lean_inc(v___x_3070_);
v___x_3071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v_a_3065_);
v_a_3063_ = v_n_3069_;
v_a_3064_ = v___x_3070_;
v_a_3065_ = v___x_3071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object* v_step_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_List_range_x27TR_go(v_step_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
lean_dec(v_step_3073_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object* v_s_3078_, lean_object* v_n_3079_, lean_object* v_step_3080_){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3081_ = lean_nat_mul(v_step_3080_, v_n_3079_);
v___x_3082_ = lean_nat_add(v_s_3078_, v___x_3081_);
lean_dec(v___x_3081_);
v___x_3083_ = lean_box(0);
v___x_3084_ = l_List_range_x27TR_go(v_step_3080_, v_n_3079_, v___x_3082_, v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object* v_s_3085_, lean_object* v_n_3086_, lean_object* v_step_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_List_range_x27TR(v_s_3085_, v_n_3086_, v_step_3087_);
lean_dec(v_step_3087_);
lean_dec(v_s_3085_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg(lean_object* v_sep_3089_, lean_object* v_init_3090_, lean_object* v_x_3091_){
_start:
{
if (lean_obj_tag(v_x_3091_) == 0)
{
lean_dec(v_sep_3089_);
lean_inc(v_init_3090_);
return v_init_3090_;
}
else
{
lean_object* v_head_3092_; lean_object* v_tail_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3102_; 
v_head_3092_ = lean_ctor_get(v_x_3091_, 0);
v_tail_3093_ = lean_ctor_get(v_x_3091_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_x_3091_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3095_ = v_x_3091_;
v_isShared_3096_ = v_isSharedCheck_3102_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_tail_3093_);
lean_inc(v_head_3092_);
lean_dec(v_x_3091_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3102_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
lean_inc(v_sep_3089_);
v___x_3097_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3089_, v_init_3090_, v_tail_3093_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 1, v___x_3097_);
v___x_3099_ = v___x_3095_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_head_3092_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3100_, 0, v_sep_3089_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
return v___x_3100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(lean_object* v_sep_3103_, lean_object* v_init_3104_, lean_object* v_x_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3103_, v_init_3104_, v_x_3105_);
lean_dec(v_init_3104_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object* v_sep_3107_, lean_object* v_x_3108_){
_start:
{
if (lean_obj_tag(v_x_3108_) == 0)
{
lean_dec(v_sep_3107_);
return v_x_3108_;
}
else
{
lean_object* v_tail_3109_; 
v_tail_3109_ = lean_ctor_get(v_x_3108_, 1);
lean_inc(v_tail_3109_);
if (lean_obj_tag(v_tail_3109_) == 0)
{
lean_dec(v_sep_3107_);
return v_x_3108_;
}
else
{
lean_object* v_head_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3129_; 
v_head_3110_ = lean_ctor_get(v_x_3108_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_x_3108_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v_x_3108_, 1);
lean_dec(v_unused_3130_);
v___x_3112_ = v_x_3108_;
v_isShared_3113_ = v_isSharedCheck_3129_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_head_3110_);
lean_dec(v_x_3108_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3129_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v_head_3114_; lean_object* v_tail_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3128_; 
v_head_3114_ = lean_ctor_get(v_tail_3109_, 0);
v_tail_3115_ = lean_ctor_get(v_tail_3109_, 1);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_tail_3109_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3117_ = v_tail_3109_;
v_isShared_3118_ = v_isSharedCheck_3128_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_tail_3115_);
lean_inc(v_head_3114_);
lean_dec(v_tail_3109_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3128_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3119_ = lean_box(0);
lean_inc(v_sep_3107_);
v___x_3120_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3107_, v___x_3119_, v_tail_3115_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___x_3120_);
v___x_3122_ = v___x_3117_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_head_3114_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3124_; 
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 1, v___x_3122_);
lean_ctor_set(v___x_3112_, 0, v_sep_3107_);
v___x_3124_ = v___x_3112_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_sep_3107_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_head_3110_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
return v___x_3125_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object* v_00_u03b1_3131_, lean_object* v_sep_3132_, lean_object* v_x_3133_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_List_intersperseTR___redArg(v_sep_3132_, v_x_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0(lean_object* v_00_u03b1_3135_, lean_object* v_sep_3136_, lean_object* v_init_3137_, lean_object* v_x_3138_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3136_, v_init_3137_, v_x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___boxed(lean_object* v_00_u03b1_3140_, lean_object* v_sep_3141_, lean_object* v_init_3142_, lean_object* v_x_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_List_foldr___at___00List_intersperseTR_spec__0(v_00_u03b1_3140_, v_sep_3141_, v_init_3142_, v_x_3143_);
lean_dec(v_init_3142_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(lean_object* v_x_3145_, lean_object* v_h__1_3146_, lean_object* v_h__2_3147_, lean_object* v_h__3_3148_){
_start:
{
if (lean_obj_tag(v_x_3145_) == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec(v_h__3_3148_);
lean_dec(v_h__2_3147_);
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_apply_1(v_h__1_3146_, v___x_3149_);
return v___x_3150_;
}
else
{
lean_object* v_tail_3151_; 
lean_dec(v_h__1_3146_);
v_tail_3151_ = lean_ctor_get(v_x_3145_, 1);
if (lean_obj_tag(v_tail_3151_) == 0)
{
lean_object* v_head_3152_; lean_object* v___x_3153_; 
lean_dec(v_h__3_3148_);
v_head_3152_ = lean_ctor_get(v_x_3145_, 0);
lean_inc(v_head_3152_);
lean_dec_ref_known(v_x_3145_, 2);
v___x_3153_ = lean_apply_1(v_h__2_3147_, v_head_3152_);
return v___x_3153_;
}
else
{
lean_object* v_head_3154_; lean_object* v_head_3155_; lean_object* v_tail_3156_; lean_object* v___x_3157_; 
lean_inc_ref(v_tail_3151_);
lean_dec(v_h__2_3147_);
v_head_3154_ = lean_ctor_get(v_x_3145_, 0);
lean_inc(v_head_3154_);
lean_dec_ref_known(v_x_3145_, 2);
v_head_3155_ = lean_ctor_get(v_tail_3151_, 0);
lean_inc(v_head_3155_);
v_tail_3156_ = lean_ctor_get(v_tail_3151_, 1);
lean_inc(v_tail_3156_);
lean_dec_ref_known(v_tail_3151_, 2);
v___x_3157_ = lean_apply_3(v_h__3_3148_, v_head_3154_, v_head_3155_, v_tail_3156_);
return v___x_3157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object* v_00_u03b1_3158_, lean_object* v_motive_3159_, lean_object* v_x_3160_, lean_object* v_h__1_3161_, lean_object* v_h__2_3162_, lean_object* v_h__3_3163_){
_start:
{
if (lean_obj_tag(v_x_3160_) == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec(v_h__3_3163_);
lean_dec(v_h__2_3162_);
v___x_3164_ = lean_box(0);
v___x_3165_ = lean_apply_1(v_h__1_3161_, v___x_3164_);
return v___x_3165_;
}
else
{
lean_object* v_tail_3166_; 
lean_dec(v_h__1_3161_);
v_tail_3166_ = lean_ctor_get(v_x_3160_, 1);
if (lean_obj_tag(v_tail_3166_) == 0)
{
lean_object* v_head_3167_; lean_object* v___x_3168_; 
lean_dec(v_h__3_3163_);
v_head_3167_ = lean_ctor_get(v_x_3160_, 0);
lean_inc(v_head_3167_);
lean_dec_ref_known(v_x_3160_, 2);
v___x_3168_ = lean_apply_1(v_h__2_3162_, v_head_3167_);
return v___x_3168_;
}
else
{
lean_object* v_head_3169_; lean_object* v_head_3170_; lean_object* v_tail_3171_; lean_object* v___x_3172_; 
lean_inc_ref(v_tail_3166_);
lean_dec(v_h__2_3162_);
v_head_3169_ = lean_ctor_get(v_x_3160_, 0);
lean_inc(v_head_3169_);
lean_dec_ref_known(v_x_3160_, 2);
v_head_3170_ = lean_ctor_get(v_tail_3166_, 0);
lean_inc(v_head_3170_);
v_tail_3171_ = lean_ctor_get(v_tail_3166_, 1);
lean_inc(v_tail_3171_);
lean_dec_ref_known(v_tail_3166_, 2);
v___x_3172_ = lean_apply_3(v_h__3_3163_, v_head_3169_, v_head_3170_, v_tail_3171_);
return v___x_3172_;
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
