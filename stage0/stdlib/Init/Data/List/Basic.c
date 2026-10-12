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
uint8_t l_List_isEqv___redArg(lean_object* v_x_6_, lean_object* v_x_7_, lean_object* v_x_8_){
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
LEAN_EXPORT void l_List_isEqv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_6_ = stack[0].m_obj;
lean_object* v_x_7_ = stack[1].m_obj;
lean_object* v_x_8_ = stack[2].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_List_isEqv___redArg(v_x_6_, v_x_7_, v_x_8_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_List_isEqv___redArg___boxed(lean_object* v_x_21_, lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_List_isEqv___redArg(v_x_21_, v_x_22_, v_x_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
uint8_t l_List_isEqv(lean_object* v_00_u03b1_26_, lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = l_List_isEqv___redArg(v_x_27_, v_x_28_, v_x_29_);
return v___x_30_;
}
}
LEAN_EXPORT void l_List_isEqv_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_27_ = stack[1].m_obj;
lean_object* v_x_28_ = stack[2].m_obj;
lean_object* v_x_29_ = stack[3].m_obj;
uint8_t v_res_31_;
v_res_31_ = l_List_isEqv(lean_box(0), v_x_27_, v_x_28_, v_x_29_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l_List_isEqv___boxed(lean_object* v_00_u03b1_32_, lean_object* v_x_33_, lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_List_isEqv(v_00_u03b1_32_, v_x_33_, v_x_34_, v_x_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
uint8_t l_List_decidableLex___redArg(lean_object* v_inst_38_, lean_object* v_h_39_, lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
lean_dec_ref(v_h_39_);
lean_dec_ref(v_inst_38_);
if (lean_obj_tag(v_x_41_) == 0)
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
else
{
uint8_t v___x_43_; 
lean_dec_ref_known(v_x_41_, 2);
v___x_43_ = 1;
return v___x_43_;
}
}
else
{
if (lean_obj_tag(v_x_41_) == 0)
{
uint8_t v___x_44_; 
lean_dec_ref_known(v_x_40_, 2);
lean_dec_ref(v_h_39_);
lean_dec_ref(v_inst_38_);
v___x_44_ = 0;
return v___x_44_;
}
else
{
lean_object* v_head_45_; lean_object* v_tail_46_; lean_object* v_head_47_; lean_object* v_tail_48_; lean_object* v_decide_49_; uint8_t v___x_50_; 
v_head_45_ = lean_ctor_get(v_x_40_, 0);
lean_inc_n(v_head_45_, 2);
v_tail_46_ = lean_ctor_get(v_x_40_, 1);
lean_inc(v_tail_46_);
lean_dec_ref_known(v_x_40_, 2);
v_head_47_ = lean_ctor_get(v_x_41_, 0);
lean_inc_n(v_head_47_, 2);
v_tail_48_ = lean_ctor_get(v_x_41_, 1);
lean_inc(v_tail_48_);
lean_dec_ref_known(v_x_41_, 2);
lean_inc_ref(v_h_39_);
v_decide_49_ = lean_apply_2(v_h_39_, v_head_45_, v_head_47_);
v___x_50_ = lean_unbox(v_decide_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; uint8_t v___x_52_; 
lean_inc_ref(v_inst_38_);
v___x_51_ = lean_apply_2(v_inst_38_, v_head_45_, v_head_47_);
v___x_52_ = lean_unbox(v___x_51_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
lean_dec(v_tail_48_);
lean_dec(v_tail_46_);
lean_dec_ref(v_h_39_);
lean_dec_ref(v_inst_38_);
v___x_53_ = lean_unbox(v___x_51_);
return v___x_53_;
}
else
{
uint8_t v_decide_54_; 
v_decide_54_ = l_List_decidableLex___redArg(v_inst_38_, v_h_39_, v_tail_46_, v_tail_48_);
if (v_decide_54_ == 0)
{
return v_decide_54_;
}
else
{
uint8_t v___x_55_; 
v___x_55_ = lean_unbox(v___x_51_);
return v___x_55_;
}
}
}
else
{
uint8_t v___x_56_; 
lean_dec(v_tail_48_);
lean_dec(v_head_47_);
lean_dec(v_tail_46_);
lean_dec(v_head_45_);
lean_dec_ref(v_h_39_);
lean_dec_ref(v_inst_38_);
v___x_56_ = lean_unbox(v_decide_49_);
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT void l_List_decidableLex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_38_ = stack[0].m_obj;
lean_object* v_h_39_ = stack[1].m_obj;
lean_object* v_x_40_ = stack[2].m_obj;
lean_object* v_x_41_ = stack[3].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_List_decidableLex___redArg(v_inst_38_, v_h_39_, v_x_40_, v_x_41_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_List_decidableLex___redArg___boxed(lean_object* v_inst_58_, lean_object* v_h_59_, lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_List_decidableLex___redArg(v_inst_58_, v_h_59_, v_x_60_, v_x_61_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
uint8_t l_List_decidableLex(lean_object* v_00_u03b1_64_, lean_object* v_inst_65_, lean_object* v_r_66_, lean_object* v_h_67_, lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = l_List_decidableLex___redArg(v_inst_65_, v_h_67_, v_x_68_, v_x_69_);
return v___x_70_;
}
}
LEAN_EXPORT void l_List_decidableLex_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_65_ = stack[1].m_obj;
lean_object* v_h_67_ = stack[3].m_obj;
lean_object* v_x_68_ = stack[4].m_obj;
lean_object* v_x_69_ = stack[5].m_obj;
uint8_t v_res_71_;
v_res_71_ = l_List_decidableLex(lean_box(0), v_inst_65_, lean_box(0), v_h_67_, v_x_68_, v_x_69_);
stack->m_num = v_res_71_;
}
LEAN_EXPORT lean_object* l_List_decidableLex___boxed(lean_object* v_00_u03b1_72_, lean_object* v_inst_73_, lean_object* v_r_74_, lean_object* v_h_75_, lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_List_decidableLex(v_00_u03b1_72_, v_inst_73_, v_r_74_, v_h_75_, v_x_76_, v_x_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
lean_object* l_List_instLT___redArg(){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(0);
return v___x_81_;
}
}
LEAN_EXPORT void l_List_instLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_82_;
v_res_82_ = l_List_instLT___redArg();
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l_List_instLT___redArg___boxed(lean_object* v___dummy_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_List_instLT___redArg();
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_List_instLT(lean_object* v_00_u03b1_85_, lean_object* v_inst_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(0);
return v___x_87_;
}
}
uint8_t l_List_decidableLT___redArg(lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_l_u2081_90_, lean_object* v_l_u2082_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = l_List_decidableLex___redArg(v_inst_88_, v_inst_89_, v_l_u2081_90_, v_l_u2082_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l_List_decidableLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_88_ = stack[0].m_obj;
lean_object* v_inst_89_ = stack[1].m_obj;
lean_object* v_l_u2081_90_ = stack[2].m_obj;
lean_object* v_l_u2082_91_ = stack[3].m_obj;
uint8_t v_res_93_;
v_res_93_ = l_List_decidableLT___redArg(v_inst_88_, v_inst_89_, v_l_u2081_90_, v_l_u2082_91_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_List_decidableLT___redArg___boxed(lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_l_u2081_96_, lean_object* v_l_u2082_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_List_decidableLT___redArg(v_inst_94_, v_inst_95_, v_l_u2081_96_, v_l_u2082_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
uint8_t l_List_decidableLT(lean_object* v_00_u03b1_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_l_u2081_104_, lean_object* v_l_u2082_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = l_List_decidableLex___redArg(v_inst_101_, v_inst_103_, v_l_u2081_104_, v_l_u2082_105_);
return v___x_106_;
}
}
LEAN_EXPORT void l_List_decidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_101_ = stack[1].m_obj;
lean_object* v_inst_102_ = stack[2].m_obj;
lean_object* v_inst_103_ = stack[3].m_obj;
lean_object* v_l_u2081_104_ = stack[4].m_obj;
lean_object* v_l_u2082_105_ = stack[5].m_obj;
uint8_t v_res_107_;
v_res_107_ = l_List_decidableLT(lean_box(0), v_inst_101_, v_inst_102_, v_inst_103_, v_l_u2081_104_, v_l_u2082_105_);
stack->m_num = v_res_107_;
}
LEAN_EXPORT lean_object* l_List_decidableLT___boxed(lean_object* v_00_u03b1_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_l_u2081_112_, lean_object* v_l_u2082_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_List_decidableLT(v_00_u03b1_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_l_u2081_112_, v_l_u2082_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
lean_object* l_List_instLE___redArg(){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
return v___x_117_;
}
}
LEAN_EXPORT void l_List_instLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_118_;
v_res_118_ = l_List_instLE___redArg();
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_List_instLE___redArg___boxed(lean_object* v___dummy_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_List_instLE___redArg();
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_List_instLE(lean_object* v_00_u03b1_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
uint8_t l_List_decidableLE___redArg(lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_l_u2081_126_, lean_object* v_l_u2082_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = l_List_decidableLex___redArg(v_inst_124_, v_inst_125_, v_l_u2082_127_, v_l_u2081_126_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = 1;
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
}
LEAN_EXPORT void l_List_decidableLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_124_ = stack[0].m_obj;
lean_object* v_inst_125_ = stack[1].m_obj;
lean_object* v_l_u2081_126_ = stack[2].m_obj;
lean_object* v_l_u2082_127_ = stack[3].m_obj;
uint8_t v_res_131_;
v_res_131_ = l_List_decidableLE___redArg(v_inst_124_, v_inst_125_, v_l_u2081_126_, v_l_u2082_127_);
stack->m_num = v_res_131_;
}
LEAN_EXPORT lean_object* l_List_decidableLE___redArg___boxed(lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_l_u2081_134_, lean_object* v_l_u2082_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_List_decidableLE___redArg(v_inst_132_, v_inst_133_, v_l_u2081_134_, v_l_u2082_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
uint8_t l_List_decidableLE(lean_object* v_00_u03b1_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_l_u2081_142_, lean_object* v_l_u2082_143_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = l_List_decidableLE___redArg(v_inst_139_, v_inst_141_, v_l_u2081_142_, v_l_u2082_143_);
return v___x_144_;
}
}
LEAN_EXPORT void l_List_decidableLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_139_ = stack[1].m_obj;
lean_object* v_inst_140_ = stack[2].m_obj;
lean_object* v_inst_141_ = stack[3].m_obj;
lean_object* v_l_u2081_142_ = stack[4].m_obj;
lean_object* v_l_u2082_143_ = stack[5].m_obj;
uint8_t v_res_145_;
v_res_145_ = l_List_decidableLE(lean_box(0), v_inst_139_, v_inst_140_, v_inst_141_, v_l_u2081_142_, v_l_u2082_143_);
stack->m_num = v_res_145_;
}
LEAN_EXPORT lean_object* l_List_decidableLE___boxed(lean_object* v_00_u03b1_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_l_u2081_150_, lean_object* v_l_u2082_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_List_decidableLE(v_00_u03b1_146_, v_inst_147_, v_inst_148_, v_inst_149_, v_l_u2081_150_, v_l_u2082_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__12(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = ((lean_object*)(l_List_lex___auto__1___closed__10));
v___x_181_ = l_Lean_mkAtom(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_obj_once(&l_List_lex___auto__1___closed__12, &l_List_lex___auto__1___closed__12_once, _init_l_List_lex___auto__1___closed__12);
v___x_183_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_184_ = lean_array_push(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_List_lex___auto__1___closed__19));
v___x_200_ = l_Lean_mkAtom(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__21(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&l_List_lex___auto__1___closed__20, &l_List_lex___auto__1___closed__20_once, _init_l_List_lex___auto__1___closed__20);
v___x_202_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_203_ = lean_array_push(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = ((lean_object*)(l_List_lex___auto__1___closed__26));
v___x_218_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_219_ = lean_array_push(v___x_218_, v___x_217_);
return v___x_219_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = lean_obj_once(&l_List_lex___auto__1___closed__27, &l_List_lex___auto__1___closed__27_once, _init_l_List_lex___auto__1___closed__27);
v___x_221_ = ((lean_object*)(l_List_lex___auto__1___closed__23));
v___x_222_ = lean_box(2);
v___x_223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
lean_ctor_set(v___x_223_, 2, v___x_220_);
return v___x_223_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_obj_once(&l_List_lex___auto__1___closed__28, &l_List_lex___auto__1___closed__28_once, _init_l_List_lex___auto__1___closed__28);
v___x_225_ = lean_obj_once(&l_List_lex___auto__1___closed__21, &l_List_lex___auto__1___closed__21_once, _init_l_List_lex___auto__1___closed__21);
v___x_226_ = lean_array_push(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_227_ = lean_obj_once(&l_List_lex___auto__1___closed__29, &l_List_lex___auto__1___closed__29_once, _init_l_List_lex___auto__1___closed__29);
v___x_228_ = ((lean_object*)(l_List_lex___auto__1___closed__18));
v___x_229_ = lean_box(2);
v___x_230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_227_);
return v___x_230_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_obj_once(&l_List_lex___auto__1___closed__30, &l_List_lex___auto__1___closed__30_once, _init_l_List_lex___auto__1___closed__30);
v___x_232_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_233_ = lean_array_push(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l_List_lex___auto__1___closed__36));
v___x_245_ = l_Lean_mkAtom(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&l_List_lex___auto__1___closed__37, &l_List_lex___auto__1___closed__37_once, _init_l_List_lex___auto__1___closed__37);
v___x_247_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_248_ = lean_array_push(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_obj_once(&l_List_lex___auto__1___closed__28, &l_List_lex___auto__1___closed__28_once, _init_l_List_lex___auto__1___closed__28);
v___x_250_ = lean_obj_once(&l_List_lex___auto__1___closed__38, &l_List_lex___auto__1___closed__38_once, _init_l_List_lex___auto__1___closed__38);
v___x_251_ = lean_array_push(v___x_250_, v___x_249_);
return v___x_251_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_252_ = lean_obj_once(&l_List_lex___auto__1___closed__39, &l_List_lex___auto__1___closed__39_once, _init_l_List_lex___auto__1___closed__39);
v___x_253_ = ((lean_object*)(l_List_lex___auto__1___closed__35));
v___x_254_ = lean_box(2);
v___x_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
lean_ctor_set(v___x_255_, 2, v___x_252_);
return v___x_255_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_obj_once(&l_List_lex___auto__1___closed__40, &l_List_lex___auto__1___closed__40_once, _init_l_List_lex___auto__1___closed__40);
v___x_257_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_258_ = lean_array_push(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_List_lex___auto__1___closed__42));
v___x_261_ = l_Lean_mkAtom(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l_List_lex___auto__1___closed__43, &l_List_lex___auto__1___closed__43_once, _init_l_List_lex___auto__1___closed__43);
v___x_263_ = lean_obj_once(&l_List_lex___auto__1___closed__41, &l_List_lex___auto__1___closed__41_once, _init_l_List_lex___auto__1___closed__41);
v___x_264_ = lean_array_push(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_obj_once(&l_List_lex___auto__1___closed__40, &l_List_lex___auto__1___closed__40_once, _init_l_List_lex___auto__1___closed__40);
v___x_266_ = lean_obj_once(&l_List_lex___auto__1___closed__44, &l_List_lex___auto__1___closed__44_once, _init_l_List_lex___auto__1___closed__44);
v___x_267_ = lean_array_push(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = lean_obj_once(&l_List_lex___auto__1___closed__45, &l_List_lex___auto__1___closed__45_once, _init_l_List_lex___auto__1___closed__45);
v___x_269_ = ((lean_object*)(l_List_lex___auto__1___closed__33));
v___x_270_ = lean_box(2);
v___x_271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
lean_ctor_set(v___x_271_, 2, v___x_268_);
return v___x_271_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_List_lex___auto__1___closed__46, &l_List_lex___auto__1___closed__46_once, _init_l_List_lex___auto__1___closed__46);
v___x_273_ = lean_obj_once(&l_List_lex___auto__1___closed__31, &l_List_lex___auto__1___closed__31_once, _init_l_List_lex___auto__1___closed__31);
v___x_274_ = lean_array_push(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__49(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l_List_lex___auto__1___closed__48));
v___x_277_ = l_Lean_mkAtom(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__50(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_obj_once(&l_List_lex___auto__1___closed__49, &l_List_lex___auto__1___closed__49_once, _init_l_List_lex___auto__1___closed__49);
v___x_279_ = lean_obj_once(&l_List_lex___auto__1___closed__47, &l_List_lex___auto__1___closed__47_once, _init_l_List_lex___auto__1___closed__47);
v___x_280_ = lean_array_push(v___x_279_, v___x_278_);
return v___x_280_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__51(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_281_ = lean_obj_once(&l_List_lex___auto__1___closed__50, &l_List_lex___auto__1___closed__50_once, _init_l_List_lex___auto__1___closed__50);
v___x_282_ = ((lean_object*)(l_List_lex___auto__1___closed__16));
v___x_283_ = lean_box(2);
v___x_284_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_282_);
lean_ctor_set(v___x_284_, 2, v___x_281_);
return v___x_284_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__52(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_obj_once(&l_List_lex___auto__1___closed__51, &l_List_lex___auto__1___closed__51_once, _init_l_List_lex___auto__1___closed__51);
v___x_286_ = lean_obj_once(&l_List_lex___auto__1___closed__13, &l_List_lex___auto__1___closed__13_once, _init_l_List_lex___auto__1___closed__13);
v___x_287_ = lean_array_push(v___x_286_, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__53(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_288_ = lean_obj_once(&l_List_lex___auto__1___closed__52, &l_List_lex___auto__1___closed__52_once, _init_l_List_lex___auto__1___closed__52);
v___x_289_ = ((lean_object*)(l_List_lex___auto__1___closed__11));
v___x_290_ = lean_box(2);
v___x_291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_289_);
lean_ctor_set(v___x_291_, 2, v___x_288_);
return v___x_291_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__54(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_obj_once(&l_List_lex___auto__1___closed__53, &l_List_lex___auto__1___closed__53_once, _init_l_List_lex___auto__1___closed__53);
v___x_293_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_294_ = lean_array_push(v___x_293_, v___x_292_);
return v___x_294_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__55(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_295_ = lean_obj_once(&l_List_lex___auto__1___closed__54, &l_List_lex___auto__1___closed__54_once, _init_l_List_lex___auto__1___closed__54);
v___x_296_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_297_ = lean_box(2);
v___x_298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
lean_ctor_set(v___x_298_, 2, v___x_295_);
return v___x_298_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__56(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_obj_once(&l_List_lex___auto__1___closed__55, &l_List_lex___auto__1___closed__55_once, _init_l_List_lex___auto__1___closed__55);
v___x_300_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_301_ = lean_array_push(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__57(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = lean_obj_once(&l_List_lex___auto__1___closed__56, &l_List_lex___auto__1___closed__56_once, _init_l_List_lex___auto__1___closed__56);
v___x_303_ = ((lean_object*)(l_List_lex___auto__1___closed__7));
v___x_304_ = lean_box(2);
v___x_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
lean_ctor_set(v___x_305_, 2, v___x_302_);
return v___x_305_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__58(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&l_List_lex___auto__1___closed__57, &l_List_lex___auto__1___closed__57_once, _init_l_List_lex___auto__1___closed__57);
v___x_307_ = ((lean_object*)(l_List_lex___auto__1___closed__5));
v___x_308_ = lean_array_push(v___x_307_, v___x_306_);
return v___x_308_;
}
}
static lean_object* _init_l_List_lex___auto__1___closed__59(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_obj_once(&l_List_lex___auto__1___closed__58, &l_List_lex___auto__1___closed__58_once, _init_l_List_lex___auto__1___closed__58);
v___x_310_ = ((lean_object*)(l_List_lex___auto__1___closed__4));
v___x_311_ = lean_box(2);
v___x_312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___x_310_);
lean_ctor_set(v___x_312_, 2, v___x_309_);
return v___x_312_;
}
}
static lean_object* _init_l_List_lex___auto__1(void){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_List_lex___auto__1___closed__59, &l_List_lex___auto__1___closed__59_once, _init_l_List_lex___auto__1___closed__59);
return v___x_313_;
}
}
uint8_t l_List_lex___redArg(lean_object* v_inst_314_, lean_object* v_l_u2081_315_, lean_object* v_l_u2082_316_, lean_object* v_lt_317_){
_start:
{
if (lean_obj_tag(v_l_u2081_315_) == 0)
{
lean_dec_ref(v_lt_317_);
lean_dec_ref(v_inst_314_);
if (lean_obj_tag(v_l_u2082_316_) == 0)
{
uint8_t v___x_318_; 
v___x_318_ = 0;
return v___x_318_;
}
else
{
uint8_t v___x_319_; 
lean_dec_ref_known(v_l_u2082_316_, 2);
v___x_319_ = 1;
return v___x_319_;
}
}
else
{
if (lean_obj_tag(v_l_u2082_316_) == 0)
{
uint8_t v___x_320_; 
lean_dec_ref_known(v_l_u2081_315_, 2);
lean_dec_ref(v_lt_317_);
lean_dec_ref(v_inst_314_);
v___x_320_ = 0;
return v___x_320_;
}
else
{
lean_object* v_head_321_; lean_object* v_tail_322_; lean_object* v_head_323_; lean_object* v_tail_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_head_321_ = lean_ctor_get(v_l_u2081_315_, 0);
lean_inc_n(v_head_321_, 2);
v_tail_322_ = lean_ctor_get(v_l_u2081_315_, 1);
lean_inc(v_tail_322_);
lean_dec_ref_known(v_l_u2081_315_, 2);
v_head_323_ = lean_ctor_get(v_l_u2082_316_, 0);
lean_inc_n(v_head_323_, 2);
v_tail_324_ = lean_ctor_get(v_l_u2082_316_, 1);
lean_inc(v_tail_324_);
lean_dec_ref_known(v_l_u2082_316_, 2);
lean_inc_ref(v_lt_317_);
v___x_325_ = lean_apply_2(v_lt_317_, v_head_321_, v_head_323_);
v___x_326_ = lean_unbox(v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
lean_inc_ref(v_inst_314_);
v___x_327_ = lean_apply_2(v_inst_314_, v_head_321_, v_head_323_);
v___x_328_ = lean_unbox(v___x_327_);
if (v___x_328_ == 0)
{
uint8_t v___x_329_; 
lean_dec(v_tail_324_);
lean_dec(v_tail_322_);
lean_dec_ref(v_lt_317_);
lean_dec_ref(v_inst_314_);
v___x_329_ = lean_unbox(v___x_327_);
return v___x_329_;
}
else
{
v_l_u2081_315_ = v_tail_322_;
v_l_u2082_316_ = v_tail_324_;
goto _start;
}
}
else
{
uint8_t v___x_331_; 
lean_dec(v_tail_324_);
lean_dec(v_head_323_);
lean_dec(v_tail_322_);
lean_dec(v_head_321_);
lean_dec_ref(v_lt_317_);
lean_dec_ref(v_inst_314_);
v___x_331_ = lean_unbox(v___x_325_);
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT void l_List_lex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_314_ = stack[0].m_obj;
lean_object* v_l_u2081_315_ = stack[1].m_obj;
lean_object* v_l_u2082_316_ = stack[2].m_obj;
lean_object* v_lt_317_ = stack[3].m_obj;
uint8_t v_res_332_;
v_res_332_ = l_List_lex___redArg(v_inst_314_, v_l_u2081_315_, v_l_u2082_316_, v_lt_317_);
stack->m_num = v_res_332_;
}
LEAN_EXPORT lean_object* l_List_lex___redArg___boxed(lean_object* v_inst_333_, lean_object* v_l_u2081_334_, lean_object* v_l_u2082_335_, lean_object* v_lt_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_List_lex___redArg(v_inst_333_, v_l_u2081_334_, v_l_u2082_335_, v_lt_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
uint8_t l_List_lex(lean_object* v_00_u03b1_339_, lean_object* v_inst_340_, lean_object* v_l_u2081_341_, lean_object* v_l_u2082_342_, lean_object* v_lt_343_){
_start:
{
uint8_t v___x_344_; 
v___x_344_ = l_List_lex___redArg(v_inst_340_, v_l_u2081_341_, v_l_u2082_342_, v_lt_343_);
return v___x_344_;
}
}
LEAN_EXPORT void l_List_lex_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_340_ = stack[1].m_obj;
lean_object* v_l_u2081_341_ = stack[2].m_obj;
lean_object* v_l_u2082_342_ = stack[3].m_obj;
lean_object* v_lt_343_ = stack[4].m_obj;
uint8_t v_res_345_;
v_res_345_ = l_List_lex(lean_box(0), v_inst_340_, v_l_u2081_341_, v_l_u2082_342_, v_lt_343_);
stack->m_num = v_res_345_;
}
LEAN_EXPORT lean_object* l_List_lex___boxed(lean_object* v_00_u03b1_346_, lean_object* v_inst_347_, lean_object* v_l_u2081_348_, lean_object* v_l_u2082_349_, lean_object* v_lt_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_List_lex(v_00_u03b1_346_, v_inst_347_, v_l_u2081_348_, v_l_u2082_349_, v_lt_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg(lean_object* v_x_353_){
_start:
{
lean_object* v_tail_354_; 
v_tail_354_ = lean_ctor_get(v_x_353_, 1);
if (lean_obj_tag(v_tail_354_) == 0)
{
lean_object* v_head_355_; 
v_head_355_ = lean_ctor_get(v_x_353_, 0);
lean_inc(v_head_355_);
return v_head_355_;
}
else
{
v_x_353_ = v_tail_354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast___redArg___boxed(lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_List_getLast___redArg(v_x_357_);
lean_dec(v_x_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_List_getLast(lean_object* v_00_u03b1_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_List_getLast___redArg(v_x_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_List_getLast___boxed(lean_object* v_00_u03b1_363_, lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_List_getLast(v_00_u03b1_363_, v_x_364_, v_x_365_);
lean_dec(v_x_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg(lean_object* v_x_367_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_object* v___x_368_; 
v___x_368_ = lean_box(0);
return v___x_368_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_List_getLast___redArg(v_x_367_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___redArg___boxed(lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_List_getLast_x3f___redArg(v_x_371_);
lean_dec(v_x_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f(lean_object* v_00_u03b1_373_, lean_object* v_x_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_List_getLast_x3f___redArg(v_x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___boxed(lean_object* v_00_u03b1_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_List_getLast_x3f(v_00_u03b1_376_, v_x_377_);
lean_dec(v_x_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg(lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
if (lean_obj_tag(v_x_379_) == 0)
{
lean_inc(v_x_380_);
return v_x_380_;
}
else
{
lean_object* v___x_381_; 
v___x_381_ = l_List_getLast___redArg(v_x_379_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLastD___redArg___boxed(lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_List_getLastD___redArg(v_x_382_, v_x_383_);
lean_dec(v_x_383_);
lean_dec(v_x_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD(lean_object* v_00_u03b1_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_List_getLastD___redArg(v_x_386_, v_x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___boxed(lean_object* v_00_u03b1_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_List_getLastD(v_00_u03b1_389_, v_x_390_, v_x_391_);
lean_dec(v_x_391_);
lean_dec(v_x_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg(lean_object* v_x_393_){
_start:
{
lean_object* v_head_394_; 
v_head_394_ = lean_ctor_get(v_x_393_, 0);
lean_inc(v_head_394_);
return v_head_394_;
}
}
LEAN_EXPORT lean_object* l_List_head___redArg___boxed(lean_object* v_x_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_List_head___redArg(v_x_395_);
lean_dec(v_x_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_List_head(lean_object* v_00_u03b1_397_, lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
lean_object* v_head_400_; 
v_head_400_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_head_400_);
return v_head_400_;
}
}
LEAN_EXPORT lean_object* l_List_head___boxed(lean_object* v_00_u03b1_401_, lean_object* v_x_402_, lean_object* v_x_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_List_head(v_00_u03b1_401_, v_x_402_, v_x_403_);
lean_dec(v_x_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg(lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_object* v___x_406_; 
v___x_406_ = lean_box(0);
return v___x_406_;
}
else
{
lean_object* v_head_407_; lean_object* v___x_408_; 
v_head_407_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_head_407_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v_head_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___redArg___boxed(lean_object* v_x_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_List_head_x3f___redArg(v_x_409_);
lean_dec(v_x_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f(lean_object* v_00_u03b1_411_, lean_object* v_x_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_List_head_x3f___redArg(v_x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___boxed(lean_object* v_00_u03b1_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_List_head_x3f(v_00_u03b1_414_, v_x_415_);
lean_dec(v_x_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg(lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
lean_inc(v_x_418_);
return v_x_418_;
}
else
{
lean_object* v_head_419_; 
v_head_419_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_head_419_);
return v_head_419_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___redArg___boxed(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_List_headD___redArg(v_x_420_, v_x_421_);
lean_dec(v_x_421_);
lean_dec(v_x_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_List_headD(lean_object* v_00_u03b1_423_, lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
if (lean_obj_tag(v_x_424_) == 0)
{
lean_inc(v_x_425_);
return v_x_425_;
}
else
{
lean_object* v_head_426_; 
v_head_426_ = lean_ctor_get(v_x_424_, 0);
lean_inc(v_head_426_);
return v_head_426_;
}
}
}
LEAN_EXPORT lean_object* l_List_headD___boxed(lean_object* v_00_u03b1_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_List_headD(v_00_u03b1_427_, v_x_428_, v_x_429_);
lean_dec(v_x_429_);
lean_dec(v_x_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg(lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
return v_x_431_;
}
else
{
lean_object* v_tail_432_; 
v_tail_432_ = lean_ctor_get(v_x_431_, 1);
lean_inc(v_tail_432_);
return v_tail_432_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___redArg___boxed(lean_object* v_x_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_List_tail___redArg(v_x_433_);
lean_dec(v_x_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_List_tail(lean_object* v_00_u03b1_435_, lean_object* v_x_436_){
_start:
{
if (lean_obj_tag(v_x_436_) == 0)
{
return v_x_436_;
}
else
{
lean_object* v_tail_437_; 
v_tail_437_ = lean_ctor_get(v_x_436_, 1);
lean_inc(v_tail_437_);
return v_tail_437_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail___boxed(lean_object* v_00_u03b1_438_, lean_object* v_x_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_List_tail(v_00_u03b1_438_, v_x_439_);
lean_dec(v_x_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg(lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_box(0);
return v___x_442_;
}
else
{
lean_object* v_tail_443_; lean_object* v___x_444_; 
v_tail_443_ = lean_ctor_get(v_x_441_, 1);
lean_inc(v_tail_443_);
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v_tail_443_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___redArg___boxed(lean_object* v_x_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_List_tail_x3f___redArg(v_x_445_);
lean_dec(v_x_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f(lean_object* v_00_u03b1_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_List_tail_x3f___redArg(v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___boxed(lean_object* v_00_u03b1_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_List_tail_x3f(v_00_u03b1_450_, v_x_451_);
lean_dec(v_x_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg(lean_object* v_l_453_, lean_object* v_fallback_454_){
_start:
{
if (lean_obj_tag(v_l_453_) == 0)
{
lean_inc(v_fallback_454_);
return v_fallback_454_;
}
else
{
lean_object* v_tail_455_; 
v_tail_455_ = lean_ctor_get(v_l_453_, 1);
lean_inc(v_tail_455_);
return v_tail_455_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___redArg___boxed(lean_object* v_l_456_, lean_object* v_fallback_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_List_tailD___redArg(v_l_456_, v_fallback_457_);
lean_dec(v_fallback_457_);
lean_dec(v_l_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_List_tailD(lean_object* v_00_u03b1_459_, lean_object* v_l_460_, lean_object* v_fallback_461_){
_start:
{
if (lean_obj_tag(v_l_460_) == 0)
{
lean_inc(v_fallback_461_);
return v_fallback_461_;
}
else
{
lean_object* v_tail_462_; 
v_tail_462_ = lean_ctor_get(v_l_460_, 1);
lean_inc(v_tail_462_);
return v_tail_462_;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD___boxed(lean_object* v_00_u03b1_463_, lean_object* v_l_464_, lean_object* v_fallback_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_List_tailD(v_00_u03b1_463_, v_l_464_, v_fallback_465_);
lean_dec(v_fallback_465_);
lean_dec(v_l_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_List_filter___redArg(lean_object* v_p_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
lean_dec_ref(v_p_467_);
return v_x_468_;
}
else
{
lean_object* v_head_469_; lean_object* v_tail_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_481_; 
v_head_469_ = lean_ctor_get(v_x_468_, 0);
v_tail_470_ = lean_ctor_get(v_x_468_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_468_);
if (v_isSharedCheck_481_ == 0)
{
v___x_472_ = v_x_468_;
v_isShared_473_ = v_isSharedCheck_481_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_tail_470_);
lean_inc(v_head_469_);
lean_dec(v_x_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_481_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
lean_inc_ref(v_p_467_);
lean_inc(v_head_469_);
v___x_474_ = lean_apply_1(v_p_467_, v_head_469_);
v___x_475_ = lean_unbox(v___x_474_);
if (v___x_475_ == 0)
{
lean_del_object(v___x_472_);
lean_dec(v_head_469_);
v_x_468_ = v_tail_470_;
goto _start;
}
else
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l_List_filter___redArg(v_p_467_, v_tail_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v___x_477_);
v___x_479_ = v___x_472_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_head_469_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filter(lean_object* v_00_u03b1_482_, lean_object* v_p_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_List_filter___redArg(v_p_483_, v_x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg(lean_object* v_f_486_, lean_object* v_init_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_dec(v_f_486_);
lean_inc(v_init_487_);
return v_init_487_;
}
else
{
lean_object* v_head_489_; lean_object* v_tail_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_head_489_ = lean_ctor_get(v_x_488_, 0);
lean_inc(v_head_489_);
v_tail_490_ = lean_ctor_get(v_x_488_, 1);
lean_inc(v_tail_490_);
lean_dec_ref_known(v_x_488_, 2);
lean_inc(v_f_486_);
v___x_491_ = l_List_foldr___redArg(v_f_486_, v_init_487_, v_tail_490_);
v___x_492_ = lean_apply_2(v_f_486_, v_head_489_, v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___redArg___boxed(lean_object* v_f_493_, lean_object* v_init_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_List_foldr___redArg(v_f_493_, v_init_494_, v_x_495_);
lean_dec(v_init_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_List_foldr(lean_object* v_00_u03b1_497_, lean_object* v_00_u03b2_498_, lean_object* v_f_499_, lean_object* v_init_500_, lean_object* v_x_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_List_foldr___redArg(v_f_499_, v_init_500_, v_x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___boxed(lean_object* v_00_u03b1_503_, lean_object* v_00_u03b2_504_, lean_object* v_f_505_, lean_object* v_init_506_, lean_object* v_x_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_List_foldr(v_00_u03b1_503_, v_00_u03b2_504_, v_f_505_, v_init_506_, v_x_507_);
lean_dec(v_init_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_List_reverseAux___redArg(lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
return v_x_510_;
}
else
{
lean_object* v_head_511_; lean_object* v_tail_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_520_; 
v_head_511_ = lean_ctor_get(v_x_509_, 0);
v_tail_512_ = lean_ctor_get(v_x_509_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_509_);
if (v_isSharedCheck_520_ == 0)
{
v___x_514_ = v_x_509_;
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_tail_512_);
lean_inc(v_head_511_);
lean_dec(v_x_509_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v_x_510_);
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_head_511_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_x_510_);
v___x_517_ = v_reuseFailAlloc_519_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
v_x_509_ = v_tail_512_;
v_x_510_ = v___x_517_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object* v_00_u03b1_521_, lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_List_reverseAux___redArg(v_x_522_, v_x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_List_reverse___redArg(lean_object* v_as_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_box(0);
v___x_527_ = l_List_reverseAux___redArg(v_as_525_, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_List_reverse(lean_object* v_00_u03b1_528_, lean_object* v_as_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_List_reverse___redArg(v_as_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR___redArg(lean_object* v_as_531_, lean_object* v_bs_532_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = l_List_reverse___redArg(v_as_531_);
v___x_534_ = l_List_reverseAux___redArg(v___x_533_, v_bs_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_List_appendTR(lean_object* v_00_u03b1_535_, lean_object* v_as_536_, lean_object* v_bs_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_List_appendTR___redArg(v_as_536_, v_bs_537_);
return v___x_538_;
}
}
lean_object* l_List_instAppend___redArg(){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = ((lean_object*)(l_List_instAppend___redArg___closed__0));
return v___x_541_;
}
}
LEAN_EXPORT void l_List_instAppend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_542_;
v_res_542_ = l_List_instAppend___redArg();
stack->m_obj
 = v_res_542_;
}
LEAN_EXPORT lean_object* l_List_instAppend___redArg___boxed(lean_object* v___dummy_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_List_instAppend___redArg();
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_List_instAppend(lean_object* v_00_u03b1_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l_List_instAppend___redArg___closed__0));
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_List_singleton___redArg(lean_object* v_a_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_box(0);
v___x_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_549_, 0, v_a_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_List_singleton(lean_object* v_00_u03b1_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v_a_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg(lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v_zero_556_; uint8_t v_isZero_557_; 
v_zero_556_ = lean_unsigned_to_nat(0u);
v_isZero_557_ = lean_nat_dec_eq(v_x_554_, v_zero_556_);
if (v_isZero_557_ == 1)
{
lean_object* v___x_558_; 
lean_dec(v_x_555_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
else
{
lean_object* v_one_559_; lean_object* v_n_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_one_559_ = lean_unsigned_to_nat(1u);
v_n_560_ = lean_nat_sub(v_x_554_, v_one_559_);
lean_inc(v_x_555_);
v___x_561_ = l_List_replicate___redArg(v_n_560_, v_x_555_);
lean_dec(v_n_560_);
v___x_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_562_, 0, v_x_555_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_List_replicate___redArg___boxed(lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_List_replicate___redArg(v_x_563_, v_x_564_);
lean_dec(v_x_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_List_replicate(lean_object* v_00_u03b1_566_, lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_List_replicate___redArg(v_x_567_, v_x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_List_replicate___boxed(lean_object* v_00_u03b1_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_List_replicate(v_00_u03b1_570_, v_x_571_, v_x_572_);
lean_dec(v_x_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg(lean_object* v_n_574_, lean_object* v_a_575_, lean_object* v_l_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = l_List_length___redArg(v_l_576_);
v___x_578_ = lean_nat_sub(v_n_574_, v___x_577_);
lean_dec(v___x_577_);
v___x_579_ = l_List_replicate___redArg(v___x_578_, v_a_575_);
lean_dec(v___x_578_);
v___x_580_ = l_List_appendTR___redArg(v___x_579_, v_l_576_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___redArg___boxed(lean_object* v_n_581_, lean_object* v_a_582_, lean_object* v_l_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_List_leftpad___redArg(v_n_581_, v_a_582_, v_l_583_);
lean_dec(v_n_581_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad(lean_object* v_00_u03b1_585_, lean_object* v_n_586_, lean_object* v_a_587_, lean_object* v_l_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_List_leftpad___redArg(v_n_586_, v_a_587_, v_l_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___boxed(lean_object* v_00_u03b1_590_, lean_object* v_n_591_, lean_object* v_a_592_, lean_object* v_l_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_List_leftpad(v_00_u03b1_590_, v_n_591_, v_a_592_, v_l_593_);
lean_dec(v_n_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg(lean_object* v_n_595_, lean_object* v_a_596_, lean_object* v_l_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_598_ = l_List_length___redArg(v_l_597_);
v___x_599_ = lean_nat_sub(v_n_595_, v___x_598_);
lean_dec(v___x_598_);
v___x_600_ = l_List_replicate___redArg(v___x_599_, v_a_596_);
lean_dec(v___x_599_);
v___x_601_ = l_List_appendTR___redArg(v_l_597_, v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___redArg___boxed(lean_object* v_n_602_, lean_object* v_a_603_, lean_object* v_l_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_List_rightpad___redArg(v_n_602_, v_a_603_, v_l_604_);
lean_dec(v_n_602_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad(lean_object* v_00_u03b1_606_, lean_object* v_n_607_, lean_object* v_a_608_, lean_object* v_l_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_List_rightpad___redArg(v_n_607_, v_a_608_, v_l_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___boxed(lean_object* v_00_u03b1_611_, lean_object* v_n_612_, lean_object* v_a_613_, lean_object* v_l_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_List_rightpad(v_00_u03b1_611_, v_n_612_, v_a_613_, v_l_614_);
lean_dec(v_n_612_);
return v_res_615_;
}
}
lean_object* l_List_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_box(0);
return v___x_617_;
}
}
LEAN_EXPORT void l_List_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_618_;
v_res_618_ = l_List_instEmptyCollection___redArg();
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection___redArg___boxed(lean_object* v___dummy_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_List_instEmptyCollection___redArg();
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object* v_00_u03b1_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_box(0);
return v___x_622_;
}
}
uint8_t l_List_isEmpty___redArg(lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
uint8_t v___x_624_; 
v___x_624_ = 1;
return v___x_624_;
}
else
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
}
}
LEAN_EXPORT void l_List_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_623_ = stack[0].m_obj;
uint8_t v_res_626_;
v_res_626_ = l_List_isEmpty___redArg(v_x_623_);
stack->m_num = v_res_626_;
}
LEAN_EXPORT lean_object* l_List_isEmpty___redArg___boxed(lean_object* v_x_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_List_isEmpty___redArg(v_x_627_);
lean_dec(v_x_627_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
uint8_t l_List_isEmpty(lean_object* v_00_u03b1_630_, lean_object* v_x_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = l_List_isEmpty___redArg(v_x_631_);
return v___x_632_;
}
}
LEAN_EXPORT void l_List_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_631_ = stack[1].m_obj;
uint8_t v_res_633_;
v_res_633_ = l_List_isEmpty(lean_box(0), v_x_631_);
stack->m_num = v_res_633_;
}
LEAN_EXPORT lean_object* l_List_isEmpty___boxed(lean_object* v_00_u03b1_634_, lean_object* v_x_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_List_isEmpty(v_00_u03b1_634_, v_x_635_);
lean_dec(v_x_635_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
uint8_t l_List_elem___redArg(lean_object* v_inst_638_, lean_object* v_a_639_, lean_object* v_x_640_){
_start:
{
if (lean_obj_tag(v_x_640_) == 0)
{
uint8_t v___x_641_; 
lean_dec(v_a_639_);
lean_dec_ref(v_inst_638_);
v___x_641_ = 0;
return v___x_641_;
}
else
{
lean_object* v_head_642_; lean_object* v_tail_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_head_642_ = lean_ctor_get(v_x_640_, 0);
lean_inc(v_head_642_);
v_tail_643_ = lean_ctor_get(v_x_640_, 1);
lean_inc(v_tail_643_);
lean_dec_ref_known(v_x_640_, 2);
lean_inc_ref(v_inst_638_);
lean_inc(v_a_639_);
v___x_644_ = lean_apply_2(v_inst_638_, v_a_639_, v_head_642_);
v___x_645_ = lean_unbox(v___x_644_);
if (v___x_645_ == 0)
{
v_x_640_ = v_tail_643_;
goto _start;
}
else
{
uint8_t v___x_647_; 
lean_dec(v_tail_643_);
lean_dec(v_a_639_);
lean_dec_ref(v_inst_638_);
v___x_647_ = lean_unbox(v___x_644_);
return v___x_647_;
}
}
}
}
LEAN_EXPORT void l_List_elem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_638_ = stack[0].m_obj;
lean_object* v_a_639_ = stack[1].m_obj;
lean_object* v_x_640_ = stack[2].m_obj;
uint8_t v_res_648_;
v_res_648_ = l_List_elem___redArg(v_inst_638_, v_a_639_, v_x_640_);
stack->m_num = v_res_648_;
}
LEAN_EXPORT lean_object* l_List_elem___redArg___boxed(lean_object* v_inst_649_, lean_object* v_a_650_, lean_object* v_x_651_){
_start:
{
uint8_t v_res_652_; lean_object* v_r_653_; 
v_res_652_ = l_List_elem___redArg(v_inst_649_, v_a_650_, v_x_651_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
uint8_t l_List_elem(lean_object* v_00_u03b1_654_, lean_object* v_inst_655_, lean_object* v_a_656_, lean_object* v_x_657_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = l_List_elem___redArg(v_inst_655_, v_a_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT void l_List_elem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_655_ = stack[1].m_obj;
lean_object* v_a_656_ = stack[2].m_obj;
lean_object* v_x_657_ = stack[3].m_obj;
uint8_t v_res_659_;
v_res_659_ = l_List_elem(lean_box(0), v_inst_655_, v_a_656_, v_x_657_);
stack->m_num = v_res_659_;
}
LEAN_EXPORT lean_object* l_List_elem___boxed(lean_object* v_00_u03b1_660_, lean_object* v_inst_661_, lean_object* v_a_662_, lean_object* v_x_663_){
_start:
{
uint8_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_List_elem(v_00_u03b1_660_, v_inst_661_, v_a_662_, v_x_663_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
uint8_t l_List_contains___redArg(lean_object* v_inst_666_, lean_object* v_as_667_, lean_object* v_a_668_){
_start:
{
uint8_t v___x_669_; 
v___x_669_ = l_List_elem___redArg(v_inst_666_, v_a_668_, v_as_667_);
return v___x_669_;
}
}
LEAN_EXPORT void l_List_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_666_ = stack[0].m_obj;
lean_object* v_as_667_ = stack[1].m_obj;
lean_object* v_a_668_ = stack[2].m_obj;
uint8_t v_res_670_;
v_res_670_ = l_List_contains___redArg(v_inst_666_, v_as_667_, v_a_668_);
stack->m_num = v_res_670_;
}
LEAN_EXPORT lean_object* l_List_contains___redArg___boxed(lean_object* v_inst_671_, lean_object* v_as_672_, lean_object* v_a_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l_List_contains___redArg(v_inst_671_, v_as_672_, v_a_673_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
uint8_t l_List_contains(lean_object* v_00_u03b1_676_, lean_object* v_inst_677_, lean_object* v_as_678_, lean_object* v_a_679_){
_start:
{
uint8_t v___x_680_; 
v___x_680_ = l_List_elem___redArg(v_inst_677_, v_a_679_, v_as_678_);
return v___x_680_;
}
}
LEAN_EXPORT void l_List_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_677_ = stack[1].m_obj;
lean_object* v_as_678_ = stack[2].m_obj;
lean_object* v_a_679_ = stack[3].m_obj;
uint8_t v_res_681_;
v_res_681_ = l_List_contains(lean_box(0), v_inst_677_, v_as_678_, v_a_679_);
stack->m_num = v_res_681_;
}
LEAN_EXPORT lean_object* l_List_contains___boxed(lean_object* v_00_u03b1_682_, lean_object* v_inst_683_, lean_object* v_as_684_, lean_object* v_a_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_List_contains(v_00_u03b1_682_, v_inst_683_, v_as_684_, v_a_685_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
lean_object* l_List_instMembership___redArg(){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_box(0);
return v___x_689_;
}
}
LEAN_EXPORT void l_List_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_690_;
v_res_690_ = l_List_instMembership___redArg();
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l_List_instMembership___redArg___boxed(lean_object* v___dummy_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_List_instMembership___redArg();
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_List_instMembership(lean_object* v_00_u03b1_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = lean_box(0);
return v___x_694_;
}
}
lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(uint8_t v_x_695_, lean_object* v_h__1_696_, lean_object* v_h__2_697_){
_start:
{
if (v_x_695_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec(v_h__1_696_);
v___x_698_ = lean_box(0);
v___x_699_ = lean_apply_1(v_h__2_697_, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec(v_h__2_697_);
v___x_700_ = lean_box(0);
v___x_701_ = lean_apply_1(v_h__1_696_, v___x_700_);
return v___x_701_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_695_ = stack[0].m_num;
lean_object* v_h__1_696_ = stack[1].m_obj;
lean_object* v_h__2_697_ = stack[2].m_obj;
lean_object* v_res_702_;
v_res_702_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(v_x_695_, v_h__1_696_, v_h__2_697_);
stack->m_obj
 = v_res_702_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_703_, lean_object* v_h__1_704_, lean_object* v_h__2_705_){
_start:
{
uint8_t v_x_24__boxed_706_; lean_object* v_res_707_; 
v_x_24__boxed_706_ = lean_unbox(v_x_703_);
v_res_707_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_706_, v_h__1_704_, v_h__2_705_);
return v_res_707_;
}
}
lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object* v_motive_708_, uint8_t v_x_709_, lean_object* v_h__1_710_, lean_object* v_h__2_711_){
_start:
{
if (v_x_709_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec(v_h__1_710_);
v___x_712_ = lean_box(0);
v___x_713_ = lean_apply_1(v_h__2_711_, v___x_712_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v_h__2_711_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_apply_1(v_h__1_710_, v___x_714_);
return v___x_715_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_709_ = stack[1].m_num;
lean_object* v_h__1_710_ = stack[2].m_obj;
lean_object* v_h__2_711_ = stack[3].m_obj;
lean_object* v_res_716_;
v_res_716_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_box(0), v_x_709_, v_h__1_710_, v_h__2_711_);
stack->m_obj
 = v_res_716_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_717_, lean_object* v_x_718_, lean_object* v_h__1_719_, lean_object* v_h__2_720_){
_start:
{
uint8_t v_x_41__boxed_721_; lean_object* v_res_722_; 
v_x_41__boxed_721_ = lean_unbox(v_x_718_);
v_res_722_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(v_motive_717_, v_x_41__boxed_721_, v_h__1_719_, v_h__2_720_);
return v_res_722_;
}
}
uint8_t l_List_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_723_, lean_object* v_a_724_, lean_object* v_as_725_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = l_List_elem___redArg(v_inst_723_, v_a_724_, v_as_725_);
return v___x_726_;
}
}
LEAN_EXPORT void l_List_instDecidableMemOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_723_ = stack[0].m_obj;
lean_object* v_a_724_ = stack[1].m_obj;
lean_object* v_as_725_ = stack[2].m_obj;
uint8_t v_res_727_;
v_res_727_ = l_List_instDecidableMemOfLawfulBEq___redArg(v_inst_723_, v_a_724_, v_as_725_);
stack->m_num = v_res_727_;
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_728_, lean_object* v_a_729_, lean_object* v_as_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_List_instDecidableMemOfLawfulBEq___redArg(v_inst_728_, v_a_729_, v_as_730_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
uint8_t l_List_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_a_736_, lean_object* v_as_737_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = l_List_elem___redArg(v_inst_734_, v_a_736_, v_as_737_);
return v___x_738_;
}
}
LEAN_EXPORT void l_List_instDecidableMemOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_734_ = stack[1].m_obj;
lean_object* v_a_736_ = stack[3].m_obj;
lean_object* v_as_737_ = stack[4].m_obj;
uint8_t v_res_739_;
v_res_739_ = l_List_instDecidableMemOfLawfulBEq(lean_box(0), v_inst_734_, lean_box(0), v_a_736_, v_as_737_);
stack->m_num = v_res_739_;
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_a_743_, lean_object* v_as_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_List_instDecidableMemOfLawfulBEq(v_00_u03b1_740_, v_inst_741_, v_inst_742_, v_a_743_, v_as_744_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
uint8_t l_List_decidableBEx___redArg(lean_object* v_inst_747_, lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
uint8_t v___x_749_; 
lean_dec_ref(v_inst_747_);
v___x_749_ = 0;
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
uint8_t v_decide_754_; 
v_decide_754_ = l_List_decidableBEx___redArg(v_inst_747_, v_tail_751_);
if (v_decide_754_ == 0)
{
uint8_t v___x_755_; 
v___x_755_ = lean_unbox(v___x_752_);
return v___x_755_;
}
else
{
return v_decide_754_;
}
}
else
{
uint8_t v___x_756_; 
lean_dec(v_tail_751_);
lean_dec_ref(v_inst_747_);
v___x_756_ = lean_unbox(v___x_752_);
return v___x_756_;
}
}
}
}
LEAN_EXPORT void l_List_decidableBEx___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_747_ = stack[0].m_obj;
lean_object* v_x_748_ = stack[1].m_obj;
uint8_t v_res_757_;
v_res_757_ = l_List_decidableBEx___redArg(v_inst_747_, v_x_748_);
stack->m_num = v_res_757_;
}
LEAN_EXPORT lean_object* l_List_decidableBEx___redArg___boxed(lean_object* v_inst_758_, lean_object* v_x_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_List_decidableBEx___redArg(v_inst_758_, v_x_759_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
uint8_t l_List_decidableBEx(lean_object* v_00_u03b1_762_, lean_object* v_p_763_, lean_object* v_inst_764_, lean_object* v_x_765_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = l_List_decidableBEx___redArg(v_inst_764_, v_x_765_);
return v___x_766_;
}
}
LEAN_EXPORT void l_List_decidableBEx_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_764_ = stack[2].m_obj;
lean_object* v_x_765_ = stack[3].m_obj;
uint8_t v_res_767_;
v_res_767_ = l_List_decidableBEx(lean_box(0), lean_box(0), v_inst_764_, v_x_765_);
stack->m_num = v_res_767_;
}
LEAN_EXPORT lean_object* l_List_decidableBEx___boxed(lean_object* v_00_u03b1_768_, lean_object* v_p_769_, lean_object* v_inst_770_, lean_object* v_x_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_List_decidableBEx(v_00_u03b1_768_, v_p_769_, v_inst_770_, v_x_771_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
uint8_t l_List_decidableBAll___redArg(lean_object* v_inst_774_, lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_775_) == 0)
{
uint8_t v___x_776_; 
lean_dec_ref(v_inst_774_);
v___x_776_ = 1;
return v___x_776_;
}
else
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_head_777_ = lean_ctor_get(v_x_775_, 0);
lean_inc(v_head_777_);
v_tail_778_ = lean_ctor_get(v_x_775_, 1);
lean_inc(v_tail_778_);
lean_dec_ref_known(v_x_775_, 2);
lean_inc_ref(v_inst_774_);
v___x_779_ = lean_apply_1(v_inst_774_, v_head_777_);
v___x_780_ = lean_unbox(v___x_779_);
if (v___x_780_ == 0)
{
uint8_t v___x_781_; 
lean_dec(v_tail_778_);
lean_dec_ref(v_inst_774_);
v___x_781_ = lean_unbox(v___x_779_);
return v___x_781_;
}
else
{
uint8_t v_decide_782_; 
v_decide_782_ = l_List_decidableBAll___redArg(v_inst_774_, v_tail_778_);
if (v_decide_782_ == 0)
{
return v_decide_782_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = lean_unbox(v___x_779_);
return v___x_783_;
}
}
}
}
}
LEAN_EXPORT void l_List_decidableBAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_774_ = stack[0].m_obj;
lean_object* v_x_775_ = stack[1].m_obj;
uint8_t v_res_784_;
v_res_784_ = l_List_decidableBAll___redArg(v_inst_774_, v_x_775_);
stack->m_num = v_res_784_;
}
LEAN_EXPORT lean_object* l_List_decidableBAll___redArg___boxed(lean_object* v_inst_785_, lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_List_decidableBAll___redArg(v_inst_785_, v_x_786_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
uint8_t l_List_decidableBAll(lean_object* v_00_u03b1_789_, lean_object* v_p_790_, lean_object* v_inst_791_, lean_object* v_x_792_){
_start:
{
uint8_t v___x_793_; 
v___x_793_ = l_List_decidableBAll___redArg(v_inst_791_, v_x_792_);
return v___x_793_;
}
}
LEAN_EXPORT void l_List_decidableBAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_791_ = stack[2].m_obj;
lean_object* v_x_792_ = stack[3].m_obj;
uint8_t v_res_794_;
v_res_794_ = l_List_decidableBAll(lean_box(0), lean_box(0), v_inst_791_, v_x_792_);
stack->m_num = v_res_794_;
}
LEAN_EXPORT lean_object* l_List_decidableBAll___boxed(lean_object* v_00_u03b1_795_, lean_object* v_p_796_, lean_object* v_inst_797_, lean_object* v_x_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_List_decidableBAll(v_00_u03b1_795_, v_p_796_, v_inst_797_, v_x_798_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT lean_object* l_List_take___redArg(lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v_zero_803_; uint8_t v_isZero_804_; 
v_zero_803_ = lean_unsigned_to_nat(0u);
v_isZero_804_ = lean_nat_dec_eq(v_x_801_, v_zero_803_);
if (v_isZero_804_ == 1)
{
lean_object* v___x_805_; 
lean_dec(v_x_802_);
v___x_805_ = lean_box(0);
return v___x_805_;
}
else
{
if (lean_obj_tag(v_x_802_) == 0)
{
return v_x_802_;
}
else
{
lean_object* v_head_806_; lean_object* v_tail_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_817_; 
v_head_806_ = lean_ctor_get(v_x_802_, 0);
v_tail_807_ = lean_ctor_get(v_x_802_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_817_ == 0)
{
v___x_809_ = v_x_802_;
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_tail_807_);
lean_inc(v_head_806_);
lean_dec(v_x_802_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_one_811_; lean_object* v_n_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v_one_811_ = lean_unsigned_to_nat(1u);
v_n_812_ = lean_nat_sub(v_x_801_, v_one_811_);
v___x_813_ = l_List_take___redArg(v_n_812_, v_tail_807_);
lean_dec(v_n_812_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v___x_813_);
v___x_815_ = v___x_809_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_head_806_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_take___redArg___boxed(lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_List_take___redArg(v_x_818_, v_x_819_);
lean_dec(v_x_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_List_take(lean_object* v_00_u03b1_821_, lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_List_take___redArg(v_x_822_, v_x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_List_take___boxed(lean_object* v_00_u03b1_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_List_take(v_00_u03b1_825_, v_x_826_, v_x_827_);
lean_dec(v_x_826_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg(lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
lean_object* v_zero_831_; uint8_t v_isZero_832_; 
v_zero_831_ = lean_unsigned_to_nat(0u);
v_isZero_832_ = lean_nat_dec_eq(v_x_829_, v_zero_831_);
if (v_isZero_832_ == 1)
{
lean_dec(v_x_829_);
lean_inc(v_x_830_);
return v_x_830_;
}
else
{
if (lean_obj_tag(v_x_830_) == 0)
{
lean_dec(v_x_829_);
return v_x_830_;
}
else
{
lean_object* v_tail_833_; lean_object* v_one_834_; lean_object* v_n_835_; 
v_tail_833_ = lean_ctor_get(v_x_830_, 1);
v_one_834_ = lean_unsigned_to_nat(1u);
v_n_835_ = lean_nat_sub(v_x_829_, v_one_834_);
lean_dec(v_x_829_);
v_x_829_ = v_n_835_;
v_x_830_ = v_tail_833_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_drop___redArg___boxed(lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_List_drop___redArg(v_x_837_, v_x_838_);
lean_dec(v_x_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_List_drop(lean_object* v_00_u03b1_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_List_drop___redArg(v_x_841_, v_x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_List_drop___boxed(lean_object* v_00_u03b1_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_List_drop(v_00_u03b1_844_, v_x_845_, v_x_846_);
lean_dec(v_x_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg(lean_object* v_l_848_, lean_object* v_start_849_, lean_object* v_stop_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_nat_sub(v_stop_850_, v_start_849_);
v___x_852_ = l_List_drop___redArg(v_start_849_, v_l_848_);
v___x_853_ = l_List_take___redArg(v___x_851_, v___x_852_);
lean_dec(v___x_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_List_extract___redArg___boxed(lean_object* v_l_854_, lean_object* v_start_855_, lean_object* v_stop_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_List_extract___redArg(v_l_854_, v_start_855_, v_stop_856_);
lean_dec(v_stop_856_);
lean_dec(v_l_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_List_extract(lean_object* v_00_u03b1_858_, lean_object* v_l_859_, lean_object* v_start_860_, lean_object* v_stop_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_nat_sub(v_stop_861_, v_start_860_);
v___x_863_ = l_List_drop___redArg(v_start_860_, v_l_859_);
v___x_864_ = l_List_take___redArg(v___x_862_, v___x_863_);
lean_dec(v___x_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_List_extract___boxed(lean_object* v_00_u03b1_865_, lean_object* v_l_866_, lean_object* v_start_867_, lean_object* v_stop_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_List_extract(v_00_u03b1_865_, v_l_866_, v_start_867_, v_stop_868_);
lean_dec(v_stop_868_);
lean_dec(v_l_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhile___redArg(lean_object* v_p_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_dec_ref(v_p_870_);
return v_x_871_;
}
else
{
lean_object* v_head_872_; lean_object* v_tail_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_884_; 
v_head_872_ = lean_ctor_get(v_x_871_, 0);
v_tail_873_ = lean_ctor_get(v_x_871_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_884_ == 0)
{
v___x_875_ = v_x_871_;
v_isShared_876_ = v_isSharedCheck_884_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_tail_873_);
lean_inc(v_head_872_);
lean_dec(v_x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_884_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; uint8_t v___x_878_; 
lean_inc_ref(v_p_870_);
lean_inc(v_head_872_);
v___x_877_ = lean_apply_1(v_p_870_, v_head_872_);
v___x_878_ = lean_unbox(v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
lean_del_object(v___x_875_);
lean_dec(v_tail_873_);
lean_dec(v_head_872_);
lean_dec_ref(v_p_870_);
v___x_879_ = lean_box(0);
return v___x_879_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = l_List_takeWhile___redArg(v_p_870_, v_tail_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v___x_880_);
v___x_882_ = v___x_875_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_head_872_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_takeWhile(lean_object* v_00_u03b1_885_, lean_object* v_p_886_, lean_object* v_x_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_List_takeWhile___redArg(v_p_886_, v_x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___redArg(lean_object* v_p_889_, lean_object* v_x_890_){
_start:
{
if (lean_obj_tag(v_x_890_) == 0)
{
lean_dec_ref(v_p_889_);
return v_x_890_;
}
else
{
lean_object* v_head_891_; lean_object* v_tail_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_head_891_ = lean_ctor_get(v_x_890_, 0);
v_tail_892_ = lean_ctor_get(v_x_890_, 1);
lean_inc_ref(v_p_889_);
lean_inc(v_head_891_);
v___x_893_ = lean_apply_1(v_p_889_, v_head_891_);
v___x_894_ = lean_unbox(v___x_893_);
if (v___x_894_ == 0)
{
lean_dec_ref(v_p_889_);
return v_x_890_;
}
else
{
lean_inc(v_tail_892_);
lean_dec_ref_known(v_x_890_, 2);
v_x_890_ = v_tail_892_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object* v_00_u03b1_896_, lean_object* v_p_897_, lean_object* v_x_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_List_dropWhile___redArg(v_p_897_, v_x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___redArg(lean_object* v_p_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
if (lean_obj_tag(v_a_901_) == 0)
{
lean_object* v_fst_903_; lean_object* v_snd_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_913_; 
lean_dec_ref(v_p_900_);
v_fst_903_ = lean_ctor_get(v_a_902_, 0);
v_snd_904_ = lean_ctor_get(v_a_902_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_902_);
if (v_isSharedCheck_913_ == 0)
{
v___x_906_ = v_a_902_;
v_isShared_907_ = v_isSharedCheck_913_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_snd_904_);
lean_inc(v_fst_903_);
lean_dec(v_a_902_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_913_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_908_ = l_List_reverse___redArg(v_fst_903_);
v___x_909_ = l_List_reverse___redArg(v_snd_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v___x_909_);
lean_ctor_set(v___x_906_, 0, v___x_908_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
else
{
lean_object* v_head_914_; lean_object* v_tail_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_941_; 
v_head_914_ = lean_ctor_get(v_a_901_, 0);
v_tail_915_ = lean_ctor_get(v_a_901_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_a_901_);
if (v_isSharedCheck_941_ == 0)
{
v___x_917_ = v_a_901_;
v_isShared_918_ = v_isSharedCheck_941_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_tail_915_);
lean_inc(v_head_914_);
lean_dec(v_a_901_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_941_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_fst_919_; lean_object* v_snd_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_940_; 
v_fst_919_ = lean_ctor_get(v_a_902_, 0);
v_snd_920_ = lean_ctor_get(v_a_902_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_a_902_);
if (v_isSharedCheck_940_ == 0)
{
v___x_922_ = v_a_902_;
v_isShared_923_ = v_isSharedCheck_940_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_snd_920_);
lean_inc(v_fst_919_);
lean_dec(v_a_902_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_940_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; uint8_t v___x_925_; 
lean_inc_ref(v_p_900_);
lean_inc(v_head_914_);
v___x_924_ = lean_apply_1(v_p_900_, v_head_914_);
v___x_925_ = lean_unbox(v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_927_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v_snd_920_);
v___x_927_ = v___x_917_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_head_914_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_snd_920_);
v___x_927_ = v_reuseFailAlloc_932_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v___x_927_);
v___x_929_ = v___x_922_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_fst_919_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_927_);
v___x_929_ = v_reuseFailAlloc_931_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
v_a_901_ = v_tail_915_;
v_a_902_ = v___x_929_;
goto _start;
}
}
}
else
{
lean_object* v___x_934_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v_fst_919_);
v___x_934_ = v___x_917_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_head_914_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_fst_919_);
v___x_934_ = v_reuseFailAlloc_939_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_934_);
v___x_936_ = v___x_922_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_snd_920_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
v_a_901_ = v_tail_915_;
v_a_902_ = v___x_936_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object* v_00_u03b1_942_, lean_object* v_p_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_List_partition_loop___redArg(v_p_943_, v_a_944_, v_a_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_List_partition___redArg(lean_object* v_p_949_, lean_object* v_as_950_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_952_ = l_List_partition_loop___redArg(v_p_949_, v_as_950_, v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_List_partition(lean_object* v_00_u03b1_953_, lean_object* v_p_954_, lean_object* v_as_955_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_957_ = l_List_partition_loop___redArg(v_p_954_, v_as_955_, v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_List_dropLast___redArg(lean_object* v_x_958_){
_start:
{
if (lean_obj_tag(v_x_958_) == 0)
{
return v_x_958_;
}
else
{
lean_object* v_tail_959_; 
v_tail_959_ = lean_ctor_get(v_x_958_, 1);
lean_inc(v_tail_959_);
if (lean_obj_tag(v_tail_959_) == 0)
{
lean_dec_ref_known(v_x_958_, 2);
return v_tail_959_;
}
else
{
lean_object* v_head_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v_head_960_ = lean_ctor_get(v_x_958_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v_x_958_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v_x_958_, 1);
lean_dec(v_unused_969_);
v___x_962_ = v_x_958_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_head_960_);
lean_dec(v_x_958_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = l_List_dropLast___redArg(v_tail_959_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_head_960_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropLast(lean_object* v_00_u03b1_970_, lean_object* v_x_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_List_dropLast___redArg(v_x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_973_, lean_object* v_h__1_974_, lean_object* v_h__2_975_, lean_object* v_h__3_976_){
_start:
{
if (lean_obj_tag(v_x_973_) == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec(v_h__3_976_);
lean_dec(v_h__2_975_);
v___x_977_ = lean_box(0);
v___x_978_ = lean_apply_1(v_h__1_974_, v___x_977_);
return v___x_978_;
}
else
{
lean_object* v_tail_979_; 
lean_dec(v_h__1_974_);
v_tail_979_ = lean_ctor_get(v_x_973_, 1);
if (lean_obj_tag(v_tail_979_) == 0)
{
lean_object* v_head_980_; lean_object* v___x_981_; 
lean_dec(v_h__3_976_);
v_head_980_ = lean_ctor_get(v_x_973_, 0);
lean_inc(v_head_980_);
lean_dec_ref_known(v_x_973_, 2);
v___x_981_ = lean_apply_1(v_h__2_975_, v_head_980_);
return v___x_981_;
}
else
{
lean_object* v_head_982_; lean_object* v___x_983_; 
lean_inc_ref(v_tail_979_);
lean_dec(v_h__2_975_);
v_head_982_ = lean_ctor_get(v_x_973_, 0);
lean_inc(v_head_982_);
lean_dec_ref_known(v_x_973_, 2);
v___x_983_ = lean_apply_3(v_h__3_976_, v_head_982_, v_tail_979_, lean_box(0));
return v___x_983_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_984_, lean_object* v_motive_985_, lean_object* v_x_986_, lean_object* v_h__1_987_, lean_object* v_h__2_988_, lean_object* v_h__3_989_){
_start:
{
if (lean_obj_tag(v_x_986_) == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v_h__3_989_);
lean_dec(v_h__2_988_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_apply_1(v_h__1_987_, v___x_990_);
return v___x_991_;
}
else
{
lean_object* v_tail_992_; 
lean_dec(v_h__1_987_);
v_tail_992_ = lean_ctor_get(v_x_986_, 1);
if (lean_obj_tag(v_tail_992_) == 0)
{
lean_object* v_head_993_; lean_object* v___x_994_; 
lean_dec(v_h__3_989_);
v_head_993_ = lean_ctor_get(v_x_986_, 0);
lean_inc(v_head_993_);
lean_dec_ref_known(v_x_986_, 2);
v___x_994_ = lean_apply_1(v_h__2_988_, v_head_993_);
return v___x_994_;
}
else
{
lean_object* v_head_995_; lean_object* v___x_996_; 
lean_inc_ref(v_tail_992_);
lean_dec(v_h__2_988_);
v_head_995_ = lean_ctor_get(v_x_986_, 0);
lean_inc(v_head_995_);
lean_dec_ref_known(v_x_986_, 2);
v___x_996_ = lean_apply_3(v_h__3_989_, v_head_995_, v_tail_992_, lean_box(0));
return v___x_996_;
}
}
}
}
lean_object* l_List_instHasSubset___redArg(){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lean_box(0);
return v___x_998_;
}
}
LEAN_EXPORT void l_List_instHasSubset___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_999_;
v_res_999_ = l_List_instHasSubset___redArg();
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l_List_instHasSubset___redArg___boxed(lean_object* v___dummy_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_List_instHasSubset___redArg();
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object* v_00_u03b1_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_box(0);
return v___x_1003_;
}
}
uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(lean_object* v___f_1004_, lean_object* v_x_1005_, lean_object* v_a_1006_){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = l_List_elem___redArg(v___f_1004_, v_a_1006_, v_x_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT void l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1004_ = stack[0].m_obj;
lean_object* v_x_1005_ = stack[1].m_obj;
lean_object* v_a_1006_ = stack[2].m_obj;
uint8_t v_res_1008_;
v_res_1008_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(v___f_1004_, v_x_1005_, v_a_1006_);
stack->m_num = v_res_1008_;
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(lean_object* v___f_1009_, lean_object* v_x_1010_, lean_object* v_a_1011_){
_start:
{
uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_res_1012_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(v___f_1009_, v_x_1010_, v_a_1011_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg(lean_object* v_inst_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v___f_1017_; lean_object* v___f_1018_; uint8_t v___x_1019_; 
v___f_1017_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1017_, 0, v_inst_1014_);
v___f_1018_ = lean_alloc_closure((void*)(l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1018_, 0, v___f_1017_);
lean_closure_set(v___f_1018_, 1, v_x_1016_);
v___x_1019_ = l_List_decidableBAll___redArg(v___f_1018_, v_x_1015_);
return v___x_1019_;
}
}
LEAN_EXPORT void l_List_instDecidableRelSubsetOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1014_ = stack[0].m_obj;
lean_object* v_x_1015_ = stack[1].m_obj;
lean_object* v_x_1016_ = stack[2].m_obj;
uint8_t v_res_1020_;
v_res_1020_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1014_, v_x_1015_, v_x_1016_);
stack->m_num = v_res_1020_;
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(lean_object* v_inst_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
uint8_t v_res_1024_; lean_object* v_r_1025_; 
v_res_1024_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1021_, v_x_1022_, v_x_1023_);
v_r_1025_ = lean_box(v_res_1024_);
return v_r_1025_;
}
}
uint8_t l_List_instDecidableRelSubsetOfDecidableEq(lean_object* v_00_u03b1_1026_, lean_object* v_inst_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_1027_, v_x_1028_, v_x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT void l_List_instDecidableRelSubsetOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1027_ = stack[1].m_obj;
lean_object* v_x_1028_ = stack[2].m_obj;
lean_object* v_x_1029_ = stack[3].m_obj;
uint8_t v_res_1031_;
v_res_1031_ = l_List_instDecidableRelSubsetOfDecidableEq(lean_box(0), v_inst_1027_, v_x_1028_, v_x_1029_);
stack->m_num = v_res_1031_;
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___boxed(lean_object* v_00_u03b1_1032_, lean_object* v_inst_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
uint8_t v_res_1036_; lean_object* v_r_1037_; 
v_res_1036_ = l_List_instDecidableRelSubsetOfDecidableEq(v_00_u03b1_1032_, v_inst_1033_, v_x_1034_, v_x_1035_);
v_r_1037_ = lean_box(v_res_1036_);
return v_r_1037_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2));
v___x_1072_ = l_String_toRawSubstring_x27(v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object* v_x_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
lean_inc(v_x_1092_);
v___x_1096_ = l_Lean_Syntax_isOfKind(v_x_1092_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v_x_1092_);
v___x_1097_ = lean_box(1);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_a_1094_);
return v___x_1098_;
}
else
{
lean_object* v_quotContext_1099_; lean_object* v_currMacroScope_1100_; lean_object* v_ref_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_quotContext_1099_ = lean_ctor_get(v_a_1093_, 1);
v_currMacroScope_1100_ = lean_ctor_get(v_a_1093_, 2);
v_ref_1101_ = lean_ctor_get(v_a_1093_, 5);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = l_Lean_Syntax_getArg(v_x_1092_, v___x_1102_);
v___x_1104_ = lean_unsigned_to_nat(2u);
v___x_1105_ = l_Lean_Syntax_getArg(v_x_1092_, v___x_1104_);
lean_dec(v_x_1092_);
v___x_1106_ = 0;
v___x_1107_ = l_Lean_SourceInfo_fromRef(v_ref_1101_, v___x_1106_);
v___x_1108_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1109_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
v___x_1110_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4));
lean_inc(v_currMacroScope_1100_);
lean_inc(v_quotContext_1099_);
v___x_1111_ = l_Lean_addMacroScope(v_quotContext_1099_, v___x_1110_, v_currMacroScope_1100_);
v___x_1112_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10));
lean_inc_n(v___x_1107_, 2);
v___x_1113_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1107_);
lean_ctor_set(v___x_1113_, 1, v___x_1109_);
lean_ctor_set(v___x_1113_, 2, v___x_1111_);
lean_ctor_set(v___x_1113_, 3, v___x_1112_);
v___x_1114_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1115_ = l_Lean_Syntax_node2(v___x_1107_, v___x_1114_, v___x_1103_, v___x_1105_);
v___x_1116_ = l_Lean_Syntax_node2(v___x_1107_, v___x_1108_, v___x_1113_, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_a_1094_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___boxed(lean_object* v_x_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(v_x_1118_, v_a_1119_, v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object* v_x_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1125_);
v___x_1129_ = l_Lean_Syntax_isOfKind(v_x_1125_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_x_1125_);
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v_a_1127_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = l_Lean_Syntax_getArg(v_x_1125_, v___x_1132_);
v___x_1134_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1133_);
v___x_1135_ = l_Lean_Syntax_isOfKind(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v___x_1133_);
lean_dec(v_x_1125_);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_a_1127_);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = l_Lean_Syntax_getArg(v_x_1125_, v___x_1138_);
lean_dec(v_x_1125_);
v___x_1140_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1139_);
v___x_1141_ = l_Lean_Syntax_matchesNull(v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec(v___x_1139_);
lean_dec(v___x_1133_);
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v_a_1127_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v_ref_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1144_ = l_Lean_Syntax_getArg(v___x_1139_, v___x_1132_);
v___x_1145_ = l_Lean_Syntax_getArg(v___x_1139_, v___x_1138_);
lean_dec(v___x_1139_);
v_ref_1146_ = l_Lean_replaceRef(v___x_1133_, v_a_1126_);
lean_dec(v___x_1133_);
v___x_1147_ = 0;
v___x_1148_ = l_Lean_SourceInfo_fromRef(v_ref_1146_, v___x_1147_);
lean_dec(v_ref_1146_);
v___x_1149_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__2));
v___x_1150_ = ((lean_object*)(l_List_term___x3c_x2b___00__closed__5));
lean_inc(v___x_1148_);
v___x_1151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1148_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_Syntax_node3(v___x_1148_, v___x_1149_, v___x_1144_, v___x_1151_, v___x_1145_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_a_1127_);
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object* v_x_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(v_x_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1155_);
return v_res_1157_;
}
}
uint8_t l_List_isSublist___redArg(lean_object* v_inst_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
if (lean_obj_tag(v_x_1159_) == 0)
{
uint8_t v___x_1161_; 
lean_dec(v_x_1160_);
lean_dec_ref(v_inst_1158_);
v___x_1161_ = 1;
return v___x_1161_;
}
else
{
if (lean_obj_tag(v_x_1160_) == 0)
{
uint8_t v___x_1162_; 
lean_dec_ref_known(v_x_1159_, 2);
lean_dec_ref(v_inst_1158_);
v___x_1162_ = 0;
return v___x_1162_;
}
else
{
lean_object* v_head_1163_; lean_object* v_tail_1164_; lean_object* v_head_1165_; lean_object* v_tail_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v_head_1163_ = lean_ctor_get(v_x_1159_, 0);
v_tail_1164_ = lean_ctor_get(v_x_1159_, 1);
v_head_1165_ = lean_ctor_get(v_x_1160_, 0);
lean_inc(v_head_1165_);
v_tail_1166_ = lean_ctor_get(v_x_1160_, 1);
lean_inc(v_tail_1166_);
lean_dec_ref_known(v_x_1160_, 2);
lean_inc_ref(v_inst_1158_);
lean_inc(v_head_1163_);
v___x_1167_ = lean_apply_2(v_inst_1158_, v_head_1163_, v_head_1165_);
v___x_1168_ = lean_unbox(v___x_1167_);
if (v___x_1168_ == 0)
{
v_x_1160_ = v_tail_1166_;
goto _start;
}
else
{
lean_inc(v_tail_1164_);
lean_dec_ref_known(v_x_1159_, 2);
v_x_1159_ = v_tail_1164_;
v_x_1160_ = v_tail_1166_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_isSublist___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1158_ = stack[0].m_obj;
lean_object* v_x_1159_ = stack[1].m_obj;
lean_object* v_x_1160_ = stack[2].m_obj;
uint8_t v_res_1171_;
v_res_1171_ = l_List_isSublist___redArg(v_inst_1158_, v_x_1159_, v_x_1160_);
stack->m_num = v_res_1171_;
}
LEAN_EXPORT lean_object* l_List_isSublist___redArg___boxed(lean_object* v_inst_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
uint8_t v_res_1175_; lean_object* v_r_1176_; 
v_res_1175_ = l_List_isSublist___redArg(v_inst_1172_, v_x_1173_, v_x_1174_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
uint8_t l_List_isSublist(lean_object* v_00_u03b1_1177_, lean_object* v_inst_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = l_List_isSublist___redArg(v_inst_1178_, v_x_1179_, v_x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT void l_List_isSublist_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1178_ = stack[1].m_obj;
lean_object* v_x_1179_ = stack[2].m_obj;
lean_object* v_x_1180_ = stack[3].m_obj;
uint8_t v_res_1182_;
v_res_1182_ = l_List_isSublist(lean_box(0), v_inst_1178_, v_x_1179_, v_x_1180_);
stack->m_num = v_res_1182_;
}
LEAN_EXPORT lean_object* l_List_isSublist___boxed(lean_object* v_00_u03b1_1183_, lean_object* v_inst_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_){
_start:
{
uint8_t v_res_1187_; lean_object* v_r_1188_; 
v_res_1187_ = l_List_isSublist(v_00_u03b1_1183_, v_inst_1184_, v_x_1185_, v_x_1186_);
v_r_1188_ = lean_box(v_res_1187_);
return v_r_1188_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0));
v___x_1207_ = l_String_toRawSubstring_x27(v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object* v_x_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
lean_inc(v_x_1219_);
v___x_1223_ = l_Lean_Syntax_isOfKind(v_x_1219_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec(v_x_1219_);
v___x_1224_ = lean_box(1);
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v_a_1221_);
return v___x_1225_;
}
else
{
lean_object* v_quotContext_1226_; lean_object* v_currMacroScope_1227_; lean_object* v_ref_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_quotContext_1226_ = lean_ctor_get(v_a_1220_, 1);
v_currMacroScope_1227_ = lean_ctor_get(v_a_1220_, 2);
v_ref_1228_ = lean_ctor_get(v_a_1220_, 5);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1229_);
v___x_1231_ = lean_unsigned_to_nat(2u);
v___x_1232_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1231_);
lean_dec(v_x_1219_);
v___x_1233_ = 0;
v___x_1234_ = l_Lean_SourceInfo_fromRef(v_ref_1228_, v___x_1233_);
v___x_1235_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1236_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
v___x_1237_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1227_);
lean_inc(v_quotContext_1226_);
v___x_1238_ = l_Lean_addMacroScope(v_quotContext_1226_, v___x_1237_, v_currMacroScope_1227_);
v___x_1239_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1234_, 2);
v___x_1240_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1234_);
lean_ctor_set(v___x_1240_, 1, v___x_1236_);
lean_ctor_set(v___x_1240_, 2, v___x_1238_);
lean_ctor_set(v___x_1240_, 3, v___x_1239_);
v___x_1241_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1242_ = l_Lean_Syntax_node2(v___x_1234_, v___x_1241_, v___x_1230_, v___x_1232_);
v___x_1243_ = l_Lean_Syntax_node2(v___x_1234_, v___x_1235_, v___x_1240_, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v_a_1221_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___boxed(lean_object* v_x_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(v_x_1245_, v_a_1246_, v_a_1247_);
lean_dec_ref(v_a_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object* v_x_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1249_);
v___x_1253_ = l_Lean_Syntax_isOfKind(v_x_1249_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec(v_x_1249_);
v___x_1254_ = lean_box(0);
v___x_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v_a_1251_);
return v___x_1255_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = l_Lean_Syntax_getArg(v_x_1249_, v___x_1256_);
v___x_1258_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1257_);
v___x_1259_ = l_Lean_Syntax_isOfKind(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_dec(v___x_1257_);
lean_dec(v_x_1249_);
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v_a_1251_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = l_Lean_Syntax_getArg(v_x_1249_, v___x_1262_);
lean_dec(v_x_1249_);
v___x_1264_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1263_);
v___x_1265_ = l_Lean_Syntax_matchesNull(v___x_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v___x_1263_);
lean_dec(v___x_1257_);
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v_a_1251_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_ref_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1268_ = l_Lean_Syntax_getArg(v___x_1263_, v___x_1256_);
v___x_1269_ = l_Lean_Syntax_getArg(v___x_1263_, v___x_1262_);
lean_dec(v___x_1263_);
v_ref_1270_ = l_Lean_replaceRef(v___x_1257_, v_a_1250_);
lean_dec(v___x_1257_);
v___x_1271_ = 0;
v___x_1272_ = l_Lean_SourceInfo_fromRef(v_ref_1270_, v___x_1271_);
lean_dec(v_ref_1270_);
v___x_1273_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__1));
v___x_1274_ = ((lean_object*)(l_List_term___x3c_x2b_x3a___00__closed__2));
lean_inc(v___x_1272_);
v___x_1275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1272_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lean_Syntax_node3(v___x_1272_, v___x_1273_, v___x_1268_, v___x_1275_, v___x_1269_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_a_1251_);
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object* v_x_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(v_x_1278_, v_a_1279_, v_a_1280_);
lean_dec(v_a_1279_);
return v_res_1281_;
}
}
uint8_t l_List_isPrefixOf___redArg(lean_object* v_inst_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
if (lean_obj_tag(v_x_1283_) == 0)
{
uint8_t v___x_1285_; 
lean_dec(v_x_1284_);
lean_dec_ref(v_inst_1282_);
v___x_1285_ = 1;
return v___x_1285_;
}
else
{
if (lean_obj_tag(v_x_1284_) == 0)
{
uint8_t v___x_1286_; 
lean_dec_ref_known(v_x_1283_, 2);
lean_dec_ref(v_inst_1282_);
v___x_1286_ = 0;
return v___x_1286_;
}
else
{
lean_object* v_head_1287_; lean_object* v_tail_1288_; lean_object* v_head_1289_; lean_object* v_tail_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_head_1287_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_head_1287_);
v_tail_1288_ = lean_ctor_get(v_x_1283_, 1);
lean_inc(v_tail_1288_);
lean_dec_ref_known(v_x_1283_, 2);
v_head_1289_ = lean_ctor_get(v_x_1284_, 0);
lean_inc(v_head_1289_);
v_tail_1290_ = lean_ctor_get(v_x_1284_, 1);
lean_inc(v_tail_1290_);
lean_dec_ref_known(v_x_1284_, 2);
lean_inc_ref(v_inst_1282_);
v___x_1291_ = lean_apply_2(v_inst_1282_, v_head_1287_, v_head_1289_);
v___x_1292_ = lean_unbox(v___x_1291_);
if (v___x_1292_ == 0)
{
uint8_t v___x_1293_; 
lean_dec(v_tail_1290_);
lean_dec(v_tail_1288_);
lean_dec_ref(v_inst_1282_);
v___x_1293_ = lean_unbox(v___x_1291_);
return v___x_1293_;
}
else
{
v_x_1283_ = v_tail_1288_;
v_x_1284_ = v_tail_1290_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_isPrefixOf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1282_ = stack[0].m_obj;
lean_object* v_x_1283_ = stack[1].m_obj;
lean_object* v_x_1284_ = stack[2].m_obj;
uint8_t v_res_1295_;
v_res_1295_ = l_List_isPrefixOf___redArg(v_inst_1282_, v_x_1283_, v_x_1284_);
stack->m_num = v_res_1295_;
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___redArg___boxed(lean_object* v_inst_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_res_1299_ = l_List_isPrefixOf___redArg(v_inst_1296_, v_x_1297_, v_x_1298_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
uint8_t l_List_isPrefixOf(lean_object* v_00_u03b1_1301_, lean_object* v_inst_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
uint8_t v___x_1305_; 
v___x_1305_ = l_List_isPrefixOf___redArg(v_inst_1302_, v_x_1303_, v_x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT void l_List_isPrefixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1302_ = stack[1].m_obj;
lean_object* v_x_1303_ = stack[2].m_obj;
lean_object* v_x_1304_ = stack[3].m_obj;
uint8_t v_res_1306_;
v_res_1306_ = l_List_isPrefixOf(lean_box(0), v_inst_1302_, v_x_1303_, v_x_1304_);
stack->m_num = v_res_1306_;
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_inst_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l_List_isPrefixOf(v_00_u03b1_1307_, v_inst_1308_, v_x_1309_, v_x_1310_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_h__1_1315_, lean_object* v_h__2_1316_, lean_object* v_h__3_1317_){
_start:
{
if (lean_obj_tag(v_x_1313_) == 0)
{
lean_object* v___x_1318_; 
lean_dec(v_h__3_1317_);
lean_dec(v_h__2_1316_);
v___x_1318_ = lean_apply_1(v_h__1_1315_, v_x_1314_);
return v___x_1318_;
}
else
{
lean_dec(v_h__1_1315_);
if (lean_obj_tag(v_x_1314_) == 0)
{
lean_object* v___x_1319_; 
lean_dec(v_h__3_1317_);
v___x_1319_ = lean_apply_2(v_h__2_1316_, v_x_1313_, lean_box(0));
return v___x_1319_;
}
else
{
lean_object* v_head_1320_; lean_object* v_tail_1321_; lean_object* v_head_1322_; lean_object* v_tail_1323_; lean_object* v___x_1324_; 
lean_dec(v_h__2_1316_);
v_head_1320_ = lean_ctor_get(v_x_1313_, 0);
lean_inc(v_head_1320_);
v_tail_1321_ = lean_ctor_get(v_x_1313_, 1);
lean_inc(v_tail_1321_);
lean_dec_ref_known(v_x_1313_, 2);
v_head_1322_ = lean_ctor_get(v_x_1314_, 0);
lean_inc(v_head_1322_);
v_tail_1323_ = lean_ctor_get(v_x_1314_, 1);
lean_inc(v_tail_1323_);
lean_dec_ref_known(v_x_1314_, 2);
v___x_1324_ = lean_apply_4(v_h__3_1317_, v_head_1320_, v_tail_1321_, v_head_1322_, v_tail_1323_);
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object* v_00_u03b1_1325_, lean_object* v_motive_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_, lean_object* v_h__1_1329_, lean_object* v_h__2_1330_, lean_object* v_h__3_1331_){
_start:
{
if (lean_obj_tag(v_x_1327_) == 0)
{
lean_object* v___x_1332_; 
lean_dec(v_h__3_1331_);
lean_dec(v_h__2_1330_);
v___x_1332_ = lean_apply_1(v_h__1_1329_, v_x_1328_);
return v___x_1332_;
}
else
{
lean_dec(v_h__1_1329_);
if (lean_obj_tag(v_x_1328_) == 0)
{
lean_object* v___x_1333_; 
lean_dec(v_h__3_1331_);
v___x_1333_ = lean_apply_2(v_h__2_1330_, v_x_1327_, lean_box(0));
return v___x_1333_;
}
else
{
lean_object* v_head_1334_; lean_object* v_tail_1335_; lean_object* v_head_1336_; lean_object* v_tail_1337_; lean_object* v___x_1338_; 
lean_dec(v_h__2_1330_);
v_head_1334_ = lean_ctor_get(v_x_1327_, 0);
lean_inc(v_head_1334_);
v_tail_1335_ = lean_ctor_get(v_x_1327_, 1);
lean_inc(v_tail_1335_);
lean_dec_ref_known(v_x_1327_, 2);
v_head_1336_ = lean_ctor_get(v_x_1328_, 0);
lean_inc(v_head_1336_);
v_tail_1337_ = lean_ctor_get(v_x_1328_, 1);
lean_inc(v_tail_1337_);
lean_dec_ref_known(v_x_1328_, 2);
v___x_1338_ = lean_apply_4(v_h__3_1331_, v_head_1334_, v_tail_1335_, v_head_1336_, v_tail_1337_);
return v___x_1338_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___redArg(lean_object* v_inst_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
if (lean_obj_tag(v_x_1340_) == 0)
{
lean_object* v___x_1342_; 
lean_dec_ref(v_inst_1339_);
v___x_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_x_1341_);
return v___x_1342_;
}
else
{
if (lean_obj_tag(v_x_1341_) == 0)
{
lean_object* v___x_1343_; 
lean_dec_ref_known(v_x_1340_, 2);
lean_dec_ref(v_inst_1339_);
v___x_1343_ = lean_box(0);
return v___x_1343_;
}
else
{
lean_object* v_head_1344_; lean_object* v_tail_1345_; lean_object* v_head_1346_; lean_object* v_tail_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_head_1344_ = lean_ctor_get(v_x_1340_, 0);
lean_inc(v_head_1344_);
v_tail_1345_ = lean_ctor_get(v_x_1340_, 1);
lean_inc(v_tail_1345_);
lean_dec_ref_known(v_x_1340_, 2);
v_head_1346_ = lean_ctor_get(v_x_1341_, 0);
lean_inc(v_head_1346_);
v_tail_1347_ = lean_ctor_get(v_x_1341_, 1);
lean_inc(v_tail_1347_);
lean_dec_ref_known(v_x_1341_, 2);
lean_inc_ref(v_inst_1339_);
v___x_1348_ = lean_apply_2(v_inst_1339_, v_head_1344_, v_head_1346_);
v___x_1349_ = lean_unbox(v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_tail_1347_);
lean_dec(v_tail_1345_);
lean_dec_ref(v_inst_1339_);
v___x_1350_ = lean_box(0);
return v___x_1350_;
}
else
{
v_x_1340_ = v_tail_1345_;
v_x_1341_ = v_tail_1347_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object* v_00_u03b1_1352_, lean_object* v_inst_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_List_isPrefixOf_x3f___redArg(v_inst_1353_, v_x_1354_, v_x_1355_);
return v___x_1356_;
}
}
uint8_t l_List_isSuffixOf___redArg(lean_object* v_inst_1357_, lean_object* v_l_u2081_1358_, lean_object* v_l_u2082_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1360_ = l_List_reverse___redArg(v_l_u2081_1358_);
v___x_1361_ = l_List_reverse___redArg(v_l_u2082_1359_);
v___x_1362_ = l_List_isPrefixOf___redArg(v_inst_1357_, v___x_1360_, v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT void l_List_isSuffixOf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1357_ = stack[0].m_obj;
lean_object* v_l_u2081_1358_ = stack[1].m_obj;
lean_object* v_l_u2082_1359_ = stack[2].m_obj;
uint8_t v_res_1363_;
v_res_1363_ = l_List_isSuffixOf___redArg(v_inst_1357_, v_l_u2081_1358_, v_l_u2082_1359_);
stack->m_num = v_res_1363_;
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___redArg___boxed(lean_object* v_inst_1364_, lean_object* v_l_u2081_1365_, lean_object* v_l_u2082_1366_){
_start:
{
uint8_t v_res_1367_; lean_object* v_r_1368_; 
v_res_1367_ = l_List_isSuffixOf___redArg(v_inst_1364_, v_l_u2081_1365_, v_l_u2082_1366_);
v_r_1368_ = lean_box(v_res_1367_);
return v_r_1368_;
}
}
uint8_t l_List_isSuffixOf(lean_object* v_00_u03b1_1369_, lean_object* v_inst_1370_, lean_object* v_l_u2081_1371_, lean_object* v_l_u2082_1372_){
_start:
{
uint8_t v___x_1373_; 
v___x_1373_ = l_List_isSuffixOf___redArg(v_inst_1370_, v_l_u2081_1371_, v_l_u2082_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT void l_List_isSuffixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1370_ = stack[1].m_obj;
lean_object* v_l_u2081_1371_ = stack[2].m_obj;
lean_object* v_l_u2082_1372_ = stack[3].m_obj;
uint8_t v_res_1374_;
v_res_1374_ = l_List_isSuffixOf(lean_box(0), v_inst_1370_, v_l_u2081_1371_, v_l_u2082_1372_);
stack->m_num = v_res_1374_;
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___boxed(lean_object* v_00_u03b1_1375_, lean_object* v_inst_1376_, lean_object* v_l_u2081_1377_, lean_object* v_l_u2082_1378_){
_start:
{
uint8_t v_res_1379_; lean_object* v_r_1380_; 
v_res_1379_ = l_List_isSuffixOf(v_00_u03b1_1375_, v_inst_1376_, v_l_u2081_1377_, v_l_u2082_1378_);
v_r_1380_ = lean_box(v_res_1379_);
return v_r_1380_;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___redArg(lean_object* v_inst_1381_, lean_object* v_l_u2081_1382_, lean_object* v_l_u2082_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = l_List_reverse___redArg(v_l_u2081_1382_);
v___x_1385_ = l_List_reverse___redArg(v_l_u2082_1383_);
v___x_1386_ = l_List_isPrefixOf_x3f___redArg(v_inst_1381_, v___x_1384_, v___x_1385_);
if (lean_obj_tag(v___x_1386_) == 0)
{
return v___x_1386_;
}
else
{
lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1395_; 
v_val_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = l_List_reverse___redArg(v_val_1387_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1391_);
v___x_1393_ = v___x_1389_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object* v_00_u03b1_1396_, lean_object* v_inst_1397_, lean_object* v_l_u2081_1398_, lean_object* v_l_u2082_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_List_isSuffixOf_x3f___redArg(v_inst_1397_, v_l_u2081_1398_, v_l_u2082_1399_);
return v___x_1400_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0));
v___x_1419_ = l_String_toRawSubstring_x27(v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object* v_x_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
lean_inc(v_x_1431_);
v___x_1435_ = l_Lean_Syntax_isOfKind(v_x_1431_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v_x_1431_);
v___x_1436_ = lean_box(1);
v___x_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v_a_1433_);
return v___x_1437_;
}
else
{
lean_object* v_quotContext_1438_; lean_object* v_currMacroScope_1439_; lean_object* v_ref_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_quotContext_1438_ = lean_ctor_get(v_a_1432_, 1);
v_currMacroScope_1439_ = lean_ctor_get(v_a_1432_, 2);
v_ref_1440_ = lean_ctor_get(v_a_1432_, 5);
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = l_Lean_Syntax_getArg(v_x_1431_, v___x_1441_);
v___x_1443_ = lean_unsigned_to_nat(2u);
v___x_1444_ = l_Lean_Syntax_getArg(v_x_1431_, v___x_1443_);
lean_dec(v_x_1431_);
v___x_1445_ = 0;
v___x_1446_ = l_Lean_SourceInfo_fromRef(v_ref_1440_, v___x_1445_);
v___x_1447_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1448_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
v___x_1449_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2));
lean_inc(v_currMacroScope_1439_);
lean_inc(v_quotContext_1438_);
v___x_1450_ = l_Lean_addMacroScope(v_quotContext_1438_, v___x_1449_, v_currMacroScope_1439_);
v___x_1451_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5));
lean_inc_n(v___x_1446_, 2);
v___x_1452_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1446_);
lean_ctor_set(v___x_1452_, 1, v___x_1448_);
lean_ctor_set(v___x_1452_, 2, v___x_1450_);
lean_ctor_set(v___x_1452_, 3, v___x_1451_);
v___x_1453_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1454_ = l_Lean_Syntax_node2(v___x_1446_, v___x_1453_, v___x_1442_, v___x_1444_);
v___x_1455_ = l_Lean_Syntax_node2(v___x_1446_, v___x_1447_, v___x_1452_, v___x_1454_);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v_a_1433_);
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___boxed(lean_object* v_x_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(v_x_1457_, v_a_1458_, v_a_1459_);
lean_dec_ref(v_a_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object* v_x_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1461_);
v___x_1465_ = l_Lean_Syntax_isOfKind(v_x_1461_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec(v_x_1461_);
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_a_1463_);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = l_Lean_Syntax_getArg(v_x_1461_, v___x_1468_);
v___x_1470_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1469_);
v___x_1471_ = l_Lean_Syntax_isOfKind(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v___x_1469_);
lean_dec(v_x_1461_);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v_a_1463_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1474_ = lean_unsigned_to_nat(1u);
v___x_1475_ = l_Lean_Syntax_getArg(v_x_1461_, v___x_1474_);
lean_dec(v_x_1461_);
v___x_1476_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1475_);
v___x_1477_ = l_Lean_Syntax_matchesNull(v___x_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v___x_1475_);
lean_dec(v___x_1469_);
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v_a_1463_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_ref_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1480_ = l_Lean_Syntax_getArg(v___x_1475_, v___x_1468_);
v___x_1481_ = l_Lean_Syntax_getArg(v___x_1475_, v___x_1474_);
lean_dec(v___x_1475_);
v_ref_1482_ = l_Lean_replaceRef(v___x_1469_, v_a_1462_);
lean_dec(v___x_1469_);
v___x_1483_ = 0;
v___x_1484_ = l_Lean_SourceInfo_fromRef(v_ref_1482_, v___x_1483_);
lean_dec(v_ref_1482_);
v___x_1485_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__1));
v___x_1486_ = ((lean_object*)(l_List_term___x3c_x3a_x2b___00__closed__2));
lean_inc(v___x_1484_);
v___x_1487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1484_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_Syntax_node3(v___x_1484_, v___x_1485_, v___x_1480_, v___x_1487_, v___x_1481_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v_a_1463_);
return v___x_1489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object* v_x_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(v_x_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1491_);
return v_res_1493_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0));
v___x_1512_ = l_String_toRawSubstring_x27(v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object* v_x_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
lean_inc(v_x_1524_);
v___x_1528_ = l_Lean_Syntax_isOfKind(v_x_1524_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_x_1524_);
v___x_1529_ = lean_box(1);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v_a_1526_);
return v___x_1530_;
}
else
{
lean_object* v_quotContext_1531_; lean_object* v_currMacroScope_1532_; lean_object* v_ref_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_quotContext_1531_ = lean_ctor_get(v_a_1525_, 1);
v_currMacroScope_1532_ = lean_ctor_get(v_a_1525_, 2);
v_ref_1533_ = lean_ctor_get(v_a_1525_, 5);
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = l_Lean_Syntax_getArg(v_x_1524_, v___x_1534_);
v___x_1536_ = lean_unsigned_to_nat(2u);
v___x_1537_ = l_Lean_Syntax_getArg(v_x_1524_, v___x_1536_);
lean_dec(v_x_1524_);
v___x_1538_ = 0;
v___x_1539_ = l_Lean_SourceInfo_fromRef(v_ref_1533_, v___x_1538_);
v___x_1540_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_1541_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
v___x_1542_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2));
lean_inc(v_currMacroScope_1532_);
lean_inc(v_quotContext_1531_);
v___x_1543_ = l_Lean_addMacroScope(v_quotContext_1531_, v___x_1542_, v_currMacroScope_1532_);
v___x_1544_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5));
lean_inc_n(v___x_1539_, 2);
v___x_1545_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1539_);
lean_ctor_set(v___x_1545_, 1, v___x_1541_);
lean_ctor_set(v___x_1545_, 2, v___x_1543_);
lean_ctor_set(v___x_1545_, 3, v___x_1544_);
v___x_1546_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_1547_ = l_Lean_Syntax_node2(v___x_1539_, v___x_1546_, v___x_1535_, v___x_1537_);
v___x_1548_ = l_Lean_Syntax_node2(v___x_1539_, v___x_1540_, v___x_1545_, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v_a_1526_);
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___boxed(lean_object* v_x_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(v_x_1550_, v_a_1551_, v_a_1552_);
lean_dec_ref(v_a_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object* v_x_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_1554_);
v___x_1558_ = l_Lean_Syntax_isOfKind(v_x_1554_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec(v_x_1554_);
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v_a_1556_);
return v___x_1560_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = l_Lean_Syntax_getArg(v_x_1554_, v___x_1561_);
v___x_1563_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_1562_);
v___x_1564_ = l_Lean_Syntax_isOfKind(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v___x_1562_);
lean_dec(v_x_1554_);
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v_a_1556_);
return v___x_1566_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1567_ = lean_unsigned_to_nat(1u);
v___x_1568_ = l_Lean_Syntax_getArg(v_x_1554_, v___x_1567_);
lean_dec(v_x_1554_);
v___x_1569_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1568_);
v___x_1570_ = l_Lean_Syntax_matchesNull(v___x_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec(v___x_1568_);
lean_dec(v___x_1562_);
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_a_1556_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v_ref_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1573_ = l_Lean_Syntax_getArg(v___x_1568_, v___x_1561_);
v___x_1574_ = l_Lean_Syntax_getArg(v___x_1568_, v___x_1567_);
lean_dec(v___x_1568_);
v_ref_1575_ = l_Lean_replaceRef(v___x_1562_, v_a_1555_);
lean_dec(v___x_1562_);
v___x_1576_ = 0;
v___x_1577_ = l_Lean_SourceInfo_fromRef(v_ref_1575_, v___x_1576_);
lean_dec(v_ref_1575_);
v___x_1578_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__1));
v___x_1579_ = ((lean_object*)(l_List_term___x3c_x3a_x2b_x3a___00__closed__2));
lean_inc(v___x_1577_);
v___x_1580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1577_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_Syntax_node3(v___x_1577_, v___x_1578_, v___x_1573_, v___x_1580_, v___x_1574_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v_a_1556_);
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object* v_x_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(v_x_1583_, v_a_1584_, v_a_1585_);
lean_dec(v_a_1584_);
return v_res_1586_;
}
}
uint8_t l_List_isInfixOf__internal___redArg(lean_object* v_inst_1587_, lean_object* v_l_u2081_1588_, lean_object* v_l_u2082_1589_){
_start:
{
uint8_t v___x_1590_; 
lean_inc(v_l_u2082_1589_);
lean_inc(v_l_u2081_1588_);
lean_inc_ref(v_inst_1587_);
v___x_1590_ = l_List_isPrefixOf___redArg(v_inst_1587_, v_l_u2081_1588_, v_l_u2082_1589_);
if (v___x_1590_ == 0)
{
if (lean_obj_tag(v_l_u2082_1589_) == 0)
{
lean_dec(v_l_u2081_1588_);
lean_dec_ref(v_inst_1587_);
return v___x_1590_;
}
else
{
lean_object* v_tail_1591_; 
v_tail_1591_ = lean_ctor_get(v_l_u2082_1589_, 1);
lean_inc(v_tail_1591_);
lean_dec_ref_known(v_l_u2082_1589_, 2);
v_l_u2082_1589_ = v_tail_1591_;
goto _start;
}
}
else
{
lean_dec(v_l_u2082_1589_);
lean_dec(v_l_u2081_1588_);
lean_dec_ref(v_inst_1587_);
return v___x_1590_;
}
}
}
LEAN_EXPORT void l_List_isInfixOf__internal___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1587_ = stack[0].m_obj;
lean_object* v_l_u2081_1588_ = stack[1].m_obj;
lean_object* v_l_u2082_1589_ = stack[2].m_obj;
uint8_t v_res_1593_;
v_res_1593_ = l_List_isInfixOf__internal___redArg(v_inst_1587_, v_l_u2081_1588_, v_l_u2082_1589_);
stack->m_num = v_res_1593_;
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___redArg___boxed(lean_object* v_inst_1594_, lean_object* v_l_u2081_1595_, lean_object* v_l_u2082_1596_){
_start:
{
uint8_t v_res_1597_; lean_object* v_r_1598_; 
v_res_1597_ = l_List_isInfixOf__internal___redArg(v_inst_1594_, v_l_u2081_1595_, v_l_u2082_1596_);
v_r_1598_ = lean_box(v_res_1597_);
return v_r_1598_;
}
}
uint8_t l_List_isInfixOf__internal(lean_object* v_00_u03b1_1599_, lean_object* v_inst_1600_, lean_object* v_l_u2081_1601_, lean_object* v_l_u2082_1602_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = l_List_isInfixOf__internal___redArg(v_inst_1600_, v_l_u2081_1601_, v_l_u2082_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT void l_List_isInfixOf__internal_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1600_ = stack[1].m_obj;
lean_object* v_l_u2081_1601_ = stack[2].m_obj;
lean_object* v_l_u2082_1602_ = stack[3].m_obj;
uint8_t v_res_1604_;
v_res_1604_ = l_List_isInfixOf__internal(lean_box(0), v_inst_1600_, v_l_u2081_1601_, v_l_u2082_1602_);
stack->m_num = v_res_1604_;
}
LEAN_EXPORT lean_object* l_List_isInfixOf__internal___boxed(lean_object* v_00_u03b1_1605_, lean_object* v_inst_1606_, lean_object* v_l_u2081_1607_, lean_object* v_l_u2082_1608_){
_start:
{
uint8_t v_res_1609_; lean_object* v_r_1610_; 
v_res_1609_ = l_List_isInfixOf__internal(v_00_u03b1_1605_, v_inst_1606_, v_l_u2081_1607_, v_l_u2082_1608_);
v_r_1610_ = lean_box(v_res_1609_);
return v_r_1610_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go___redArg(lean_object* v_l_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
if (lean_obj_tag(v_a_1612_) == 0)
{
lean_object* v___x_1615_; 
lean_dec(v_a_1614_);
lean_dec(v_a_1613_);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v_l_1611_);
lean_ctor_set(v___x_1615_, 1, v_a_1612_);
return v___x_1615_;
}
else
{
lean_object* v_head_1616_; lean_object* v_tail_1617_; lean_object* v_zero_1618_; uint8_t v_isZero_1619_; 
v_head_1616_ = lean_ctor_get(v_a_1612_, 0);
v_tail_1617_ = lean_ctor_get(v_a_1612_, 1);
v_zero_1618_ = lean_unsigned_to_nat(0u);
v_isZero_1619_ = lean_nat_dec_eq(v_a_1613_, v_zero_1618_);
if (v_isZero_1619_ == 1)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec(v_a_1613_);
lean_dec(v_l_1611_);
v___x_1620_ = l_List_reverse___redArg(v_a_1614_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v_a_1612_);
return v___x_1621_;
}
else
{
lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1631_; 
lean_inc(v_tail_1617_);
lean_inc(v_head_1616_);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_a_1612_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; lean_object* v_unused_1633_; 
v_unused_1632_ = lean_ctor_get(v_a_1612_, 1);
lean_dec(v_unused_1632_);
v_unused_1633_ = lean_ctor_get(v_a_1612_, 0);
lean_dec(v_unused_1633_);
v___x_1623_ = v_a_1612_;
v_isShared_1624_ = v_isSharedCheck_1631_;
goto v_resetjp_1622_;
}
else
{
lean_dec(v_a_1612_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1631_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_one_1625_; lean_object* v_n_1626_; lean_object* v___x_1628_; 
v_one_1625_ = lean_unsigned_to_nat(1u);
v_n_1626_ = lean_nat_sub(v_a_1613_, v_one_1625_);
lean_dec(v_a_1613_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 1, v_a_1614_);
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_head_1616_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_a_1614_);
v___x_1628_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
v_a_1612_ = v_tail_1617_;
v_a_1613_ = v_n_1626_;
v_a_1614_ = v___x_1628_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object* v_00_u03b1_1634_, lean_object* v_l_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_List_splitAt_go___redArg(v_l_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt___redArg(lean_object* v_n_1640_, lean_object* v_l_1641_){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_box(0);
lean_inc(v_l_1641_);
v___x_1643_ = l_List_splitAt_go___redArg(v_l_1641_, v_l_1641_, v_n_1640_, v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_List_splitAt(lean_object* v_00_u03b1_1644_, lean_object* v_n_1645_, lean_object* v_l_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_List_splitAt___redArg(v_n_1645_, v_l_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg(lean_object* v_xs_1648_, lean_object* v_i_1649_){
_start:
{
lean_object* v_len_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v_len_1650_ = l_List_length___redArg(v_xs_1648_);
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_nat_dec_le(v_len_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v_i_1653_; lean_object* v_ys_1654_; lean_object* v_zs_1655_; lean_object* v___x_1656_; 
v_i_1653_ = lean_nat_mod(v_i_1649_, v_len_1650_);
lean_dec(v_len_1650_);
lean_inc(v_xs_1648_);
v_ys_1654_ = l_List_take___redArg(v_i_1653_, v_xs_1648_);
v_zs_1655_ = l_List_drop___redArg(v_i_1653_, v_xs_1648_);
lean_dec(v_xs_1648_);
v___x_1656_ = l_List_appendTR___redArg(v_zs_1655_, v_ys_1654_);
return v___x_1656_;
}
else
{
lean_dec(v_len_1650_);
return v_xs_1648_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___redArg___boxed(lean_object* v_xs_1657_, lean_object* v_i_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_List_rotateLeft___redArg(v_xs_1657_, v_i_1658_);
lean_dec(v_i_1658_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft(lean_object* v_00_u03b1_1660_, lean_object* v_xs_1661_, lean_object* v_i_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_List_rotateLeft___redArg(v_xs_1661_, v_i_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___boxed(lean_object* v_00_u03b1_1664_, lean_object* v_xs_1665_, lean_object* v_i_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_List_rotateLeft(v_00_u03b1_1664_, v_xs_1665_, v_i_1666_);
lean_dec(v_i_1666_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg(lean_object* v_xs_1668_, lean_object* v_i_1669_){
_start:
{
lean_object* v_len_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v_len_1670_ = l_List_length___redArg(v_xs_1668_);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_dec_le(v_len_1670_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v_i_1674_; lean_object* v_ys_1675_; lean_object* v_zs_1676_; lean_object* v___x_1677_; 
v___x_1673_ = lean_nat_mod(v_i_1669_, v_len_1670_);
v_i_1674_ = lean_nat_sub(v_len_1670_, v___x_1673_);
lean_dec(v___x_1673_);
lean_dec(v_len_1670_);
lean_inc(v_xs_1668_);
v_ys_1675_ = l_List_take___redArg(v_i_1674_, v_xs_1668_);
v_zs_1676_ = l_List_drop___redArg(v_i_1674_, v_xs_1668_);
lean_dec(v_xs_1668_);
v___x_1677_ = l_List_appendTR___redArg(v_zs_1676_, v_ys_1675_);
return v___x_1677_;
}
else
{
lean_dec(v_len_1670_);
return v_xs_1668_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___redArg___boxed(lean_object* v_xs_1678_, lean_object* v_i_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_List_rotateRight___redArg(v_xs_1678_, v_i_1679_);
lean_dec(v_i_1679_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight(lean_object* v_00_u03b1_1681_, lean_object* v_xs_1682_, lean_object* v_i_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_List_rotateRight___redArg(v_xs_1682_, v_i_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___boxed(lean_object* v_00_u03b1_1685_, lean_object* v_xs_1686_, lean_object* v_i_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_List_rotateRight(v_00_u03b1_1685_, v_xs_1686_, v_i_1687_);
lean_dec(v_i_1687_);
return v_res_1688_;
}
}
uint8_t l_List_instDecidablePairwise___redArg(lean_object* v_inst_1689_, lean_object* v_x_1690_){
_start:
{
if (lean_obj_tag(v_x_1690_) == 0)
{
uint8_t v___x_1691_; 
lean_dec_ref(v_inst_1689_);
v___x_1691_ = 1;
return v___x_1691_;
}
else
{
lean_object* v_head_1692_; lean_object* v_tail_1693_; uint8_t v_decide_1694_; 
v_head_1692_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_head_1692_);
v_tail_1693_ = lean_ctor_get(v_x_1690_, 1);
lean_inc_n(v_tail_1693_, 2);
lean_dec_ref_known(v_x_1690_, 2);
lean_inc_ref(v_inst_1689_);
v_decide_1694_ = l_List_instDecidablePairwise___redArg(v_inst_1689_, v_tail_1693_);
if (v_decide_1694_ == 0)
{
lean_dec(v_tail_1693_);
lean_dec(v_head_1692_);
lean_dec_ref(v_inst_1689_);
return v_decide_1694_;
}
else
{
lean_object* v___x_1695_; uint8_t v_decide_1696_; 
v___x_1695_ = lean_apply_1(v_inst_1689_, v_head_1692_);
v_decide_1696_ = l_List_decidableBAll___redArg(v___x_1695_, v_tail_1693_);
return v_decide_1696_;
}
}
}
}
LEAN_EXPORT void l_List_instDecidablePairwise___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1689_ = stack[0].m_obj;
lean_object* v_x_1690_ = stack[1].m_obj;
uint8_t v_res_1697_;
v_res_1697_ = l_List_instDecidablePairwise___redArg(v_inst_1689_, v_x_1690_);
stack->m_num = v_res_1697_;
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___redArg___boxed(lean_object* v_inst_1698_, lean_object* v_x_1699_){
_start:
{
uint8_t v_res_1700_; lean_object* v_r_1701_; 
v_res_1700_ = l_List_instDecidablePairwise___redArg(v_inst_1698_, v_x_1699_);
v_r_1701_ = lean_box(v_res_1700_);
return v_r_1701_;
}
}
uint8_t l_List_instDecidablePairwise(lean_object* v_00_u03b1_1702_, lean_object* v_R_1703_, lean_object* v_inst_1704_, lean_object* v_x_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = l_List_instDecidablePairwise___redArg(v_inst_1704_, v_x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT void l_List_instDecidablePairwise_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1704_ = stack[2].m_obj;
lean_object* v_x_1705_ = stack[3].m_obj;
uint8_t v_res_1707_;
v_res_1707_ = l_List_instDecidablePairwise(lean_box(0), lean_box(0), v_inst_1704_, v_x_1705_);
stack->m_num = v_res_1707_;
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_R_1709_, lean_object* v_inst_1710_, lean_object* v_x_1711_){
_start:
{
uint8_t v_res_1712_; lean_object* v_r_1713_; 
v_res_1712_ = l_List_instDecidablePairwise(v_00_u03b1_1708_, v_R_1709_, v_inst_1710_, v_x_1711_);
v_r_1713_ = lean_box(v_res_1712_);
return v_r_1713_;
}
}
uint8_t l_List_nodupDecidable___redArg___lam__0(lean_object* v_inst_1714_, lean_object* v_a_1715_, lean_object* v_b_1716_){
_start:
{
lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1717_ = lean_apply_2(v_inst_1714_, v_a_1715_, v_b_1716_);
v___x_1718_ = lean_unbox(v___x_1717_);
if (v___x_1718_ == 0)
{
uint8_t v___x_1719_; 
v___x_1719_ = 1;
return v___x_1719_;
}
else
{
uint8_t v___x_1720_; 
v___x_1720_ = 0;
return v___x_1720_;
}
}
}
LEAN_EXPORT void l_List_nodupDecidable___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1714_ = stack[0].m_obj;
lean_object* v_a_1715_ = stack[1].m_obj;
lean_object* v_b_1716_ = stack[2].m_obj;
uint8_t v_res_1721_;
v_res_1721_ = l_List_nodupDecidable___redArg___lam__0(v_inst_1714_, v_a_1715_, v_b_1716_);
stack->m_num = v_res_1721_;
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___lam__0___boxed(lean_object* v_inst_1722_, lean_object* v_a_1723_, lean_object* v_b_1724_){
_start:
{
uint8_t v_res_1725_; lean_object* v_r_1726_; 
v_res_1725_ = l_List_nodupDecidable___redArg___lam__0(v_inst_1722_, v_a_1723_, v_b_1724_);
v_r_1726_ = lean_box(v_res_1725_);
return v_r_1726_;
}
}
uint8_t l_List_nodupDecidable___redArg(lean_object* v_inst_1727_, lean_object* v_l_1728_){
_start:
{
lean_object* v___f_1729_; uint8_t v___x_1730_; 
v___f_1729_ = lean_alloc_closure((void*)(l_List_nodupDecidable___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1729_, 0, v_inst_1727_);
v___x_1730_ = l_List_instDecidablePairwise___redArg(v___f_1729_, v_l_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT void l_List_nodupDecidable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1727_ = stack[0].m_obj;
lean_object* v_l_1728_ = stack[1].m_obj;
uint8_t v_res_1731_;
v_res_1731_ = l_List_nodupDecidable___redArg(v_inst_1727_, v_l_1728_);
stack->m_num = v_res_1731_;
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___redArg___boxed(lean_object* v_inst_1732_, lean_object* v_l_1733_){
_start:
{
uint8_t v_res_1734_; lean_object* v_r_1735_; 
v_res_1734_ = l_List_nodupDecidable___redArg(v_inst_1732_, v_l_1733_);
v_r_1735_ = lean_box(v_res_1734_);
return v_r_1735_;
}
}
uint8_t l_List_nodupDecidable(lean_object* v_00_u03b1_1736_, lean_object* v_inst_1737_, lean_object* v_l_1738_){
_start:
{
uint8_t v___x_1739_; 
v___x_1739_ = l_List_nodupDecidable___redArg(v_inst_1737_, v_l_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT void l_List_nodupDecidable_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1737_ = stack[1].m_obj;
lean_object* v_l_1738_ = stack[2].m_obj;
uint8_t v_res_1740_;
v_res_1740_ = l_List_nodupDecidable(lean_box(0), v_inst_1737_, v_l_1738_);
stack->m_num = v_res_1740_;
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___boxed(lean_object* v_00_u03b1_1741_, lean_object* v_inst_1742_, lean_object* v_l_1743_){
_start:
{
uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_res_1744_ = l_List_nodupDecidable(v_00_u03b1_1741_, v_inst_1742_, v_l_1743_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
LEAN_EXPORT lean_object* l_List_replace___redArg(lean_object* v_inst_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
lean_dec(v_x_1749_);
lean_dec(v_x_1748_);
lean_dec_ref(v_inst_1746_);
return v_x_1747_;
}
else
{
lean_object* v_head_1750_; lean_object* v_tail_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1764_; 
v_head_1750_ = lean_ctor_get(v_x_1747_, 0);
v_tail_1751_ = lean_ctor_get(v_x_1747_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_x_1747_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1753_ = v_x_1747_;
v_isShared_1754_ = v_isSharedCheck_1764_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_tail_1751_);
lean_inc(v_head_1750_);
lean_dec(v_x_1747_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1764_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; uint8_t v___x_1756_; 
lean_inc_ref(v_inst_1746_);
lean_inc(v_head_1750_);
lean_inc(v_x_1748_);
v___x_1755_ = lean_apply_2(v_inst_1746_, v_x_1748_, v_head_1750_);
v___x_1756_ = lean_unbox(v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = l_List_replace___redArg(v_inst_1746_, v_tail_1751_, v_x_1748_, v_x_1749_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 1, v___x_1757_);
v___x_1759_ = v___x_1753_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_head_1750_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
else
{
lean_object* v___x_1762_; 
lean_dec(v_head_1750_);
lean_dec(v_x_1748_);
lean_dec_ref(v_inst_1746_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v_x_1749_);
v___x_1762_ = v___x_1753_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_x_1749_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_tail_1751_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_replace(lean_object* v_00_u03b1_1765_, lean_object* v_inst_1766_, lean_object* v_x_1767_, lean_object* v_x_1768_, lean_object* v_x_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_List_replace___redArg(v_inst_1766_, v_x_1767_, v_x_1768_, v_x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg(lean_object* v_f_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_zero_1774_; uint8_t v_isZero_1775_; 
v_zero_1774_ = lean_unsigned_to_nat(0u);
v_isZero_1775_ = lean_nat_dec_eq(v_a_1772_, v_zero_1774_);
if (v_isZero_1775_ == 1)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_apply_1(v_f_1771_, v_a_1773_);
return v___x_1776_;
}
else
{
if (lean_obj_tag(v_a_1773_) == 0)
{
lean_dec_ref(v_f_1771_);
return v_a_1773_;
}
else
{
lean_object* v_head_1777_; lean_object* v_tail_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1788_; 
v_head_1777_ = lean_ctor_get(v_a_1773_, 0);
v_tail_1778_ = lean_ctor_get(v_a_1773_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_a_1773_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1780_ = v_a_1773_;
v_isShared_1781_ = v_isSharedCheck_1788_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_tail_1778_);
lean_inc(v_head_1777_);
lean_dec(v_a_1773_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1788_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_one_1782_; lean_object* v_n_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v_one_1782_ = lean_unsigned_to_nat(1u);
v_n_1783_ = lean_nat_sub(v_a_1772_, v_one_1782_);
v___x_1784_ = l_List_modifyTailIdx_go___redArg(v_f_1771_, v_n_1783_, v_tail_1778_);
lean_dec(v_n_1783_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v___x_1784_);
v___x_1786_ = v___x_1780_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_head_1777_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___redArg___boxed(lean_object* v_f_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_List_modifyTailIdx_go___redArg(v_f_1789_, v_a_1790_, v_a_1791_);
lean_dec(v_a_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go(lean_object* v_00_u03b1_1793_, lean_object* v_f_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_List_modifyTailIdx_go___redArg(v_f_1794_, v_a_1795_, v_a_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_f_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_List_modifyTailIdx_go(v_00_u03b1_1798_, v_f_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg(lean_object* v_l_1803_, lean_object* v_i_1804_, lean_object* v_f_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_List_modifyTailIdx_go___redArg(v_f_1805_, v_i_1804_, v_l_1803_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___redArg___boxed(lean_object* v_l_1807_, lean_object* v_i_1808_, lean_object* v_f_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_List_modifyTailIdx___redArg(v_l_1807_, v_i_1808_, v_f_1809_);
lean_dec(v_i_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx(lean_object* v_00_u03b1_1811_, lean_object* v_l_1812_, lean_object* v_i_1813_, lean_object* v_f_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_List_modifyTailIdx_go___redArg(v_f_1814_, v_i_1813_, v_l_1812_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx___boxed(lean_object* v_00_u03b1_1816_, lean_object* v_l_1817_, lean_object* v_i_1818_, lean_object* v_f_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_List_modifyTailIdx(v_00_u03b1_1816_, v_l_1817_, v_i_1818_, v_f_1819_);
lean_dec(v_i_1818_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_List_modifyHead___redArg(lean_object* v_f_1821_, lean_object* v_x_1822_){
_start:
{
if (lean_obj_tag(v_x_1822_) == 0)
{
lean_dec(v_f_1821_);
return v_x_1822_;
}
else
{
lean_object* v_head_1823_; lean_object* v_tail_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1832_; 
v_head_1823_ = lean_ctor_get(v_x_1822_, 0);
v_tail_1824_ = lean_ctor_get(v_x_1822_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_x_1822_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1826_ = v_x_1822_;
v_isShared_1827_ = v_isSharedCheck_1832_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_tail_1824_);
lean_inc(v_head_1823_);
lean_dec(v_x_1822_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1832_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_apply_1(v_f_1821_, v_head_1823_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1828_);
v___x_1830_ = v___x_1826_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_tail_1824_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyHead(lean_object* v_00_u03b1_1833_, lean_object* v_f_1834_, lean_object* v_x_1835_){
_start:
{
if (lean_obj_tag(v_x_1835_) == 0)
{
lean_dec(v_f_1834_);
return v_x_1835_;
}
else
{
lean_object* v_head_1836_; lean_object* v_tail_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1845_; 
v_head_1836_ = lean_ctor_get(v_x_1835_, 0);
v_tail_1837_ = lean_ctor_get(v_x_1835_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_x_1835_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1839_ = v_x_1835_;
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_tail_1837_);
lean_inc(v_head_1836_);
lean_dec(v_x_1835_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_apply_1(v_f_1834_, v_head_1836_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_tail_1837_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg(lean_object* v_l_1846_, lean_object* v_i_1847_, lean_object* v_f_1848_){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1849_, 0, lean_box(0));
lean_closure_set(v___x_1849_, 1, v_f_1848_);
v___x_1850_ = l_List_modifyTailIdx_go___redArg(v___x_1849_, v_i_1847_, v_l_1846_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_List_modify___redArg___boxed(lean_object* v_l_1851_, lean_object* v_i_1852_, lean_object* v_f_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_List_modify___redArg(v_l_1851_, v_i_1852_, v_f_1853_);
lean_dec(v_i_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_List_modify(lean_object* v_00_u03b1_1855_, lean_object* v_l_1856_, lean_object* v_i_1857_, lean_object* v_f_1858_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_alloc_closure((void*)(l_List_modifyHead), 3, 2);
lean_closure_set(v___x_1859_, 0, lean_box(0));
lean_closure_set(v___x_1859_, 1, v_f_1858_);
v___x_1860_ = l_List_modifyTailIdx_go___redArg(v___x_1859_, v_i_1857_, v_l_1856_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_List_modify___boxed(lean_object* v_00_u03b1_1861_, lean_object* v_l_1862_, lean_object* v_i_1863_, lean_object* v_f_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_List_modify(v_00_u03b1_1861_, v_l_1862_, v_i_1863_, v_f_1864_);
lean_dec(v_i_1863_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_List_insert___redArg(lean_object* v_inst_1866_, lean_object* v_a_1867_, lean_object* v_l_1868_){
_start:
{
uint8_t v___x_1869_; 
lean_inc(v_l_1868_);
lean_inc(v_a_1867_);
v___x_1869_ = l_List_elem___redArg(v_inst_1866_, v_a_1867_, v_l_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_a_1867_);
lean_ctor_set(v___x_1870_, 1, v_l_1868_);
return v___x_1870_;
}
else
{
lean_dec(v_a_1867_);
return v_l_1868_;
}
}
}
LEAN_EXPORT lean_object* l_List_insert(lean_object* v_00_u03b1_1871_, lean_object* v_inst_1872_, lean_object* v_a_1873_, lean_object* v_l_1874_){
_start:
{
uint8_t v___x_1875_; 
lean_inc(v_l_1874_);
lean_inc(v_a_1873_);
v___x_1875_ = l_List_elem___redArg(v_inst_1872_, v_a_1873_, v_l_1874_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_a_1873_);
lean_ctor_set(v___x_1876_, 1, v_l_1874_);
return v___x_1876_;
}
else
{
lean_dec(v_a_1873_);
return v_l_1874_;
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_zero_1880_; uint8_t v_isZero_1881_; 
v_zero_1880_ = lean_unsigned_to_nat(0u);
v_isZero_1881_ = lean_nat_dec_eq(v_a_1878_, v_zero_1880_);
if (v_isZero_1881_ == 1)
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_a_1877_);
lean_ctor_set(v___x_1882_, 1, v_a_1879_);
return v___x_1882_;
}
else
{
if (lean_obj_tag(v_a_1879_) == 0)
{
lean_dec(v_a_1877_);
return v_a_1879_;
}
else
{
lean_object* v_head_1883_; lean_object* v_tail_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1894_; 
v_head_1883_ = lean_ctor_get(v_a_1879_, 0);
v_tail_1884_ = lean_ctor_get(v_a_1879_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_a_1879_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1886_ = v_a_1879_;
v_isShared_1887_ = v_isSharedCheck_1894_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_tail_1884_);
lean_inc(v_head_1883_);
lean_dec(v_a_1879_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1894_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_one_1888_; lean_object* v_n_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v_one_1888_ = lean_unsigned_to_nat(1u);
v_n_1889_ = lean_nat_sub(v_a_1878_, v_one_1888_);
v___x_1890_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1877_, v_n_1889_, v_tail_1884_);
lean_dec(v_n_1889_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v___x_1890_);
v___x_1892_ = v___x_1886_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_head_1883_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg___boxed(lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg(lean_object* v_xs_1899_, lean_object* v_i_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1901_, v_i_1900_, v_xs_1899_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___redArg___boxed(lean_object* v_xs_1903_, lean_object* v_i_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_List_insertIdx___redArg(v_xs_1903_, v_i_1904_, v_a_1905_);
lean_dec(v_i_1904_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx(lean_object* v_00_u03b1_1907_, lean_object* v_xs_1908_, lean_object* v_i_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1910_, v_i_1909_, v_xs_1908_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdx___boxed(lean_object* v_00_u03b1_1912_, lean_object* v_xs_1913_, lean_object* v_i_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_List_insertIdx(v_00_u03b1_1912_, v_xs_1913_, v_i_1914_, v_a_1915_);
lean_dec(v_i_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(lean_object* v_00_u03b1_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(v_a_1918_, v_a_1919_, v_a_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___boxed(lean_object* v_00_u03b1_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(v_00_u03b1_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
lean_dec(v_a_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_List_erase___redArg(lean_object* v_inst_1927_, lean_object* v_x_1928_, lean_object* v_x_1929_){
_start:
{
if (lean_obj_tag(v_x_1928_) == 0)
{
lean_dec(v_x_1929_);
lean_dec_ref(v_inst_1927_);
return v_x_1928_;
}
else
{
lean_object* v_head_1930_; lean_object* v_tail_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1941_; 
v_head_1930_ = lean_ctor_get(v_x_1928_, 0);
v_tail_1931_ = lean_ctor_get(v_x_1928_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_x_1928_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1933_ = v_x_1928_;
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_tail_1931_);
lean_inc(v_head_1930_);
lean_dec(v_x_1928_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; uint8_t v___x_1936_; 
lean_inc_ref(v_inst_1927_);
lean_inc(v_x_1929_);
lean_inc(v_head_1930_);
v___x_1935_ = lean_apply_2(v_inst_1927_, v_head_1930_, v_x_1929_);
v___x_1936_ = lean_unbox(v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1937_ = l_List_erase___redArg(v_inst_1927_, v_tail_1931_, v_x_1929_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v___x_1937_);
v___x_1939_ = v___x_1933_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_head_1930_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
else
{
lean_del_object(v___x_1933_);
lean_dec(v_head_1930_);
lean_dec(v_x_1929_);
lean_dec_ref(v_inst_1927_);
return v_tail_1931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_erase(lean_object* v_00_u03b1_1942_, lean_object* v_inst_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_List_erase___redArg(v_inst_1943_, v_x_1944_, v_x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_List_eraseP___redArg(lean_object* v_p_1947_, lean_object* v_x_1948_){
_start:
{
if (lean_obj_tag(v_x_1948_) == 0)
{
lean_dec_ref(v_p_1947_);
return v_x_1948_;
}
else
{
lean_object* v_head_1949_; lean_object* v_tail_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1960_; 
v_head_1949_ = lean_ctor_get(v_x_1948_, 0);
v_tail_1950_ = lean_ctor_get(v_x_1948_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_x_1948_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1952_ = v_x_1948_;
v_isShared_1953_ = v_isSharedCheck_1960_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_tail_1950_);
lean_inc(v_head_1949_);
lean_dec(v_x_1948_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1960_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
lean_inc_ref(v_p_1947_);
lean_inc(v_head_1949_);
v___x_1954_ = lean_apply_1(v_p_1947_, v_head_1949_);
v___x_1955_ = lean_unbox(v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = l_List_eraseP___redArg(v_p_1947_, v_tail_1950_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v___x_1956_);
v___x_1958_ = v___x_1952_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_head_1949_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
else
{
lean_del_object(v___x_1952_);
lean_dec(v_head_1949_);
lean_dec_ref(v_p_1947_);
return v_tail_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP(lean_object* v_00_u03b1_1961_, lean_object* v_p_1962_, lean_object* v_x_1963_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_List_eraseP___redArg(v_p_1962_, v_x_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg(lean_object* v_x_1965_, lean_object* v_x_1966_){
_start:
{
if (lean_obj_tag(v_x_1965_) == 0)
{
return v_x_1965_;
}
else
{
lean_object* v_head_1967_; lean_object* v_tail_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1980_; 
v_head_1967_ = lean_ctor_get(v_x_1965_, 0);
v_tail_1968_ = lean_ctor_get(v_x_1965_, 1);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_x_1965_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1970_ = v_x_1965_;
v_isShared_1971_ = v_isSharedCheck_1980_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_tail_1968_);
lean_inc(v_head_1967_);
lean_dec(v_x_1965_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1980_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v_zero_1972_; uint8_t v_isZero_1973_; 
v_zero_1972_ = lean_unsigned_to_nat(0u);
v_isZero_1973_ = lean_nat_dec_eq(v_x_1966_, v_zero_1972_);
if (v_isZero_1973_ == 1)
{
lean_del_object(v___x_1970_);
lean_dec(v_head_1967_);
return v_tail_1968_;
}
else
{
lean_object* v_one_1974_; lean_object* v_n_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v_one_1974_ = lean_unsigned_to_nat(1u);
v_n_1975_ = lean_nat_sub(v_x_1966_, v_one_1974_);
v___x_1976_ = l_List_eraseIdx___redArg(v_tail_1968_, v_n_1975_);
lean_dec(v_n_1975_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 1, v___x_1976_);
v___x_1978_ = v___x_1970_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_head_1967_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___redArg___boxed(lean_object* v_x_1981_, lean_object* v_x_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_List_eraseIdx___redArg(v_x_1981_, v_x_1982_);
lean_dec(v_x_1982_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object* v_00_u03b1_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_List_eraseIdx___redArg(v_x_1985_, v_x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___boxed(lean_object* v_00_u03b1_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_List_eraseIdx(v_00_u03b1_1988_, v_x_1989_, v_x_1990_);
lean_dec(v_x_1990_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___redArg(lean_object* v_p_1992_, lean_object* v_x_1993_){
_start:
{
if (lean_obj_tag(v_x_1993_) == 0)
{
lean_object* v___x_1994_; 
lean_dec_ref(v_p_1992_);
v___x_1994_ = lean_box(0);
return v___x_1994_;
}
else
{
lean_object* v_head_1995_; lean_object* v_tail_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_head_1995_ = lean_ctor_get(v_x_1993_, 0);
lean_inc_n(v_head_1995_, 2);
v_tail_1996_ = lean_ctor_get(v_x_1993_, 1);
lean_inc(v_tail_1996_);
lean_dec_ref_known(v_x_1993_, 2);
lean_inc_ref(v_p_1992_);
v___x_1997_ = lean_apply_1(v_p_1992_, v_head_1995_);
v___x_1998_ = lean_unbox(v___x_1997_);
if (v___x_1998_ == 0)
{
lean_dec(v_head_1995_);
v_x_1993_ = v_tail_1996_;
goto _start;
}
else
{
lean_object* v___x_2000_; 
lean_dec(v_tail_1996_);
lean_dec_ref(v_p_1992_);
v___x_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_head_1995_);
return v___x_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object* v_00_u03b1_2001_, lean_object* v_p_2002_, lean_object* v_x_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_List_find_x3f___redArg(v_p_2002_, v_x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___redArg(lean_object* v_f_2005_, lean_object* v_x_2006_){
_start:
{
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v___x_2007_; 
lean_dec_ref(v_f_2005_);
v___x_2007_ = lean_box(0);
return v___x_2007_;
}
else
{
lean_object* v_head_2008_; lean_object* v_tail_2009_; lean_object* v___x_2010_; 
v_head_2008_ = lean_ctor_get(v_x_2006_, 0);
lean_inc(v_head_2008_);
v_tail_2009_ = lean_ctor_get(v_x_2006_, 1);
lean_inc(v_tail_2009_);
lean_dec_ref_known(v_x_2006_, 2);
lean_inc_ref(v_f_2005_);
v___x_2010_ = lean_apply_1(v_f_2005_, v_head_2008_);
if (lean_obj_tag(v___x_2010_) == 0)
{
v_x_2006_ = v_tail_2009_;
goto _start;
}
else
{
lean_dec(v_tail_2009_);
lean_dec_ref(v_f_2005_);
return v___x_2010_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object* v_00_u03b1_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_f_2014_, lean_object* v_x_2015_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_List_findSome_x3f___redArg(v_f_2014_, v_x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f___redArg(lean_object* v_p_2017_, lean_object* v_x_2018_){
_start:
{
if (lean_obj_tag(v_x_2018_) == 0)
{
lean_object* v___x_2019_; 
lean_dec_ref(v_p_2017_);
v___x_2019_ = lean_box(0);
return v___x_2019_;
}
else
{
lean_object* v_head_2020_; lean_object* v_tail_2021_; lean_object* v___x_2022_; 
v_head_2020_ = lean_ctor_get(v_x_2018_, 0);
lean_inc(v_head_2020_);
v_tail_2021_ = lean_ctor_get(v_x_2018_, 1);
lean_inc(v_tail_2021_);
lean_dec_ref_known(v_x_2018_, 2);
lean_inc_ref(v_p_2017_);
v___x_2022_ = l_List_findRev_x3f___redArg(v_p_2017_, v_tail_2021_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
lean_inc(v_head_2020_);
v___x_2023_ = lean_apply_1(v_p_2017_, v_head_2020_);
v___x_2024_ = lean_unbox(v___x_2023_);
if (v___x_2024_ == 0)
{
lean_dec(v_head_2020_);
return v___x_2022_;
}
else
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v_head_2020_);
return v___x_2025_;
}
}
else
{
lean_dec(v_head_2020_);
lean_dec_ref(v_p_2017_);
return v___x_2022_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3f(lean_object* v_00_u03b1_2026_, lean_object* v_p_2027_, lean_object* v_x_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_List_findRev_x3f___redArg(v_p_2027_, v_x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f___redArg(lean_object* v_f_2030_, lean_object* v_x_2031_){
_start:
{
if (lean_obj_tag(v_x_2031_) == 0)
{
lean_object* v___x_2032_; 
lean_dec_ref(v_f_2030_);
v___x_2032_ = lean_box(0);
return v___x_2032_;
}
else
{
lean_object* v_head_2033_; lean_object* v_tail_2034_; lean_object* v___x_2035_; 
v_head_2033_ = lean_ctor_get(v_x_2031_, 0);
lean_inc(v_head_2033_);
v_tail_2034_ = lean_ctor_get(v_x_2031_, 1);
lean_inc(v_tail_2034_);
lean_dec_ref_known(v_x_2031_, 2);
lean_inc_ref(v_f_2030_);
v___x_2035_ = l_List_findSomeRev_x3f___redArg(v_f_2030_, v_tail_2034_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_apply_1(v_f_2030_, v_head_2033_);
return v___x_2036_;
}
else
{
lean_dec(v_head_2033_);
lean_dec_ref(v_f_2030_);
return v___x_2035_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3f(lean_object* v_00_u03b1_2037_, lean_object* v_00_u03b2_2038_, lean_object* v_f_2039_, lean_object* v_x_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_List_findSomeRev_x3f___redArg(v_f_2039_, v_x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___redArg(lean_object* v_p_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
if (lean_obj_tag(v_a_2043_) == 0)
{
lean_dec_ref(v_p_2042_);
return v_a_2044_;
}
else
{
lean_object* v_head_2045_; lean_object* v_tail_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_head_2045_ = lean_ctor_get(v_a_2043_, 0);
lean_inc(v_head_2045_);
v_tail_2046_ = lean_ctor_get(v_a_2043_, 1);
lean_inc(v_tail_2046_);
lean_dec_ref_known(v_a_2043_, 2);
lean_inc_ref(v_p_2042_);
v___x_2047_ = lean_apply_1(v_p_2042_, v_head_2045_);
v___x_2048_ = lean_unbox(v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_nat_add(v_a_2044_, v___x_2049_);
lean_dec(v_a_2044_);
v_a_2043_ = v_tail_2046_;
v_a_2044_ = v___x_2050_;
goto _start;
}
else
{
lean_dec(v_tail_2046_);
lean_dec_ref(v_p_2042_);
return v_a_2044_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object* v_00_u03b1_2052_, lean_object* v_p_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_List_findIdx_go___redArg(v_p_2053_, v_a_2054_, v_a_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx___redArg(lean_object* v_p_2057_, lean_object* v_l_2058_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = l_List_findIdx_go___redArg(v_p_2057_, v_l_2058_, v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx(lean_object* v_00_u03b1_2061_, lean_object* v_p_2062_, lean_object* v_l_2063_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v___x_2065_ = l_List_findIdx_go___redArg(v_p_2062_, v_l_2063_, v___x_2064_);
return v___x_2065_;
}
}
uint8_t l_List_idxOf___redArg___lam__0(lean_object* v_inst_2066_, lean_object* v_a_2067_, lean_object* v_x_2068_){
_start:
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = lean_apply_2(v_inst_2066_, v_x_2068_, v_a_2067_);
v___x_2070_ = lean_unbox(v___x_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT void l_List_idxOf___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2066_ = stack[0].m_obj;
lean_object* v_a_2067_ = stack[1].m_obj;
lean_object* v_x_2068_ = stack[2].m_obj;
uint8_t v_res_2071_;
v_res_2071_ = l_List_idxOf___redArg___lam__0(v_inst_2066_, v_a_2067_, v_x_2068_);
stack->m_num = v_res_2071_;
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg___lam__0___boxed(lean_object* v_inst_2072_, lean_object* v_a_2073_, lean_object* v_x_2074_){
_start:
{
uint8_t v_res_2075_; lean_object* v_r_2076_; 
v_res_2075_ = l_List_idxOf___redArg___lam__0(v_inst_2072_, v_a_2073_, v_x_2074_);
v_r_2076_ = lean_box(v_res_2075_);
return v_r_2076_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf___redArg(lean_object* v_inst_2077_, lean_object* v_a_2078_, lean_object* v_l_2079_){
_start:
{
lean_object* v___f_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___f_2080_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2080_, 0, v_inst_2077_);
lean_closure_set(v___f_2080_, 1, v_a_2078_);
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = l_List_findIdx_go___redArg(v___f_2080_, v_l_2079_, v___x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf(lean_object* v_00_u03b1_2083_, lean_object* v_inst_2084_, lean_object* v_a_2085_, lean_object* v_l_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_List_idxOf___redArg(v_inst_2084_, v_a_2085_, v_l_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___redArg(lean_object* v_p_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
if (lean_obj_tag(v_a_2089_) == 0)
{
lean_object* v___x_2091_; 
lean_dec(v_a_2090_);
lean_dec_ref(v_p_2088_);
v___x_2091_ = lean_box(0);
return v___x_2091_;
}
else
{
lean_object* v_head_2092_; lean_object* v_tail_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_head_2092_ = lean_ctor_get(v_a_2089_, 0);
lean_inc(v_head_2092_);
v_tail_2093_ = lean_ctor_get(v_a_2089_, 1);
lean_inc(v_tail_2093_);
lean_dec_ref_known(v_a_2089_, 2);
lean_inc_ref(v_p_2088_);
v___x_2094_ = lean_apply_1(v_p_2088_, v_head_2092_);
v___x_2095_ = lean_unbox(v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_unsigned_to_nat(1u);
v___x_2097_ = lean_nat_add(v_a_2090_, v___x_2096_);
lean_dec(v_a_2090_);
v_a_2089_ = v_tail_2093_;
v_a_2090_ = v___x_2097_;
goto _start;
}
else
{
lean_object* v___x_2099_; 
lean_dec(v_tail_2093_);
lean_dec_ref(v_p_2088_);
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_a_2090_);
return v___x_2099_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go(lean_object* v_00_u03b1_2100_, lean_object* v_p_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_List_findIdx_x3f_go___redArg(v_p_2101_, v_a_2102_, v_a_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f___redArg(lean_object* v_p_2105_, lean_object* v_l_2106_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_unsigned_to_nat(0u);
v___x_2108_ = l_List_findIdx_x3f_go___redArg(v_p_2105_, v_l_2106_, v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object* v_00_u03b1_2109_, lean_object* v_p_2110_, lean_object* v_l_2111_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_unsigned_to_nat(0u);
v___x_2113_ = l_List_findIdx_x3f_go___redArg(v_p_2110_, v_l_2111_, v___x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f___redArg(lean_object* v_inst_2114_, lean_object* v_a_2115_, lean_object* v_l_2116_){
_start:
{
lean_object* v___f_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___f_2117_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2117_, 0, v_inst_2114_);
lean_closure_set(v___f_2117_, 1, v_a_2115_);
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = l_List_findIdx_x3f_go___redArg(v___f_2117_, v_l_2116_, v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_List_idxOf_x3f(lean_object* v_00_u03b1_2120_, lean_object* v_inst_2121_, lean_object* v_a_2122_, lean_object* v_l_2123_){
_start:
{
lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___f_2124_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2124_, 0, v_inst_2121_);
lean_closure_set(v___f_2124_, 1, v_a_2122_);
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = l_List_findIdx_x3f_go___redArg(v___f_2124_, v_l_2123_, v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___redArg(lean_object* v_p_2127_, lean_object* v_l_x27_2128_, lean_object* v_i_2129_){
_start:
{
if (lean_obj_tag(v_l_x27_2128_) == 0)
{
lean_object* v___x_2130_; 
lean_dec(v_i_2129_);
lean_dec_ref(v_p_2127_);
v___x_2130_ = lean_box(0);
return v___x_2130_;
}
else
{
lean_object* v_head_2131_; lean_object* v_tail_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v_head_2131_ = lean_ctor_get(v_l_x27_2128_, 0);
lean_inc(v_head_2131_);
v_tail_2132_ = lean_ctor_get(v_l_x27_2128_, 1);
lean_inc(v_tail_2132_);
lean_dec_ref_known(v_l_x27_2128_, 2);
lean_inc_ref(v_p_2127_);
v___x_2133_ = lean_apply_1(v_p_2127_, v_head_2131_);
v___x_2134_ = lean_unbox(v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = lean_nat_add(v_i_2129_, v___x_2135_);
lean_dec(v_i_2129_);
v_l_x27_2128_ = v_tail_2132_;
v_i_2129_ = v___x_2136_;
goto _start;
}
else
{
lean_object* v___x_2138_; 
lean_dec(v_tail_2132_);
lean_dec_ref(v_p_2127_);
v___x_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2138_, 0, v_i_2129_);
return v___x_2138_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go(lean_object* v_00_u03b1_2139_, lean_object* v_p_2140_, lean_object* v_l_2141_, lean_object* v_l_x27_2142_, lean_object* v_i_2143_, lean_object* v_h_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_List_findFinIdx_x3f_go___redArg(v_p_2140_, v_l_x27_2142_, v_i_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f_go___boxed(lean_object* v_00_u03b1_2146_, lean_object* v_p_2147_, lean_object* v_l_2148_, lean_object* v_l_x27_2149_, lean_object* v_i_2150_, lean_object* v_h_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_List_findFinIdx_x3f_go(v_00_u03b1_2146_, v_p_2147_, v_l_2148_, v_l_x27_2149_, v_i_2150_, v_h_2151_);
lean_dec(v_l_2148_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f___redArg(lean_object* v_p_2153_, lean_object* v_l_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = l_List_findFinIdx_x3f_go___redArg(v_p_2153_, v_l_2154_, v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_List_findFinIdx_x3f(lean_object* v_00_u03b1_2157_, lean_object* v_p_2158_, lean_object* v_l_2159_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = l_List_findFinIdx_x3f_go___redArg(v_p_2158_, v_l_2159_, v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f___redArg(lean_object* v_inst_2162_, lean_object* v_a_2163_, lean_object* v_l_2164_){
_start:
{
lean_object* v___f_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___f_2165_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2165_, 0, v_inst_2162_);
lean_closure_set(v___f_2165_, 1, v_a_2163_);
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = l_List_findFinIdx_x3f_go___redArg(v___f_2165_, v_l_2164_, v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_List_finIdxOf_x3f(lean_object* v_00_u03b1_2168_, lean_object* v_inst_2169_, lean_object* v_a_2170_, lean_object* v_l_2171_){
_start:
{
lean_object* v___f_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___f_2172_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2172_, 0, v_inst_2169_);
lean_closure_set(v___f_2172_, 1, v_a_2170_);
v___x_2173_ = lean_unsigned_to_nat(0u);
v___x_2174_ = l_List_findFinIdx_x3f_go___redArg(v___f_2172_, v_l_2171_, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___redArg(lean_object* v_p_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
if (lean_obj_tag(v_a_2176_) == 0)
{
lean_dec_ref(v_p_2175_);
return v_a_2177_;
}
else
{
lean_object* v_head_2178_; lean_object* v_tail_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v_head_2178_ = lean_ctor_get(v_a_2176_, 0);
lean_inc(v_head_2178_);
v_tail_2179_ = lean_ctor_get(v_a_2176_, 1);
lean_inc(v_tail_2179_);
lean_dec_ref_known(v_a_2176_, 2);
lean_inc_ref(v_p_2175_);
v___x_2180_ = lean_apply_1(v_p_2175_, v_head_2178_);
v___x_2181_ = lean_unbox(v___x_2180_);
if (v___x_2181_ == 0)
{
v_a_2176_ = v_tail_2179_;
goto _start;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_unsigned_to_nat(1u);
v___x_2184_ = lean_nat_add(v_a_2177_, v___x_2183_);
lean_dec(v_a_2177_);
v_a_2176_ = v_tail_2179_;
v_a_2177_ = v___x_2184_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go(lean_object* v_00_u03b1_2186_, lean_object* v_p_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_List_countP_go___redArg(v_p_2187_, v_a_2188_, v_a_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_List_countP___redArg(lean_object* v_p_2191_, lean_object* v_l_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_unsigned_to_nat(0u);
v___x_2194_ = l_List_countP_go___redArg(v_p_2191_, v_l_2192_, v___x_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_List_countP(lean_object* v_00_u03b1_2195_, lean_object* v_p_2196_, lean_object* v_l_2197_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = l_List_countP_go___redArg(v_p_2196_, v_l_2197_, v___x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_List_count___redArg(lean_object* v_inst_2200_, lean_object* v_a_2201_, lean_object* v_l_2202_){
_start:
{
lean_object* v___f_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___f_2203_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2203_, 0, v_inst_2200_);
lean_closure_set(v___f_2203_, 1, v_a_2201_);
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = l_List_countP_go___redArg(v___f_2203_, v_l_2202_, v___x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_List_count(lean_object* v_00_u03b1_2206_, lean_object* v_inst_2207_, lean_object* v_a_2208_, lean_object* v_l_2209_){
_start:
{
lean_object* v___f_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___f_2210_ = lean_alloc_closure((void*)(l_List_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2210_, 0, v_inst_2207_);
lean_closure_set(v___f_2210_, 1, v_a_2208_);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = l_List_countP_go___redArg(v___f_2210_, v_l_2209_, v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___redArg(lean_object* v_inst_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_){
_start:
{
if (lean_obj_tag(v_x_2215_) == 0)
{
lean_object* v___x_2216_; 
lean_dec(v_x_2214_);
lean_dec_ref(v_inst_2213_);
v___x_2216_ = lean_box(0);
return v___x_2216_;
}
else
{
lean_object* v_head_2217_; lean_object* v_tail_2218_; lean_object* v_fst_2219_; lean_object* v_snd_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v_head_2217_ = lean_ctor_get(v_x_2215_, 0);
lean_inc(v_head_2217_);
v_tail_2218_ = lean_ctor_get(v_x_2215_, 1);
lean_inc(v_tail_2218_);
lean_dec_ref_known(v_x_2215_, 2);
v_fst_2219_ = lean_ctor_get(v_head_2217_, 0);
lean_inc(v_fst_2219_);
v_snd_2220_ = lean_ctor_get(v_head_2217_, 1);
lean_inc(v_snd_2220_);
lean_dec(v_head_2217_);
lean_inc_ref(v_inst_2213_);
lean_inc(v_x_2214_);
v___x_2221_ = lean_apply_2(v_inst_2213_, v_x_2214_, v_fst_2219_);
v___x_2222_ = lean_unbox(v___x_2221_);
if (v___x_2222_ == 0)
{
lean_dec(v_snd_2220_);
v_x_2215_ = v_tail_2218_;
goto _start;
}
else
{
lean_object* v___x_2224_; 
lean_dec(v_tail_2218_);
lean_dec(v_x_2214_);
lean_dec_ref(v_inst_2213_);
v___x_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_snd_2220_);
return v___x_2224_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup(lean_object* v_00_u03b1_2225_, lean_object* v_00_u03b2_2226_, lean_object* v_inst_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_List_lookup___redArg(v_inst_2227_, v_x_2228_, v_x_2229_);
return v___x_2230_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0));
v___x_2249_ = l_String_toRawSubstring_x27(v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object* v_x_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
lean_inc(v_x_2269_);
v___x_2273_ = l_Lean_Syntax_isOfKind(v_x_2269_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec(v_x_2269_);
v___x_2274_ = lean_box(1);
v___x_2275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v_a_2271_);
return v___x_2275_;
}
else
{
lean_object* v_quotContext_2276_; lean_object* v_currMacroScope_2277_; lean_object* v_ref_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_quotContext_2276_ = lean_ctor_get(v_a_2270_, 1);
v_currMacroScope_2277_ = lean_ctor_get(v_a_2270_, 2);
v_ref_2278_ = lean_ctor_get(v_a_2270_, 5);
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = l_Lean_Syntax_getArg(v_x_2269_, v___x_2279_);
v___x_2281_ = lean_unsigned_to_nat(2u);
v___x_2282_ = l_Lean_Syntax_getArg(v_x_2269_, v___x_2281_);
lean_dec(v_x_2269_);
v___x_2283_ = 0;
v___x_2284_ = l_Lean_SourceInfo_fromRef(v_ref_2278_, v___x_2283_);
v___x_2285_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
v___x_2286_ = lean_obj_once(&l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1, &l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once, _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
v___x_2287_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2));
lean_inc(v_currMacroScope_2277_);
lean_inc(v_quotContext_2276_);
v___x_2288_ = l_Lean_addMacroScope(v_quotContext_2276_, v___x_2287_, v_currMacroScope_2277_);
v___x_2289_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8));
lean_inc_n(v___x_2284_, 2);
v___x_2290_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2284_);
lean_ctor_set(v___x_2290_, 1, v___x_2286_);
lean_ctor_set(v___x_2290_, 2, v___x_2288_);
lean_ctor_set(v___x_2290_, 3, v___x_2289_);
v___x_2291_ = ((lean_object*)(l_List_lex___auto__1___closed__9));
v___x_2292_ = l_Lean_Syntax_node2(v___x_2284_, v___x_2291_, v___x_2280_, v___x_2282_);
v___x_2293_ = l_Lean_Syntax_node2(v___x_2284_, v___x_2285_, v___x_2290_, v___x_2292_);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v_a_2271_);
return v___x_2294_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___boxed(lean_object* v_x_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(v_x_2295_, v_a_2296_, v_a_2297_);
lean_dec_ref(v_a_2296_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object* v_x_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1));
lean_inc(v_x_2299_);
v___x_2303_ = l_Lean_Syntax_isOfKind(v_x_2299_, v___x_2302_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_dec(v_x_2299_);
v___x_2304_ = lean_box(0);
v___x_2305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
lean_ctor_set(v___x_2305_, 1, v_a_2301_);
return v___x_2305_;
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2306_ = lean_unsigned_to_nat(0u);
v___x_2307_ = l_Lean_Syntax_getArg(v_x_2299_, v___x_2306_);
v___x_2308_ = ((lean_object*)(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1));
lean_inc(v___x_2307_);
v___x_2309_ = l_Lean_Syntax_isOfKind(v___x_2307_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_dec(v___x_2307_);
lean_dec(v_x_2299_);
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v_a_2301_);
return v___x_2311_;
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2312_ = lean_unsigned_to_nat(1u);
v___x_2313_ = l_Lean_Syntax_getArg(v_x_2299_, v___x_2312_);
lean_dec(v_x_2299_);
v___x_2314_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2313_);
v___x_2315_ = l_Lean_Syntax_matchesNull(v___x_2313_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_dec(v___x_2313_);
lean_dec(v___x_2307_);
v___x_2316_ = lean_box(0);
v___x_2317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v_a_2301_);
return v___x_2317_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v_ref_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2318_ = l_Lean_Syntax_getArg(v___x_2313_, v___x_2306_);
v___x_2319_ = l_Lean_Syntax_getArg(v___x_2313_, v___x_2312_);
lean_dec(v___x_2313_);
v_ref_2320_ = l_Lean_replaceRef(v___x_2307_, v_a_2300_);
lean_dec(v___x_2307_);
v___x_2321_ = 0;
v___x_2322_ = l_Lean_SourceInfo_fromRef(v_ref_2320_, v___x_2321_);
lean_dec(v_ref_2320_);
v___x_2323_ = ((lean_object*)(l_List_term___x7e___00__closed__1));
v___x_2324_ = ((lean_object*)(l_List_term___x7e___00__closed__2));
lean_inc(v___x_2322_);
v___x_2325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2322_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = l_Lean_Syntax_node3(v___x_2322_, v___x_2323_, v___x_2318_, v___x_2325_, v___x_2319_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v_a_2301_);
return v___x_2327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object* v_x_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(v_x_2328_, v_a_2329_, v_a_2330_);
lean_dec(v_a_2329_);
return v_res_2331_;
}
}
uint8_t l_List_isPerm___redArg(lean_object* v_inst_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_){
_start:
{
if (lean_obj_tag(v_x_2333_) == 0)
{
uint8_t v___x_2335_; 
lean_dec_ref(v_inst_2332_);
v___x_2335_ = l_List_isEmpty___redArg(v_x_2334_);
lean_dec(v_x_2334_);
return v___x_2335_;
}
else
{
lean_object* v_head_2336_; lean_object* v_tail_2337_; uint8_t v___x_2338_; 
v_head_2336_ = lean_ctor_get(v_x_2333_, 0);
lean_inc_n(v_head_2336_, 2);
v_tail_2337_ = lean_ctor_get(v_x_2333_, 1);
lean_inc(v_tail_2337_);
lean_dec_ref_known(v_x_2333_, 2);
lean_inc(v_x_2334_);
lean_inc_ref(v_inst_2332_);
v___x_2338_ = l_List_elem___redArg(v_inst_2332_, v_head_2336_, v_x_2334_);
if (v___x_2338_ == 0)
{
lean_dec(v_tail_2337_);
lean_dec(v_head_2336_);
lean_dec(v_x_2334_);
lean_dec_ref(v_inst_2332_);
return v___x_2338_;
}
else
{
lean_object* v___x_2339_; 
lean_inc_ref(v_inst_2332_);
v___x_2339_ = l_List_erase___redArg(v_inst_2332_, v_x_2334_, v_head_2336_);
v_x_2333_ = v_tail_2337_;
v_x_2334_ = v___x_2339_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_isPerm___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2332_ = stack[0].m_obj;
lean_object* v_x_2333_ = stack[1].m_obj;
lean_object* v_x_2334_ = stack[2].m_obj;
uint8_t v_res_2341_;
v_res_2341_ = l_List_isPerm___redArg(v_inst_2332_, v_x_2333_, v_x_2334_);
stack->m_num = v_res_2341_;
}
LEAN_EXPORT lean_object* l_List_isPerm___redArg___boxed(lean_object* v_inst_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
uint8_t v_res_2345_; lean_object* v_r_2346_; 
v_res_2345_ = l_List_isPerm___redArg(v_inst_2342_, v_x_2343_, v_x_2344_);
v_r_2346_ = lean_box(v_res_2345_);
return v_r_2346_;
}
}
uint8_t l_List_isPerm(lean_object* v_00_u03b1_2347_, lean_object* v_inst_2348_, lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
uint8_t v___x_2351_; 
v___x_2351_ = l_List_isPerm___redArg(v_inst_2348_, v_x_2349_, v_x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT void l_List_isPerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2348_ = stack[1].m_obj;
lean_object* v_x_2349_ = stack[2].m_obj;
lean_object* v_x_2350_ = stack[3].m_obj;
uint8_t v_res_2352_;
v_res_2352_ = l_List_isPerm(lean_box(0), v_inst_2348_, v_x_2349_, v_x_2350_);
stack->m_num = v_res_2352_;
}
LEAN_EXPORT lean_object* l_List_isPerm___boxed(lean_object* v_00_u03b1_2353_, lean_object* v_inst_2354_, lean_object* v_x_2355_, lean_object* v_x_2356_){
_start:
{
uint8_t v_res_2357_; lean_object* v_r_2358_; 
v_res_2357_ = l_List_isPerm(v_00_u03b1_2353_, v_inst_2354_, v_x_2355_, v_x_2356_);
v_r_2358_ = lean_box(v_res_2357_);
return v_r_2358_;
}
}
uint8_t l_List_any___redArg(lean_object* v_x_2359_, lean_object* v_x_2360_){
_start:
{
if (lean_obj_tag(v_x_2359_) == 0)
{
uint8_t v___x_2361_; 
lean_dec_ref(v_x_2360_);
v___x_2361_ = 0;
return v___x_2361_;
}
else
{
lean_object* v_head_2362_; lean_object* v_tail_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
v_head_2362_ = lean_ctor_get(v_x_2359_, 0);
lean_inc(v_head_2362_);
v_tail_2363_ = lean_ctor_get(v_x_2359_, 1);
lean_inc(v_tail_2363_);
lean_dec_ref_known(v_x_2359_, 2);
lean_inc_ref(v_x_2360_);
v___x_2364_ = lean_apply_1(v_x_2360_, v_head_2362_);
v___x_2365_ = lean_unbox(v___x_2364_);
if (v___x_2365_ == 0)
{
v_x_2359_ = v_tail_2363_;
goto _start;
}
else
{
uint8_t v___x_2367_; 
lean_dec(v_tail_2363_);
lean_dec_ref(v_x_2360_);
v___x_2367_ = lean_unbox(v___x_2364_);
return v___x_2367_;
}
}
}
}
LEAN_EXPORT void l_List_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2359_ = stack[0].m_obj;
lean_object* v_x_2360_ = stack[1].m_obj;
uint8_t v_res_2368_;
v_res_2368_ = l_List_any___redArg(v_x_2359_, v_x_2360_);
stack->m_num = v_res_2368_;
}
LEAN_EXPORT lean_object* l_List_any___redArg___boxed(lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
uint8_t v_res_2371_; lean_object* v_r_2372_; 
v_res_2371_ = l_List_any___redArg(v_x_2369_, v_x_2370_);
v_r_2372_ = lean_box(v_res_2371_);
return v_r_2372_;
}
}
uint8_t l_List_any(lean_object* v_00_u03b1_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_){
_start:
{
uint8_t v___x_2376_; 
v___x_2376_ = l_List_any___redArg(v_x_2374_, v_x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT void l_List_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2374_ = stack[1].m_obj;
lean_object* v_x_2375_ = stack[2].m_obj;
uint8_t v_res_2377_;
v_res_2377_ = l_List_any(lean_box(0), v_x_2374_, v_x_2375_);
stack->m_num = v_res_2377_;
}
LEAN_EXPORT lean_object* l_List_any___boxed(lean_object* v_00_u03b1_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_){
_start:
{
uint8_t v_res_2381_; lean_object* v_r_2382_; 
v_res_2381_ = l_List_any(v_00_u03b1_2378_, v_x_2379_, v_x_2380_);
v_r_2382_ = lean_box(v_res_2381_);
return v_r_2382_;
}
}
uint8_t l_List_all___redArg(lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
if (lean_obj_tag(v_x_2383_) == 0)
{
uint8_t v___x_2385_; 
lean_dec_ref(v_x_2384_);
v___x_2385_ = 1;
return v___x_2385_;
}
else
{
lean_object* v_head_2386_; lean_object* v_tail_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v_head_2386_ = lean_ctor_get(v_x_2383_, 0);
lean_inc(v_head_2386_);
v_tail_2387_ = lean_ctor_get(v_x_2383_, 1);
lean_inc(v_tail_2387_);
lean_dec_ref_known(v_x_2383_, 2);
lean_inc_ref(v_x_2384_);
v___x_2388_ = lean_apply_1(v_x_2384_, v_head_2386_);
v___x_2389_ = lean_unbox(v___x_2388_);
if (v___x_2389_ == 0)
{
uint8_t v___x_2390_; 
lean_dec(v_tail_2387_);
lean_dec_ref(v_x_2384_);
v___x_2390_ = lean_unbox(v___x_2388_);
return v___x_2390_;
}
else
{
v_x_2383_ = v_tail_2387_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2383_ = stack[0].m_obj;
lean_object* v_x_2384_ = stack[1].m_obj;
uint8_t v_res_2392_;
v_res_2392_ = l_List_all___redArg(v_x_2383_, v_x_2384_);
stack->m_num = v_res_2392_;
}
LEAN_EXPORT lean_object* l_List_all___redArg___boxed(lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
uint8_t v_res_2395_; lean_object* v_r_2396_; 
v_res_2395_ = l_List_all___redArg(v_x_2393_, v_x_2394_);
v_r_2396_ = lean_box(v_res_2395_);
return v_r_2396_;
}
}
uint8_t l_List_all(lean_object* v_00_u03b1_2397_, lean_object* v_x_2398_, lean_object* v_x_2399_){
_start:
{
uint8_t v___x_2400_; 
v___x_2400_ = l_List_all___redArg(v_x_2398_, v_x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT void l_List_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2398_ = stack[1].m_obj;
lean_object* v_x_2399_ = stack[2].m_obj;
uint8_t v_res_2401_;
v_res_2401_ = l_List_all(lean_box(0), v_x_2398_, v_x_2399_);
stack->m_num = v_res_2401_;
}
LEAN_EXPORT lean_object* l_List_all___boxed(lean_object* v_00_u03b1_2402_, lean_object* v_x_2403_, lean_object* v_x_2404_){
_start:
{
uint8_t v_res_2405_; lean_object* v_r_2406_; 
v_res_2405_ = l_List_all(v_00_u03b1_2402_, v_x_2403_, v_x_2404_);
v_r_2406_ = lean_box(v_res_2405_);
return v_r_2406_;
}
}
uint8_t l_List_any___at___00List_or_spec__0(lean_object* v_x_2407_){
_start:
{
if (lean_obj_tag(v_x_2407_) == 0)
{
uint8_t v___x_2408_; 
v___x_2408_ = 0;
return v___x_2408_;
}
else
{
lean_object* v_head_2409_; uint8_t v___x_2410_; 
v_head_2409_ = lean_ctor_get(v_x_2407_, 0);
v___x_2410_ = lean_unbox(v_head_2409_);
if (v___x_2410_ == 0)
{
lean_object* v_tail_2411_; 
v_tail_2411_ = lean_ctor_get(v_x_2407_, 1);
v_x_2407_ = v_tail_2411_;
goto _start;
}
else
{
uint8_t v___x_2413_; 
v___x_2413_ = lean_unbox(v_head_2409_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00List_or_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2407_ = stack[0].m_obj;
uint8_t v_res_2414_;
v_res_2414_ = l_List_any___at___00List_or_spec__0(v_x_2407_);
stack->m_num = v_res_2414_;
}
LEAN_EXPORT lean_object* l_List_any___at___00List_or_spec__0___boxed(lean_object* v_x_2415_){
_start:
{
uint8_t v_res_2416_; lean_object* v_r_2417_; 
v_res_2416_ = l_List_any___at___00List_or_spec__0(v_x_2415_);
lean_dec(v_x_2415_);
v_r_2417_ = lean_box(v_res_2416_);
return v_r_2417_;
}
}
uint8_t l_List_or(lean_object* v_bs_2418_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = l_List_any___at___00List_or_spec__0(v_bs_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT void l_List_or_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_2418_ = stack[0].m_obj;
uint8_t v_res_2420_;
v_res_2420_ = l_List_or(v_bs_2418_);
stack->m_num = v_res_2420_;
}
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object* v_bs_2421_){
_start:
{
uint8_t v_res_2422_; lean_object* v_r_2423_; 
v_res_2422_ = l_List_or(v_bs_2421_);
lean_dec(v_bs_2421_);
v_r_2423_ = lean_box(v_res_2422_);
return v_r_2423_;
}
}
uint8_t l_List_all___at___00List_and_spec__0(lean_object* v_x_2424_){
_start:
{
if (lean_obj_tag(v_x_2424_) == 0)
{
uint8_t v___x_2425_; 
v___x_2425_ = 1;
return v___x_2425_;
}
else
{
lean_object* v_head_2426_; uint8_t v___x_2427_; 
v_head_2426_ = lean_ctor_get(v_x_2424_, 0);
v___x_2427_ = lean_unbox(v_head_2426_);
if (v___x_2427_ == 0)
{
uint8_t v___x_2428_; 
v___x_2428_ = lean_unbox(v_head_2426_);
return v___x_2428_;
}
else
{
lean_object* v_tail_2429_; 
v_tail_2429_ = lean_ctor_get(v_x_2424_, 1);
v_x_2424_ = v_tail_2429_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_all___at___00List_and_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2424_ = stack[0].m_obj;
uint8_t v_res_2431_;
v_res_2431_ = l_List_all___at___00List_and_spec__0(v_x_2424_);
stack->m_num = v_res_2431_;
}
LEAN_EXPORT lean_object* l_List_all___at___00List_and_spec__0___boxed(lean_object* v_x_2432_){
_start:
{
uint8_t v_res_2433_; lean_object* v_r_2434_; 
v_res_2433_ = l_List_all___at___00List_and_spec__0(v_x_2432_);
lean_dec(v_x_2432_);
v_r_2434_ = lean_box(v_res_2433_);
return v_r_2434_;
}
}
uint8_t l_List_and(lean_object* v_bs_2435_){
_start:
{
uint8_t v___x_2436_; 
v___x_2436_ = l_List_all___at___00List_and_spec__0(v_bs_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT void l_List_and_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_2435_ = stack[0].m_obj;
uint8_t v_res_2437_;
v_res_2437_ = l_List_and(v_bs_2435_);
stack->m_num = v_res_2437_;
}
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object* v_bs_2438_){
_start:
{
uint8_t v_res_2439_; lean_object* v_r_2440_; 
v_res_2439_ = l_List_and(v_bs_2438_);
lean_dec(v_bs_2438_);
v_r_2440_ = lean_box(v_res_2439_);
return v_r_2440_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___redArg(lean_object* v_f_2441_, lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
if (lean_obj_tag(v_x_2442_) == 0)
{
lean_object* v___x_2444_; 
lean_dec(v_x_2443_);
lean_dec(v_f_2441_);
v___x_2444_ = lean_box(0);
return v___x_2444_;
}
else
{
if (lean_obj_tag(v_x_2443_) == 0)
{
lean_object* v___x_2445_; 
lean_dec_ref_known(v_x_2442_, 2);
lean_dec(v_f_2441_);
v___x_2445_ = lean_box(0);
return v___x_2445_;
}
else
{
lean_object* v_head_2446_; lean_object* v_tail_2447_; lean_object* v_head_2448_; lean_object* v_tail_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2458_; 
v_head_2446_ = lean_ctor_get(v_x_2442_, 0);
lean_inc(v_head_2446_);
v_tail_2447_ = lean_ctor_get(v_x_2442_, 1);
lean_inc(v_tail_2447_);
lean_dec_ref_known(v_x_2442_, 2);
v_head_2448_ = lean_ctor_get(v_x_2443_, 0);
v_tail_2449_ = lean_ctor_get(v_x_2443_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_x_2443_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2451_ = v_x_2443_;
v_isShared_2452_ = v_isSharedCheck_2458_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_tail_2449_);
lean_inc(v_head_2448_);
lean_dec(v_x_2443_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2458_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_inc(v_f_2441_);
v___x_2453_ = lean_apply_2(v_f_2441_, v_head_2446_, v_head_2448_);
v___x_2454_ = l_List_zipWith___redArg(v_f_2441_, v_tail_2447_, v_tail_2449_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___x_2454_);
lean_ctor_set(v___x_2451_, 0, v___x_2453_);
v___x_2456_ = v___x_2451_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith(lean_object* v_00_u03b1_2459_, lean_object* v_00_u03b2_2460_, lean_object* v_00_u03b3_2461_, lean_object* v_f_2462_, lean_object* v_x_2463_, lean_object* v_x_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_List_zipWith___redArg(v_f_2462_, v_x_2463_, v_x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(lean_object* v_x_2466_, lean_object* v_x_2467_, lean_object* v_h__1_2468_, lean_object* v_h__2_2469_){
_start:
{
if (lean_obj_tag(v_x_2466_) == 0)
{
lean_object* v___x_2470_; 
lean_dec(v_h__1_2468_);
v___x_2470_ = lean_apply_3(v_h__2_2469_, v_x_2466_, v_x_2467_, lean_box(0));
return v___x_2470_;
}
else
{
if (lean_obj_tag(v_x_2467_) == 0)
{
lean_object* v___x_2471_; 
lean_dec(v_h__1_2468_);
v___x_2471_ = lean_apply_3(v_h__2_2469_, v_x_2466_, v_x_2467_, lean_box(0));
return v___x_2471_;
}
else
{
lean_object* v_head_2472_; lean_object* v_tail_2473_; lean_object* v_head_2474_; lean_object* v_tail_2475_; lean_object* v___x_2476_; 
lean_dec(v_h__2_2469_);
v_head_2472_ = lean_ctor_get(v_x_2466_, 0);
lean_inc(v_head_2472_);
v_tail_2473_ = lean_ctor_get(v_x_2466_, 1);
lean_inc(v_tail_2473_);
lean_dec_ref_known(v_x_2466_, 2);
v_head_2474_ = lean_ctor_get(v_x_2467_, 0);
lean_inc(v_head_2474_);
v_tail_2475_ = lean_ctor_get(v_x_2467_, 1);
lean_inc(v_tail_2475_);
lean_dec_ref_known(v_x_2467_, 2);
v___x_2476_ = lean_apply_4(v_h__1_2468_, v_head_2472_, v_tail_2473_, v_head_2474_, v_tail_2475_);
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object* v_00_u03b1_2477_, lean_object* v_00_u03b2_2478_, lean_object* v_motive_2479_, lean_object* v_x_2480_, lean_object* v_x_2481_, lean_object* v_h__1_2482_, lean_object* v_h__2_2483_){
_start:
{
if (lean_obj_tag(v_x_2480_) == 0)
{
lean_object* v___x_2484_; 
lean_dec(v_h__1_2482_);
v___x_2484_ = lean_apply_3(v_h__2_2483_, v_x_2480_, v_x_2481_, lean_box(0));
return v___x_2484_;
}
else
{
if (lean_obj_tag(v_x_2481_) == 0)
{
lean_object* v___x_2485_; 
lean_dec(v_h__1_2482_);
v___x_2485_ = lean_apply_3(v_h__2_2483_, v_x_2480_, v_x_2481_, lean_box(0));
return v___x_2485_;
}
else
{
lean_object* v_head_2486_; lean_object* v_tail_2487_; lean_object* v_head_2488_; lean_object* v_tail_2489_; lean_object* v___x_2490_; 
lean_dec(v_h__2_2483_);
v_head_2486_ = lean_ctor_get(v_x_2480_, 0);
lean_inc(v_head_2486_);
v_tail_2487_ = lean_ctor_get(v_x_2480_, 1);
lean_inc(v_tail_2487_);
lean_dec_ref_known(v_x_2480_, 2);
v_head_2488_ = lean_ctor_get(v_x_2481_, 0);
lean_inc(v_head_2488_);
v_tail_2489_ = lean_ctor_get(v_x_2481_, 1);
lean_inc(v_tail_2489_);
lean_dec_ref_known(v_x_2481_, 2);
v___x_2490_ = lean_apply_4(v_h__1_2482_, v_head_2486_, v_tail_2487_, v_head_2488_, v_tail_2489_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object* v_x_2491_, lean_object* v_x_2492_){
_start:
{
if (lean_obj_tag(v_x_2491_) == 0)
{
lean_object* v___x_2493_; 
lean_dec(v_x_2492_);
v___x_2493_ = lean_box(0);
return v___x_2493_;
}
else
{
if (lean_obj_tag(v_x_2492_) == 0)
{
lean_object* v___x_2494_; 
lean_dec_ref_known(v_x_2491_, 2);
v___x_2494_ = lean_box(0);
return v___x_2494_;
}
else
{
lean_object* v_head_2495_; lean_object* v_tail_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2513_; 
v_head_2495_ = lean_ctor_get(v_x_2491_, 0);
v_tail_2496_ = lean_ctor_get(v_x_2491_, 1);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_x_2491_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2498_ = v_x_2491_;
v_isShared_2499_ = v_isSharedCheck_2513_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_tail_2496_);
lean_inc(v_head_2495_);
lean_dec(v_x_2491_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2513_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_head_2500_; lean_object* v_tail_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2512_; 
v_head_2500_ = lean_ctor_get(v_x_2492_, 0);
v_tail_2501_ = lean_ctor_get(v_x_2492_, 1);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_x_2492_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2503_ = v_x_2492_;
v_isShared_2504_ = v_isSharedCheck_2512_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_tail_2501_);
lean_inc(v_head_2500_);
lean_dec(v_x_2492_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2512_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2499_ == 0)
{
lean_ctor_set_tag(v___x_2498_, 0);
lean_ctor_set(v___x_2498_, 1, v_head_2500_);
v___x_2506_ = v___x_2498_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_head_2495_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_head_2500_);
v___x_2506_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_tail_2496_, v_tail_2501_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 1, v___x_2507_);
lean_ctor_set(v___x_2503_, 0, v___x_2506_);
v___x_2509_ = v___x_2503_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zip___redArg(lean_object* v_xs_2514_, lean_object* v_ys_2515_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2514_, v_ys_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_List_zip(lean_object* v_00_u03b1_2517_, lean_object* v_00_u03b2_2518_, lean_object* v_xs_2519_, lean_object* v_ys_2520_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_2519_, v_ys_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object* v_00_u03b1_2522_, lean_object* v_00_u03b2_2523_, lean_object* v_x_2524_, lean_object* v_x_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_x_2524_, v_x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__0(lean_object* v_f_2527_, lean_object* v_b_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2530_, 0, v_b_2528_);
v___x_2531_ = lean_apply_2(v_f_2527_, v___x_2529_, v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg___lam__1(lean_object* v_f_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_a_2533_);
v___x_2535_ = lean_box(0);
v___x_2536_ = lean_apply_2(v_f_2532_, v___x_2534_, v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___redArg(lean_object* v_f_2537_, lean_object* v_x_2538_, lean_object* v_x_2539_){
_start:
{
if (lean_obj_tag(v_x_2538_) == 0)
{
lean_object* v___f_2540_; lean_object* v___x_2541_; 
v___f_2540_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2540_, 0, v_f_2537_);
v___x_2541_ = l_List_map___redArg(v___f_2540_, v_x_2539_);
return v___x_2541_;
}
else
{
if (lean_obj_tag(v_x_2539_) == 0)
{
lean_object* v___f_2542_; lean_object* v___x_2543_; 
v___f_2542_ = lean_alloc_closure((void*)(l_List_zipWithAll___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2542_, 0, v_f_2537_);
v___x_2543_ = l_List_map___redArg(v___f_2542_, v_x_2538_);
return v___x_2543_;
}
else
{
lean_object* v_head_2544_; lean_object* v_tail_2545_; lean_object* v_head_2546_; lean_object* v_tail_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2558_; 
v_head_2544_ = lean_ctor_get(v_x_2538_, 0);
lean_inc(v_head_2544_);
v_tail_2545_ = lean_ctor_get(v_x_2538_, 1);
lean_inc(v_tail_2545_);
lean_dec_ref_known(v_x_2538_, 2);
v_head_2546_ = lean_ctor_get(v_x_2539_, 0);
v_tail_2547_ = lean_ctor_get(v_x_2539_, 1);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_x_2539_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2549_ = v_x_2539_;
v_isShared_2550_ = v_isSharedCheck_2558_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_tail_2547_);
lean_inc(v_head_2546_);
lean_dec(v_x_2539_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2558_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_head_2544_);
v___x_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_head_2546_);
lean_inc(v_f_2537_);
v___x_2553_ = lean_apply_2(v_f_2537_, v___x_2551_, v___x_2552_);
v___x_2554_ = l_List_zipWithAll___redArg(v_f_2537_, v_tail_2545_, v_tail_2547_);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 1, v___x_2554_);
lean_ctor_set(v___x_2549_, 0, v___x_2553_);
v___x_2556_ = v___x_2549_;
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
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object* v_00_u03b1_2559_, lean_object* v_00_u03b2_2560_, lean_object* v_00_u03b3_2561_, lean_object* v_f_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_List_zipWithAll___redArg(v_f_2562_, v_x_2563_, v_x_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_List_unzip___redArg(lean_object* v_x_2566_){
_start:
{
if (lean_obj_tag(v_x_2566_) == 0)
{
lean_object* v___x_2567_; 
v___x_2567_ = ((lean_object*)(l_List_partition___redArg___closed__0));
return v___x_2567_;
}
else
{
lean_object* v_head_2568_; lean_object* v_tail_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2595_; 
v_head_2568_ = lean_ctor_get(v_x_2566_, 0);
v_tail_2569_ = lean_ctor_get(v_x_2566_, 1);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_x_2566_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2571_ = v_x_2566_;
v_isShared_2572_ = v_isSharedCheck_2595_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_tail_2569_);
lean_inc(v_head_2568_);
lean_dec(v_x_2566_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2595_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v_fst_2573_; lean_object* v_snd_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2594_; 
v_fst_2573_ = lean_ctor_get(v_head_2568_, 0);
v_snd_2574_ = lean_ctor_get(v_head_2568_, 1);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_head_2568_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2576_ = v_head_2568_;
v_isShared_2577_ = v_isSharedCheck_2594_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_snd_2574_);
lean_inc(v_fst_2573_);
lean_dec(v_head_2568_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2594_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v_fst_2579_; lean_object* v_snd_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2593_; 
v___x_2578_ = l_List_unzip___redArg(v_tail_2569_);
v_fst_2579_ = lean_ctor_get(v___x_2578_, 0);
v_snd_2580_ = lean_ctor_get(v___x_2578_, 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2582_ = v___x_2578_;
v_isShared_2583_ = v_isSharedCheck_2593_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_snd_2580_);
lean_inc(v_fst_2579_);
lean_dec(v___x_2578_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2593_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v_fst_2579_);
lean_ctor_set(v___x_2571_, 0, v_fst_2573_);
v___x_2585_ = v___x_2571_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_fst_2573_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_fst_2579_);
v___x_2585_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2587_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set_tag(v___x_2576_, 1);
lean_ctor_set(v___x_2576_, 1, v_snd_2580_);
lean_ctor_set(v___x_2576_, 0, v_snd_2574_);
v___x_2587_ = v___x_2576_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_snd_2574_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_snd_2580_);
v___x_2587_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2589_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 1, v___x_2587_);
lean_ctor_set(v___x_2582_, 0, v___x_2585_);
v___x_2589_ = v___x_2582_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2585_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_unzip(lean_object* v_00_u03b1_2596_, lean_object* v_00_u03b2_2597_, lean_object* v_x_2598_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_List_unzip___redArg(v_x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___lam__0(lean_object* v_inst_2600_, lean_object* v_x1_2601_, lean_object* v_x2_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_apply_2(v_inst_2600_, v_x1_2601_, v_x2_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg(lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v_l_2606_){
_start:
{
lean_object* v___f_2607_; lean_object* v___x_2608_; 
v___f_2607_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2607_, 0, v_inst_2604_);
v___x_2608_ = l_List_foldr___redArg(v___f_2607_, v_inst_2605_, v_l_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_List_sum___redArg___boxed(lean_object* v_inst_2609_, lean_object* v_inst_2610_, lean_object* v_l_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_List_sum___redArg(v_inst_2609_, v_inst_2610_, v_l_2611_);
lean_dec(v_inst_2610_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_List_sum(lean_object* v_00_u03b1_2613_, lean_object* v_inst_2614_, lean_object* v_inst_2615_, lean_object* v_l_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_List_sum___redArg(v_inst_2614_, v_inst_2615_, v_l_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_List_sum___boxed(lean_object* v_00_u03b1_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_l_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_List_sum(v_00_u03b1_2618_, v_inst_2619_, v_inst_2620_, v_l_2621_);
lean_dec(v_inst_2620_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg(lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_l_2625_){
_start:
{
lean_object* v___f_2626_; lean_object* v___x_2627_; 
v___f_2626_ = lean_alloc_closure((void*)(l_List_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2626_, 0, v_inst_2623_);
v___x_2627_ = l_List_foldr___redArg(v___f_2626_, v_inst_2624_, v_l_2625_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_List_prod___redArg___boxed(lean_object* v_inst_2628_, lean_object* v_inst_2629_, lean_object* v_l_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_List_prod___redArg(v_inst_2628_, v_inst_2629_, v_l_2630_);
lean_dec(v_inst_2629_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_List_prod(lean_object* v_00_u03b1_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_l_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_List_prod___redArg(v_inst_2633_, v_inst_2634_, v_l_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_List_prod___boxed(lean_object* v_00_u03b1_2637_, lean_object* v_inst_2638_, lean_object* v_inst_2639_, lean_object* v_l_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_List_prod(v_00_u03b1_2637_, v_inst_2638_, v_inst_2639_, v_l_2640_);
lean_dec(v_inst_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_List_range_loop(lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_zero_2644_; uint8_t v_isZero_2645_; 
v_zero_2644_ = lean_unsigned_to_nat(0u);
v_isZero_2645_ = lean_nat_dec_eq(v_a_2642_, v_zero_2644_);
if (v_isZero_2645_ == 1)
{
lean_dec(v_a_2642_);
return v_a_2643_;
}
else
{
lean_object* v_one_2646_; lean_object* v_n_2647_; lean_object* v___x_2648_; 
v_one_2646_ = lean_unsigned_to_nat(1u);
v_n_2647_ = lean_nat_sub(v_a_2642_, v_one_2646_);
lean_dec(v_a_2642_);
lean_inc(v_n_2647_);
v___x_2648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2648_, 0, v_n_2647_);
lean_ctor_set(v___x_2648_, 1, v_a_2643_);
v_a_2642_ = v_n_2647_;
v_a_2643_ = v___x_2648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range(lean_object* v_n_2650_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = lean_box(0);
v___x_2652_ = l_List_range_loop(v_n_2650_, v___x_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27(lean_object* v_x_2653_, lean_object* v_x_2654_, lean_object* v_x_2655_){
_start:
{
lean_object* v_zero_2656_; uint8_t v_isZero_2657_; 
v_zero_2656_ = lean_unsigned_to_nat(0u);
v_isZero_2657_ = lean_nat_dec_eq(v_x_2654_, v_zero_2656_);
if (v_isZero_2657_ == 1)
{
lean_object* v___x_2658_; 
lean_dec(v_x_2653_);
v___x_2658_ = lean_box(0);
return v___x_2658_;
}
else
{
lean_object* v_one_2659_; lean_object* v_n_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v_one_2659_ = lean_unsigned_to_nat(1u);
v_n_2660_ = lean_nat_sub(v_x_2654_, v_one_2659_);
v___x_2661_ = lean_nat_add(v_x_2653_, v_x_2655_);
v___x_2662_ = l_List_range_x27(v___x_2661_, v_n_2660_, v_x_2655_);
lean_dec(v_n_2660_);
v___x_2663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2663_, 0, v_x_2653_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_List_range_x27(v_x_2664_, v_x_2665_, v_x_2666_);
lean_dec(v_x_2666_);
lean_dec(v_x_2665_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdx___redArg(lean_object* v_x_2668_, lean_object* v_x_2669_){
_start:
{
if (lean_obj_tag(v_x_2668_) == 0)
{
lean_object* v___x_2670_; 
lean_dec(v_x_2669_);
v___x_2670_ = lean_box(0);
return v___x_2670_;
}
else
{
lean_object* v_head_2671_; lean_object* v_tail_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2683_; 
v_head_2671_ = lean_ctor_get(v_x_2668_, 0);
v_tail_2672_ = lean_ctor_get(v_x_2668_, 1);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_x_2668_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2674_ = v_x_2668_;
v_isShared_2675_ = v_isSharedCheck_2683_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_tail_2672_);
lean_inc(v_head_2671_);
lean_dec(v_x_2668_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2683_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
lean_inc(v_x_2669_);
v___x_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2676_, 0, v_head_2671_);
lean_ctor_set(v___x_2676_, 1, v_x_2669_);
v___x_2677_ = lean_unsigned_to_nat(1u);
v___x_2678_ = lean_nat_add(v_x_2669_, v___x_2677_);
lean_dec(v_x_2669_);
v___x_2679_ = l_List_zipIdx___redArg(v_tail_2672_, v___x_2678_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 1, v___x_2679_);
lean_ctor_set(v___x_2674_, 0, v___x_2676_);
v___x_2681_ = v___x_2674_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdx(lean_object* v_00_u03b1_2684_, lean_object* v_x_2685_, lean_object* v_x_2686_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_List_zipIdx___redArg(v_x_2685_, v_x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___redArg(lean_object* v_inst_2688_, lean_object* v_x_2689_){
_start:
{
if (lean_obj_tag(v_x_2689_) == 0)
{
lean_object* v___x_2690_; 
lean_dec(v_inst_2688_);
v___x_2690_ = lean_box(0);
return v___x_2690_;
}
else
{
lean_object* v_head_2691_; lean_object* v_tail_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_head_2691_ = lean_ctor_get(v_x_2689_, 0);
lean_inc(v_head_2691_);
v_tail_2692_ = lean_ctor_get(v_x_2689_, 1);
lean_inc(v_tail_2692_);
lean_dec_ref_known(v_x_2689_, 2);
v___x_2693_ = l_List_foldl___redArg(v_inst_2688_, v_head_2691_, v_tail_2692_);
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
return v___x_2694_;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object* v_00_u03b1_2695_, lean_object* v_inst_2696_, lean_object* v_x_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_List_min_x3f___redArg(v_inst_2696_, v_x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_List_min___redArg(lean_object* v_inst_2699_, lean_object* v_x_2700_){
_start:
{
lean_object* v_head_2701_; lean_object* v_tail_2702_; lean_object* v___x_2703_; 
v_head_2701_ = lean_ctor_get(v_x_2700_, 0);
lean_inc(v_head_2701_);
v_tail_2702_ = lean_ctor_get(v_x_2700_, 1);
lean_inc(v_tail_2702_);
lean_dec(v_x_2700_);
v___x_2703_ = l_List_foldl___redArg(v_inst_2699_, v_head_2701_, v_tail_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_List_min(lean_object* v_00_u03b1_2704_, lean_object* v_inst_2705_, lean_object* v_x_2706_, lean_object* v_x_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_List_min___redArg(v_inst_2705_, v_x_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___redArg(lean_object* v_inst_2709_, lean_object* v_x_2710_){
_start:
{
if (lean_obj_tag(v_x_2710_) == 0)
{
lean_object* v___x_2711_; 
lean_dec(v_inst_2709_);
v___x_2711_ = lean_box(0);
return v___x_2711_;
}
else
{
lean_object* v_head_2712_; lean_object* v_tail_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_head_2712_ = lean_ctor_get(v_x_2710_, 0);
lean_inc(v_head_2712_);
v_tail_2713_ = lean_ctor_get(v_x_2710_, 1);
lean_inc(v_tail_2713_);
lean_dec_ref_known(v_x_2710_, 2);
v___x_2714_ = l_List_foldl___redArg(v_inst_2709_, v_head_2712_, v_tail_2713_);
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object* v_00_u03b1_2716_, lean_object* v_inst_2717_, lean_object* v_x_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_List_max_x3f___redArg(v_inst_2717_, v_x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_List_max___redArg(lean_object* v_inst_2720_, lean_object* v_x_2721_){
_start:
{
lean_object* v_head_2722_; lean_object* v_tail_2723_; lean_object* v___x_2724_; 
v_head_2722_ = lean_ctor_get(v_x_2721_, 0);
lean_inc(v_head_2722_);
v_tail_2723_ = lean_ctor_get(v_x_2721_, 1);
lean_inc(v_tail_2723_);
lean_dec(v_x_2721_);
v___x_2724_ = l_List_foldl___redArg(v_inst_2720_, v_head_2722_, v_tail_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_List_max(lean_object* v_00_u03b1_2725_, lean_object* v_inst_2726_, lean_object* v_x_2727_, lean_object* v_x_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_List_max___redArg(v_inst_2726_, v_x_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_List_intersperse___redArg(lean_object* v_sep_2730_, lean_object* v_x_2731_){
_start:
{
if (lean_obj_tag(v_x_2731_) == 0)
{
lean_dec(v_sep_2730_);
return v_x_2731_;
}
else
{
lean_object* v_tail_2732_; 
v_tail_2732_ = lean_ctor_get(v_x_2731_, 1);
if (lean_obj_tag(v_tail_2732_) == 0)
{
lean_dec(v_sep_2730_);
return v_x_2731_;
}
else
{
lean_object* v_head_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2742_; 
lean_inc_ref(v_tail_2732_);
v_head_2733_ = lean_ctor_get(v_x_2731_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_x_2731_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v_x_2731_, 1);
lean_dec(v_unused_2743_);
v___x_2735_ = v_x_2731_;
v_isShared_2736_ = v_isSharedCheck_2742_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_head_2733_);
lean_dec(v_x_2731_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2742_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
lean_inc(v_sep_2730_);
v___x_2737_ = l_List_intersperse___redArg(v_sep_2730_, v_tail_2732_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 1, v___x_2737_);
lean_ctor_set(v___x_2735_, 0, v_sep_2730_);
v___x_2739_ = v___x_2735_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_sep_2730_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2740_, 0, v_head_2733_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
return v___x_2740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperse(lean_object* v_00_u03b1_2744_, lean_object* v_sep_2745_, lean_object* v_x_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_List_intersperse___redArg(v_sep_2745_, v_x_2746_);
return v___x_2747_;
}
}
uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(lean_object* v___x_2748_, lean_object* v_x_2749_){
_start:
{
if (lean_obj_tag(v_x_2749_) == 0)
{
uint8_t v___x_2750_; 
lean_dec_ref(v___x_2748_);
v___x_2750_ = 0;
return v___x_2750_;
}
else
{
lean_object* v_head_2751_; lean_object* v_tail_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v_head_2751_ = lean_ctor_get(v_x_2749_, 0);
lean_inc(v_head_2751_);
v_tail_2752_ = lean_ctor_get(v_x_2749_, 1);
lean_inc(v_tail_2752_);
lean_dec_ref_known(v_x_2749_, 2);
lean_inc_ref(v___x_2748_);
v___x_2753_ = lean_apply_1(v___x_2748_, v_head_2751_);
v___x_2754_ = lean_unbox(v___x_2753_);
if (v___x_2754_ == 0)
{
v_x_2749_ = v_tail_2752_;
goto _start;
}
else
{
uint8_t v___x_2756_; 
lean_dec(v_tail_2752_);
lean_dec_ref(v___x_2748_);
v___x_2756_ = lean_unbox(v___x_2753_);
return v___x_2756_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2748_ = stack[0].m_obj;
lean_object* v_x_2749_ = stack[1].m_obj;
uint8_t v_res_2757_;
v_res_2757_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2748_, v_x_2749_);
stack->m_num = v_res_2757_;
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg___boxed(lean_object* v___x_2758_, lean_object* v_x_2759_){
_start:
{
uint8_t v_res_2760_; lean_object* v_r_2761_; 
v_res_2760_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2758_, v_x_2759_);
v_r_2761_ = lean_box(v_res_2760_);
return v_r_2761_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop___redArg(lean_object* v_r_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
if (lean_obj_tag(v_a_2763_) == 0)
{
lean_object* v___x_2765_; 
lean_dec_ref(v_r_2762_);
v___x_2765_ = l_List_reverse___redArg(v_a_2764_);
return v___x_2765_;
}
else
{
lean_object* v_head_2766_; lean_object* v_tail_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2778_; 
v_head_2766_ = lean_ctor_get(v_a_2763_, 0);
v_tail_2767_ = lean_ctor_get(v_a_2763_, 1);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_a_2763_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2769_ = v_a_2763_;
v_isShared_2770_ = v_isSharedCheck_2778_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_tail_2767_);
lean_inc(v_head_2766_);
lean_dec(v_a_2763_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2778_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; uint8_t v___x_2772_; 
lean_inc_ref(v_r_2762_);
lean_inc(v_head_2766_);
v___x_2771_ = lean_apply_1(v_r_2762_, v_head_2766_);
lean_inc(v_a_2764_);
v___x_2772_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2771_, v_a_2764_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2774_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v_a_2764_);
v___x_2774_ = v___x_2769_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_head_2766_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_a_2764_);
v___x_2774_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
v_a_2763_ = v_tail_2767_;
v_a_2764_ = v___x_2774_;
goto _start;
}
}
else
{
lean_del_object(v___x_2769_);
lean_dec(v_head_2766_);
v_a_2763_ = v_tail_2767_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy_loop(lean_object* v_00_u03b1_2779_, lean_object* v_r_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_List_eraseDupsBy_loop___redArg(v_r_2780_, v_a_2781_, v_a_2782_);
return v___x_2783_;
}
}
uint8_t l_List_any___at___00List_eraseDupsBy_loop_spec__0(lean_object* v_00_u03b1_2784_, lean_object* v___x_2785_, lean_object* v_x_2786_){
_start:
{
uint8_t v___x_2787_; 
v___x_2787_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_2785_, v_x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT void l_List_any___at___00List_eraseDupsBy_loop_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2785_ = stack[1].m_obj;
lean_object* v_x_2786_ = stack[2].m_obj;
uint8_t v_res_2788_;
v_res_2788_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0(lean_box(0), v___x_2785_, v_x_2786_);
stack->m_num = v_res_2788_;
}
LEAN_EXPORT lean_object* l_List_any___at___00List_eraseDupsBy_loop_spec__0___boxed(lean_object* v_00_u03b1_2789_, lean_object* v___x_2790_, lean_object* v_x_2791_){
_start:
{
uint8_t v_res_2792_; lean_object* v_r_2793_; 
v_res_2792_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0(v_00_u03b1_2789_, v___x_2790_, v_x_2791_);
v_r_2793_ = lean_box(v_res_2792_);
return v_r_2793_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy___redArg(lean_object* v_r_2794_, lean_object* v_as_2795_){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_box(0);
v___x_2797_ = l_List_eraseDupsBy_loop___redArg(v_r_2794_, v_as_2795_, v___x_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDupsBy(lean_object* v_00_u03b1_2798_, lean_object* v_r_2799_, lean_object* v_as_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_List_eraseDupsBy___redArg(v_r_2799_, v_as_2800_);
return v___x_2801_;
}
}
uint8_t l_List_eraseDups___redArg___lam__0(lean_object* v_inst_2802_, lean_object* v_x1_2803_, lean_object* v_x2_2804_){
_start:
{
lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2805_ = lean_apply_2(v_inst_2802_, v_x1_2803_, v_x2_2804_);
v___x_2806_ = lean_unbox(v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT void l_List_eraseDups___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2802_ = stack[0].m_obj;
lean_object* v_x1_2803_ = stack[1].m_obj;
lean_object* v_x2_2804_ = stack[2].m_obj;
uint8_t v_res_2807_;
v_res_2807_ = l_List_eraseDups___redArg___lam__0(v_inst_2802_, v_x1_2803_, v_x2_2804_);
stack->m_num = v_res_2807_;
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg___lam__0___boxed(lean_object* v_inst_2808_, lean_object* v_x1_2809_, lean_object* v_x2_2810_){
_start:
{
uint8_t v_res_2811_; lean_object* v_r_2812_; 
v_res_2811_ = l_List_eraseDups___redArg___lam__0(v_inst_2808_, v_x1_2809_, v_x2_2810_);
v_r_2812_ = lean_box(v_res_2811_);
return v_r_2812_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___redArg(lean_object* v_inst_2813_, lean_object* v_as_2814_){
_start:
{
lean_object* v___f_2815_; lean_object* v___x_2816_; 
v___f_2815_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2815_, 0, v_inst_2813_);
v___x_2816_ = l_List_eraseDupsBy___redArg(v___f_2815_, v_as_2814_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object* v_00_u03b1_2817_, lean_object* v_inst_2818_, lean_object* v_as_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_List_eraseDups___redArg(v_inst_2818_, v_as_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop___redArg(lean_object* v_r_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
if (lean_obj_tag(v_a_2823_) == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec_ref(v_r_2821_);
v___x_2825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2825_, 0, v_a_2822_);
lean_ctor_set(v___x_2825_, 1, v_a_2824_);
v___x_2826_ = l_List_reverse___redArg(v___x_2825_);
return v___x_2826_;
}
else
{
lean_object* v_head_2827_; lean_object* v_tail_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2839_; 
v_head_2827_ = lean_ctor_get(v_a_2823_, 0);
v_tail_2828_ = lean_ctor_get(v_a_2823_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_a_2823_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2830_ = v_a_2823_;
v_isShared_2831_ = v_isSharedCheck_2839_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_tail_2828_);
lean_inc(v_head_2827_);
lean_dec(v_a_2823_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2839_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; uint8_t v___x_2833_; 
lean_inc_ref(v_r_2821_);
lean_inc(v_head_2827_);
lean_inc(v_a_2822_);
v___x_2832_ = lean_apply_2(v_r_2821_, v_a_2822_, v_head_2827_);
v___x_2833_ = lean_unbox(v___x_2832_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2835_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 1, v_a_2824_);
lean_ctor_set(v___x_2830_, 0, v_a_2822_);
v___x_2835_ = v___x_2830_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2822_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_a_2824_);
v___x_2835_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
v_a_2822_ = v_head_2827_;
v_a_2823_ = v_tail_2828_;
v_a_2824_ = v___x_2835_;
goto _start;
}
}
else
{
lean_del_object(v___x_2830_);
lean_dec(v_head_2827_);
v_a_2823_ = v_tail_2828_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy_loop(lean_object* v_00_u03b1_2840_, lean_object* v_r_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l_List_eraseRepsBy_loop___redArg(v_r_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy___redArg(lean_object* v_r_2846_, lean_object* v_x_2847_){
_start:
{
if (lean_obj_tag(v_x_2847_) == 0)
{
lean_dec_ref(v_r_2846_);
return v_x_2847_;
}
else
{
lean_object* v_head_2848_; lean_object* v_tail_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v_head_2848_ = lean_ctor_get(v_x_2847_, 0);
lean_inc(v_head_2848_);
v_tail_2849_ = lean_ctor_get(v_x_2847_, 1);
lean_inc(v_tail_2849_);
lean_dec_ref_known(v_x_2847_, 2);
v___x_2850_ = lean_box(0);
v___x_2851_ = l_List_eraseRepsBy_loop___redArg(v_r_2846_, v_head_2848_, v_tail_2849_, v___x_2850_);
return v___x_2851_;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseRepsBy(lean_object* v_00_u03b1_2852_, lean_object* v_r_2853_, lean_object* v_x_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_List_eraseRepsBy___redArg(v_r_2853_, v_x_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___redArg(lean_object* v_inst_2856_, lean_object* v_as_2857_){
_start:
{
lean_object* v___f_2858_; lean_object* v___x_2859_; 
v___f_2858_ = lean_alloc_closure((void*)(l_List_eraseDups___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2858_, 0, v_inst_2856_);
v___x_2859_ = l_List_eraseRepsBy___redArg(v___f_2858_, v_as_2857_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object* v_00_u03b1_2860_, lean_object* v_inst_2861_, lean_object* v_as_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_List_eraseReps___redArg(v_inst_2861_, v_as_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___redArg(lean_object* v_p_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
if (lean_obj_tag(v_a_2865_) == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec_ref(v_p_2864_);
v___x_2867_ = l_List_reverse___redArg(v_a_2866_);
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
lean_ctor_set(v___x_2868_, 1, v_a_2865_);
return v___x_2868_;
}
else
{
lean_object* v_head_2869_; lean_object* v_tail_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v_head_2869_ = lean_ctor_get(v_a_2865_, 0);
v_tail_2870_ = lean_ctor_get(v_a_2865_, 1);
lean_inc_ref(v_p_2864_);
lean_inc(v_head_2869_);
v___x_2871_ = lean_apply_1(v_p_2864_, v_head_2869_);
v___x_2872_ = lean_unbox(v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_dec_ref(v_p_2864_);
v___x_2873_ = l_List_reverse___redArg(v_a_2866_);
v___x_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
lean_ctor_set(v___x_2874_, 1, v_a_2865_);
return v___x_2874_;
}
else
{
lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2882_; 
lean_inc(v_tail_2870_);
lean_inc(v_head_2869_);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_a_2865_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; lean_object* v_unused_2884_; 
v_unused_2883_ = lean_ctor_get(v_a_2865_, 1);
lean_dec(v_unused_2883_);
v_unused_2884_ = lean_ctor_get(v_a_2865_, 0);
lean_dec(v_unused_2884_);
v___x_2876_ = v_a_2865_;
v_isShared_2877_ = v_isSharedCheck_2882_;
goto v_resetjp_2875_;
}
else
{
lean_dec(v_a_2865_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2882_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 1, v_a_2866_);
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_head_2869_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_a_2866_);
v___x_2879_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
v_a_2865_ = v_tail_2870_;
v_a_2866_ = v___x_2879_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop(lean_object* v_00_u03b1_2885_, lean_object* v_p_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_List_span_loop___redArg(v_p_2886_, v_a_2887_, v_a_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_List_span___redArg(lean_object* v_p_2890_, lean_object* v_as_2891_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_box(0);
v___x_2893_ = l_List_span_loop___redArg(v_p_2890_, v_as_2891_, v___x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_List_span(lean_object* v_00_u03b1_2894_, lean_object* v_p_2895_, lean_object* v_as_2896_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_box(0);
v___x_2898_ = l_List_span_loop___redArg(v_p_2895_, v_as_2896_, v___x_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___redArg(lean_object* v_R_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
if (lean_obj_tag(v_a_2900_) == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec_ref(v_R_2899_);
v___x_2904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2904_, 0, v_a_2901_);
lean_ctor_set(v___x_2904_, 1, v_a_2902_);
v___x_2905_ = l_List_reverse___redArg(v___x_2904_);
v___x_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
lean_ctor_set(v___x_2906_, 1, v_a_2903_);
v___x_2907_ = l_List_reverse___redArg(v___x_2906_);
return v___x_2907_;
}
else
{
lean_object* v_head_2908_; lean_object* v_tail_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2926_; 
v_head_2908_ = lean_ctor_get(v_a_2900_, 0);
v_tail_2909_ = lean_ctor_get(v_a_2900_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2900_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2911_ = v_a_2900_;
v_isShared_2912_ = v_isSharedCheck_2926_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_tail_2909_);
lean_inc(v_head_2908_);
lean_dec(v_a_2900_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2926_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2913_; uint8_t v___x_2914_; 
lean_inc_ref(v_R_2899_);
lean_inc(v_head_2908_);
lean_inc(v_a_2901_);
v___x_2913_ = lean_apply_2(v_R_2899_, v_a_2901_, v_head_2908_);
v___x_2914_ = lean_unbox(v___x_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = lean_box(0);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v_a_2902_);
lean_ctor_set(v___x_2911_, 0, v_a_2901_);
v___x_2917_ = v___x_2911_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2901_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_a_2902_);
v___x_2917_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = l_List_reverse___redArg(v___x_2917_);
v___x_2919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
lean_ctor_set(v___x_2919_, 1, v_a_2903_);
v_a_2900_ = v_tail_2909_;
v_a_2901_ = v_head_2908_;
v_a_2902_ = v___x_2915_;
v_a_2903_ = v___x_2919_;
goto _start;
}
}
else
{
lean_object* v___x_2923_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v_a_2902_);
lean_ctor_set(v___x_2911_, 0, v_a_2901_);
v___x_2923_ = v___x_2911_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2901_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_a_2902_);
v___x_2923_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
v_a_2900_ = v_tail_2909_;
v_a_2901_ = v_head_2908_;
v_a_2902_ = v___x_2923_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop(lean_object* v_00_u03b1_2927_, lean_object* v_R_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_List_splitBy_loop___redArg(v_R_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___redArg(lean_object* v_R_2934_, lean_object* v_x_2935_){
_start:
{
if (lean_obj_tag(v_x_2935_) == 0)
{
lean_object* v___x_2936_; 
lean_dec_ref(v_R_2934_);
v___x_2936_ = lean_box(0);
return v___x_2936_;
}
else
{
lean_object* v_head_2937_; lean_object* v_tail_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_head_2937_ = lean_ctor_get(v_x_2935_, 0);
lean_inc(v_head_2937_);
v_tail_2938_ = lean_ctor_get(v_x_2935_, 1);
lean_inc(v_tail_2938_);
lean_dec_ref_known(v_x_2935_, 2);
v___x_2939_ = lean_box(0);
v___x_2940_ = l_List_splitBy_loop___redArg(v_R_2934_, v_tail_2938_, v_head_2937_, v___x_2939_, v___x_2939_);
return v___x_2940_;
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy(lean_object* v_00_u03b1_2941_, lean_object* v_R_2942_, lean_object* v_x_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_List_splitBy___redArg(v_R_2942_, v_x_2943_);
return v___x_2944_;
}
}
uint8_t l_List_removeAll___redArg___lam__0(lean_object* v_inst_2945_, lean_object* v_ys_2946_, lean_object* v_x_2947_){
_start:
{
uint8_t v___x_2948_; 
v___x_2948_ = l_List_elem___redArg(v_inst_2945_, v_x_2947_, v_ys_2946_);
if (v___x_2948_ == 0)
{
uint8_t v___x_2949_; 
v___x_2949_ = 1;
return v___x_2949_;
}
else
{
uint8_t v___x_2950_; 
v___x_2950_ = 0;
return v___x_2950_;
}
}
}
LEAN_EXPORT void l_List_removeAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2945_ = stack[0].m_obj;
lean_object* v_ys_2946_ = stack[1].m_obj;
lean_object* v_x_2947_ = stack[2].m_obj;
uint8_t v_res_2951_;
v_res_2951_ = l_List_removeAll___redArg___lam__0(v_inst_2945_, v_ys_2946_, v_x_2947_);
stack->m_num = v_res_2951_;
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg___lam__0___boxed(lean_object* v_inst_2952_, lean_object* v_ys_2953_, lean_object* v_x_2954_){
_start:
{
uint8_t v_res_2955_; lean_object* v_r_2956_; 
v_res_2955_ = l_List_removeAll___redArg___lam__0(v_inst_2952_, v_ys_2953_, v_x_2954_);
v_r_2956_ = lean_box(v_res_2955_);
return v_r_2956_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___redArg(lean_object* v_inst_2957_, lean_object* v_xs_2958_, lean_object* v_ys_2959_){
_start:
{
lean_object* v___f_2960_; lean_object* v___x_2961_; 
v___f_2960_ = lean_alloc_closure((void*)(l_List_removeAll___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2960_, 0, v_inst_2957_);
lean_closure_set(v___f_2960_, 1, v_ys_2959_);
v___x_2961_ = l_List_filter___redArg(v___f_2960_, v_xs_2958_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll(lean_object* v_00_u03b1_2962_, lean_object* v_inst_2963_, lean_object* v_xs_2964_, lean_object* v_ys_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_List_removeAll___redArg(v_inst_2963_, v_xs_2964_, v_ys_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___redArg(lean_object* v_f_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
if (lean_obj_tag(v_a_2968_) == 0)
{
lean_object* v___x_2970_; 
lean_dec(v_f_2967_);
v___x_2970_ = l_List_reverse___redArg(v_a_2969_);
return v___x_2970_;
}
else
{
lean_object* v_head_2971_; lean_object* v_tail_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2981_; 
v_head_2971_ = lean_ctor_get(v_a_2968_, 0);
v_tail_2972_ = lean_ctor_get(v_a_2968_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_a_2968_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2974_ = v_a_2968_;
v_isShared_2975_ = v_isSharedCheck_2981_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_tail_2972_);
lean_inc(v_head_2971_);
lean_dec(v_a_2968_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2981_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
lean_inc(v_f_2967_);
v___x_2976_ = lean_apply_1(v_f_2967_, v_head_2971_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 1, v_a_2969_);
lean_ctor_set(v___x_2974_, 0, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2976_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_a_2969_);
v___x_2978_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
v_a_2968_ = v_tail_2972_;
v_a_2969_ = v___x_2978_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object* v_00_u03b1_2982_, lean_object* v_00_u03b2_2983_, lean_object* v_f_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_List_mapTR_loop___redArg(v_f_2984_, v_a_2985_, v_a_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR___redArg(lean_object* v_f_2988_, lean_object* v_as_2989_){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_box(0);
v___x_2991_ = l_List_mapTR_loop___redArg(v_f_2988_, v_as_2989_, v___x_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR(lean_object* v_00_u03b1_2992_, lean_object* v_00_u03b2_2993_, lean_object* v_f_2994_, lean_object* v_as_2995_){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_box(0);
v___x_2997_ = l_List_mapTR_loop___redArg(v_f_2994_, v_as_2995_, v___x_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___redArg(lean_object* v_p_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
if (lean_obj_tag(v_a_2999_) == 0)
{
lean_object* v___x_3001_; 
lean_dec_ref(v_p_2998_);
v___x_3001_ = l_List_reverse___redArg(v_a_3000_);
return v___x_3001_;
}
else
{
lean_object* v_head_3002_; lean_object* v_tail_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3014_; 
v_head_3002_ = lean_ctor_get(v_a_2999_, 0);
v_tail_3003_ = lean_ctor_get(v_a_2999_, 1);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_a_2999_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3005_ = v_a_2999_;
v_isShared_3006_ = v_isSharedCheck_3014_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_tail_3003_);
lean_inc(v_head_3002_);
lean_dec(v_a_2999_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3014_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; uint8_t v___x_3008_; 
lean_inc_ref(v_p_2998_);
lean_inc(v_head_3002_);
v___x_3007_ = lean_apply_1(v_p_2998_, v_head_3002_);
v___x_3008_ = lean_unbox(v___x_3007_);
if (v___x_3008_ == 0)
{
lean_del_object(v___x_3005_);
lean_dec(v_head_3002_);
v_a_2999_ = v_tail_3003_;
goto _start;
}
else
{
lean_object* v___x_3011_; 
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 1, v_a_3000_);
v___x_3011_ = v___x_3005_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_head_3002_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_a_3000_);
v___x_3011_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
v_a_2999_ = v_tail_3003_;
v_a_3000_ = v___x_3011_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object* v_00_u03b1_3015_, lean_object* v_p_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_List_filterTR_loop___redArg(v_p_3016_, v_a_3017_, v_a_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR___redArg(lean_object* v_p_3020_, lean_object* v_as_3021_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_box(0);
v___x_3023_ = l_List_filterTR_loop___redArg(v_p_3020_, v_as_3021_, v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR(lean_object* v_00_u03b1_3024_, lean_object* v_p_3025_, lean_object* v_as_3026_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_box(0);
v___x_3028_ = l_List_filterTR_loop___redArg(v_p_3025_, v_as_3026_, v___x_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop___redArg(lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_zero_3032_; uint8_t v_isZero_3033_; 
v_zero_3032_ = lean_unsigned_to_nat(0u);
v_isZero_3033_ = lean_nat_dec_eq(v_a_3030_, v_zero_3032_);
if (v_isZero_3033_ == 1)
{
lean_dec(v_a_3030_);
lean_dec(v_a_3029_);
return v_a_3031_;
}
else
{
lean_object* v_one_3034_; lean_object* v_n_3035_; lean_object* v___x_3036_; 
v_one_3034_ = lean_unsigned_to_nat(1u);
v_n_3035_ = lean_nat_sub(v_a_3030_, v_one_3034_);
lean_dec(v_a_3030_);
lean_inc(v_a_3029_);
v___x_3036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3036_, 0, v_a_3029_);
lean_ctor_set(v___x_3036_, 1, v_a_3031_);
v_a_3030_ = v_n_3035_;
v_a_3031_ = v___x_3036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object* v_00_u03b1_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_List_replicateTR_loop___redArg(v_a_3039_, v_a_3040_, v_a_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR___redArg(lean_object* v_n_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = lean_box(0);
v___x_3046_ = l_List_replicateTR_loop___redArg(v_a_3044_, v_n_3043_, v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object* v_00_u03b1_3047_, lean_object* v_n_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_List_replicateTR___redArg(v_n_3048_, v_a_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg(lean_object* v_n_3051_, lean_object* v_a_3052_, lean_object* v_l_3053_){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = l_List_lengthTR___redArg(v_l_3053_);
v___x_3055_ = lean_nat_sub(v_n_3051_, v___x_3054_);
lean_dec(v___x_3054_);
v___x_3056_ = l_List_replicateTR_loop___redArg(v_a_3052_, v___x_3055_, v_l_3053_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___redArg___boxed(lean_object* v_n_3057_, lean_object* v_a_3058_, lean_object* v_l_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_List_leftpadTR___redArg(v_n_3057_, v_a_3058_, v_l_3059_);
lean_dec(v_n_3057_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object* v_00_u03b1_3061_, lean_object* v_n_3062_, lean_object* v_a_3063_, lean_object* v_l_3064_){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = l_List_lengthTR___redArg(v_l_3064_);
v___x_3066_ = lean_nat_sub(v_n_3062_, v___x_3065_);
lean_dec(v___x_3065_);
v___x_3067_ = l_List_replicateTR_loop___redArg(v_a_3063_, v___x_3066_, v_l_3064_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___boxed(lean_object* v_00_u03b1_3068_, lean_object* v_n_3069_, lean_object* v_a_3070_, lean_object* v_l_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_List_leftpadTR(v_00_u03b1_3068_, v_n_3069_, v_a_3070_, v_l_3071_);
lean_dec(v_n_3069_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg(lean_object* v_init_3073_, lean_object* v_x_3074_){
_start:
{
if (lean_obj_tag(v_x_3074_) == 0)
{
lean_inc_ref(v_init_3073_);
return v_init_3073_;
}
else
{
lean_object* v_head_3075_; lean_object* v_tail_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3102_; 
v_head_3075_ = lean_ctor_get(v_x_3074_, 0);
v_tail_3076_ = lean_ctor_get(v_x_3074_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_x_3074_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3078_ = v_x_3074_;
v_isShared_3079_ = v_isSharedCheck_3102_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_tail_3076_);
lean_inc(v_head_3075_);
lean_dec(v_x_3074_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3102_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v_fst_3080_; lean_object* v_snd_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3101_; 
v_fst_3080_ = lean_ctor_get(v_head_3075_, 0);
v_snd_3081_ = lean_ctor_get(v_head_3075_, 1);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_head_3075_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3083_ = v_head_3075_;
v_isShared_3084_ = v_isSharedCheck_3101_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_snd_3081_);
lean_inc(v_fst_3080_);
lean_dec(v_head_3075_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3101_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; lean_object* v_fst_3086_; lean_object* v_snd_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3100_; 
v___x_3085_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3073_, v_tail_3076_);
v_fst_3086_ = lean_ctor_get(v___x_3085_, 0);
v_snd_3087_ = lean_ctor_get(v___x_3085_, 1);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3089_ = v___x_3085_;
v_isShared_3090_ = v_isSharedCheck_3100_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_snd_3087_);
lean_inc(v_fst_3086_);
lean_dec(v___x_3085_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3100_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v_fst_3086_);
lean_ctor_set(v___x_3078_, 0, v_fst_3080_);
v___x_3092_ = v___x_3078_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_fst_3080_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_fst_3086_);
v___x_3092_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3094_; 
if (v_isShared_3084_ == 0)
{
lean_ctor_set_tag(v___x_3083_, 1);
lean_ctor_set(v___x_3083_, 1, v_snd_3087_);
lean_ctor_set(v___x_3083_, 0, v_snd_3081_);
v___x_3094_ = v___x_3083_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_snd_3081_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_snd_3087_);
v___x_3094_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3096_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 1, v___x_3094_);
lean_ctor_set(v___x_3089_, 0, v___x_3092_);
v___x_3096_ = v___x_3089_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___redArg___boxed(lean_object* v_init_3103_, lean_object* v_x_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3103_, v_x_3104_);
lean_dec_ref(v_init_3103_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object* v_l_3106_){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l_List_partition___redArg___closed__0));
v___x_3108_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v___x_3107_, v_l_3106_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object* v_00_u03b1_3109_, lean_object* v_00_u03b2_3110_, lean_object* v_l_3111_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l_List_unzipTR___redArg(v_l_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0(lean_object* v_00_u03b1_3113_, lean_object* v_00_u03b2_3114_, lean_object* v_init_3115_, lean_object* v_x_3116_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_3115_, v_x_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_unzipTR_spec__0___boxed(lean_object* v_00_u03b1_3118_, lean_object* v_00_u03b2_3119_, lean_object* v_init_3120_, lean_object* v_x_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_List_foldr___at___00List_unzipTR_spec__0(v_00_u03b1_3118_, v_00_u03b2_3119_, v_init_3120_, v_x_3121_);
lean_dec_ref(v_init_3120_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object* v_step_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v_zero_3127_; uint8_t v_isZero_3128_; 
v_zero_3127_ = lean_unsigned_to_nat(0u);
v_isZero_3128_ = lean_nat_dec_eq(v_a_3124_, v_zero_3127_);
if (v_isZero_3128_ == 1)
{
lean_dec(v_a_3125_);
lean_dec(v_a_3124_);
return v_a_3126_;
}
else
{
lean_object* v_one_3129_; lean_object* v_n_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_one_3129_ = lean_unsigned_to_nat(1u);
v_n_3130_ = lean_nat_sub(v_a_3124_, v_one_3129_);
lean_dec(v_a_3124_);
v___x_3131_ = lean_nat_sub(v_a_3125_, v_step_3123_);
lean_dec(v_a_3125_);
lean_inc(v___x_3131_);
v___x_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v_a_3126_);
v_a_3124_ = v_n_3130_;
v_a_3125_ = v___x_3131_;
v_a_3126_ = v___x_3132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object* v_step_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_List_range_x27TR_go(v_step_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec(v_step_3134_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object* v_s_3139_, lean_object* v_n_3140_, lean_object* v_step_3141_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3142_ = lean_nat_mul(v_step_3141_, v_n_3140_);
v___x_3143_ = lean_nat_add(v_s_3139_, v___x_3142_);
lean_dec(v___x_3142_);
v___x_3144_ = lean_box(0);
v___x_3145_ = l_List_range_x27TR_go(v_step_3141_, v_n_3140_, v___x_3143_, v___x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object* v_s_3146_, lean_object* v_n_3147_, lean_object* v_step_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l_List_range_x27TR(v_s_3146_, v_n_3147_, v_step_3148_);
lean_dec(v_step_3148_);
lean_dec(v_s_3146_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg(lean_object* v_sep_3150_, lean_object* v_init_3151_, lean_object* v_x_3152_){
_start:
{
if (lean_obj_tag(v_x_3152_) == 0)
{
lean_dec(v_sep_3150_);
lean_inc(v_init_3151_);
return v_init_3151_;
}
else
{
lean_object* v_head_3153_; lean_object* v_tail_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3163_; 
v_head_3153_ = lean_ctor_get(v_x_3152_, 0);
v_tail_3154_ = lean_ctor_get(v_x_3152_, 1);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_x_3152_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3156_ = v_x_3152_;
v_isShared_3157_ = v_isSharedCheck_3163_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_tail_3154_);
lean_inc(v_head_3153_);
lean_dec(v_x_3152_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3163_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3158_; lean_object* v___x_3160_; 
lean_inc(v_sep_3150_);
v___x_3158_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3150_, v_init_3151_, v_tail_3154_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 1, v___x_3158_);
v___x_3160_ = v___x_3156_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_head_3153_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v___x_3158_);
v___x_3160_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3161_, 0, v_sep_3150_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
return v___x_3161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(lean_object* v_sep_3164_, lean_object* v_init_3165_, lean_object* v_x_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3164_, v_init_3165_, v_x_3166_);
lean_dec(v_init_3165_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object* v_sep_3168_, lean_object* v_x_3169_){
_start:
{
if (lean_obj_tag(v_x_3169_) == 0)
{
lean_dec(v_sep_3168_);
return v_x_3169_;
}
else
{
lean_object* v_tail_3170_; 
v_tail_3170_ = lean_ctor_get(v_x_3169_, 1);
lean_inc(v_tail_3170_);
if (lean_obj_tag(v_tail_3170_) == 0)
{
lean_dec(v_sep_3168_);
return v_x_3169_;
}
else
{
lean_object* v_head_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3190_; 
v_head_3171_ = lean_ctor_get(v_x_3169_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_x_3169_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v_x_3169_, 1);
lean_dec(v_unused_3191_);
v___x_3173_ = v_x_3169_;
v_isShared_3174_ = v_isSharedCheck_3190_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_head_3171_);
lean_dec(v_x_3169_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3190_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v_head_3175_; lean_object* v_tail_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3189_; 
v_head_3175_ = lean_ctor_get(v_tail_3170_, 0);
v_tail_3176_ = lean_ctor_get(v_tail_3170_, 1);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_tail_3170_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3178_ = v_tail_3170_;
v_isShared_3179_ = v_isSharedCheck_3189_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_tail_3176_);
lean_inc(v_head_3175_);
lean_dec(v_tail_3170_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3189_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3183_; 
v___x_3180_ = lean_box(0);
lean_inc(v_sep_3168_);
v___x_3181_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3168_, v___x_3180_, v_tail_3176_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 1, v___x_3181_);
v___x_3183_ = v___x_3178_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_head_3175_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3185_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 1, v___x_3183_);
lean_ctor_set(v___x_3173_, 0, v_sep_3168_);
v___x_3185_ = v___x_3173_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_sep_3168_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3186_; 
v___x_3186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3186_, 0, v_head_3171_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
return v___x_3186_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object* v_00_u03b1_3192_, lean_object* v_sep_3193_, lean_object* v_x_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_List_intersperseTR___redArg(v_sep_3193_, v_x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0(lean_object* v_00_u03b1_3196_, lean_object* v_sep_3197_, lean_object* v_init_3198_, lean_object* v_x_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(v_sep_3197_, v_init_3198_, v_x_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00List_intersperseTR_spec__0___boxed(lean_object* v_00_u03b1_3201_, lean_object* v_sep_3202_, lean_object* v_init_3203_, lean_object* v_x_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_List_foldr___at___00List_intersperseTR_spec__0(v_00_u03b1_3201_, v_sep_3202_, v_init_3203_, v_x_3204_);
lean_dec(v_init_3203_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(lean_object* v_x_3206_, lean_object* v_h__1_3207_, lean_object* v_h__2_3208_, lean_object* v_h__3_3209_){
_start:
{
if (lean_obj_tag(v_x_3206_) == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec(v_h__3_3209_);
lean_dec(v_h__2_3208_);
v___x_3210_ = lean_box(0);
v___x_3211_ = lean_apply_1(v_h__1_3207_, v___x_3210_);
return v___x_3211_;
}
else
{
lean_object* v_tail_3212_; 
lean_dec(v_h__1_3207_);
v_tail_3212_ = lean_ctor_get(v_x_3206_, 1);
if (lean_obj_tag(v_tail_3212_) == 0)
{
lean_object* v_head_3213_; lean_object* v___x_3214_; 
lean_dec(v_h__3_3209_);
v_head_3213_ = lean_ctor_get(v_x_3206_, 0);
lean_inc(v_head_3213_);
lean_dec_ref_known(v_x_3206_, 2);
v___x_3214_ = lean_apply_1(v_h__2_3208_, v_head_3213_);
return v___x_3214_;
}
else
{
lean_object* v_head_3215_; lean_object* v_head_3216_; lean_object* v_tail_3217_; lean_object* v___x_3218_; 
lean_inc_ref(v_tail_3212_);
lean_dec(v_h__2_3208_);
v_head_3215_ = lean_ctor_get(v_x_3206_, 0);
lean_inc(v_head_3215_);
lean_dec_ref_known(v_x_3206_, 2);
v_head_3216_ = lean_ctor_get(v_tail_3212_, 0);
lean_inc(v_head_3216_);
v_tail_3217_ = lean_ctor_get(v_tail_3212_, 1);
lean_inc(v_tail_3217_);
lean_dec_ref_known(v_tail_3212_, 2);
v___x_3218_ = lean_apply_3(v_h__3_3209_, v_head_3215_, v_head_3216_, v_tail_3217_);
return v___x_3218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object* v_00_u03b1_3219_, lean_object* v_motive_3220_, lean_object* v_x_3221_, lean_object* v_h__1_3222_, lean_object* v_h__2_3223_, lean_object* v_h__3_3224_){
_start:
{
if (lean_obj_tag(v_x_3221_) == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_dec(v_h__3_3224_);
lean_dec(v_h__2_3223_);
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_apply_1(v_h__1_3222_, v___x_3225_);
return v___x_3226_;
}
else
{
lean_object* v_tail_3227_; 
lean_dec(v_h__1_3222_);
v_tail_3227_ = lean_ctor_get(v_x_3221_, 1);
if (lean_obj_tag(v_tail_3227_) == 0)
{
lean_object* v_head_3228_; lean_object* v___x_3229_; 
lean_dec(v_h__3_3224_);
v_head_3228_ = lean_ctor_get(v_x_3221_, 0);
lean_inc(v_head_3228_);
lean_dec_ref_known(v_x_3221_, 2);
v___x_3229_ = lean_apply_1(v_h__2_3223_, v_head_3228_);
return v___x_3229_;
}
else
{
lean_object* v_head_3230_; lean_object* v_head_3231_; lean_object* v_tail_3232_; lean_object* v___x_3233_; 
lean_inc_ref(v_tail_3227_);
lean_dec(v_h__2_3223_);
v_head_3230_ = lean_ctor_get(v_x_3221_, 0);
lean_inc(v_head_3230_);
lean_dec_ref_known(v_x_3221_, 2);
v_head_3231_ = lean_ctor_get(v_tail_3227_, 0);
lean_inc(v_head_3231_);
v_tail_3232_ = lean_ctor_get(v_tail_3227_, 1);
lean_inc(v_tail_3232_);
lean_dec_ref_known(v_tail_3227_, 2);
v___x_3233_ = lean_apply_3(v_h__3_3224_, v_head_3230_, v_head_3231_, v_tail_3232_);
return v___x_3233_;
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
