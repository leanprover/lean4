// Lean compiler output
// Module: Init.TacticsExtra
// Imports: public meta import Init.Meta public import Init.Tactics import Init.Data.Array.Basic
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
extern lean_object* l_Lean_Parser_Tactic_location;
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_rwRuleSeq;
extern lean_object* l_Lean_Parser_Tactic_optConfig;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__3 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__3_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__5 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__5_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__8 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__8_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__10 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__10_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__12 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__12_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "withAnnotateState"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__14 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__14_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(27, 100, 151, 108, 10, 177, 75, 150)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "with_annotate_state"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__16 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__16_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(244, 42, 145, 170, 145, 147, 228, 105)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18_value;
static lean_once_cell_t l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__20 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__20_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "case"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(216, 244, 120, 128, 139, 198, 139, 51)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__26 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__26_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__30 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__30_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__31 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__31_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__31_value),LEAN_SCALAR_PTR_LITERAL(138, 85, 70, 0, 206, 11, 146, 59)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32_value;
static const lean_array_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33_value;
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__1 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__1_value;
static lean_once_cell_t l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(175, 67, 188, 228, 198, 126, 180, 88)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__3 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0_value;
static lean_once_cell_t l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 129, 35, 203, 24, 252, 22, 100)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value;
static const lean_closure_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value;
static const lean_closure_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value)} };
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2_value;
static const lean_closure_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value)} };
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__3 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__3_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4_value),LEAN_SCALAR_PTR_LITERAL(68, 209, 138, 110, 159, 245, 114, 22)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__6 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__6_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openSimple"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__7 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__7_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__7_value),LEAN_SCALAR_PTR_LITERAL(171, 238, 134, 92, 162, 110, 43, 67)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9_value;
static lean_once_cell_t l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11_value)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__12 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__12_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__13 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__13_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__14 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__14_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "refine"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value_aux_2),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15_value),LEAN_SCALAR_PTR_LITERAL(49, 130, 130, 160, 131, 48, 178, 245)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16_value;
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17_value;
static const lean_array_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18_value;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13_value),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18_value)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19_value;
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDepIfThenElse"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 94, 17, 11, 145, 108, 236, 173)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tacDepIfThenElse"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 194, 228, 123, 20, 164, 36, 28)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacIfThenElse"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 110, 54, 113, 164, 84, 110, 206)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticIterate____"};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 47, 56, 55, 14, 165, 150, 141)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "iterate"};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__11_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__16_value),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__18_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__18_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__19_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__17_value),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__19_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__20_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticIterate_________00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticIterate_________00__closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__21_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_tacticIterate________ = (const lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__21_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tacticRw_mod_cast___"};
static const lean_object* l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 49, 244, 227, 69, 23, 138, 35)}};
static const lean_object* l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rw_mod_cast"};
static const lean_object* l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticRw__mod__cast______;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticNorm_cast__"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(236, 48, 221, 117, 176, 58, 9, 174)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "norm_cast"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "locationWildcard"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(134, 218, 71, 35, 220, 118, 132, 17)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rwSeq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(50, 16, 185, 246, 153, 187, 181, 153)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rw"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__17_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticExact_mod_cast_"};
static const lean_object* l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 115, 207, 153, 244, 77, 215, 161)}};
static const lean_object* l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "exact_mod_cast "};
static const lean_object* l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_tacticExact__mod__cast__ = (const lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "modCast"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 150, 13, 6, 253, 161, 172, 138)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mod_cast"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__11_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticApply_mod_cast_"};
static const lean_object* l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 137, 51, 123, 254, 235, 255, 128)}};
static const lean_object* l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "apply_mod_cast "};
static const lean_object* l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticIterate_________00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_tacticApply__mod__cast__ = (const lean_object*)&l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_0),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_1),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Array_mkArray0(lean_box(0));
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(lean_object* v_tk_79_, lean_object* v_holeOrTacticSeq_80_, lean_object* v_mkName_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4));
lean_inc(v_holeOrTacticSeq_80_);
v___x_85_ = l_Lean_Syntax_isOfKind(v_holeOrTacticSeq_80_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6));
lean_inc(v_holeOrTacticSeq_80_);
v___x_87_ = l_Lean_Syntax_isOfKind(v_holeOrTacticSeq_80_, v___x_86_);
if (v___x_87_ == 0)
{
uint8_t v___x_88_; 
v___x_88_ = l_Lean_Syntax_isMissing(v_tk_79_);
if (v___x_88_ == 0)
{
lean_object* v_macroScope_89_; lean_object* v_traceMsgs_90_; lean_object* v_expandedMacroDecls_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_169_; 
v_macroScope_89_ = lean_ctor_get(v___y_83_, 0);
v_traceMsgs_90_ = lean_ctor_get(v___y_83_, 1);
v_expandedMacroDecls_91_ = lean_ctor_get(v___y_83_, 2);
v_isSharedCheck_169_ = !lean_is_exclusive(v___y_83_);
if (v_isSharedCheck_169_ == 0)
{
v___x_93_ = v___y_83_;
v_isShared_94_ = v_isSharedCheck_169_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_expandedMacroDecls_91_);
lean_inc(v_traceMsgs_90_);
lean_inc(v_macroScope_89_);
lean_dec(v___y_83_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_169_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_methods_95_; lean_object* v_quotContext_96_; lean_object* v_currRecDepth_97_; lean_object* v_maxRecDepth_98_; lean_object* v_ref_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v_methods_95_ = lean_ctor_get(v___y_82_, 0);
v_quotContext_96_ = lean_ctor_get(v___y_82_, 1);
v_currRecDepth_97_ = lean_ctor_get(v___y_82_, 3);
v_maxRecDepth_98_ = lean_ctor_get(v___y_82_, 4);
v_ref_99_ = lean_ctor_get(v___y_82_, 5);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_add(v_macroScope_89_, v___x_100_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_101_);
v___x_103_ = v___x_93_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_traceMsgs_90_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_expandedMacroDecls_91_);
v___x_103_ = v_reuseFailAlloc_168_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_inc(v_ref_99_);
lean_inc(v_maxRecDepth_98_);
lean_inc(v_currRecDepth_97_);
lean_inc(v_quotContext_96_);
lean_inc(v_methods_95_);
v___x_104_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_104_, 0, v_methods_95_);
lean_ctor_set(v___x_104_, 1, v_quotContext_96_);
lean_ctor_set(v___x_104_, 2, v_macroScope_89_);
lean_ctor_set(v___x_104_, 3, v_currRecDepth_97_);
lean_ctor_set(v___x_104_, 4, v_maxRecDepth_98_);
lean_ctor_set(v___x_104_, 5, v_ref_99_);
v___x_105_ = lean_apply_2(v_mkName_81_, v___x_104_, v___x_103_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_158_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_a_107_ = lean_ctor_get(v___x_105_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_158_ == 0)
{
v___x_109_ = v___x_105_;
v_isShared_110_ = v_isSharedCheck_158_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_158_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v_ref_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_111_ = 1;
v___x_112_ = l_Lean_Syntax_getArg(v_a_106_, v___x_100_);
v___x_113_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
v___x_114_ = lean_box(0);
v___x_115_ = l_Lean_SourceInfo_fromRef(v___x_114_, v___x_88_);
v___x_116_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11));
v___x_117_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_118_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__15));
v___x_119_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__16));
lean_inc_n(v___x_115_, 10);
v___x_120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_115_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17));
v___x_122_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18));
v___x_123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_115_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
v___x_124_ = l_Lean_Syntax_node1(v___x_115_, v___x_122_, v___x_123_);
lean_inc(v_tk_79_);
v___x_125_ = l_Lean_Syntax_node3(v___x_115_, v___x_118_, v___x_120_, v_tk_79_, v___x_124_);
v___x_126_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
v___x_127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_127_, 0, v___x_115_);
lean_ctor_set(v___x_127_, 1, v___x_117_);
lean_ctor_set(v___x_127_, 2, v___x_126_);
v___x_128_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_129_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
v___x_130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_115_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
v___x_132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_115_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = l_Lean_Syntax_node3(v___x_115_, v___x_128_, v___x_130_, v_holeOrTacticSeq_80_, v___x_132_);
v___x_134_ = l_Lean_Syntax_node3(v___x_115_, v___x_117_, v___x_125_, v___x_127_, v___x_133_);
v___x_135_ = l_Lean_Syntax_node1(v___x_115_, v___x_116_, v___x_134_);
v___x_136_ = l_Lean_Syntax_node1(v___x_115_, v___x_113_, v___x_135_);
v_ref_137_ = l_Lean_replaceRef(v_tk_79_, v_ref_99_);
v___x_138_ = l_Lean_SourceInfo_fromRef(v_ref_137_, v___x_88_);
lean_dec(v_ref_137_);
v___x_139_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24));
v___x_140_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25));
lean_inc_n(v___x_138_, 5);
v___x_141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
v___x_142_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27));
v___x_143_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29));
v___x_144_ = l_Lean_Syntax_node1(v___x_138_, v___x_143_, v___x_112_);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_138_);
lean_ctor_set(v___x_145_, 1, v___x_117_);
lean_ctor_set(v___x_145_, 2, v___x_126_);
v___x_146_ = l_Lean_Syntax_node2(v___x_138_, v___x_142_, v___x_144_, v___x_145_);
v___x_147_ = l_Lean_Syntax_node1(v___x_138_, v___x_117_, v___x_146_);
v___x_148_ = l_Lean_SourceInfo_fromRef(v_tk_79_, v___x_111_);
lean_dec(v_tk_79_);
v___x_149_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__30));
v___x_150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = l_Lean_Syntax_node4(v___x_138_, v___x_140_, v___x_141_, v___x_147_, v___x_150_, v___x_136_);
v___x_152_ = lean_mk_empty_array_with_capacity(v___x_100_);
v___x_153_ = lean_array_push(v___x_152_, v___x_151_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_a_106_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_154_);
v___x_156_ = v___x_109_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_a_107_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
lean_object* v_a_159_; lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec(v_holeOrTacticSeq_80_);
lean_dec(v_tk_79_);
v_a_159_ = lean_ctor_get(v___x_105_, 0);
v_a_160_ = lean_ctor_get(v___x_105_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_105_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_inc(v_a_159_);
lean_dec(v___x_105_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_159_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
}
else
{
lean_object* v_ref_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec_ref(v_mkName_81_);
lean_dec(v_holeOrTacticSeq_80_);
lean_dec(v_tk_79_);
v_ref_170_ = lean_ctor_get(v___y_82_, 5);
v___x_171_ = l_Lean_SourceInfo_fromRef(v_ref_170_, v___x_87_);
v___x_172_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__31));
v___x_173_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__32));
lean_inc(v___x_171_);
v___x_174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_171_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
v___x_175_ = l_Lean_Syntax_node1(v___x_171_, v___x_173_, v___x_174_);
v___x_176_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33));
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_175_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___y_83_);
return v___x_178_;
}
}
else
{
lean_object* v___x_179_; 
lean_dec(v_holeOrTacticSeq_80_);
lean_dec(v_tk_79_);
lean_inc_ref(v___y_82_);
v___x_179_ = lean_apply_2(v_mkName_81_, v___y_82_, v___y_83_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_190_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_a_181_ = lean_ctor_get(v___x_179_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_190_ == 0)
{
v___x_183_ = v___x_179_;
v_isShared_184_ = v_isSharedCheck_190_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_190_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_185_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33));
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_a_180_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_186_);
v___x_188_ = v___x_183_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_a_181_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
lean_object* v_a_191_; lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_191_ = lean_ctor_get(v___x_179_, 0);
v_a_192_ = lean_ctor_get(v___x_179_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_179_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_inc(v_a_191_);
lean_dec(v___x_179_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_191_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec_ref(v_mkName_81_);
lean_dec(v_tk_79_);
v___x_200_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__33));
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v_holeOrTacticSeq_80_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___y_83_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___boxed(lean_object* v_tk_203_, lean_object* v_holeOrTacticSeq_204_, lean_object* v_mkName_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(v_tk_203_, v_holeOrTacticSeq_204_, v_mkName_205_, v___y_206_, v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1(lean_object* v_ctx_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_ref_212_; lean_object* v___x_213_; 
v_ref_212_ = lean_ctor_get(v_ctx_209_, 5);
lean_inc(v_ref_212_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v_ref_212_);
lean_ctor_set(v___x_213_, 1, v___y_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1___boxed(lean_object* v_ctx_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1(v_ctx_214_, v___y_215_, v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec_ref(v_ctx_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2(lean_object* v_____do__lift_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = 0;
v___x_222_ = l_Lean_SourceInfo_fromRef(v_____do__lift_218_, v___x_221_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___y_220_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2___boxed(lean_object* v_____do__lift_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2(v_____do__lift_224_, v___y_225_, v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v_____do__lift_224_);
return v_res_227_;
}
}
static lean_object* _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__1));
v___x_231_ = l_String_toRawSubstring_x27(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3(lean_object* v___f_234_, lean_object* v___f_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_238_; 
lean_inc_ref_n(v___y_236_, 2);
v___x_238_ = lean_apply_3(v___f_234_, v___y_236_, v___y_236_, v___y_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v_a_240_; lean_object* v___x_241_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
v_a_240_ = lean_ctor_get(v___x_238_, 1);
lean_inc(v_a_240_);
lean_dec_ref(v___x_238_);
lean_inc_ref(v___y_236_);
v___x_241_ = lean_apply_3(v___f_235_, v_a_239_, v___y_236_, v_a_240_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_261_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_a_243_ = lean_ctor_get(v___x_241_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_261_ == 0)
{
v___x_245_ = v___x_241_;
v_isShared_246_ = v_isSharedCheck_261_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_261_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_quotContext_247_; lean_object* v_currMacroScope_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v_quotContext_247_ = lean_ctor_get(v___y_236_, 1);
v_currMacroScope_248_ = lean_ctor_get(v___y_236_, 2);
v___x_249_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4));
v___x_250_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0));
lean_inc_n(v_a_242_, 2);
v___x_251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_251_, 0, v_a_242_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2);
v___x_253_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__3));
lean_inc(v_currMacroScope_248_);
lean_inc(v_quotContext_247_);
v___x_254_ = l_Lean_addMacroScope(v_quotContext_247_, v___x_253_, v_currMacroScope_248_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_256_, 0, v_a_242_);
lean_ctor_set(v___x_256_, 1, v___x_252_);
lean_ctor_set(v___x_256_, 2, v___x_254_);
lean_ctor_set(v___x_256_, 3, v___x_255_);
v___x_257_ = l_Lean_Syntax_node2(v_a_242_, v___x_249_, v___x_251_, v___x_256_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_257_);
v___x_259_ = v___x_245_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_a_243_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
lean_object* v_a_262_; lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_262_ = lean_ctor_get(v___x_241_, 0);
v_a_263_ = lean_ctor_get(v___x_241_, 1);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_241_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_inc(v_a_262_);
lean_dec(v___x_241_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_262_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec_ref(v___f_235_);
v_a_271_ = lean_ctor_get(v___x_238_, 0);
v_a_272_ = lean_ctor_get(v___x_238_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_238_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_inc(v_a_271_);
lean_dec(v___x_238_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_271_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___boxed(lean_object* v___f_280_, lean_object* v___f_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3(v___f_280_, v___f_281_, v___y_282_, v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_284_;
}
}
static lean_object* _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0));
v___x_287_ = l_String_toRawSubstring_x27(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4(lean_object* v___f_290_, lean_object* v___f_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_294_; 
lean_inc_ref_n(v___y_292_, 2);
v___x_294_ = lean_apply_3(v___f_290_, v___y_292_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v_a_296_; lean_object* v___x_297_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
v_a_296_ = lean_ctor_get(v___x_294_, 1);
lean_inc(v_a_296_);
lean_dec_ref(v___x_294_);
lean_inc_ref(v___y_292_);
v___x_297_ = lean_apply_3(v___f_291_, v_a_295_, v___y_292_, v_a_296_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_317_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_a_299_ = lean_ctor_get(v___x_297_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_317_ == 0)
{
v___x_301_ = v___x_297_;
v_isShared_302_ = v_isSharedCheck_317_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_317_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_quotContext_303_; lean_object* v_currMacroScope_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v_quotContext_303_ = lean_ctor_get(v___y_292_, 1);
v_currMacroScope_304_ = lean_ctor_get(v___y_292_, 2);
v___x_305_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4));
v___x_306_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0));
lean_inc_n(v_a_298_, 2);
v___x_307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_307_, 0, v_a_298_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1);
v___x_309_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2));
lean_inc(v_currMacroScope_304_);
lean_inc(v_quotContext_303_);
v___x_310_ = l_Lean_addMacroScope(v_quotContext_303_, v___x_309_, v_currMacroScope_304_);
v___x_311_ = lean_box(0);
v___x_312_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_312_, 0, v_a_298_);
lean_ctor_set(v___x_312_, 1, v___x_308_);
lean_ctor_set(v___x_312_, 2, v___x_310_);
lean_ctor_set(v___x_312_, 3, v___x_311_);
v___x_313_ = l_Lean_Syntax_node2(v_a_298_, v___x_305_, v___x_307_, v___x_312_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_313_);
v___x_315_ = v___x_301_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_a_299_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
else
{
lean_object* v_a_318_; lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_a_318_ = lean_ctor_get(v___x_297_, 0);
v_a_319_ = lean_ctor_get(v___x_297_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_297_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_inc(v_a_318_);
lean_dec(v___x_297_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_318_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v___f_291_);
v_a_327_ = lean_ctor_get(v___x_294_, 0);
v_a_328_ = lean_ctor_get(v___x_294_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_294_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_inc(v_a_327_);
lean_dec(v___x_294_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_327_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___boxed(lean_object* v___f_336_, lean_object* v___f_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4(v___f_336_, v___f_337_, v___y_338_, v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(size_t v_sz_341_, size_t v_i_342_, lean_object* v_bs_343_){
_start:
{
uint8_t v___x_344_; 
v___x_344_ = lean_usize_dec_lt(v_i_342_, v_sz_341_);
if (v___x_344_ == 0)
{
return v_bs_343_;
}
else
{
lean_object* v_v_345_; lean_object* v___x_346_; lean_object* v_bs_x27_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v___x_350_; 
v_v_345_ = lean_array_uget(v_bs_343_, v_i_342_);
v___x_346_ = lean_unsigned_to_nat(0u);
v_bs_x27_347_ = lean_array_uset(v_bs_343_, v_i_342_, v___x_346_);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_add(v_i_342_, v___x_348_);
v___x_350_ = lean_array_uset(v_bs_x27_347_, v_i_342_, v_v_345_);
v_i_342_ = v___x_349_;
v_bs_343_ = v___x_350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0___boxed(lean_object* v_sz_352_, lean_object* v_i_353_, lean_object* v_bs_354_){
_start:
{
size_t v_sz_boxed_355_; size_t v_i_boxed_356_; lean_object* v_res_357_; 
v_sz_boxed_355_ = lean_unbox_usize(v_sz_352_);
lean_dec(v_sz_352_);
v_i_boxed_356_ = lean_unbox_usize(v_i_353_);
lean_dec(v_i_353_);
v_res_357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(v_sz_boxed_355_, v_i_boxed_356_, v_bs_354_);
return v_res_357_;
}
}
static lean_object* _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9));
v___x_381_ = l_String_toRawSubstring_x27(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(lean_object* v_ifTk_403_, lean_object* v_thenTk_404_, lean_object* v_elseTk_405_, lean_object* v_pos_406_, lean_object* v_neg_407_, lean_object* v_mkIf_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___f_411_; lean_object* v___x_412_; 
v___f_411_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2));
v___x_412_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(v_thenTk_404_, v_pos_406_, v___f_411_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_a_414_; lean_object* v_fst_415_; lean_object* v_snd_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_507_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
v_a_414_ = lean_ctor_get(v___x_412_, 1);
lean_inc(v_a_414_);
lean_dec_ref(v___x_412_);
v_fst_415_ = lean_ctor_get(v_a_413_, 0);
v_snd_416_ = lean_ctor_get(v_a_413_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_a_413_);
if (v_isSharedCheck_507_ == 0)
{
v___x_418_ = v_a_413_;
v_isShared_419_ = v_isSharedCheck_507_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_snd_416_);
lean_inc(v_fst_415_);
lean_dec(v_a_413_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_507_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___f_420_; lean_object* v___x_421_; 
v___f_420_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__3));
v___x_421_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(v_elseTk_405_, v_neg_407_, v___f_420_, v_a_409_, v_a_414_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v_a_423_; lean_object* v_fst_424_; lean_object* v_snd_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_497_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
v_a_423_ = lean_ctor_get(v___x_421_, 1);
lean_inc(v_a_423_);
lean_dec_ref(v___x_421_);
v_fst_424_ = lean_ctor_get(v_a_422_, 0);
v_snd_425_ = lean_ctor_get(v_a_422_, 1);
v_isSharedCheck_497_ = !lean_is_exclusive(v_a_422_);
if (v_isSharedCheck_497_ == 0)
{
v___x_427_ = v_a_422_;
v_isShared_428_ = v_isSharedCheck_497_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_snd_425_);
lean_inc(v_fst_424_);
lean_dec(v_a_422_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_497_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; 
lean_inc_ref(v_a_409_);
v___x_429_ = lean_apply_4(v_mkIf_408_, v_fst_415_, v_fst_424_, v_a_409_, v_a_423_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_496_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_a_431_ = lean_ctor_get(v___x_429_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_496_ == 0)
{
v___x_433_ = v___x_429_;
v_isShared_434_ = v_isSharedCheck_496_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_496_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_quotContext_435_; lean_object* v_currMacroScope_436_; lean_object* v_ref_437_; uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v_quotContext_435_ = lean_ctor_get(v_a_409_, 1);
v_currMacroScope_436_ = lean_ctor_get(v_a_409_, 2);
v_ref_437_ = lean_ctor_get(v_a_409_, 5);
v___x_438_ = 0;
v___x_439_ = l_Lean_SourceInfo_fromRef(v_ref_437_, v___x_438_);
v___x_440_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_441_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc(v___x_439_);
if (v_isShared_428_ == 0)
{
lean_ctor_set_tag(v___x_427_, 2);
lean_ctor_set(v___x_427_, 1, v___x_441_);
lean_ctor_set(v___x_427_, 0, v___x_439_);
v___x_443_ = v___x_427_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_495_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_444_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
v___x_445_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11));
v___x_446_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_447_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4));
v___x_448_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5));
lean_inc(v___x_439_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 2);
lean_ctor_set(v___x_418_, 1, v___x_447_);
lean_ctor_set(v___x_418_, 0, v___x_439_);
v___x_450_ = v___x_418_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_447_);
v___x_450_ = v_reuseFailAlloc_494_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; size_t v_sz_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_451_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8));
v___x_452_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10);
v___x_453_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11));
lean_inc(v_currMacroScope_436_);
lean_inc(v_quotContext_435_);
v___x_454_ = l_Lean_addMacroScope(v_quotContext_435_, v___x_453_, v_currMacroScope_436_);
v___x_455_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__13));
lean_inc_n(v___x_439_, 18);
v___x_456_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_456_, 0, v___x_439_);
lean_ctor_set(v___x_456_, 1, v___x_452_);
lean_ctor_set(v___x_456_, 2, v___x_454_);
lean_ctor_set(v___x_456_, 3, v___x_455_);
v___x_457_ = l_Lean_Syntax_node1(v___x_439_, v___x_446_, v___x_456_);
v___x_458_ = l_Lean_Syntax_node1(v___x_439_, v___x_451_, v___x_457_);
v___x_459_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__14));
v___x_460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_439_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15));
v___x_462_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16));
v___x_463_ = 1;
v___x_464_ = l_Lean_SourceInfo_fromRef(v_ifTk_403_, v___x_463_);
v___x_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_461_);
v___x_466_ = l_Lean_Syntax_node2(v___x_439_, v___x_462_, v___x_465_, v_a_430_);
v___x_467_ = l_Lean_Syntax_node1(v___x_439_, v___x_446_, v___x_466_);
v___x_468_ = l_Lean_Syntax_node1(v___x_439_, v___x_445_, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___x_439_, v___x_444_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node4(v___x_439_, v___x_448_, v___x_450_, v___x_458_, v___x_460_, v___x_469_);
v___x_471_ = l_Lean_Syntax_node1(v___x_439_, v___x_446_, v___x_470_);
v___x_472_ = l_Lean_Syntax_node1(v___x_439_, v___x_445_, v___x_471_);
v___x_473_ = l_Lean_Syntax_node1(v___x_439_, v___x_444_, v___x_472_);
v___x_474_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
v___x_475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_439_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
lean_inc_ref(v___x_475_);
lean_inc_ref(v___x_443_);
v___x_476_ = l_Lean_Syntax_node3(v___x_439_, v___x_440_, v___x_443_, v___x_473_, v___x_475_);
v___x_477_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17));
v___x_478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_439_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l_Array_mkArray2___redArg(v___x_476_, v___x_478_);
v___x_480_ = l_Array_append___redArg(v_snd_416_, v_snd_425_);
lean_dec(v_snd_425_);
v_sz_481_ = lean_array_size(v___x_480_);
v___x_482_ = ((size_t)0ULL);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(v_sz_481_, v___x_482_, v___x_480_);
v___x_484_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19));
v___x_485_ = l_Lean_mkSepArray(v___x_483_, v___x_484_);
lean_dec_ref(v___x_483_);
v___x_486_ = l_Array_append___redArg(v___x_479_, v___x_485_);
lean_dec_ref(v___x_485_);
v___x_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_487_, 0, v___x_439_);
lean_ctor_set(v___x_487_, 1, v___x_446_);
lean_ctor_set(v___x_487_, 2, v___x_486_);
v___x_488_ = l_Lean_Syntax_node1(v___x_439_, v___x_445_, v___x_487_);
v___x_489_ = l_Lean_Syntax_node1(v___x_439_, v___x_444_, v___x_488_);
v___x_490_ = l_Lean_Syntax_node3(v___x_439_, v___x_440_, v___x_443_, v___x_489_, v___x_475_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_490_);
v___x_492_ = v___x_433_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_a_431_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
else
{
lean_del_object(v___x_427_);
lean_dec(v_snd_425_);
lean_del_object(v___x_418_);
lean_dec(v_snd_416_);
return v___x_429_;
}
}
}
else
{
lean_object* v_a_498_; lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_del_object(v___x_418_);
lean_dec(v_snd_416_);
lean_dec(v_fst_415_);
lean_dec_ref(v_mkIf_408_);
v_a_498_ = lean_ctor_get(v___x_421_, 0);
v_a_499_ = lean_ctor_get(v___x_421_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_421_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_inc(v_a_498_);
lean_dec(v___x_421_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_498_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v_mkIf_408_);
lean_dec(v_neg_407_);
lean_dec(v_elseTk_405_);
v_a_508_ = lean_ctor_get(v___x_412_, 0);
v_a_509_ = lean_ctor_get(v___x_412_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_412_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_inc(v_a_508_);
lean_dec(v___x_412_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_508_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___boxed(lean_object* v_ifTk_517_, lean_object* v_thenTk_518_, lean_object* v_elseTk_519_, lean_object* v_pos_520_, lean_object* v_neg_521_, lean_object* v_mkIf_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(v_ifTk_517_, v_thenTk_518_, v_elseTk_519_, v_pos_520_, v_neg_521_, v_mkIf_522_, v_a_523_, v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_ifTk_517_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0(lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v_pos_535_, lean_object* v_neg_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_ref_539_; uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_ref_539_ = lean_ctor_get(v___y_537_, 5);
v___x_540_ = 0;
v___x_541_ = l_Lean_SourceInfo_fromRef(v_ref_539_, v___x_540_);
v___x_542_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1));
v___x_543_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2));
lean_inc_n(v___x_541_, 4);
v___x_544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_541_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3));
v___x_546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_541_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4));
v___x_548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_541_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5));
v___x_550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_541_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = l_Lean_Syntax_node8(v___x_541_, v___x_542_, v___x_544_, v___x_533_, v___x_546_, v___x_534_, v___x_548_, v_pos_535_, v___x_550_, v_neg_536_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v___y_538_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___boxed(lean_object* v___x_553_, lean_object* v___x_554_, lean_object* v_pos_555_, lean_object* v_neg_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0(v___x_553_, v___x_554_, v_pos_555_, v_neg_556_, v___y_557_, v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1(lean_object* v_x_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1));
lean_inc(v_x_566_);
v___x_570_ = l_Lean_Syntax_isOfKind(v_x_566_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v_x_566_);
v___x_571_ = lean_box(1);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_a_568_);
return v___x_572_;
}
else
{
lean_object* v_methods_573_; lean_object* v_quotContext_574_; lean_object* v_currMacroScope_575_; lean_object* v_currRecDepth_576_; lean_object* v_maxRecDepth_577_; lean_object* v_ref_578_; lean_object* v___x_579_; lean_object* v_tk_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v_ttk_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v_etk_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_ref_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_methods_573_ = lean_ctor_get(v_a_567_, 0);
v_quotContext_574_ = lean_ctor_get(v_a_567_, 1);
v_currMacroScope_575_ = lean_ctor_get(v_a_567_, 2);
v_currRecDepth_576_ = lean_ctor_get(v_a_567_, 3);
v_maxRecDepth_577_ = lean_ctor_get(v_a_567_, 4);
v_ref_578_ = lean_ctor_get(v_a_567_, 5);
v___x_579_ = lean_unsigned_to_nat(0u);
v_tk_580_ = l_Lean_Syntax_getArg(v_x_566_, v___x_579_);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = l_Lean_Syntax_getArg(v_x_566_, v___x_581_);
v___x_583_ = lean_unsigned_to_nat(3u);
v___x_584_ = l_Lean_Syntax_getArg(v_x_566_, v___x_583_);
v___f_585_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___boxed), 6, 2);
lean_closure_set(v___f_585_, 0, v___x_582_);
lean_closure_set(v___f_585_, 1, v___x_584_);
v___x_586_ = lean_unsigned_to_nat(4u);
v_ttk_587_ = l_Lean_Syntax_getArg(v_x_566_, v___x_586_);
v___x_588_ = lean_unsigned_to_nat(5u);
v___x_589_ = l_Lean_Syntax_getArg(v_x_566_, v___x_588_);
v___x_590_ = lean_unsigned_to_nat(6u);
v_etk_591_ = l_Lean_Syntax_getArg(v_x_566_, v___x_590_);
v___x_592_ = lean_unsigned_to_nat(7u);
v___x_593_ = l_Lean_Syntax_getArg(v_x_566_, v___x_592_);
lean_dec(v_x_566_);
v_ref_594_ = l_Lean_replaceRef(v_tk_580_, v_ref_578_);
lean_inc(v_maxRecDepth_577_);
lean_inc(v_currRecDepth_576_);
lean_inc(v_currMacroScope_575_);
lean_inc(v_quotContext_574_);
lean_inc(v_methods_573_);
v___x_595_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_595_, 0, v_methods_573_);
lean_ctor_set(v___x_595_, 1, v_quotContext_574_);
lean_ctor_set(v___x_595_, 2, v_currMacroScope_575_);
lean_ctor_set(v___x_595_, 3, v_currRecDepth_576_);
lean_ctor_set(v___x_595_, 4, v_maxRecDepth_577_);
lean_ctor_set(v___x_595_, 5, v_ref_594_);
v___x_596_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(v_tk_580_, v_ttk_587_, v_etk_591_, v___x_589_, v___x_593_, v___f_585_, v___x_595_, v_a_568_);
lean_dec_ref(v___x_595_);
lean_dec(v_tk_580_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_a_598_ = lean_ctor_get(v___x_596_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_596_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_597_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_a_606_ = lean_ctor_get(v___x_596_, 0);
v_a_607_ = lean_ctor_get(v___x_596_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_596_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_inc(v_a_606_);
lean_dec(v___x_596_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_606_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___boxed(lean_object* v_x_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1(v_x_615_, v_a_616_, v_a_617_);
lean_dec_ref(v_a_616_);
return v_res_618_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0));
v___x_621_ = l_String_toRawSubstring_x27(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0(lean_object* v___x_624_, lean_object* v___x_625_, lean_object* v_pos_626_, lean_object* v_neg_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_quotContext_630_; lean_object* v_currMacroScope_631_; lean_object* v_ref_632_; uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_quotContext_630_ = lean_ctor_get(v___y_628_, 1);
v_currMacroScope_631_ = lean_ctor_get(v___y_628_, 2);
v_ref_632_ = lean_ctor_get(v___y_628_, 5);
v___x_633_ = 0;
v___x_634_ = l_Lean_SourceInfo_fromRef(v_ref_632_, v___x_633_);
v___x_635_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1));
v___x_636_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2));
lean_inc_n(v___x_634_, 6);
v___x_637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_634_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28));
v___x_639_ = l_Lean_Name_mkStr2(v___x_624_, v___x_638_);
v___x_640_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1, &l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1_once, _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1);
v___x_641_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__2));
lean_inc(v_currMacroScope_631_);
lean_inc(v_quotContext_630_);
v___x_642_ = l_Lean_addMacroScope(v_quotContext_630_, v___x_641_, v_currMacroScope_631_);
v___x_643_ = lean_box(0);
v___x_644_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_644_, 0, v___x_634_);
lean_ctor_set(v___x_644_, 1, v___x_640_);
lean_ctor_set(v___x_644_, 2, v___x_642_);
lean_ctor_set(v___x_644_, 3, v___x_643_);
v___x_645_ = l_Lean_Syntax_node1(v___x_634_, v___x_639_, v___x_644_);
v___x_646_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3));
v___x_647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_634_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4));
v___x_649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_634_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5));
v___x_651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_634_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = l_Lean_Syntax_node8(v___x_634_, v___x_635_, v___x_637_, v___x_645_, v___x_647_, v___x_625_, v___x_649_, v_pos_626_, v___x_651_, v_neg_627_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___y_629_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___boxed(lean_object* v___x_654_, lean_object* v___x_655_, lean_object* v_pos_656_, lean_object* v_neg_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0(v___x_654_, v___x_655_, v_pos_656_, v_neg_657_, v___y_658_, v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1(lean_object* v_x_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0));
v___x_671_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1));
lean_inc(v_x_667_);
v___x_672_ = l_Lean_Syntax_isOfKind(v_x_667_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v_x_667_);
v___x_673_ = lean_box(1);
v___x_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v_a_669_);
return v___x_674_;
}
else
{
lean_object* v_methods_675_; lean_object* v_quotContext_676_; lean_object* v_currMacroScope_677_; lean_object* v_currRecDepth_678_; lean_object* v_maxRecDepth_679_; lean_object* v_ref_680_; lean_object* v___x_681_; lean_object* v_tk_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v_ttk_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_etk_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_ref_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_methods_675_ = lean_ctor_get(v_a_668_, 0);
v_quotContext_676_ = lean_ctor_get(v_a_668_, 1);
v_currMacroScope_677_ = lean_ctor_get(v_a_668_, 2);
v_currRecDepth_678_ = lean_ctor_get(v_a_668_, 3);
v_maxRecDepth_679_ = lean_ctor_get(v_a_668_, 4);
v_ref_680_ = lean_ctor_get(v_a_668_, 5);
v___x_681_ = lean_unsigned_to_nat(0u);
v_tk_682_ = l_Lean_Syntax_getArg(v_x_667_, v___x_681_);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = l_Lean_Syntax_getArg(v_x_667_, v___x_683_);
v___f_685_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___boxed), 6, 2);
lean_closure_set(v___f_685_, 0, v___x_670_);
lean_closure_set(v___f_685_, 1, v___x_684_);
v___x_686_ = lean_unsigned_to_nat(2u);
v_ttk_687_ = l_Lean_Syntax_getArg(v_x_667_, v___x_686_);
v___x_688_ = lean_unsigned_to_nat(3u);
v___x_689_ = l_Lean_Syntax_getArg(v_x_667_, v___x_688_);
v___x_690_ = lean_unsigned_to_nat(4u);
v_etk_691_ = l_Lean_Syntax_getArg(v_x_667_, v___x_690_);
v___x_692_ = lean_unsigned_to_nat(5u);
v___x_693_ = l_Lean_Syntax_getArg(v_x_667_, v___x_692_);
lean_dec(v_x_667_);
v_ref_694_ = l_Lean_replaceRef(v_tk_682_, v_ref_680_);
lean_inc(v_maxRecDepth_679_);
lean_inc(v_currRecDepth_678_);
lean_inc(v_currMacroScope_677_);
lean_inc(v_quotContext_676_);
lean_inc(v_methods_675_);
v___x_695_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_695_, 0, v_methods_675_);
lean_ctor_set(v___x_695_, 1, v_quotContext_676_);
lean_ctor_set(v___x_695_, 2, v_currMacroScope_677_);
lean_ctor_set(v___x_695_, 3, v_currRecDepth_678_);
lean_ctor_set(v___x_695_, 4, v_maxRecDepth_679_);
lean_ctor_set(v___x_695_, 5, v_ref_694_);
v___x_696_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(v_tk_682_, v_ttk_687_, v_etk_691_, v___x_689_, v___x_693_, v___f_685_, v___x_695_, v_a_669_);
lean_dec_ref(v___x_695_);
lean_dec(v_tk_682_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_a_698_ = lean_ctor_get(v___x_696_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_696_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_697_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
lean_object* v_a_706_; lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_706_ = lean_ctor_get(v___x_696_, 0);
v_a_707_ = lean_ctor_get(v___x_696_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_696_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_inc(v_a_706_);
lean_dec(v___x_696_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_706_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___boxed(lean_object* v_x_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1(v_x_715_, v_a_716_, v_a_717_);
lean_dec_ref(v_a_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1(lean_object* v_x_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__1));
lean_inc(v_x_786_);
v___x_790_ = l_Lean_Syntax_isOfKind(v_x_786_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec(v_x_786_);
v___x_791_ = lean_box(1);
v___x_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v_a_788_);
return v___x_792_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = l_Lean_Syntax_getArg(v_x_786_, v___x_794_);
lean_inc(v___x_795_);
v___x_796_ = l_Lean_Syntax_matchesNull(v___x_795_, v___x_793_);
if (v___x_796_ == 0)
{
uint8_t v___x_797_; 
lean_inc(v___x_795_);
v___x_797_ = l_Lean_Syntax_matchesNull(v___x_795_, v___x_794_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v___x_795_);
lean_dec(v_x_786_);
v___x_798_ = lean_box(1);
v___x_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_a_788_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_800_ = lean_unsigned_to_nat(2u);
v___x_801_ = l_Lean_Syntax_getArg(v_x_786_, v___x_800_);
lean_dec(v_x_786_);
v___x_802_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
lean_inc(v___x_801_);
v___x_803_ = l_Lean_Syntax_isOfKind(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec(v___x_801_);
lean_dec(v___x_795_);
v___x_804_ = lean_box(1);
v___x_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v_a_788_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v_isZero_808_; 
v___x_806_ = l_Lean_Syntax_getArg(v___x_795_, v___x_793_);
lean_dec(v___x_795_);
v___x_807_ = l_Lean_Syntax_toNat(v___x_806_);
lean_dec(v___x_806_);
v_isZero_808_ = lean_nat_dec_eq(v___x_807_, v___x_793_);
if (v_isZero_808_ == 1)
{
lean_object* v_ref_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v___x_807_);
lean_dec(v___x_801_);
v_ref_809_ = lean_ctor_get(v_a_787_, 5);
v___x_810_ = l_Lean_SourceInfo_fromRef(v_ref_809_, v___x_796_);
v___x_811_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17));
v___x_812_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18));
lean_inc(v___x_810_);
v___x_813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_810_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
v___x_814_ = l_Lean_Syntax_node1(v___x_810_, v___x_812_, v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v_a_788_);
return v___x_815_;
}
else
{
lean_object* v_ref_816_; lean_object* v_n_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_ref_816_ = lean_ctor_get(v_a_787_, 5);
v_n_817_ = lean_nat_sub(v___x_807_, v___x_794_);
lean_dec(v___x_807_);
v___x_818_ = l_Lean_SourceInfo_fromRef(v_ref_816_, v___x_796_);
v___x_819_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1));
v___x_820_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_821_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_822_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc_n(v___x_818_, 8);
v___x_823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_818_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
v___x_825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_818_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
lean_inc(v___x_801_);
v___x_826_ = l_Lean_Syntax_node3(v___x_818_, v___x_821_, v___x_823_, v___x_801_, v___x_825_);
v___x_827_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17));
v___x_828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_818_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__4));
v___x_830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_818_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Nat_reprFast(v_n_817_);
v___x_832_ = lean_box(2);
v___x_833_ = l_Lean_Syntax_mkNumLit(v___x_831_, v___x_832_);
v___x_834_ = l_Lean_Syntax_node1(v___x_818_, v___x_820_, v___x_833_);
v___x_835_ = l_Lean_Syntax_node3(v___x_818_, v___x_789_, v___x_830_, v___x_834_, v___x_801_);
v___x_836_ = l_Lean_Syntax_node3(v___x_818_, v___x_820_, v___x_826_, v___x_828_, v___x_835_);
v___x_837_ = l_Lean_Syntax_node1(v___x_818_, v___x_819_, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_a_788_);
return v___x_838_;
}
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
lean_dec(v___x_795_);
v___x_839_ = lean_unsigned_to_nat(2u);
v___x_840_ = l_Lean_Syntax_getArg(v_x_786_, v___x_839_);
lean_dec(v_x_786_);
v___x_841_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
lean_inc(v___x_840_);
v___x_842_ = l_Lean_Syntax_isOfKind(v___x_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec(v___x_840_);
v___x_843_ = lean_box(1);
v___x_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v_a_788_);
return v___x_844_;
}
else
{
lean_object* v_ref_845_; uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_ref_845_ = lean_ctor_get(v_a_787_, 5);
v___x_846_ = 0;
v___x_847_ = l_Lean_SourceInfo_fromRef(v_ref_845_, v___x_846_);
v___x_848_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3));
v___x_849_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__4));
lean_inc_n(v___x_847_, 11);
v___x_850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_847_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11));
v___x_852_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_853_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_854_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
v___x_855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_847_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
v___x_857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_847_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
lean_inc(v___x_840_);
v___x_858_ = l_Lean_Syntax_node3(v___x_847_, v___x_853_, v___x_855_, v___x_840_, v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17));
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_847_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__4));
v___x_862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_847_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
v___x_864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_864_, 0, v___x_847_);
lean_ctor_set(v___x_864_, 1, v___x_852_);
lean_ctor_set(v___x_864_, 2, v___x_863_);
v___x_865_ = l_Lean_Syntax_node3(v___x_847_, v___x_789_, v___x_862_, v___x_864_, v___x_840_);
v___x_866_ = l_Lean_Syntax_node3(v___x_847_, v___x_852_, v___x_858_, v___x_860_, v___x_865_);
v___x_867_ = l_Lean_Syntax_node1(v___x_847_, v___x_851_, v___x_866_);
v___x_868_ = l_Lean_Syntax_node1(v___x_847_, v___x_841_, v___x_867_);
v___x_869_ = l_Lean_Syntax_node2(v___x_847_, v___x_848_, v___x_850_, v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v_a_788_);
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___boxed(lean_object* v_x_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1(v_x_871_, v_a_872_, v_a_873_);
lean_dec_ref(v_a_872_);
return v_res_874_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_885_ = l_Lean_Parser_Tactic_optConfig;
v___x_886_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__3));
v___x_887_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3));
v___x_888_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_886_);
lean_ctor_set(v___x_888_, 2, v___x_885_);
return v___x_888_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_889_ = l_Lean_Parser_Tactic_rwRuleSeq;
v___x_890_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4, &l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4_once, _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4);
v___x_891_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3));
v___x_892_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v___x_890_);
lean_ctor_set(v___x_892_, 2, v___x_889_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = l_Lean_Parser_Tactic_location;
v___x_894_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__7));
v___x_895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_896_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6, &l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6_once, _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6);
v___x_897_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5, &l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5_once, _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5);
v___x_898_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3));
v___x_899_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v___x_897_);
lean_ctor_set(v___x_899_, 2, v___x_896_);
return v___x_899_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_900_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7, &l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7_once, _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7);
v___x_901_ = lean_unsigned_to_nat(1022u);
v___x_902_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1));
v___x_903_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_901_);
lean_ctor_set(v___x_903_, 2, v___x_900_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast______(void){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8, &l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8_once, _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0(lean_object* v___x_947_, lean_object* v_loc_948_, size_t v_sz_949_, size_t v_i_950_, lean_object* v_bs_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_lt(v_i_950_, v_sz_949_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
lean_dec(v_loc_948_);
lean_dec(v___x_947_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_bs_951_);
lean_ctor_set(v___x_955_, 1, v___y_953_);
return v___x_955_;
}
else
{
lean_object* v_ref_956_; lean_object* v___x_957_; lean_object* v_v_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v_bs_x27_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___y_998_; 
v_ref_956_ = lean_ctor_get(v___y_952_, 5);
v___x_957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1));
v_v_958_ = lean_array_uget(v_bs_951_, v_i_950_);
v___x_959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3));
v___x_960_ = lean_unsigned_to_nat(0u);
v_bs_x27_961_ = lean_array_uset(v_bs_951_, v_i_950_, v___x_960_);
v___x_962_ = 0;
v___x_963_ = l_Lean_SourceInfo_fromRef(v_ref_956_, v___x_962_);
v___x_964_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_965_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc_n(v___x_963_, 16);
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_963_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
v___x_968_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11));
v___x_969_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5));
v___x_971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__6));
v___x_972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_963_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
v___x_974_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_974_, 0, v___x_963_);
lean_ctor_set(v___x_974_, 1, v___x_969_);
lean_ctor_set(v___x_974_, 2, v___x_973_);
v___x_975_ = l_Lean_Syntax_node1(v___x_963_, v___x_957_, v___x_974_);
v___x_976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8));
v___x_977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__9));
v___x_978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_963_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11));
v___x_980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__12));
v___x_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_963_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_Syntax_node1(v___x_963_, v___x_979_, v___x_981_);
v___x_983_ = l_Lean_Syntax_node2(v___x_963_, v___x_976_, v___x_978_, v___x_982_);
v___x_984_ = l_Lean_Syntax_node1(v___x_963_, v___x_969_, v___x_983_);
v___x_985_ = l_Lean_Syntax_node3(v___x_963_, v___x_970_, v___x_972_, v___x_975_, v___x_984_);
v___x_986_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17));
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_963_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14));
v___x_989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__15));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_963_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__16));
v___x_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_963_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_Syntax_node1(v___x_963_, v___x_969_, v_v_958_);
v___x_994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__17));
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_963_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l_Lean_Syntax_node3(v___x_963_, v___x_959_, v___x_992_, v___x_993_, v___x_995_);
if (lean_obj_tag(v_loc_948_) == 1)
{
lean_object* v_val_1012_; lean_object* v___x_1013_; 
v_val_1012_ = lean_ctor_get(v_loc_948_, 0);
lean_inc(v_val_1012_);
v___x_1013_ = l_Array_mkArray1___redArg(v_val_1012_);
v___y_998_ = v___x_1013_;
goto v___jp_997_;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18));
v___y_998_ = v___x_1014_;
goto v___jp_997_;
}
v___jp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
v___x_999_ = l_Array_append___redArg(v___x_973_, v___y_998_);
lean_dec_ref(v___y_998_);
lean_inc_n(v___x_963_, 6);
v___x_1000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1000_, 0, v___x_963_);
lean_ctor_set(v___x_1000_, 1, v___x_969_);
lean_ctor_set(v___x_1000_, 2, v___x_999_);
lean_inc(v___x_947_);
v___x_1001_ = l_Lean_Syntax_node4(v___x_963_, v___x_988_, v___x_990_, v___x_947_, v___x_996_, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_node3(v___x_963_, v___x_969_, v___x_985_, v___x_987_, v___x_1001_);
v___x_1003_ = l_Lean_Syntax_node1(v___x_963_, v___x_968_, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node1(v___x_963_, v___x_967_, v___x_1003_);
v___x_1005_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_963_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l_Lean_Syntax_node3(v___x_963_, v___x_964_, v___x_966_, v___x_1004_, v___x_1006_);
v___x_1008_ = ((size_t)1ULL);
v___x_1009_ = lean_usize_add(v_i_950_, v___x_1008_);
v___x_1010_ = lean_array_uset(v_bs_x27_961_, v_i_950_, v___x_1007_);
v_i_950_ = v___x_1009_;
v_bs_951_ = v___x_1010_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___boxed(lean_object* v___x_1015_, lean_object* v_loc_1016_, lean_object* v_sz_1017_, lean_object* v_i_1018_, lean_object* v_bs_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
size_t v_sz_boxed_1022_; size_t v_i_boxed_1023_; lean_object* v_res_1024_; 
v_sz_boxed_1022_ = lean_unbox_usize(v_sz_1017_);
lean_dec(v_sz_1017_);
v_i_boxed_1023_ = lean_unbox_usize(v_i_1018_);
lean_dec(v_i_1018_);
v_res_1024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0(v___x_1015_, v_loc_1016_, v_sz_boxed_1022_, v_i_boxed_1023_, v_bs_1019_, v___y_1020_, v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1(lean_object* v_x_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1));
lean_inc(v_x_1025_);
v___x_1029_ = l_Lean_Syntax_isOfKind(v_x_1025_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec(v_x_1025_);
v___x_1030_ = lean_box(1);
v___x_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v_a_1027_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1032_ = lean_unsigned_to_nat(1u);
v___x_1033_ = l_Lean_Syntax_getArg(v_x_1025_, v___x_1032_);
v___x_1034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1));
lean_inc(v___x_1033_);
v___x_1035_ = l_Lean_Syntax_isOfKind(v___x_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec(v___x_1033_);
lean_dec(v_x_1025_);
v___x_1036_ = lean_box(1);
v___x_1037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v_a_1027_);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1038_ = lean_unsigned_to_nat(2u);
v___x_1039_ = l_Lean_Syntax_getArg(v_x_1025_, v___x_1038_);
v___x_1040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3));
lean_inc(v___x_1039_);
v___x_1041_ = l_Lean_Syntax_isOfKind(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec(v___x_1039_);
lean_dec(v___x_1033_);
lean_dec(v_x_1025_);
v___x_1042_ = lean_box(1);
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v_a_1027_);
return v___x_1043_;
}
else
{
lean_object* v___x_1044_; lean_object* v_loc_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1044_ = l_Lean_Syntax_getArg(v___x_1039_, v___x_1032_);
lean_dec(v___x_1039_);
v___x_1093_ = lean_unsigned_to_nat(3u);
v___x_1094_ = l_Lean_Syntax_getArg(v_x_1025_, v___x_1093_);
lean_dec(v_x_1025_);
v___x_1095_ = l_Lean_Syntax_isNone(v___x_1094_);
if (v___x_1095_ == 0)
{
uint8_t v___x_1096_; 
lean_inc(v___x_1094_);
v___x_1096_ = l_Lean_Syntax_matchesNull(v___x_1094_, v___x_1032_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v___x_1094_);
lean_dec(v___x_1044_);
lean_dec(v___x_1033_);
v___x_1097_ = lean_box(1);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_a_1027_);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; lean_object* v_loc_1100_; lean_object* v___x_1101_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v_loc_1100_ = l_Lean_Syntax_getArg(v___x_1094_, v___x_1099_);
lean_dec(v___x_1094_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_loc_1100_);
v_loc_1046_ = v___x_1101_;
v___y_1047_ = v_a_1026_;
v___y_1048_ = v_a_1027_;
goto v___jp_1045_;
}
}
else
{
lean_object* v___x_1102_; 
lean_dec(v___x_1094_);
v___x_1102_ = lean_box(0);
v_loc_1046_ = v___x_1102_;
v___y_1047_ = v_a_1026_;
v___y_1048_ = v_a_1027_;
goto v___jp_1045_;
}
v___jp_1045_:
{
lean_object* v_rules_1049_; lean_object* v___x_1050_; size_t v_sz_1051_; size_t v___x_1052_; lean_object* v___x_1053_; 
v_rules_1049_ = l_Lean_Syntax_getArgs(v___x_1044_);
lean_dec(v___x_1044_);
v___x_1050_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_rules_1049_);
lean_dec_ref(v_rules_1049_);
v_sz_1051_ = lean_array_size(v___x_1050_);
v___x_1052_ = ((size_t)0ULL);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0(v___x_1033_, v_loc_1046_, v_sz_1051_, v___x_1052_, v___x_1050_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1083_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_a_1055_ = lean_ctor_get(v___x_1053_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1057_ = v___x_1053_;
v_isShared_1058_ = v_isSharedCheck_1083_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1083_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v_ref_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; size_t v_sz_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v_ref_1059_ = lean_ctor_get(v___y_1047_, 5);
v___x_1060_ = 0;
v___x_1061_ = l_Lean_SourceInfo_fromRef(v_ref_1059_, v___x_1060_);
v___x_1062_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_1063_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc_n(v___x_1061_, 5);
v___x_1064_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1061_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
v___x_1066_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11));
v___x_1067_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_1068_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
v_sz_1069_ = lean_array_size(v_a_1054_);
v___x_1070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(v_sz_1069_, v___x_1052_, v_a_1054_);
v___x_1071_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19));
v___x_1072_ = l_Lean_mkSepArray(v___x_1070_, v___x_1071_);
lean_dec_ref(v___x_1070_);
v___x_1073_ = l_Array_append___redArg(v___x_1068_, v___x_1072_);
lean_dec_ref(v___x_1072_);
v___x_1074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1061_);
lean_ctor_set(v___x_1074_, 1, v___x_1067_);
lean_ctor_set(v___x_1074_, 2, v___x_1073_);
v___x_1075_ = l_Lean_Syntax_node1(v___x_1061_, v___x_1066_, v___x_1074_);
v___x_1076_ = l_Lean_Syntax_node1(v___x_1061_, v___x_1065_, v___x_1075_);
v___x_1077_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
v___x_1078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1061_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = l_Lean_Syntax_node3(v___x_1061_, v___x_1062_, v___x_1064_, v___x_1076_, v___x_1078_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1079_);
v___x_1081_ = v___x_1057_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_a_1055_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1084_ = lean_ctor_get(v___x_1053_, 0);
v_a_1085_ = lean_ctor_get(v___x_1053_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1053_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_inc(v_a_1084_);
lean_dec(v___x_1053_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1084_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1___boxed(lean_object* v_x_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1(v_x_1103_, v_a_1104_, v_a_1105_);
lean_dec_ref(v_a_1104_);
return v_res_1106_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__11));
v___x_1160_ = l_String_toRawSubstring_x27(v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1(lean_object* v_x_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1));
lean_inc(v_x_1171_);
v___x_1175_ = l_Lean_Syntax_isOfKind(v_x_1171_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec(v_x_1171_);
v___x_1176_ = lean_box(1);
v___x_1177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v_a_1173_);
return v___x_1177_;
}
else
{
lean_object* v_quotContext_1178_; lean_object* v_currMacroScope_1179_; lean_object* v_ref_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_quotContext_1178_ = lean_ctor_get(v_a_1172_, 1);
v_currMacroScope_1179_ = lean_ctor_get(v_a_1172_, 2);
v_ref_1180_ = lean_ctor_get(v_a_1172_, 5);
v___x_1181_ = lean_unsigned_to_nat(1u);
v___x_1182_ = l_Lean_Syntax_getArg(v_x_1171_, v___x_1181_);
lean_dec(v_x_1171_);
v___x_1183_ = 0;
v___x_1184_ = l_Lean_SourceInfo_fromRef(v_ref_1180_, v___x_1183_);
v___x_1185_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0));
v___x_1186_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1));
lean_inc_n(v___x_1184_, 13);
v___x_1187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1184_);
lean_ctor_set(v___x_1187_, 1, v___x_1185_);
v___x_1188_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3));
v___x_1189_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4));
v___x_1190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1184_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6));
v___x_1192_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8));
v___x_1193_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
v___x_1194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1184_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10));
v___x_1196_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12, &l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12);
v___x_1197_ = lean_box(0);
lean_inc(v_currMacroScope_1179_);
lean_inc(v_quotContext_1178_);
v___x_1198_ = l_Lean_addMacroScope(v_quotContext_1178_, v___x_1197_, v_currMacroScope_1179_);
v___x_1199_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15));
v___x_1200_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1184_);
lean_ctor_set(v___x_1200_, 1, v___x_1196_);
lean_ctor_set(v___x_1200_, 2, v___x_1198_);
lean_ctor_set(v___x_1200_, 3, v___x_1199_);
v___x_1201_ = l_Lean_Syntax_node1(v___x_1184_, v___x_1195_, v___x_1200_);
v___x_1202_ = l_Lean_Syntax_node2(v___x_1184_, v___x_1192_, v___x_1194_, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3));
v___x_1204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1184_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_1206_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6));
v___x_1207_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16));
v___x_1208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1184_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l_Lean_Syntax_node1(v___x_1184_, v___x_1206_, v___x_1208_);
v___x_1210_ = l_Lean_Syntax_node1(v___x_1184_, v___x_1205_, v___x_1209_);
v___x_1211_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
v___x_1212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1184_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = l_Lean_Syntax_node5(v___x_1184_, v___x_1191_, v___x_1202_, v___x_1182_, v___x_1204_, v___x_1210_, v___x_1212_);
v___x_1214_ = l_Lean_Syntax_node2(v___x_1184_, v___x_1188_, v___x_1190_, v___x_1213_);
v___x_1215_ = l_Lean_Syntax_node2(v___x_1184_, v___x_1186_, v___x_1187_, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v_a_1173_);
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___boxed(lean_object* v_x_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1(v_x_1217_, v_a_1218_, v_a_1219_);
lean_dec_ref(v_a_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1(lean_object* v_x_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1));
lean_inc(v_x_1246_);
v___x_1250_ = l_Lean_Syntax_isOfKind(v_x_1246_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec(v_x_1246_);
v___x_1251_ = lean_box(1);
v___x_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v_a_1248_);
return v___x_1252_;
}
else
{
lean_object* v_quotContext_1253_; lean_object* v_currMacroScope_1254_; lean_object* v_ref_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_quotContext_1253_ = lean_ctor_get(v_a_1247_, 1);
v_currMacroScope_1254_ = lean_ctor_get(v_a_1247_, 2);
v_ref_1255_ = lean_ctor_get(v_a_1247_, 5);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = l_Lean_Syntax_getArg(v_x_1246_, v___x_1256_);
lean_dec(v_x_1246_);
v___x_1258_ = 0;
v___x_1259_ = l_Lean_SourceInfo_fromRef(v_ref_1255_, v___x_1258_);
v___x_1260_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0));
v___x_1261_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1));
lean_inc_n(v___x_1259_, 13);
v___x_1262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1260_);
v___x_1263_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3));
v___x_1264_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4));
v___x_1265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1259_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6));
v___x_1267_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8));
v___x_1268_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
v___x_1269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1259_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10));
v___x_1271_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12, &l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12);
v___x_1272_ = lean_box(0);
lean_inc(v_currMacroScope_1254_);
lean_inc(v_quotContext_1253_);
v___x_1273_ = l_Lean_addMacroScope(v_quotContext_1253_, v___x_1272_, v_currMacroScope_1254_);
v___x_1274_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15));
v___x_1275_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1259_);
lean_ctor_set(v___x_1275_, 1, v___x_1271_);
lean_ctor_set(v___x_1275_, 2, v___x_1273_);
lean_ctor_set(v___x_1275_, 3, v___x_1274_);
v___x_1276_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1270_, v___x_1275_);
v___x_1277_ = l_Lean_Syntax_node2(v___x_1259_, v___x_1267_, v___x_1269_, v___x_1276_);
v___x_1278_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3));
v___x_1279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1259_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_1281_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6));
v___x_1282_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16));
v___x_1283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1259_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1281_, v___x_1283_);
v___x_1285_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1280_, v___x_1284_);
v___x_1286_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
v___x_1287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1259_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_Syntax_node5(v___x_1259_, v___x_1266_, v___x_1277_, v___x_1257_, v___x_1279_, v___x_1285_, v___x_1287_);
v___x_1289_ = l_Lean_Syntax_node2(v___x_1259_, v___x_1263_, v___x_1265_, v___x_1288_);
v___x_1290_ = l_Lean_Syntax_node2(v___x_1259_, v___x_1261_, v___x_1262_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_a_1248_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___boxed(lean_object* v_x_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1(v_x_1292_, v_a_1293_, v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1295_;
}
}
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_TacticsExtra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_tacticRw__mod__cast______ = _init_l_Lean_Parser_Tactic_tacticRw__mod__cast______();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticRw__mod__cast______);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Meta(uint8_t builtin);
lean_object* initialize_Init_Tactics(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_TacticsExtra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_TacticsExtra(builtin);
}
#ifdef __cplusplus
}
#endif
