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
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0_value;
static lean_once_cell_t l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1;
static const lean_ctor_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 129, 35, 203, 24, 252, 22, 100)}};
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value;
static const lean_closure_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value;
static const lean_closure_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value)} };
static const lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2 = (const lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2_value;
static const lean_closure_object l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__0_value),((lean_object*)&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__1_value)} };
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
lean_inc(v___x_115_);
v___x_120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_115_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17));
v___x_122_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18));
lean_inc(v___x_115_);
v___x_123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_115_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_inc(v___x_115_);
v___x_124_ = l_Lean_Syntax_node1(v___x_115_, v___x_122_, v___x_123_);
lean_inc(v_tk_79_);
lean_inc(v___x_115_);
v___x_125_ = l_Lean_Syntax_node3(v___x_115_, v___x_118_, v___x_120_, v_tk_79_, v___x_124_);
v___x_126_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
lean_inc(v___x_115_);
v___x_127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_127_, 0, v___x_115_);
lean_ctor_set(v___x_127_, 1, v___x_117_);
lean_ctor_set(v___x_127_, 2, v___x_126_);
v___x_128_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_129_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc(v___x_115_);
v___x_130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_115_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
lean_inc(v___x_115_);
v___x_132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_115_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
lean_inc(v___x_115_);
v___x_133_ = l_Lean_Syntax_node3(v___x_115_, v___x_128_, v___x_130_, v_holeOrTacticSeq_80_, v___x_132_);
lean_inc(v___x_115_);
v___x_134_ = l_Lean_Syntax_node3(v___x_115_, v___x_117_, v___x_125_, v___x_127_, v___x_133_);
lean_inc(v___x_115_);
v___x_135_ = l_Lean_Syntax_node1(v___x_115_, v___x_116_, v___x_134_);
v___x_136_ = l_Lean_Syntax_node1(v___x_115_, v___x_113_, v___x_135_);
v_ref_137_ = l_Lean_replaceRef(v_tk_79_, v_ref_99_);
v___x_138_ = l_Lean_SourceInfo_fromRef(v_ref_137_, v___x_88_);
lean_dec(v_ref_137_);
v___x_139_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__24));
v___x_140_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__25));
lean_inc(v___x_138_);
v___x_141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
v___x_142_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__27));
v___x_143_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__29));
lean_inc(v___x_138_);
v___x_144_ = l_Lean_Syntax_node1(v___x_138_, v___x_143_, v___x_112_);
lean_inc(v___x_138_);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_138_);
lean_ctor_set(v___x_145_, 1, v___x_117_);
lean_ctor_set(v___x_145_, 2, v___x_126_);
lean_inc(v___x_138_);
v___x_146_ = l_Lean_Syntax_node2(v___x_138_, v___x_142_, v___x_144_, v___x_145_);
lean_inc(v___x_138_);
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
lean_inc(v_quotContext_247_);
v_currMacroScope_248_ = lean_ctor_get(v___y_236_, 2);
lean_inc(v_currMacroScope_248_);
lean_dec_ref(v___y_236_);
v___x_249_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4));
v___x_250_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0));
lean_inc(v_a_242_);
v___x_251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_251_, 0, v_a_242_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__2);
v___x_253_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__3));
v___x_254_ = l_Lean_addMacroScope(v_quotContext_247_, v___x_253_, v_currMacroScope_248_);
v___x_255_ = lean_box(0);
lean_inc(v_a_242_);
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
lean_dec_ref(v___y_236_);
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
lean_dec_ref(v___y_236_);
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
static lean_object* _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__0));
v___x_282_ = l_String_toRawSubstring_x27(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4(lean_object* v___f_285_, lean_object* v___f_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_289_; 
lean_inc_ref_n(v___y_287_, 2);
v___x_289_ = lean_apply_3(v___f_285_, v___y_287_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v_a_291_; lean_object* v___x_292_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
v_a_291_ = lean_ctor_get(v___x_289_, 1);
lean_inc(v_a_291_);
lean_dec_ref(v___x_289_);
lean_inc_ref(v___y_287_);
v___x_292_ = lean_apply_3(v___f_286_, v_a_290_, v___y_287_, v_a_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_312_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_a_294_ = lean_ctor_get(v___x_292_, 1);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_312_ == 0)
{
v___x_296_ = v___x_292_;
v_isShared_297_ = v_isSharedCheck_312_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_312_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_quotContext_298_; lean_object* v_currMacroScope_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v_quotContext_298_ = lean_ctor_get(v___y_287_, 1);
lean_inc(v_quotContext_298_);
v_currMacroScope_299_ = lean_ctor_get(v___y_287_, 2);
lean_inc(v_currMacroScope_299_);
lean_dec_ref(v___y_287_);
v___x_300_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__4));
v___x_301_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__3___closed__0));
lean_inc(v_a_293_);
v___x_302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_302_, 0, v_a_293_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__1);
v___x_304_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__4___closed__2));
v___x_305_ = l_Lean_addMacroScope(v_quotContext_298_, v___x_304_, v_currMacroScope_299_);
v___x_306_ = lean_box(0);
lean_inc(v_a_293_);
v___x_307_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_307_, 0, v_a_293_);
lean_ctor_set(v___x_307_, 1, v___x_303_);
lean_ctor_set(v___x_307_, 2, v___x_305_);
lean_ctor_set(v___x_307_, 3, v___x_306_);
v___x_308_ = l_Lean_Syntax_node2(v_a_293_, v___x_300_, v___x_302_, v___x_307_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_308_);
v___x_310_ = v___x_296_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_a_294_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v_a_313_; lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v___y_287_);
v_a_313_ = lean_ctor_get(v___x_292_, 0);
v_a_314_ = lean_ctor_get(v___x_292_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_292_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_inc(v_a_313_);
lean_dec(v___x_292_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_313_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec_ref(v___y_287_);
lean_dec_ref(v___f_286_);
v_a_322_ = lean_ctor_get(v___x_289_, 0);
v_a_323_ = lean_ctor_get(v___x_289_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_289_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_inc(v_a_322_);
lean_dec(v___x_289_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_322_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(size_t v_sz_331_, size_t v_i_332_, lean_object* v_bs_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = lean_usize_dec_lt(v_i_332_, v_sz_331_);
if (v___x_334_ == 0)
{
return v_bs_333_;
}
else
{
lean_object* v_v_335_; lean_object* v___x_336_; lean_object* v_bs_x27_337_; size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; 
v_v_335_ = lean_array_uget(v_bs_333_, v_i_332_);
v___x_336_ = lean_unsigned_to_nat(0u);
v_bs_x27_337_ = lean_array_uset(v_bs_333_, v_i_332_, v___x_336_);
v___x_338_ = ((size_t)1ULL);
v___x_339_ = lean_usize_add(v_i_332_, v___x_338_);
v___x_340_ = lean_array_uset(v_bs_x27_337_, v_i_332_, v_v_335_);
v_i_332_ = v___x_339_;
v_bs_333_ = v___x_340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0___boxed(lean_object* v_sz_342_, lean_object* v_i_343_, lean_object* v_bs_344_){
_start:
{
size_t v_sz_boxed_345_; size_t v_i_boxed_346_; lean_object* v_res_347_; 
v_sz_boxed_345_ = lean_unbox_usize(v_sz_342_);
lean_dec(v_sz_342_);
v_i_boxed_346_ = lean_unbox_usize(v_i_343_);
lean_dec(v_i_343_);
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(v_sz_boxed_345_, v_i_boxed_346_, v_bs_344_);
return v_res_347_;
}
}
static lean_object* _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__9));
v___x_371_ = l_String_toRawSubstring_x27(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(lean_object* v_ifTk_393_, lean_object* v_thenTk_394_, lean_object* v_elseTk_395_, lean_object* v_pos_396_, lean_object* v_neg_397_, lean_object* v_mkIf_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___f_401_; lean_object* v___x_402_; 
v___f_401_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__2));
v___x_402_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(v_thenTk_394_, v_pos_396_, v___f_401_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v_a_404_; lean_object* v_fst_405_; lean_object* v_snd_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_497_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
v_a_404_ = lean_ctor_get(v___x_402_, 1);
lean_inc(v_a_404_);
lean_dec_ref(v___x_402_);
v_fst_405_ = lean_ctor_get(v_a_403_, 0);
v_snd_406_ = lean_ctor_get(v_a_403_, 1);
v_isSharedCheck_497_ = !lean_is_exclusive(v_a_403_);
if (v_isSharedCheck_497_ == 0)
{
v___x_408_ = v_a_403_;
v_isShared_409_ = v_isSharedCheck_497_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_snd_406_);
lean_inc(v_fst_405_);
lean_dec(v_a_403_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_497_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___f_410_; lean_object* v___x_411_; 
v___f_410_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__3));
v___x_411_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0(v_elseTk_395_, v_neg_397_, v___f_410_, v_a_399_, v_a_404_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v_a_413_; lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_487_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
v_a_413_ = lean_ctor_get(v___x_411_, 1);
lean_inc(v_a_413_);
lean_dec_ref(v___x_411_);
v_fst_414_ = lean_ctor_get(v_a_412_, 0);
v_snd_415_ = lean_ctor_get(v_a_412_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_a_412_);
if (v_isSharedCheck_487_ == 0)
{
v___x_417_ = v_a_412_;
v_isShared_418_ = v_isSharedCheck_487_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_snd_415_);
lean_inc(v_fst_414_);
lean_dec(v_a_412_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_487_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; 
lean_inc_ref(v_a_399_);
v___x_419_ = lean_apply_4(v_mkIf_398_, v_fst_405_, v_fst_414_, v_a_399_, v_a_413_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_486_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_a_421_ = lean_ctor_get(v___x_419_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_486_ == 0)
{
v___x_423_ = v___x_419_;
v_isShared_424_ = v_isSharedCheck_486_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_486_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_quotContext_425_; lean_object* v_currMacroScope_426_; lean_object* v_ref_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v_quotContext_425_ = lean_ctor_get(v_a_399_, 1);
lean_inc(v_quotContext_425_);
v_currMacroScope_426_ = lean_ctor_get(v_a_399_, 2);
lean_inc(v_currMacroScope_426_);
v_ref_427_ = lean_ctor_get(v_a_399_, 5);
lean_inc(v_ref_427_);
lean_dec_ref(v_a_399_);
v___x_428_ = 0;
v___x_429_ = l_Lean_SourceInfo_fromRef(v_ref_427_, v___x_428_);
lean_dec(v_ref_427_);
v___x_430_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_431_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc(v___x_429_);
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 2);
lean_ctor_set(v___x_417_, 1, v___x_431_);
lean_ctor_set(v___x_417_, 0, v___x_429_);
v___x_433_ = v___x_417_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_485_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_434_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
v___x_435_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11));
v___x_436_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_437_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__4));
v___x_438_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__5));
lean_inc(v___x_429_);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 2);
lean_ctor_set(v___x_408_, 1, v___x_437_);
lean_ctor_set(v___x_408_, 0, v___x_429_);
v___x_440_ = v___x_408_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_437_);
v___x_440_ = v_reuseFailAlloc_484_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; size_t v_sz_471_; size_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_441_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__8));
v___x_442_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__10);
v___x_443_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__11));
v___x_444_ = l_Lean_addMacroScope(v_quotContext_425_, v___x_443_, v_currMacroScope_426_);
v___x_445_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__13));
lean_inc(v___x_429_);
v___x_446_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_446_, 0, v___x_429_);
lean_ctor_set(v___x_446_, 1, v___x_442_);
lean_ctor_set(v___x_446_, 2, v___x_444_);
lean_ctor_set(v___x_446_, 3, v___x_445_);
lean_inc(v___x_429_);
v___x_447_ = l_Lean_Syntax_node1(v___x_429_, v___x_436_, v___x_446_);
lean_inc(v___x_429_);
v___x_448_ = l_Lean_Syntax_node1(v___x_429_, v___x_441_, v___x_447_);
v___x_449_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__14));
lean_inc(v___x_429_);
v___x_450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_429_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__15));
v___x_452_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__16));
v___x_453_ = 1;
v___x_454_ = l_Lean_SourceInfo_fromRef(v_ifTk_393_, v___x_453_);
v___x_455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_451_);
lean_inc(v___x_429_);
v___x_456_ = l_Lean_Syntax_node2(v___x_429_, v___x_452_, v___x_455_, v_a_420_);
lean_inc(v___x_429_);
v___x_457_ = l_Lean_Syntax_node1(v___x_429_, v___x_436_, v___x_456_);
lean_inc(v___x_429_);
v___x_458_ = l_Lean_Syntax_node1(v___x_429_, v___x_435_, v___x_457_);
lean_inc(v___x_429_);
v___x_459_ = l_Lean_Syntax_node1(v___x_429_, v___x_434_, v___x_458_);
lean_inc(v___x_429_);
v___x_460_ = l_Lean_Syntax_node4(v___x_429_, v___x_438_, v___x_440_, v___x_448_, v___x_450_, v___x_459_);
lean_inc(v___x_429_);
v___x_461_ = l_Lean_Syntax_node1(v___x_429_, v___x_436_, v___x_460_);
lean_inc(v___x_429_);
v___x_462_ = l_Lean_Syntax_node1(v___x_429_, v___x_435_, v___x_461_);
lean_inc(v___x_429_);
v___x_463_ = l_Lean_Syntax_node1(v___x_429_, v___x_434_, v___x_462_);
v___x_464_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
lean_inc(v___x_429_);
v___x_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_429_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
lean_inc_ref(v___x_465_);
lean_inc_ref(v___x_433_);
lean_inc(v___x_429_);
v___x_466_ = l_Lean_Syntax_node3(v___x_429_, v___x_430_, v___x_433_, v___x_463_, v___x_465_);
v___x_467_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17));
lean_inc(v___x_429_);
v___x_468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_429_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l_Array_mkArray2___redArg(v___x_466_, v___x_468_);
v___x_470_ = l_Array_append___redArg(v_snd_406_, v_snd_415_);
lean_dec(v_snd_415_);
v_sz_471_ = lean_array_size(v___x_470_);
v___x_472_ = ((size_t)0ULL);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(v_sz_471_, v___x_472_, v___x_470_);
v___x_474_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19));
v___x_475_ = l_Lean_mkSepArray(v___x_473_, v___x_474_);
lean_dec_ref(v___x_473_);
v___x_476_ = l_Array_append___redArg(v___x_469_, v___x_475_);
lean_dec_ref(v___x_475_);
lean_inc(v___x_429_);
v___x_477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_477_, 0, v___x_429_);
lean_ctor_set(v___x_477_, 1, v___x_436_);
lean_ctor_set(v___x_477_, 2, v___x_476_);
lean_inc(v___x_429_);
v___x_478_ = l_Lean_Syntax_node1(v___x_429_, v___x_435_, v___x_477_);
lean_inc(v___x_429_);
v___x_479_ = l_Lean_Syntax_node1(v___x_429_, v___x_434_, v___x_478_);
v___x_480_ = l_Lean_Syntax_node3(v___x_429_, v___x_430_, v___x_433_, v___x_479_, v___x_465_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_480_);
v___x_482_ = v___x_423_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_a_421_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
else
{
lean_del_object(v___x_417_);
lean_dec(v_snd_415_);
lean_del_object(v___x_408_);
lean_dec(v_snd_406_);
lean_dec_ref(v_a_399_);
return v___x_419_;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_del_object(v___x_408_);
lean_dec(v_snd_406_);
lean_dec(v_fst_405_);
lean_dec_ref(v_a_399_);
lean_dec_ref(v_mkIf_398_);
v_a_488_ = lean_ctor_get(v___x_411_, 0);
v_a_489_ = lean_ctor_get(v___x_411_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_411_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_inc(v_a_488_);
lean_dec(v___x_411_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_488_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref(v_a_399_);
lean_dec_ref(v_mkIf_398_);
lean_dec(v_neg_397_);
lean_dec(v_elseTk_395_);
v_a_498_ = lean_ctor_get(v___x_402_, 0);
v_a_499_ = lean_ctor_get(v___x_402_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_402_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_inc(v_a_498_);
lean_dec(v___x_402_);
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
LEAN_EXPORT lean_object* l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___boxed(lean_object* v_ifTk_507_, lean_object* v_thenTk_508_, lean_object* v_elseTk_509_, lean_object* v_pos_510_, lean_object* v_neg_511_, lean_object* v_mkIf_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(v_ifTk_507_, v_thenTk_508_, v_elseTk_509_, v_pos_510_, v_neg_511_, v_mkIf_512_, v_a_513_, v_a_514_);
lean_dec(v_ifTk_507_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0(lean_object* v___x_523_, lean_object* v___x_524_, lean_object* v_pos_525_, lean_object* v_neg_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_ref_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_ref_529_ = lean_ctor_get(v___y_527_, 5);
v___x_530_ = 0;
v___x_531_ = l_Lean_SourceInfo_fromRef(v_ref_529_, v___x_530_);
v___x_532_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1));
v___x_533_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2));
lean_inc(v___x_531_);
v___x_534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3));
lean_inc(v___x_531_);
v___x_536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_531_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4));
lean_inc(v___x_531_);
v___x_538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_531_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5));
lean_inc(v___x_531_);
v___x_540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_531_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = l_Lean_Syntax_node8(v___x_531_, v___x_532_, v___x_534_, v___x_523_, v___x_536_, v___x_524_, v___x_538_, v_pos_525_, v___x_540_, v_neg_526_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___y_528_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___boxed(lean_object* v___x_543_, lean_object* v___x_544_, lean_object* v_pos_545_, lean_object* v_neg_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0(v___x_543_, v___x_544_, v_pos_545_, v_neg_546_, v___y_547_, v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1(lean_object* v_x_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___closed__1));
lean_inc(v_x_556_);
v___x_560_ = l_Lean_Syntax_isOfKind(v_x_556_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_x_556_);
v___x_561_ = lean_box(1);
v___x_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v_a_558_);
return v___x_562_;
}
else
{
lean_object* v_methods_563_; lean_object* v_quotContext_564_; lean_object* v_currMacroScope_565_; lean_object* v_currRecDepth_566_; lean_object* v_maxRecDepth_567_; lean_object* v_ref_568_; lean_object* v___x_569_; lean_object* v_tk_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v_ttk_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_etk_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_ref_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_methods_563_ = lean_ctor_get(v_a_557_, 0);
v_quotContext_564_ = lean_ctor_get(v_a_557_, 1);
v_currMacroScope_565_ = lean_ctor_get(v_a_557_, 2);
v_currRecDepth_566_ = lean_ctor_get(v_a_557_, 3);
v_maxRecDepth_567_ = lean_ctor_get(v_a_557_, 4);
v_ref_568_ = lean_ctor_get(v_a_557_, 5);
v___x_569_ = lean_unsigned_to_nat(0u);
v_tk_570_ = l_Lean_Syntax_getArg(v_x_556_, v___x_569_);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = l_Lean_Syntax_getArg(v_x_556_, v___x_571_);
v___x_573_ = lean_unsigned_to_nat(3u);
v___x_574_ = l_Lean_Syntax_getArg(v_x_556_, v___x_573_);
v___f_575_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___boxed), 6, 2);
lean_closure_set(v___f_575_, 0, v___x_572_);
lean_closure_set(v___f_575_, 1, v___x_574_);
v___x_576_ = lean_unsigned_to_nat(4u);
v_ttk_577_ = l_Lean_Syntax_getArg(v_x_556_, v___x_576_);
v___x_578_ = lean_unsigned_to_nat(5u);
v___x_579_ = l_Lean_Syntax_getArg(v_x_556_, v___x_578_);
v___x_580_ = lean_unsigned_to_nat(6u);
v_etk_581_ = l_Lean_Syntax_getArg(v_x_556_, v___x_580_);
v___x_582_ = lean_unsigned_to_nat(7u);
v___x_583_ = l_Lean_Syntax_getArg(v_x_556_, v___x_582_);
lean_dec(v_x_556_);
v_ref_584_ = l_Lean_replaceRef(v_tk_570_, v_ref_568_);
lean_inc(v_maxRecDepth_567_);
lean_inc(v_currRecDepth_566_);
lean_inc(v_currMacroScope_565_);
lean_inc(v_quotContext_564_);
lean_inc(v_methods_563_);
v___x_585_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_585_, 0, v_methods_563_);
lean_ctor_set(v___x_585_, 1, v_quotContext_564_);
lean_ctor_set(v___x_585_, 2, v_currMacroScope_565_);
lean_ctor_set(v___x_585_, 3, v_currRecDepth_566_);
lean_ctor_set(v___x_585_, 4, v_maxRecDepth_567_);
lean_ctor_set(v___x_585_, 5, v_ref_584_);
v___x_586_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(v_tk_570_, v_ttk_577_, v_etk_581_, v___x_579_, v___x_583_, v___f_575_, v___x_585_, v_a_558_);
lean_dec(v_tk_570_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_a_588_ = lean_ctor_get(v___x_586_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_586_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_587_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v_a_596_; lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_a_596_ = lean_ctor_get(v___x_586_, 0);
v_a_597_ = lean_ctor_get(v___x_586_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_586_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_inc(v_a_596_);
lean_dec(v___x_586_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_596_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___boxed(lean_object* v_x_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1(v_x_605_, v_a_606_, v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_608_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__0));
v___x_611_ = l_String_toRawSubstring_x27(v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0(lean_object* v___x_614_, lean_object* v___x_615_, lean_object* v_pos_616_, lean_object* v_neg_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_quotContext_620_; lean_object* v_currMacroScope_621_; lean_object* v_ref_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_quotContext_620_ = lean_ctor_get(v___y_618_, 1);
lean_inc(v_quotContext_620_);
v_currMacroScope_621_ = lean_ctor_get(v___y_618_, 2);
lean_inc(v_currMacroScope_621_);
v_ref_622_ = lean_ctor_get(v___y_618_, 5);
lean_inc(v_ref_622_);
lean_dec_ref(v___y_618_);
v___x_623_ = 0;
v___x_624_ = l_Lean_SourceInfo_fromRef(v_ref_622_, v___x_623_);
lean_dec(v_ref_622_);
v___x_625_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__1));
v___x_626_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__2));
lean_inc(v___x_624_);
v___x_627_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_624_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__28));
v___x_629_ = l_Lean_Name_mkStr2(v___x_614_, v___x_628_);
v___x_630_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1, &l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1_once, _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__1);
v___x_631_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0___closed__2));
v___x_632_ = l_Lean_addMacroScope(v_quotContext_620_, v___x_631_, v_currMacroScope_621_);
v___x_633_ = lean_box(0);
lean_inc(v___x_624_);
v___x_634_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_634_, 0, v___x_624_);
lean_ctor_set(v___x_634_, 1, v___x_630_);
lean_ctor_set(v___x_634_, 2, v___x_632_);
lean_ctor_set(v___x_634_, 3, v___x_633_);
lean_inc(v___x_624_);
v___x_635_ = l_Lean_Syntax_node1(v___x_624_, v___x_629_, v___x_634_);
v___x_636_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3));
lean_inc(v___x_624_);
v___x_637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_624_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__4));
lean_inc(v___x_624_);
v___x_639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_624_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__5));
lean_inc(v___x_624_);
v___x_641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_624_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_Syntax_node8(v___x_624_, v___x_625_, v___x_627_, v___x_635_, v___x_637_, v___x_615_, v___x_639_, v_pos_616_, v___x_641_, v_neg_617_);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___y_619_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1(lean_object* v_x_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__0));
v___x_654_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___closed__1));
lean_inc(v_x_650_);
v___x_655_ = l_Lean_Syntax_isOfKind(v_x_650_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_x_650_);
v___x_656_ = lean_box(1);
v___x_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v_a_652_);
return v___x_657_;
}
else
{
lean_object* v_methods_658_; lean_object* v_quotContext_659_; lean_object* v_currMacroScope_660_; lean_object* v_currRecDepth_661_; lean_object* v_maxRecDepth_662_; lean_object* v_ref_663_; lean_object* v___x_664_; lean_object* v_tk_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v_ttk_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_etk_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_ref_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_methods_658_ = lean_ctor_get(v_a_651_, 0);
v_quotContext_659_ = lean_ctor_get(v_a_651_, 1);
v_currMacroScope_660_ = lean_ctor_get(v_a_651_, 2);
v_currRecDepth_661_ = lean_ctor_get(v_a_651_, 3);
v_maxRecDepth_662_ = lean_ctor_get(v_a_651_, 4);
v_ref_663_ = lean_ctor_get(v_a_651_, 5);
v___x_664_ = lean_unsigned_to_nat(0u);
v_tk_665_ = l_Lean_Syntax_getArg(v_x_650_, v___x_664_);
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = l_Lean_Syntax_getArg(v_x_650_, v___x_666_);
v___f_668_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___lam__0), 6, 2);
lean_closure_set(v___f_668_, 0, v___x_653_);
lean_closure_set(v___f_668_, 1, v___x_667_);
v___x_669_ = lean_unsigned_to_nat(2u);
v_ttk_670_ = l_Lean_Syntax_getArg(v_x_650_, v___x_669_);
v___x_671_ = lean_unsigned_to_nat(3u);
v___x_672_ = l_Lean_Syntax_getArg(v_x_650_, v___x_671_);
v___x_673_ = lean_unsigned_to_nat(4u);
v_etk_674_ = l_Lean_Syntax_getArg(v_x_650_, v___x_673_);
v___x_675_ = lean_unsigned_to_nat(5u);
v___x_676_ = l_Lean_Syntax_getArg(v_x_650_, v___x_675_);
lean_dec(v_x_650_);
v_ref_677_ = l_Lean_replaceRef(v_tk_665_, v_ref_663_);
lean_inc(v_maxRecDepth_662_);
lean_inc(v_currRecDepth_661_);
lean_inc(v_currMacroScope_660_);
lean_inc(v_quotContext_659_);
lean_inc(v_methods_658_);
v___x_678_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_678_, 0, v_methods_658_);
lean_ctor_set(v___x_678_, 1, v_quotContext_659_);
lean_ctor_set(v___x_678_, 2, v_currMacroScope_660_);
lean_ctor_set(v___x_678_, 3, v_currRecDepth_661_);
lean_ctor_set(v___x_678_, 4, v_maxRecDepth_662_);
lean_ctor_set(v___x_678_, 5, v_ref_677_);
v___x_679_ = l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse(v_tk_665_, v_ttk_670_, v_etk_674_, v___x_672_, v___x_676_, v___f_668_, v___x_678_, v_a_652_);
lean_dec(v_tk_665_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_a_681_ = lean_ctor_get(v___x_679_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_679_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_680_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v_a_689_; lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_689_ = lean_ctor_get(v___x_679_, 0);
v_a_690_ = lean_ctor_get(v___x_679_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_679_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_inc(v_a_689_);
lean_dec(v___x_679_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_689_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1___boxed(lean_object* v_x_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacIfThenElse__1(v_x_698_, v_a_699_, v_a_700_);
lean_dec_ref(v_a_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1(lean_object* v_x_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__1));
lean_inc(v_x_769_);
v___x_773_ = l_Lean_Syntax_isOfKind(v_x_769_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v_x_769_);
v___x_774_ = lean_box(1);
v___x_775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v_a_771_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = l_Lean_Syntax_getArg(v_x_769_, v___x_777_);
lean_inc(v___x_778_);
v___x_779_ = l_Lean_Syntax_matchesNull(v___x_778_, v___x_776_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; 
lean_inc(v___x_778_);
v___x_780_ = l_Lean_Syntax_matchesNull(v___x_778_, v___x_777_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec(v___x_778_);
lean_dec(v_x_769_);
v___x_781_ = lean_box(1);
v___x_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_a_771_);
return v___x_782_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_783_ = lean_unsigned_to_nat(2u);
v___x_784_ = l_Lean_Syntax_getArg(v_x_769_, v___x_783_);
lean_dec(v_x_769_);
v___x_785_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
lean_inc(v___x_784_);
v___x_786_ = l_Lean_Syntax_isOfKind(v___x_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec(v___x_784_);
lean_dec(v___x_778_);
v___x_787_ = lean_box(1);
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v_a_771_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v_isZero_791_; 
v___x_789_ = l_Lean_Syntax_getArg(v___x_778_, v___x_776_);
lean_dec(v___x_778_);
v___x_790_ = l_Lean_Syntax_toNat(v___x_789_);
lean_dec(v___x_789_);
v_isZero_791_ = lean_nat_dec_eq(v___x_790_, v___x_776_);
if (v_isZero_791_ == 1)
{
lean_object* v_ref_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v___x_790_);
lean_dec(v___x_784_);
v_ref_792_ = lean_ctor_get(v_a_770_, 5);
v___x_793_ = l_Lean_SourceInfo_fromRef(v_ref_792_, v___x_779_);
v___x_794_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__17));
v___x_795_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__18));
lean_inc(v___x_793_);
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_793_);
lean_ctor_set(v___x_796_, 1, v___x_794_);
v___x_797_ = l_Lean_Syntax_node1(v___x_793_, v___x_795_, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v_a_771_);
return v___x_798_;
}
else
{
lean_object* v_ref_799_; lean_object* v_n_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_ref_799_ = lean_ctor_get(v_a_770_, 5);
v_n_800_ = lean_nat_sub(v___x_790_, v___x_777_);
lean_dec(v___x_790_);
v___x_801_ = l_Lean_SourceInfo_fromRef(v_ref_799_, v___x_779_);
v___x_802_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__1));
v___x_803_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_804_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_805_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc(v___x_801_);
v___x_806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_801_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
lean_inc(v___x_801_);
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_801_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
lean_inc(v___x_784_);
lean_inc(v___x_801_);
v___x_809_ = l_Lean_Syntax_node3(v___x_801_, v___x_804_, v___x_806_, v___x_784_, v___x_808_);
v___x_810_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17));
lean_inc(v___x_801_);
v___x_811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_801_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__4));
lean_inc(v___x_801_);
v___x_813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_801_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Nat_reprFast(v_n_800_);
v___x_815_ = lean_box(2);
v___x_816_ = l_Lean_Syntax_mkNumLit(v___x_814_, v___x_815_);
lean_inc(v___x_801_);
v___x_817_ = l_Lean_Syntax_node1(v___x_801_, v___x_803_, v___x_816_);
lean_inc(v___x_801_);
v___x_818_ = l_Lean_Syntax_node3(v___x_801_, v___x_772_, v___x_813_, v___x_817_, v___x_784_);
lean_inc(v___x_801_);
v___x_819_ = l_Lean_Syntax_node3(v___x_801_, v___x_803_, v___x_809_, v___x_811_, v___x_818_);
v___x_820_ = l_Lean_Syntax_node1(v___x_801_, v___x_802_, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v_a_771_);
return v___x_821_;
}
}
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
lean_dec(v___x_778_);
v___x_822_ = lean_unsigned_to_nat(2u);
v___x_823_ = l_Lean_Syntax_getArg(v_x_769_, v___x_822_);
lean_dec(v_x_769_);
v___x_824_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
lean_inc(v___x_823_);
v___x_825_ = l_Lean_Syntax_isOfKind(v___x_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_dec(v___x_823_);
v___x_826_ = lean_box(1);
v___x_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v_a_771_);
return v___x_827_;
}
else
{
lean_object* v_ref_828_; uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_ref_828_ = lean_ctor_get(v_a_770_, 5);
v___x_829_ = 0;
v___x_830_ = l_Lean_SourceInfo_fromRef(v_ref_828_, v___x_829_);
v___x_831_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__3));
v___x_832_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___closed__4));
lean_inc(v___x_830_);
v___x_833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_830_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11));
v___x_835_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_836_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_837_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc(v___x_830_);
v___x_838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_830_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
lean_inc(v___x_830_);
v___x_840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_830_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
lean_inc(v___x_823_);
lean_inc(v___x_830_);
v___x_841_ = l_Lean_Syntax_node3(v___x_830_, v___x_836_, v___x_838_, v___x_823_, v___x_840_);
v___x_842_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17));
lean_inc(v___x_830_);
v___x_843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_830_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__4));
lean_inc(v___x_830_);
v___x_845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_830_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
lean_inc(v___x_830_);
v___x_847_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_847_, 0, v___x_830_);
lean_ctor_set(v___x_847_, 1, v___x_835_);
lean_ctor_set(v___x_847_, 2, v___x_846_);
lean_inc(v___x_830_);
v___x_848_ = l_Lean_Syntax_node3(v___x_830_, v___x_772_, v___x_845_, v___x_847_, v___x_823_);
lean_inc(v___x_830_);
v___x_849_ = l_Lean_Syntax_node3(v___x_830_, v___x_835_, v___x_841_, v___x_843_, v___x_848_);
lean_inc(v___x_830_);
v___x_850_ = l_Lean_Syntax_node1(v___x_830_, v___x_834_, v___x_849_);
lean_inc(v___x_830_);
v___x_851_ = l_Lean_Syntax_node1(v___x_830_, v___x_824_, v___x_850_);
v___x_852_ = l_Lean_Syntax_node2(v___x_830_, v___x_831_, v___x_833_, v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v_a_771_);
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1___boxed(lean_object* v_x_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticIterate__________1(v_x_854_, v_a_855_, v_a_856_);
lean_dec_ref(v_a_855_);
return v_res_857_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_868_ = l_Lean_Parser_Tactic_optConfig;
v___x_869_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__3));
v___x_870_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3));
v___x_871_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_869_);
lean_ctor_set(v___x_871_, 2, v___x_868_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_872_ = l_Lean_Parser_Tactic_rwRuleSeq;
v___x_873_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4, &l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4_once, _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__4);
v___x_874_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3));
v___x_875_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___x_873_);
lean_ctor_set(v___x_875_, 2, v___x_872_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = l_Lean_Parser_Tactic_location;
v___x_877_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__7));
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_876_);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6, &l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6_once, _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__6);
v___x_880_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5, &l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5_once, _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__5);
v___x_881_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticIterate_________00__closed__3));
v___x_882_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_880_);
lean_ctor_set(v___x_882_, 2, v___x_879_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_883_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7, &l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7_once, _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__7);
v___x_884_ = lean_unsigned_to_nat(1022u);
v___x_885_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1));
v___x_886_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
lean_ctor_set(v___x_886_, 2, v___x_883_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticRw__mod__cast______(void){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8, &l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8_once, _init_l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__8);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0(lean_object* v___x_930_, lean_object* v_loc_931_, size_t v_sz_932_, size_t v_i_933_, lean_object* v_bs_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
uint8_t v___x_937_; 
v___x_937_ = lean_usize_dec_lt(v_i_933_, v_sz_932_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
lean_dec(v_loc_931_);
lean_dec(v___x_930_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_bs_934_);
lean_ctor_set(v___x_938_, 1, v___y_936_);
return v___x_938_;
}
else
{
lean_object* v_ref_939_; lean_object* v___x_940_; lean_object* v_v_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_bs_x27_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___y_981_; 
v_ref_939_ = lean_ctor_get(v___y_935_, 5);
v___x_940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1));
v_v_941_ = lean_array_uget(v_bs_934_, v_i_933_);
v___x_942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3));
v___x_943_ = lean_unsigned_to_nat(0u);
v_bs_x27_944_ = lean_array_uset(v_bs_934_, v_i_933_, v___x_943_);
v___x_945_ = 0;
v___x_946_ = l_Lean_SourceInfo_fromRef(v_ref_939_, v___x_945_);
v___x_947_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_948_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc(v___x_946_);
v___x_949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_946_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
v___x_951_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11));
v___x_952_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__5));
v___x_954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__6));
lean_inc(v___x_946_);
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_946_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
lean_inc(v___x_946_);
v___x_957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_957_, 0, v___x_946_);
lean_ctor_set(v___x_957_, 1, v___x_952_);
lean_ctor_set(v___x_957_, 2, v___x_956_);
lean_inc(v___x_946_);
v___x_958_ = l_Lean_Syntax_node1(v___x_946_, v___x_940_, v___x_957_);
v___x_959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__8));
v___x_960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__9));
lean_inc(v___x_946_);
v___x_961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_946_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__11));
v___x_963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__12));
lean_inc(v___x_946_);
v___x_964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_946_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
lean_inc(v___x_946_);
v___x_965_ = l_Lean_Syntax_node1(v___x_946_, v___x_962_, v___x_964_);
lean_inc(v___x_946_);
v___x_966_ = l_Lean_Syntax_node2(v___x_946_, v___x_959_, v___x_961_, v___x_965_);
lean_inc(v___x_946_);
v___x_967_ = l_Lean_Syntax_node1(v___x_946_, v___x_952_, v___x_966_);
lean_inc(v___x_946_);
v___x_968_ = l_Lean_Syntax_node3(v___x_946_, v___x_953_, v___x_955_, v___x_958_, v___x_967_);
v___x_969_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__17));
lean_inc(v___x_946_);
v___x_970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_946_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__14));
v___x_972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__15));
lean_inc(v___x_946_);
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_946_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__16));
lean_inc(v___x_946_);
v___x_975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_946_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
lean_inc(v___x_946_);
v___x_976_ = l_Lean_Syntax_node1(v___x_946_, v___x_952_, v_v_941_);
v___x_977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__17));
lean_inc(v___x_946_);
v___x_978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_946_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
lean_inc(v___x_946_);
v___x_979_ = l_Lean_Syntax_node3(v___x_946_, v___x_942_, v___x_975_, v___x_976_, v___x_978_);
if (lean_obj_tag(v_loc_931_) == 1)
{
lean_object* v_val_995_; lean_object* v___x_996_; 
v_val_995_ = lean_ctor_get(v_loc_931_, 0);
lean_inc(v_val_995_);
v___x_996_ = l_Array_mkArray1___redArg(v_val_995_);
v___y_981_ = v___x_996_;
goto v___jp_980_;
}
else
{
lean_object* v___x_997_; 
v___x_997_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__18));
v___y_981_ = v___x_997_;
goto v___jp_980_;
}
v___jp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; size_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; 
v___x_982_ = l_Array_append___redArg(v___x_956_, v___y_981_);
lean_dec_ref(v___y_981_);
lean_inc(v___x_946_);
v___x_983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_983_, 0, v___x_946_);
lean_ctor_set(v___x_983_, 1, v___x_952_);
lean_ctor_set(v___x_983_, 2, v___x_982_);
lean_inc(v___x_930_);
lean_inc(v___x_946_);
v___x_984_ = l_Lean_Syntax_node4(v___x_946_, v___x_971_, v___x_973_, v___x_930_, v___x_979_, v___x_983_);
lean_inc(v___x_946_);
v___x_985_ = l_Lean_Syntax_node3(v___x_946_, v___x_952_, v___x_968_, v___x_970_, v___x_984_);
lean_inc(v___x_946_);
v___x_986_ = l_Lean_Syntax_node1(v___x_946_, v___x_951_, v___x_985_);
lean_inc(v___x_946_);
v___x_987_ = l_Lean_Syntax_node1(v___x_946_, v___x_950_, v___x_986_);
v___x_988_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
lean_inc(v___x_946_);
v___x_989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_946_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = l_Lean_Syntax_node3(v___x_946_, v___x_947_, v___x_949_, v___x_987_, v___x_989_);
v___x_991_ = ((size_t)1ULL);
v___x_992_ = lean_usize_add(v_i_933_, v___x_991_);
v___x_993_ = lean_array_uset(v_bs_x27_944_, v_i_933_, v___x_990_);
v_i_933_ = v___x_992_;
v_bs_934_ = v___x_993_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___boxed(lean_object* v___x_998_, lean_object* v_loc_999_, lean_object* v_sz_1000_, lean_object* v_i_1001_, lean_object* v_bs_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
size_t v_sz_boxed_1005_; size_t v_i_boxed_1006_; lean_object* v_res_1007_; 
v_sz_boxed_1005_ = lean_unbox_usize(v_sz_1000_);
lean_dec(v_sz_1000_);
v_i_boxed_1006_ = lean_unbox_usize(v_i_1001_);
lean_dec(v_i_1001_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0(v___x_998_, v_loc_999_, v_sz_boxed_1005_, v_i_boxed_1006_, v_bs_1002_, v___y_1003_, v___y_1004_);
lean_dec_ref(v___y_1003_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1(lean_object* v_x_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticRw__mod__cast_______00__closed__1));
lean_inc(v_x_1008_);
v___x_1012_ = l_Lean_Syntax_isOfKind(v_x_1008_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec(v_x_1008_);
v___x_1013_ = lean_box(1);
v___x_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v_a_1010_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = l_Lean_Syntax_getArg(v_x_1008_, v___x_1015_);
v___x_1017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__1));
lean_inc(v___x_1016_);
v___x_1018_ = l_Lean_Syntax_isOfKind(v___x_1016_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v___x_1016_);
lean_dec(v_x_1008_);
v___x_1019_ = lean_box(1);
v___x_1020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_a_1010_);
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1021_ = lean_unsigned_to_nat(2u);
v___x_1022_ = l_Lean_Syntax_getArg(v_x_1008_, v___x_1021_);
v___x_1023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0___closed__3));
lean_inc(v___x_1022_);
v___x_1024_ = l_Lean_Syntax_isOfKind(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec(v___x_1022_);
lean_dec(v___x_1016_);
lean_dec(v_x_1008_);
v___x_1025_ = lean_box(1);
v___x_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v_a_1010_);
return v___x_1026_;
}
else
{
lean_object* v___x_1027_; lean_object* v_loc_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1027_ = l_Lean_Syntax_getArg(v___x_1022_, v___x_1015_);
lean_dec(v___x_1022_);
v___x_1076_ = lean_unsigned_to_nat(3u);
v___x_1077_ = l_Lean_Syntax_getArg(v_x_1008_, v___x_1076_);
lean_dec(v_x_1008_);
v___x_1078_ = l_Lean_Syntax_isNone(v___x_1077_);
if (v___x_1078_ == 0)
{
uint8_t v___x_1079_; 
lean_inc(v___x_1077_);
v___x_1079_ = l_Lean_Syntax_matchesNull(v___x_1077_, v___x_1015_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec(v___x_1077_);
lean_dec(v___x_1027_);
lean_dec(v___x_1016_);
v___x_1080_ = lean_box(1);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_a_1010_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v_loc_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_unsigned_to_nat(0u);
v_loc_1083_ = l_Lean_Syntax_getArg(v___x_1077_, v___x_1082_);
lean_dec(v___x_1077_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_loc_1083_);
v_loc_1029_ = v___x_1084_;
v___y_1030_ = v_a_1009_;
v___y_1031_ = v_a_1010_;
goto v___jp_1028_;
}
}
else
{
lean_object* v___x_1085_; 
lean_dec(v___x_1077_);
v___x_1085_ = lean_box(0);
v_loc_1029_ = v___x_1085_;
v___y_1030_ = v_a_1009_;
v___y_1031_ = v_a_1010_;
goto v___jp_1028_;
}
v___jp_1028_:
{
lean_object* v_rules_1032_; lean_object* v___x_1033_; size_t v_sz_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
v_rules_1032_ = l_Lean_Syntax_getArgs(v___x_1027_);
lean_dec(v___x_1027_);
v___x_1033_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_rules_1032_);
lean_dec_ref(v_rules_1032_);
v_sz_1034_ = lean_array_size(v___x_1033_);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1_spec__0(v___x_1016_, v_loc_1029_, v_sz_1034_, v___x_1035_, v___x_1033_, v___y_1030_, v___y_1031_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1066_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_a_1038_ = lean_ctor_get(v___x_1036_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1040_ = v___x_1036_;
v_isShared_1041_ = v_isSharedCheck_1066_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1066_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_ref_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; size_t v_sz_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v_ref_1042_ = lean_ctor_get(v___y_1030_, 5);
v___x_1043_ = 0;
v___x_1044_ = l_Lean_SourceInfo_fromRef(v_ref_1042_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__21));
v___x_1046_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc(v___x_1044_);
v___x_1047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1044_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__9));
v___x_1049_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__11));
v___x_1050_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_1051_ = lean_obj_once(&l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19, &l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19_once, _init_l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__19);
v_sz_1052_ = lean_array_size(v_a_1037_);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse_spec__0(v_sz_1052_, v___x_1035_, v_a_1037_);
v___x_1054_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___closed__19));
v___x_1055_ = l_Lean_mkSepArray(v___x_1053_, v___x_1054_);
lean_dec_ref(v___x_1053_);
v___x_1056_ = l_Array_append___redArg(v___x_1051_, v___x_1055_);
lean_dec_ref(v___x_1055_);
lean_inc(v___x_1044_);
v___x_1057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1044_);
lean_ctor_set(v___x_1057_, 1, v___x_1050_);
lean_ctor_set(v___x_1057_, 2, v___x_1056_);
lean_inc(v___x_1044_);
v___x_1058_ = l_Lean_Syntax_node1(v___x_1044_, v___x_1049_, v___x_1057_);
lean_inc(v___x_1044_);
v___x_1059_ = l_Lean_Syntax_node1(v___x_1044_, v___x_1048_, v___x_1058_);
v___x_1060_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
lean_inc(v___x_1044_);
v___x_1061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1044_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_node3(v___x_1044_, v___x_1045_, v___x_1047_, v___x_1059_, v___x_1061_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1062_);
v___x_1064_ = v___x_1040_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_a_1038_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_a_1067_ = lean_ctor_get(v___x_1036_, 0);
v_a_1068_ = lean_ctor_get(v___x_1036_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1036_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_inc(v_a_1067_);
lean_dec(v___x_1036_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1067_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1___boxed(lean_object* v_x_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticRw__mod__cast________1(v_x_1086_, v_a_1087_, v_a_1088_);
lean_dec_ref(v_a_1087_);
return v_res_1089_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__11));
v___x_1143_ = l_String_toRawSubstring_x27(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1(lean_object* v_x_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticExact__mod__cast___00__closed__1));
lean_inc(v_x_1154_);
v___x_1158_ = l_Lean_Syntax_isOfKind(v_x_1154_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec_ref(v_a_1155_);
lean_dec(v_x_1154_);
v___x_1159_ = lean_box(1);
v___x_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v_a_1156_);
return v___x_1160_;
}
else
{
lean_object* v_quotContext_1161_; lean_object* v_currMacroScope_1162_; lean_object* v_ref_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_quotContext_1161_ = lean_ctor_get(v_a_1155_, 1);
lean_inc(v_quotContext_1161_);
v_currMacroScope_1162_ = lean_ctor_get(v_a_1155_, 2);
lean_inc(v_currMacroScope_1162_);
v_ref_1163_ = lean_ctor_get(v_a_1155_, 5);
lean_inc(v_ref_1163_);
lean_dec_ref(v_a_1155_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = l_Lean_Syntax_getArg(v_x_1154_, v___x_1164_);
lean_dec(v_x_1154_);
v___x_1166_ = 0;
v___x_1167_ = l_Lean_SourceInfo_fromRef(v_ref_1163_, v___x_1166_);
lean_dec(v_ref_1163_);
v___x_1168_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__0));
v___x_1169_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__1));
lean_inc(v___x_1167_);
v___x_1170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1167_);
lean_ctor_set(v___x_1170_, 1, v___x_1168_);
v___x_1171_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3));
v___x_1172_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4));
lean_inc(v___x_1167_);
v___x_1173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1167_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6));
v___x_1175_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8));
v___x_1176_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc(v___x_1167_);
v___x_1177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1167_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10));
v___x_1179_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12, &l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12);
v___x_1180_ = lean_box(0);
v___x_1181_ = l_Lean_addMacroScope(v_quotContext_1161_, v___x_1180_, v_currMacroScope_1162_);
v___x_1182_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15));
lean_inc(v___x_1167_);
v___x_1183_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1167_);
lean_ctor_set(v___x_1183_, 1, v___x_1179_);
lean_ctor_set(v___x_1183_, 2, v___x_1181_);
lean_ctor_set(v___x_1183_, 3, v___x_1182_);
lean_inc(v___x_1167_);
v___x_1184_ = l_Lean_Syntax_node1(v___x_1167_, v___x_1178_, v___x_1183_);
lean_inc(v___x_1167_);
v___x_1185_ = l_Lean_Syntax_node2(v___x_1167_, v___x_1175_, v___x_1177_, v___x_1184_);
v___x_1186_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3));
lean_inc(v___x_1167_);
v___x_1187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1167_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_1189_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6));
v___x_1190_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16));
lean_inc(v___x_1167_);
v___x_1191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1167_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
lean_inc(v___x_1167_);
v___x_1192_ = l_Lean_Syntax_node1(v___x_1167_, v___x_1189_, v___x_1191_);
lean_inc(v___x_1167_);
v___x_1193_ = l_Lean_Syntax_node1(v___x_1167_, v___x_1188_, v___x_1192_);
v___x_1194_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
lean_inc(v___x_1167_);
v___x_1195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1167_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
lean_inc(v___x_1167_);
v___x_1196_ = l_Lean_Syntax_node5(v___x_1167_, v___x_1174_, v___x_1185_, v___x_1165_, v___x_1187_, v___x_1193_, v___x_1195_);
lean_inc(v___x_1167_);
v___x_1197_ = l_Lean_Syntax_node2(v___x_1167_, v___x_1171_, v___x_1173_, v___x_1196_);
v___x_1198_ = l_Lean_Syntax_node2(v___x_1167_, v___x_1169_, v___x_1170_, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v_a_1156_);
return v___x_1199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1(lean_object* v_x_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticApply__mod__cast___00__closed__1));
lean_inc(v_x_1225_);
v___x_1229_ = l_Lean_Syntax_isOfKind(v_x_1225_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec_ref(v_a_1226_);
lean_dec(v_x_1225_);
v___x_1230_ = lean_box(1);
v___x_1231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v_a_1227_);
return v___x_1231_;
}
else
{
lean_object* v_quotContext_1232_; lean_object* v_currMacroScope_1233_; lean_object* v_ref_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_quotContext_1232_ = lean_ctor_get(v_a_1226_, 1);
lean_inc(v_quotContext_1232_);
v_currMacroScope_1233_ = lean_ctor_get(v_a_1226_, 2);
lean_inc(v_currMacroScope_1233_);
v_ref_1234_ = lean_ctor_get(v_a_1226_, 5);
lean_inc(v_ref_1234_);
lean_dec_ref(v_a_1226_);
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = l_Lean_Syntax_getArg(v_x_1225_, v___x_1235_);
lean_dec(v_x_1225_);
v___x_1237_ = 0;
v___x_1238_ = l_Lean_SourceInfo_fromRef(v_ref_1234_, v___x_1237_);
lean_dec(v_ref_1234_);
v___x_1239_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__0));
v___x_1240_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticApply__mod__cast____1___closed__1));
lean_inc(v___x_1238_);
v___x_1241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1238_);
lean_ctor_set(v___x_1241_, 1, v___x_1239_);
v___x_1242_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__3));
v___x_1243_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__4));
lean_inc(v___x_1238_);
v___x_1244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1238_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__6));
v___x_1246_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__8));
v___x_1247_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__22));
lean_inc(v___x_1238_);
v___x_1248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1238_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__10));
v___x_1250_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12, &l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12_once, _init_l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__12);
v___x_1251_ = lean_box(0);
v___x_1252_ = l_Lean_addMacroScope(v_quotContext_1232_, v___x_1251_, v_currMacroScope_1233_);
v___x_1253_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__15));
lean_inc(v___x_1238_);
v___x_1254_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1238_);
lean_ctor_set(v___x_1254_, 1, v___x_1250_);
lean_ctor_set(v___x_1254_, 2, v___x_1252_);
lean_ctor_set(v___x_1254_, 3, v___x_1253_);
lean_inc(v___x_1238_);
v___x_1255_ = l_Lean_Syntax_node1(v___x_1238_, v___x_1249_, v___x_1254_);
lean_inc(v___x_1238_);
v___x_1256_ = l_Lean_Syntax_node2(v___x_1238_, v___x_1246_, v___x_1248_, v___x_1255_);
v___x_1257_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacDepIfThenElse__1___lam__0___closed__3));
lean_inc(v___x_1238_);
v___x_1258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1238_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__13));
v___x_1260_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__6));
v___x_1261_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Init__TacticsExtra______macroRules__Lean__Parser__Tactic__tacticExact__mod__cast____1___closed__16));
lean_inc(v___x_1238_);
v___x_1262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1238_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_inc(v___x_1238_);
v___x_1263_ = l_Lean_Syntax_node1(v___x_1238_, v___x_1260_, v___x_1262_);
lean_inc(v___x_1238_);
v___x_1264_ = l_Lean_Syntax_node1(v___x_1238_, v___x_1259_, v___x_1263_);
v___x_1265_ = ((lean_object*)(l___private_Init_TacticsExtra_0__Lean_Parser_Tactic_expandIfThenElse___lam__0___closed__23));
lean_inc(v___x_1238_);
v___x_1266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1238_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
lean_inc(v___x_1238_);
v___x_1267_ = l_Lean_Syntax_node5(v___x_1238_, v___x_1245_, v___x_1256_, v___x_1236_, v___x_1258_, v___x_1264_, v___x_1266_);
lean_inc(v___x_1238_);
v___x_1268_ = l_Lean_Syntax_node2(v___x_1238_, v___x_1242_, v___x_1244_, v___x_1267_);
v___x_1269_ = l_Lean_Syntax_node2(v___x_1238_, v___x_1240_, v___x_1241_, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v_a_1227_);
return v___x_1270_;
}
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
